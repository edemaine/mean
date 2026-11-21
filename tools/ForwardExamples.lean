import Mean.Render
import Lean.Elab.Frontend

/-! Read the forward tests' elaboration records without adding display commands to the tests. -/

open Lean Elab

private structure Comparison where
  range : Syntax.Range
  output : String

private def authoredRange? (stx : Syntax) : Option Syntax.Range := do
  guard (stx.getHeadInfo matches .original ..)
  stx.getRange? true

private def isMean (stx : Syntax) : Bool :=
  stx.getKind.getRoot == `Mean

private def termText? (ctx : ContextInfo) (term : TermInfo) : IO (Option String) :=
  term.runMetaM ctx do
    let e ← instantiateMVars term.expr
    if e.hasMVar || e.hasSorry then return none
    let showNumericType := e.isLit || e.isAppOf ``OfNat.ofNat || e.isAppOf ``Neg.neg
    withOptions (fun opts => opts.setBool `pp.numericTypes showNumericType
      |>.setBool `pp.coercions.types true |>.setBool `pp.funBinderTypes true
      |>.setBool `mean.renderProperties false) do
      return some (← Meta.ppExpr e).pretty

private def lookupTerm (terms : Array (ContextInfo × TermInfo)) (stx : Syntax) : IO String := do
  let some range := authoredRange? stx | throw (IO.userError "expected an original example term")
  for (ctx, term) in terms do
    let some candidate := term.stx.getRange? true | continue
    if range.start == candidate.start && range.stop == candidate.stop then
      if let some text ← termText? ctx term then return text
  throw (IO.userError s!"missing elaboration record for Mean input at byte {range.start.byteIdx}: {stx.reprint.getD ""}")

private def declarationRanges (ctx : ContextInfo) :
    IO (Std.HashMap Nat ConstantInfo) := ctx.runCoreM do
  let mut result := {}
  for (name, info) in ctx.env.constants.map₂.toList do
    match info with
    | .defnInfo _ | .thmInfo _ | .axiomInfo _ | .inductInfo _ =>
      if let some loc ← findDeclarationRangesCore? name then
        let pos := ctx.fileMap.ofPosition loc.range.pos
        result := result.insertIfNew pos.byteIdx info
    | _ => pure ()
  return result

private def comparisons (trees : PersistentArray InfoTree) (file : ContextInfo) :
    IO (Array Comparison) := do
  let declarations ← declarationRanges file
  let mut results := #[]
  for tree in trees do
    let terms := tree.foldInfo (init := #[]) fun ctx info entries =>
      match info with
      | .ofTermInfo term => if term.isBinder then entries else entries.push (ctx, term)
      | _ => entries
    let commands := tree.foldInfo (init := #[]) fun ctx info entries =>
      match info with
      | .ofCommandInfo command => if isMean command.stx then entries.push (ctx, command.stx) else entries
      | _ => entries
    let mut covered : Array Syntax.Range := #[]
    for (ctx, command) in commands do
      let some range := authoredRange? command | continue
      if covered.any (·.start == range.start) then continue
      covered := covered.push range
      let output ← match command with
        | `(command| Example: $statement:term Proof: $body:term) => do
          let statement ← lookupTerm terms statement
          -- The proof is already Lean and may be a tactic script.
          let some bodyRange := authoredRange? body
            | throw (IO.userError "expected an original example proof")
          let body := String.Pos.Raw.extract file.fileMap.source bodyRange.start bodyRange.stop
          pure (some s!"example : {statement} :=\n  {body.replace "\n" "\n  "}")
        | _ =>
          match declarations.get? range.start.byteIdx with
          | some info =>
            let ctx := { ctx with env := ctx.cmdEnv?.getD file.env }
            some <$> ctx.runMetaM {} (Term.TermElabM.run' do
              withOptions (fun opts => opts.setBool `mean.renderProperties false) do
                Mean.Render.leanDeclarationText info)
          | none => pure none
      if let some output := output then
        results := results.push { range, output }
    -- Choose the outermost authored Mean expressions in each test. A translated
    -- declaration already includes its own expressions.
    let candidates := terms.filterMap fun (ctx, term) => do
      guard (isMean term.stx)
      let range ← authoredRange? term.stx
      guard (!covered.any fun outer => outer.start <= range.start && range.stop <= outer.stop)
      some (range, ctx, term)
    let candidates := candidates.toList.mergeSort fun (r, _, _) (s, _, _) =>
      r.start < s.start || (r.start == s.start && s.stop <= r.stop)
    let mut stop := ({ byteIdx := 0 } : String.Pos.Raw)
    for (range, ctx, term) in candidates do
      if range.start < stop then continue
      if let some output ← termText? ctx term then
        results := results.push { range, output }
        stop := range.stop
  return results.qsort fun left right => left.range.start < right.range.start

unsafe def main (args : List String) : IO Unit := do
  let [sourcePath] := args | throw (IO.userError "expected the forward example source path")
  enableInitializersExecution
  let source := (← IO.FS.readFile sourcePath).replace "\r\n" "\n"
  let input := Parser.mkInputContext source sourcePath
  let (header, state, messages) ← Parser.parseHeader input
  -- Keep intentionally unused named binders in the tests.
  let opts := ({} : Options).setBool `Elab.async false |>.setBool `linter.unusedVariables false
  let (env, messages) ← processHeader header opts messages input (mainModule := `Examples.MeanToLean)
  let result ← IO.processCommands input state (Command.mkState env messages opts)
  for message in result.commandState.messages.toList do
    IO.println (← message.toJson).compress
  if result.commandState.messages.hasErrors then return
  let file : ContextInfo := { env := result.commandState.env, fileMap := input.fileMap, ngen := {} }
  for entry in (← comparisons result.commandState.infoState.trees file) do
    let input := String.Pos.Raw.extract file.fileMap.source entry.range.start entry.range.stop
    let data := s!"\n-- MEAN INPUT:\n{input}\n-- LEAN OUTPUT:\n{entry.output}"
    let pos := file.fileMap.toPosition entry.range.start
    IO.println (Json.mkObj [("severity", toJson "information"), ("pos", toJson pos), ("data", toJson data)]).compress
