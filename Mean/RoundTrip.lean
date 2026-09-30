import Mean.Syntax

/-! Check rendered text against an original elaborated expression. -/

namespace Mean.RoundTrip
open Lean Meta Elab Term

private def parseText (category : Name) (text : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) category text with
  | .ok stx => return stx
  | .error message => throwError "Mean renderer produced unparseable text:\n{message}\n{text}"

/-- Check actual printed text, not just an intermediate syntax tree.
The kernel checks an equality certificate after elaboration and metavariable checks. -/
def checkText (original : Expr) (text : String) (category : Name := `term) : TermElabM Unit := do
  let stx ← parseText category text
  let graphSubject := match stx with
    | `(command| Definition: a simple graph $_:ident is $_:ident if $_:term .) => true
    | `(command| Definition: a simple graph $_:ident = ($_:ident, $_:ident)
        is $_:ident if $_:term .) => true
    | _ => false
  let term ← if category == `command then
    match stx with
    | `(command| Definition: $subject:meanSubject is $_:ident if $body:term .) =>
      `(predicateOn% $subject => $body)
    | `(command| def $_:ident : $ty:term := $body:term) => `(($body : $ty))
    | _ => throwError "unsupported rendered declaration"
  else if category == `meanTheoremStatement then
    match stx with
    | `(meanTheoremStatement| Theorem $_:ident : $statement:term) => pure statement
    | _ => throwError "unsupported rendered theorem statement"
  else pure ⟨stx⟩
  let expected ← if graphSubject then pure none else pure (some (← inferType original))
  let reparsed ← elabTermEnsuringType term expected (implicitLambda := false)
  synthesizeSyntheticMVarsNoPostponing
  let mut reparsed ← instantiateMVars reparsed
  -- Type* creates a fresh rigid universe parameter. Declaration-level comparison
  -- permits alpha-renaming this parameter, but never specializing it to Type 0
  -- or collapsing multiple universe parameters into one.
  if graphSubject then
    match original.consumeMData, reparsed.consumeMData with
    | .lam _ (.sort (.succ (.param source))) _ _,
      .lam _ (.sort (.succ (.param target))) _ _ =>
        reparsed := reparsed.instantiateLevelParams [target] [.param source]
    | _, _ => throwError "Mean graph subject would change the universe signature"
  if original.hasSorry || reparsed.hasSorry then
    throwError "Mean round-trip check refuses expressions containing sorry"
  if reparsed.hasMVar || original.hasMVar then
    throwError "Mean round-trip check has unresolved metavariables:\n{text}\n{reparsed}"
  unless ← isDefEq original reparsed do
    throwError "Mean round-trip check failed: rendered text changed the expression"
  let equality ← mkEq original reparsed
  let certificate := mkApp (mkLambda `certificate .default equality (mkBVar 0))
    (← mkEqRefl original)
  -- Section variables may still carry assigned universe metavariables in their
  -- local declarations; the kernel needs the instantiated context as well.
  let lctx ← instantiateLCtxMVars (← getLCtx)
  withLCtx' lctx do checkWithKernel certificate

end Mean.RoundTrip
