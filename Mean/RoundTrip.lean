import Mean.Syntax

/-! Check rendered text against an original elaborated expression. -/

namespace Mean.RoundTrip
open Lean Meta Elab Term

private def parseText (category : Name) (text : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) category text with
  | .ok stx => return stx
  | .error message => throwError "Mean renderer produced unparseable text:\n{message}\n{text}"

/-- Kernel definitional equality ignores binder information. Function rendering
must also preserve which arguments Lean expects callers to supply or infer. -/
private partial def checkFunctionBinders (original reparsed : Expr) : TermElabM Unit := do
  let original := original.consumeMData
  let reparsed := reparsed.consumeMData
  match original, reparsed with
  | .letE _ _ value body _, _ => checkFunctionBinders (body.instantiate1 value) reparsed
  | _, .letE _ _ value body _ => checkFunctionBinders original (body.instantiate1 value)
  | .lam _ ty body bi, .lam _ ty' body' bi'
  | .forallE _ ty body bi, .forallE _ ty' body' bi' =>
    unless bi == bi' do
      throwError "Mean round-trip changed function argument implicitness"
    checkFunctionBinders ty ty'
    checkFunctionBinders body body'
  | _, _ => pure ()

/-- Expression equality is one part of the contract, separate from declaration metadata. -/
private def checkExpressions (original reparsed : Expr) (text : String) : TermElabM Unit := do
  if original.hasSorry || reparsed.hasSorry then
    throwError "Mean round-trip check refuses expressions containing sorry"
  if reparsed.hasMVar || original.hasMVar then
    throwError "Mean round-trip check has unresolved metavariables:\n{text}\n{reparsed}"
  checkFunctionBinders original reparsed
  unless ← isDefEq original reparsed do
    throwError "Mean round-trip check failed: rendered text changed the expression"
  let equality ← mkEq original reparsed
  let certificate := mkApp (mkLambda `certificate .default equality (mkBVar 0))
    (← mkEqRefl original)
  let lctx ← instantiateLCtxMVars (← getLCtx)
  withLCtx' lctx do checkWithKernel certificate

private def checkValueText (original : Expr) (text : String) (category : Name)
    (abbreviation := false) : TermElabM Unit := do
  let stx ← parseText category text
  let graphSubject := match stx with
    | `(command| Definition: a simple graph $_:ident is $_:ident if $_:term .) => true
    | `(command| Abbreviation: a simple graph $_:ident is $_:ident if $_:term .) => true
    | `(command| Definition: a simple graph $_:ident = ($_:ident, $_:ident)
        is $_:ident if $_:term .) => true
    | `(command| Abbreviation: a simple graph $_:ident = ($_:ident, $_:ident)
        is $_:ident if $_:term .) => true
    | _ => false
  let (term, actualAbbreviation) ← if category == `command then
    match stx with
    | `(command| Definition: $subject:meanSubject is $_:ident if $body:term .) => do
      pure (← `(predicateOn% $subject => $body), false)
    | `(command| Abbreviation: $subject:meanSubject is $_:ident if $body:term .) => do
      pure (← `(predicateOn% $subject => $body), true)
    | `(command| Definition: $_:ident is $value:term .) => pure (value, false)
    | `(command| Abbreviation: $_:ident is $value:term .) => pure (value, true)
    | `(command| def $_:ident : $ty:term := $body:term) => do
      pure (← `(($body : $ty)), false)
    | `(command| abbrev $_:ident : $ty:term := $body:term) => do
      pure (← `(($body : $ty)), true)
    | _ => throwError "unsupported rendered declaration"
  else if category == `meanTheoremStatement then
    match stx with
    | `(meanTheoremStatement| Theorem $_:ident : $statement:term) => pure (statement, false)
    | _ => throwError "unsupported rendered theorem statement"
  else pure (⟨stx⟩, false)
  unless category != `command || actualAbbreviation == abbreviation do
    throwError "Mean round-trip changed the declaration's abbreviation status"
  -- A declaration must infer its type from the printed text, just as a new def
  -- would. Supplying the original type could hide a missing type annotation.
  let expected ← if category == `command then pure none else pure (some (← inferType original))
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
  checkExpressions original reparsed text

/-- Check an expression or theorem statement against its parsed text.
Commands require `checkDefinition`, which also checks the actual declaration. -/
def checkText (original : Expr) (text : String) (category : Name := `term) : TermElabM Unit := do
  if category == `command then
    throwError "use checkDefinition for declarations or checkDefinitionValue for value-only probes"
  checkValueText original text category

/-- A value-only check used to choose annotations; this does not validate a declaration.
Final definition output must also pass `checkDefinition`. -/
def checkDefinitionValue (original : Expr) (text : String) (abbreviation := false) : TermElabM Unit :=
  checkValueText original text `command abbreviation

/-- Rename only the declaration being introduced, leaving its printed body intact. -/
private def renameDefinition (stx : Syntax) (name : Ident) : TermElabM (TSyntax `command) := do
  match stx with
  | `(command| Definition: $subject:meanSubject is $_:ident if $body:term .) =>
    `(command| Definition: $subject is $name if $body .)
  | `(command| Abbreviation: $subject:meanSubject is $_:ident if $body:term .) =>
    `(command| Abbreviation: $subject is $name if $body .)
  | `(command| Definition: $_:ident is $value:term .) =>
    `(command| Definition: $name is $value .)
  | `(command| Abbreviation: $_:ident is $value:term .) =>
    `(command| Abbreviation: $name is $value .)
  | `(command| def $_:ident : $ty:term := $body:term) =>
    `(command| def $name : $ty := $body)
  | `(command| abbrev $_:ident : $ty:term := $body:term) =>
    `(command| abbrev $name : $ty := $body)
  | _ => throwError "unsupported rendered declaration"

/-- Elaborate the actual output as a temporary declaration and inspect the result.
Expected metadata comes from the original environment, not from the renderer.
The temporary declaration, messages, and elaboration state are always discarded. -/
def checkDefinition (originalName : Name) (text : String) : TermElabM Unit :=
  withoutModifyingState do
    let .defnInfo original ← getConstInfo originalName
      | throwError "Mean declaration checker expects a definition or abbreviation"
    let stx ← parseText `command text
    let fresh ← mkFreshUserName `meanRoundTrip
    let renamed ← renameDefinition stx (mkIdent fresh)
    let currNamespace ← getCurrNamespace
    let openDecls ← getOpenDecls
    let levelNames := original.levelParams
    let actualName := currNamespace ++ fresh
    liftCommandElabM do
      -- Module declarations default to private; keep the temporary name predictable.
      Command.withScope (fun scope =>
          { scope with currNamespace, openDecls, levelNames, isPublic := true }) do
        Command.elabCommand renamed
    let .defnInfo actual ← getConstInfo actualName
      | throwError "Mean round-trip changed the declaration kind"
    unless original.hints.isAbbrev == actual.hints.isAbbrev do
      throwError "Mean round-trip changed the declaration's abbreviation status"
    unless (← getReducibilityStatus originalName) == (← getReducibilityStatus actualName) do
      throwError "Mean round-trip changed the declaration's reducibility"
    unless original.safety == actual.safety do
      throwError "Mean round-trip changed the declaration's safety"
    unless original.levelParams.length == actual.levelParams.length do
      throwError "Mean round-trip changed the declaration's universe signature"
    let levels := original.levelParams.map Level.param
    let actualType := actual.type.instantiateLevelParams actual.levelParams levels
    let actualValue := actual.value.instantiateLevelParams actual.levelParams levels
    checkExpressions original.type actualType text
    checkExpressions original.value actualValue text

end Mean.RoundTrip
