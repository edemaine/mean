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

private def parameterNameFailureTag : Name := `Mean.RoundTrip.parameterNames

/-- Stable failure classification, independent of the diagnostic's wording. -/
def isParameterNameFailure (ex : Exception) : Bool :=
  ex.toMessageData.hasTag (· == parameterNameFailureTag)

/-- Named arguments are a declaration interface, even for unused parameters.
Anonymous and hygienically generated names carry no public spelling to preserve. -/
private partial def checkParameterNames (original reparsed : Expr) : TermElabM Unit := do
  let original ← whnf original
  let reparsed ← whnf reparsed
  match original, reparsed with
  | .forallE name ty body bi, .forallE name' ty' body' bi' =>
    unless bi == bi' do
      throwError "Mean round-trip changed function argument implicitness"
    if !name.isAnonymous && !name.hasMacroScopes && !name.isInaccessibleUserName && name != name' then
      throwError (.tagged parameterNameFailureTag m!"Mean round-trip changed a named parameter")
    checkParameterNames ty ty'
    withLocalDecl name bi ty fun x =>
      checkParameterNames (body.instantiate1 x) (body'.instantiate1 x)
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

/-- Inspect a declaration once, retaining its original syntax for the full audit. -/
private structure DeclarationView where
  value : Term
  abbreviation : Bool
  graphSubject : Bool := false
  rename : Ident → TermElabM (TSyntax `command)

private def isGraphSubject (subject : TSyntax `meanSubject) : Bool :=
  match subject with
  | `(meanSubject| a simple graph $[$_:ident]?)
  | `(meanSubject| a simple graph $[$_:ident]? = ($_:ident, $_:ident)) => true
  | _ => false

private def declarationView (stx : Syntax) : TermElabM DeclarationView := do
  match stx with
  | `(command| Definition: a $_:ident is $description:meanWitness .) =>
    return {
      value := (← `(anonymousType% $description))
      abbreviation := false
      rename := fun name => `(command| Definition: a $name is $description .)
    }
  | `(command| Definition: an $_:ident is $description:meanWitness .) =>
    return {
      value := (← `(anonymousType% $description))
      abbreviation := false
      rename := fun name => `(command| Definition: an $name is $description .)
    }
  | `(command| Definition: $subject:meanSubject satisfies $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOn% $subject => $body))
      abbreviation := false
      graphSubject := isGraphSubject subject
      rename := fun name => `(command| Definition: $subject satisfies $name if $body .)
    }
  | `(command| Definition: $subject:meanSubject is $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOn% $subject => $body))
      abbreviation := false
      graphSubject := isGraphSubject subject
      rename := fun name => `(command| Definition: $subject is $name if $body .)
    }
  | `(command| Definition: $subjects:meanPredicateSubjects satisfy $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOver% $subjects => $body))
      abbreviation := false
      rename := fun name => `(command| Definition: $subjects satisfy $name if $body .)
    }
  | `(command| Definition: $subjects:meanPredicateSubjects are $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOver% $subjects => $body))
      abbreviation := false
      rename := fun name => `(command| Definition: $subjects are $name if $body .)
    }
  | `(command| Definition: $_:ident is $value:term .) =>
    return {
      value
      abbreviation := false
      rename := fun name => `(command| Definition: $name is $value .)
    }
  | `(command| Abbreviation: a $_:ident is $description:meanWitness .) =>
    return {
      value := (← `(anonymousType% $description))
      abbreviation := true
      rename := fun name => `(command| Abbreviation: a $name is $description .)
    }
  | `(command| Abbreviation: an $_:ident is $description:meanWitness .) =>
    return {
      value := (← `(anonymousType% $description))
      abbreviation := true
      rename := fun name => `(command| Abbreviation: an $name is $description .)
    }
  | `(command| Abbreviation: $subject:meanSubject satisfies $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOn% $subject => $body))
      abbreviation := true
      graphSubject := isGraphSubject subject
      rename := fun name => `(command| Abbreviation: $subject satisfies $name if $body .)
    }
  | `(command| Abbreviation: $subject:meanSubject is $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOn% $subject => $body))
      abbreviation := true
      graphSubject := isGraphSubject subject
      rename := fun name => `(command| Abbreviation: $subject is $name if $body .)
    }
  | `(command| Abbreviation: $subjects:meanPredicateSubjects satisfy $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOver% $subjects => $body))
      abbreviation := true
      rename := fun name => `(command| Abbreviation: $subjects satisfy $name if $body .)
    }
  | `(command| Abbreviation: $subjects:meanPredicateSubjects are $_:ident if $body:term .) =>
    return {
      value := (← `(predicateOver% $subjects => $body))
      abbreviation := true
      rename := fun name => `(command| Abbreviation: $subjects are $name if $body .)
    }
  | `(command| Abbreviation: $_:ident is $value:term .) =>
    return {
      value
      abbreviation := true
      rename := fun name => `(command| Abbreviation: $name is $value .)
    }
  | `(command| def $_:ident : $ty:term := $body:term) =>
    return {
      value := (← `(($body : $ty)))
      abbreviation := false
      rename := fun name => `(command| def $name : $ty := $body)
    }
  | `(command| abbrev $_:ident : $ty:term := $body:term) =>
    return {
      value := (← `(($body : $ty)))
      abbreviation := true
      rename := fun name => `(command| abbrev $name : $ty := $body)
    }
  | _ => throwError "unsupported rendered declaration"

private def checkValueText (original : Expr) (text : String) (category : Name)
    (abbreviation := false) : TermElabM Unit := do
  let stx ← parseText category text
  let declaration ← if category == `command then some <$> declarationView stx else pure none
  let graphSubject := declaration.any (·.graphSubject)
  let (term, actualAbbreviation) ← if let some declaration := declaration then
    pure (declaration.value, declaration.abbreviation)
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

/-- Elaborate the actual output as a temporary declaration and inspect the result.
Expected metadata comes from the original environment, not from the renderer.
The temporary declaration, messages, and elaboration state are always discarded. -/
def checkDefinition (originalName : Name) (text : String) : TermElabM Unit :=
  withoutModifyingState do
    let .defnInfo original ← getConstInfo originalName
      | throwError "Mean declaration checker expects a definition or abbreviation"
    let stx ← parseText `command text
    let fresh ← mkFreshUserName `meanRoundTrip
    let renamed ← (← declarationView stx).rename (mkIdent fresh)
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
    checkParameterNames original.type actualType
    if (← whnf original.type).isSort then
      checkParameterNames original.value actualValue

/-- Audit a complete single inductive declaration, including constructor order,
parameters, indices, safety, universes, and public binder names. -/
def checkInductive (originalName : Name) (text : String) : TermElabM Unit :=
  withoutModifyingState do
    let .inductInfo original ← getConstInfo originalName
      | throwError "expected an inductive type"
    if isStructure (← getEnv) originalName || isClass (← getEnv) originalName then
      throwError "expected an ordinary inductive type, not a structure or class"
    let stx ← parseText `command text
    let some printedName := inductiveDeclarationName? stx
      | throwError "unsupported rendered inductive declaration"
    let fresh ← mkFreshUserName `meanInductive
    let ns ← getCurrNamespace
    let actualName := ns ++ fresh
    let declaredName := ns ++ printedName.getId
    let renameSelf (stx : Syntax) : Syntax := stx.rewriteBottomUp fun node =>
      if node.isIdent && (node.getId == printedName.getId || node.getId == declaredName ||
          node.getId == (`_root_ ++ declaredName)) then mkIdent fresh else node
    let command : TSyntax `command := ⟨renameSelf stx⟩
    let openDecls ← getOpenDecls
    liftCommandElabM do
      Command.withScope (fun scope => { scope with
          currNamespace := ns
          openDecls := openDecls
          levelNames := original.levelParams
          isPublic := true }) do
        Command.elabCommand command
    let .inductInfo actual ← getConstInfo actualName
      | throwError "Mean round-trip changed the declaration kind"
    if isStructure (← getEnv) actualName || isClass (← getEnv) actualName then
      throwError "Mean round-trip changed the declaration kind"
    unless original.numParams == actual.numParams && original.numIndices == actual.numIndices &&
        original.isUnsafe == actual.isUnsafe && original.isRec == actual.isRec &&
        original.isReflexive == actual.isReflexive && original.ctors.length == actual.ctors.length &&
        original.all.length == actual.all.length && original.numNested == actual.numNested &&
        original.levelParams.length == actual.levelParams.length do
      throwError "Mean round-trip changed the inductive signature"
    let normalize (e : Expr) : Expr :=
      (e.instantiateLevelParams actual.levelParams (original.levelParams.map Level.param)).replace fun e =>
        match e with
        | .const n levels => if n == actualName then some (.const originalName levels) else none
        | _ => none
    checkExpressions original.type (normalize actual.type) text
    checkParameterNames original.type (normalize actual.type)
    for (before, after) in original.ctors.zip actual.ctors do
      -- Lean moves the temporary name's hygiene suffix after the constructor name.
      unless before.eraseMacroScopes.replacePrefix originalName.eraseMacroScopes .anonymous ==
          after.eraseMacroScopes.replacePrefix actualName.eraseMacroScopes .anonymous do
        throwError "Mean round-trip changed constructor names or order"
      let .ctorInfo before ← getConstInfo before | throwError "expected constructor"
      let .ctorInfo after ← getConstInfo after | throwError "expected constructor"
      if (after.type.find? (·.isConstOf originalName)).isSome then
        throwError "Mean round-trip retained the old type instead of recursive self references"
      checkExpressions before.type (normalize after.type) text
      checkParameterNames before.type (normalize after.type)


end Mean.RoundTrip
