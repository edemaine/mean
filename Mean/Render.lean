import Mean.RoundTrip

/-! An independent renderer of elaborated expressions, with checked text round trips.
Import this module and use `#mean declaration` or `#mean_term proposition`.
No declarations are added by the checker. -/

register_option mean.renderProperties : Bool := {
  defValue := false
  descr := "Render registered Mean property phrases inside expressions"
}

namespace Mean.Render
open Lean Meta Elab Term

-- These delaborators run only for the Mean view, leaving ordinary Lean output intact.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.SimpleGraph.edgeSet, delab app.SimpleGraph.V,
  delab app.SimpleGraph.neighborSet, delab app.SimpleGraph.incidenceSet]
def delabProperty : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  let e ← getExpr
  if e.isAppOfArity ``SimpleGraph.edgeSet 2 then
    let g ← withAppArg delab
    `(the edge set of $g)
  else if e.isAppOfArity ``SimpleGraph.V 2 then
    let g ← withAppArg delab
    `(the vertex type of $g)
  else if e.isAppOfArity ``SimpleGraph.neighborSet 3 then
    let g ← withAppFn <| withAppArg delab
    let v ← withAppArg delab
    `(the set of neighbors of $v in $g)
  else if e.isAppOfArity ``SimpleGraph.incidenceSet 3 then
    let g ← withAppFn <| withAppArg delab
    let v ← withAppArg delab
    `(the set of edges incident to $v in $g)
  else failure

private def freshName (suggestion : Name) : MetaM Name := do
  let base := suggestion.eraseMacroScopes
  let base := if base.isAnonymous || base == `_ then `x else base
  return (← getLCtx).getUnusedName base

private def nameText (n : Name) : MetaM String := do
  let s := n.toString
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok stx => if stx.isIdent && stx.getId == n then return s
  | .error _ => pure ()
  return "«" ++ s ++ "»"

/-- Ordinary Lean is the fallback, always delaborated in the current local context. -/
private def leanText (e : Expr) : MetaM String := do
  withOptions (fun opts => opts.setBool `pp.coercions.types true |>.setBool `pp.funBinderTypes true) do
    return (← Meta.ppExpr e).pretty

/-- Translate properties recursively even inside otherwise ordinary Lean syntax. -/
private def propertyText (e : Expr) : MetaM String :=
  withOptions (fun opts => opts.setBool `mean.renderProperties true) (leanText e)

/-- Explicit names inside function types are part of their named-argument interface. -/
private def typeText (e : Expr) : MetaM String :=
  withOptions (fun opts => opts.setBool `pp.piBinderNames true
    |>.setBool `pp.piBinderNames.hygienic false) (propertyText e)

private def publicParameterName (n : Name) : Bool :=
  !n.isAnonymous && !n.hasMacroScopes && !n.isInaccessibleUserName

private def atomText (e : Expr) (propertySubject := false) : MetaM String := do
  let text ← propertyText e
  if e.isFVar || e.isConst || e.isLit then return text
  -- Property phrases bind tightly enough to be adjective subjects, but not application arguments.
  if propertySubject then
    match Parser.runParserCategory (← getEnv) `term text with
    | .ok stx =>
      match stx with
      | `(the $_:meanProperty of $_:term) => return text
      | `(the $_:meanVertexProperty $_:term in $_:term) => return text
      | _ => pure ()
    | .error _ => pure ()
  return "(" ++ text ++ ")"

private def typeAtomText (e : Expr) : MetaM String :=
  withOptions (fun opts => opts.setBool `pp.piBinderNames true
    |>.setBool `pp.piBinderNames.hygienic false) (atomText e)

private def indented (s : String) : String :=
  "  " ++ s.replace "\n" "\n  "

/-- Subject types accept applications and sorts without grouping.
Probe the surrounding grammar to protect types containing binder separators. -/
private def subjectTypeText (e : Expr) : MetaM String := do
  let text ← typeText e
  let probe := s!"the function mapping an element typeProbe of {text} and a boolean binderProbe to binderProbe"
  match Parser.runParserCategory (← getEnv) `term probe with
  | .ok stx =>
    match stx with
    | `(the function mapping an element $_:ident of $_:term and a boolean $_:ident to $_:term) =>
      return text
    | _ => pure ()
  | .error _ => pure ()
  return "(" ++ text ++ ")"

/-- Only protect a sentence-ending expression when punctuation requires it
(e.g. a numeral before the period or a compound field projection). -/
private def sentenceTail (text : String) (ending : Bool) : MetaM String := do
  if !ending then return text
  let probe := s!"Definition: a natural number n is renderProbe if {text}."
  match Parser.runParserCategory (← getEnv) `command probe with
  | .ok _ => return text
  | .error _ => return "(" ++ text ++ ")"

private def leafText (e : Expr) (ending : Bool) : MetaM String := do
  sentenceTail (← propertyText e) ending

private def mentionsName (text : String) (name : Name) : MetaM Bool := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .ok stx => return (stx.find? fun s => s.isIdent && name.isPrefixOf s.getId).isSome
  | .error _ => return true

private def graphFor? (ty : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let args := decl.type.getAppArgs
      if decl.type.isAppOfArity ``SimpleGraph 1 then
        if ← withReducible (isDefEq args[0]! ty) then return some decl.toExpr
  return none

/-- Singular/plural scalar vocabulary shared by all binding forms. -/
private def scalarNouns? (ty : Expr) : Option (String × String) :=
  if ty.isConstOf ``Nat then some ("natural number", "natural numbers") else
  if ty.isConstOf ``Int then some ("integer", "integers") else
  if ty.isConstOf ``Rat then some ("rational number", "rational numbers") else
  if ty.isConstOf ``Real then some ("real number", "real numbers") else
  if ty.isConstOf ``Complex then some ("complex number", "complex numbers") else
  if ty.isConstOf ``Bool then some ("boolean", "booleans") else
  none

private def scalarDescription? (ty : Expr) : Option String := do
  let (singular, _) ← scalarNouns? ty
  return (if ty.isConstOf ``Int then "an " else "a ") ++ singular

/-- Only explicit, nondependent arrows admit the simple from/to description.
Inspect the type expression without unfolding user-defined aliases. -/
private partial def functionTypeParts? (ty : Expr) : Option (List Expr × Expr) := do
  let .forallE name domain result .default := ty.consumeMData | none
  if result.hasLooseBVars || publicParameterName name then none
  else if result.consumeMData.isForall then
    let (domains, codomain) ← functionTypeParts? result
    some (domain :: domains, codomain)
  else some ([domain], result)

private def functionSignatureText? (ty : Expr) : MetaM (Option String) := do
  let some (domains, codomain) := functionTypeParts? ty | return none
  let domains ← domains.mapM typeAtomText
  return some s!"from {String.intercalate " and " domains} to {← subjectTypeText codomain}"

/-- Propositions describe proofs; supported types supply their own noun phrases.
Use the same vocabulary for function parameters and predicate subjects. -/
private def subjectText (ty : Expr) (n : Option Name) (bi : BinderInfo) : MetaM String := do
  let suffix ← match n with
    | some n => do pure (" " ++ (← nameText n))
    | none => pure ""
  let modifier := match bi with
    | .implicit => some "an implicit"
    | .strictImplicit => some "a strictly implicit"
    | _ => none
  let typeText := subjectTypeText ty
  if bi == .instImplicit then
    return s!"an instance{suffix} of typeclass {← typeText}"
  if ← isProp ty then
    return s!"{modifier.getD "a"} proof{suffix} that {← typeText}"
  if ty.isAppOfArity ``List 1 then
    let elementText ← typeAtomText ty.getAppArgs[0]!
    return s!"{modifier.getD "a"} list{suffix} of {elementText} elements"
  if let some signature ← functionSignatureText? ty then
    return s!"{modifier.getD "a"} function{suffix} {signature}"
  if let some (noun, _) := scalarNouns? ty then
    if let some modifier := modifier then return s!"{modifier} {noun}{suffix}"
    if let some description := scalarDescription? ty then return s!"{description}{suffix}"
  return s!"{modifier.getD "an"} element{suffix} of {← typeText}"

/-- Recognize numeral syntax without evaluating arbitrary arithmetic. -/
private def unsignedNumeral? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getAppArgs[1]!.consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- Independent inverse vocabulary for typed scalar literals. -/
private def scalarLiteralText? (e : Expr) : MetaM (Option String) := do
  let ty ← inferType e
  let some (noun, _) := scalarNouns? ty | return none
  let e := e.consumeMData
  if ty.isConstOf ``Bool then
    if e.isConstOf ``Bool.true then return some "the boolean true"
    if e.isConstOf ``Bool.false then return some "the boolean false"
    return none
  if let some n := unsignedNumeral? e then return some s!"the {noun} {n}"
  if e.isAppOfArity ``Neg.neg 3 then
    if let some n := unsignedNumeral? e.getAppArgs[2]! then
      return some s!"the {noun} -{n}"
  -- Lean's delaborator preserves scientific literal notation and normalized
  -- constructor numerals. Accept only a single numeric token, optionally negated.
  let text ← propertyText e
  let magnitude := if text.startsWith "-" then (text.drop 1).toString.trimAscii.copy else text
  match Parser.runParserCategory (← getEnv) `term magnitude with
  | .ok stx =>
    if stx.isOfKind numLitKind || stx.isOfKind scientificLitKind then
      return some s!"the {noun} {text}"
  | .error _ => pure ()
  return none

/-- Domain vocabulary is independent of existential quantification. -/
private def witnessText (ty : Expr) (name : Option String) (negative := false) : MetaM String := do
  let suffix := name.map (" " ++ ·) |>.getD ""
  let article := if negative then "no" else "a"
  if (← isClass? ty).isSome then
    return s!"{if negative then "no" else "an"} instance{suffix} of typeclass {← subjectTypeText ty}"
  if ← isProp ty then
    return s!"{article} proof{suffix} that {← atomText ty}"
  if ty.isAppOfArity ``SimpleGraph.Path 4 then
    let args := ty.getAppArgs
    return s!"{article} path{suffix} in {← atomText args[1]!} from {← atomText args[2]!} to {← atomText args[3]!}"
  if ty.isAppOfArity ``List 1 then
    return s!"{article} list{suffix} of {← typeAtomText ty.getAppArgs[0]!} elements"
  if let some signature ← functionSignatureText? ty then
    return s!"{article} function{suffix} {signature}"
  if negative then
    if let some (singular, _) := scalarNouns? ty then
      return s!"no {singular}{suffix}"
  if let some description := scalarDescription? ty then
    return description ++ suffix
  let article := if negative then "no" else "an"
  return s!"{article} element{suffix} of {← typeAtomText ty}"

private def negatedExists? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Not 1 then
    let body := e.getAppArgs[0]!.consumeMData
    if body.isAppOfArity ``Exists 2 then some body else none
  else none

/-- Parentheses preserve binder scope and the right associativity of connectives. -/
private def groupOperand (e : Expr) (parent : Name) (left : Bool) (text : String) : String :=
  let e := e.consumeMData
  let grouped := e.isForall || e.isAppOfArity ``Exists 2 || (negatedExists? e).isSome ||
    (parent == ``And && e.isAppOfArity ``Or 2) ||
    (left && e.isAppOfArity parent 2)
  if grouped then "(" ++ text ++ ")" else text

/-- Independent inverse vocabulary: predicate, full application arity, adjective.
The subject is the final argument; earlier arguments are implicit type parameters. -/
private def adjectiveView? (e : Expr) : Option (Expr × String) := do
  let vocabulary : List (Name × Nat × String) := [
    (``Nonempty, 1, "nonempty"),
    (``IsEmpty, 1, "empty"),
    (``Finite, 1, "finite"),
    (``Infinite, 1, "infinite"),
    (``Countable, 1, "countable"),
    (``Function.Injective, 3, "injective"),
    (``Function.Surjective, 3, "surjective"),
    (``Function.Bijective, 3, "bijective")]
  for (predicate, arity, word) in vocabulary do
    if e.isAppOfArity predicate arity then
      return (e.getAppArgs[arity - 1]!, word)
  none

/-- Share function wording and binding scope between plain and typed forms. -/
private partial def functionText (n : Name) (ty body : Expr) (bi : BinderInfo)
    (renderBody : Expr → MetaM String)
    (annotation : Option String := none) : MetaM String := do
  let (subjects, bodyText) ← go (.lam n ty body bi)
  let signature := annotation.map (" : " ++ ·) |>.getD ""
  return s!"the function{signature} mapping {String.intercalate " and " subjects} to\n{indented bodyText}"
where
  go (e : Expr) : MetaM (List String × String) := do
    match e.consumeMData with
    | .lam suggested ty body bi =>
      let n ← freshName suggested
      return ← withLocalDecl n bi ty fun x => do
        let (subjects, bodyText) ← go (body.instantiate1 x)
        let rest := if subjects.isEmpty then bodyText else
          s!"the function mapping {String.intercalate " and " subjects} to {bodyText}"
        let keepName := publicParameterName suggested || (← mentionsName rest n)
        let subject ← subjectText ty (if keepName then some n else none) bi
        return (subject :: subjects, bodyText)
    | _ => pure ()
    return ([], ← renderBody e)

/-- Recognize supported logical structure without unfolding mathematical constants.
Embedded implications stay inline; standalone implications introduce a block.
Quantifiers retain their block layout in either context. -/
partial def renderExpr (e : Expr) (sentenceEnd := false)
    (inlineContext := false) : MetaM String := do
  let e := e.consumeMData
  match e with
  | .letE _ _ value body _ => renderExpr (body.instantiate1 value) sentenceEnd inlineContext
  | .lam n ty body bi =>
    functionText n ty body bi (fun body => renderExpr body sentenceEnd)
  | .forallE n ty body bi =>
    if bi == .default && (← isProp ty) && !body.hasLooseBVars && (← isProp e) then
      let premise ← renderExpr ty false true
      let premise := if ty.isForall then "(" ++ premise ++ ")" else premise
      let conclusion ← renderExpr body sentenceEnd inlineContext
      let text := if inlineContext then
        s!"if {premise} then {conclusion}"
      else
        s!"if {premise} then\n{indented conclusion}"
      return ← sentenceTail text sentenceEnd
    -- Scalar domains also support single binders; other domains currently bind pairs.
    if bi == .default && !(← isProp ty) then
      let n ← freshName n
      withLocalDecl n bi ty fun x => do
        let renderSingle : MetaM String := do
          if let some (singular, _) := scalarNouns? ty then
            let rest ← renderExpr (body.instantiate1 x) sentenceEnd
            return s!"for every {singular} {← nameText n}:\n{indented rest}"
          leafText e sentenceEnd
        match body.instantiate1 x with
        | .forallE m ty₂ body₂ bi₂ =>
          if bi₂ == .default && ty == ty₂ then
            let m ← freshName m
            withLocalDecl m bi₂ ty₂ fun y => do
              let binding ← match ← graphFor? ty with
                | some g => pure s!"vertices {← nameText n} and {← nameText m} of {← atomText g}"
                | none => match scalarNouns? ty with
                  | some (_, plural) => pure s!"{plural} {← nameText n} and {← nameText m}"
                  | none => pure s!"{← nameText n} and {← nameText m} in {← atomText ty}"
              return s!"for all {binding}:\n{indented (← renderExpr (body₂.instantiate1 y) sentenceEnd)}"
          else renderSingle
        | _ => renderSingle
    else leafText e sentenceEnd
  | _ =>
    if let some (subject, adjective) := adjectiveView? e then
      return ← sentenceTail s!"{← atomText subject true} is {adjective}" sentenceEnd
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
      let op := e.getAppFn.constName!
      let args := e.getAppArgs
      let left := groupOperand args[0]! op true (← renderExpr args[0]! false true)
      let right := groupOperand args[1]! op false (← renderExpr args[1]! sentenceEnd true)
      let word := if op == ``And then "and" else "or"
      return ← sentenceTail s!"{left} {word} {right}" sentenceEnd
    let negative := negatedExists? e
    let existential := negative.getD e
    if existential.isAppOfArity ``Exists 2 then
      let args := existential.getAppArgs
      let ty := args[0]!
      let predicate := args[1]!
      let suggested := match predicate with
        | .lam n _ _ _ => n
        | _ => `witness
      let n ← freshName suggested
      withLocalDeclD n ty fun x => do
        let body := (predicate.beta #[x]).consumeMData
        let used := body.containsFVar x.fvarId!
        let witnessName ← nameText n
        let description ← witnessText ty (if used then some witnessName else none) negative.isSome
        if body.isConstOf ``True then return ← sentenceTail s!"there is {description}" sentenceEnd
        return s!"there is {description} such that\n{indented (← renderExpr body sentenceEnd)}"
    else
      leafText e sentenceEnd

/-- Follow the declaration's public parameter names, which may differ from its
lambda variable names. Anonymous arrow types leave the original spelling alone. -/
private partial def declarationBinders (signatureType value : Expr) : Expr :=
  match signatureType.consumeMData, value.consumeMData with
  | .forallE publicName domain result _, .lam name _ body bi =>
    .lam (if publicParameterName publicName then publicName else name) domain
      (declarationBinders result body) bi
  | _, _ => value

/-- Prefer predicate subjects; other values use named definitions. -/
def renderDefinition (name : Name) (signatureType value : Expr) (abbreviation := false) : TermElabM String := do
  let value := declarationBinders signatureType value
  let nameStr ← nameText name
  let clause := if abbreviation then "Abbreviation" else "Definition"
  if let some text ← scalarLiteralText? value then
    return s!"{clause}:\n  {nameStr} is\n{indented (indented (text ++ "."))}"
  match value.consumeMData with
  | .lam vertexName vertexSort graphLambda vertexInfo =>
    -- Mean's graph subject quantifies one fresh universe. Fixed or compound
    -- universe levels must retain their explicit Lean signature.
    let universeFits := match vertexSort with
      | .sort (.succ (.param _)) => true
      | _ => false
    if universeFits && vertexInfo == .implicit then
      let keepVertexName := publicParameterName vertexName
      let vertexName ← freshName vertexName
      let result ← withLocalDecl vertexName vertexInfo vertexSort fun vertexType => do
        match graphLambda.instantiate1 vertexType with
        | .lam graphName graphTy body .default =>
          if graphTy.isAppOfArity ``SimpleGraph 1 && graphTy.getAppArgs[0]! == vertexType then
            let keepGraphName := publicParameterName graphName
            let graphName ← freshName graphName
            withLocalDeclD graphName graphTy fun g => do
              let body := body.instantiate1 g
              if !(← isProp body) then return none
              let edgesName ← freshName `E
              let bodyText ← renderExpr body true
              -- Public carrier parameters must retain their named-argument spelling.
              let parts ← if keepVertexName || (← mentionsName bodyText vertexName) then
                pure s!" = ({← nameText vertexName}, {← nameText edgesName})"
                else pure ""
              let graphSuffix ← if keepGraphName || (← mentionsName bodyText graphName) then
                pure s!" {← nameText graphName}"
                else pure ""
              return some s!"{clause}:\n  a simple graph{graphSuffix}{parts} is {nameStr} if\n{indented (indented (bodyText ++ "."))}"
          else return none
        | _ => return none
      if let some text := result then return text
  | _ => pure ()
  match value.consumeMData with
  | .lam n ty body .default =>
    let keepPublicName := publicParameterName n
    let n ← freshName n
    let result ← withLocalDeclD n ty fun x => do
      let body := body.instantiate1 x
      if !(← isProp body) then return none
      let bodyText ← renderExpr body true
      let keepName := keepPublicName || (← mentionsName bodyText n)
      let subject ← subjectText ty (if keepName then some n else none) .default
      return some s!"{clause}:\n  {subject} is {nameStr} if\n{indented (indented (bodyText ++ "."))}"
    if let some text := result then return text
  | _ => pure ()
  let valueText ← renderExpr value
  let text := s!"{clause}:\n  {nameStr} is\n{indented (indented ((← sentenceTail valueText true) ++ "."))}"
  -- Prefer the plain value when its text independently infers the right type.
  let untypedFits ← withoutModifyingState do
    try
      RoundTrip.checkDefinitionValue value text abbreviation
      pure true
    catch _ => pure false
  if untypedFits then return text
  -- Overloaded constants or function results may need their original type.
  if let .lam n ty body bi := value.consumeMData then
    let typedValue ← functionText n ty body bi (fun body => renderExpr body true)
      (some (← leanText (← inferType value)))
    return s!"{clause}:\n  {nameStr} is\n{indented (indented (typedValue ++ "."))}"
  let typedValue := s!"({valueText} : {← leanText (← inferType value)})."
  return s!"{clause}:\n  {nameStr} is\n{indented (indented typedValue)}"

/-- Return text only after checking its meaning. -/
def renderChecked (e : Expr) : TermElabM String := do
  let text ← renderExpr e
  let compactFits ← withoutModifyingState do
    try
      RoundTrip.checkText e text
      pure true
    catch _ => pure false
  if compactFits then return text
  -- In particular, hidden instance arguments may select a different local instance.
  let text ← withOptions (fun opts => opts.setBool `pp.explicit true) (renderExpr e)
  RoundTrip.checkText e text
  return text

/-- Share the comparison layout across terms and every declaration kind. -/
private def comparisonText (before after : String) : String :=
  s!"\n-- LEAN INPUT:\n{before}\n-- MEAN OUTPUT:\n{after}"

private def showTerm (t : Syntax) (compare : Bool) : Command.CommandElabM Unit :=
  Command.runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let after ← renderChecked e
  if compare then
    logInfo (comparisonText (← leanText e) after)
  else logInfo after

private def showDeclaration (declaration : Syntax) (compare : Bool) : Command.CommandElabM Unit :=
  Command.liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo declaration
  let info ← getConstInfo n
  withLevelNames info.levelParams do
    let context := if info.levelParams.isEmpty then "" else
      "-- Universe parameters: " ++ String.intercalate ", " (info.levelParams.map toString) ++ "\n"
    -- Module exports omit theorem proofs and may present them as axioms.
    if wasOriginallyTheorem (← getEnv) n then
      let text := s!"Theorem {← nameText n}:\n{indented (← renderExpr info.type)}"
      RoundTrip.checkText info.type text `meanTheoremStatement
      if compare then
        let before := s!"theorem {← nameText n} :\n{indented (← leanText info.type)}"
        logInfo (comparisonText (context ++ before) (context ++ text))
      else logInfo s!"{context}{text}"
      return
    match info with
    | .defnInfo d =>
      let abbreviation := d.hints.isAbbrev
      let candidate ← renderDefinition n d.type d.value abbreviation
      let text ← try
        RoundTrip.checkDefinition n candidate
        pure candidate
      catch ex =>
        if (← ex.toMessageData.toString) != "Mean round-trip changed a named parameter" then
          -- Keep the English structure but expose arguments hidden by Lean's printer.
          let text ← withOptions (fun opts => opts.setBool `pp.explicit true) do
            renderDefinition n d.type d.value abbreviation
          RoundTrip.checkDefinition n text
          pure text
        else
          -- Some function aliases need an explicit declaration type to retain
          -- their public names, even though the value is definitionally equal.
          let text ← withOptions (fun opts => opts.setBool `pp.explicit true) do
            let keyword := if abbreviation then "abbrev" else "def"
            pure s!"{keyword} {← nameText n} : {← typeText d.type} :=\n{indented (← leanText d.value)}"
          RoundTrip.checkDefinition n text
          pure text
      if compare then
        let keyword := if abbreviation then "abbrev" else "def"
        let before := s!"{keyword} {← nameText n} : {← leanText info.type} :=\n{indented (← leanText d.value)}"
        logInfo (comparisonText before text)
      else logInfo text
    | _ =>
      let text ← renderChecked info.type
      let statementHeader := s!"{context}-- Statement of {n}\n"
      if compare then
        logInfo (comparisonText s!"{statementHeader}{← leanText info.type}" text)
      else logInfo (statementHeader ++ text)

elab "#mean_term " t:term : command => showTerm t false
elab "#mean_term_compare " t:term : command => showTerm t true
elab "#mean " declaration:ident : command => showDeclaration declaration false
elab "#mean_compare " declaration:ident : command => showDeclaration declaration true

end Mean.Render
