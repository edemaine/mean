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

private def indented (s : String) : String :=
  "  " ++ s.replace "\n" "\n  "

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

/-- Domain vocabulary is independent of existential quantification. -/
private def witnessText (ty : Expr) (name : Option String) (negative := false) : MetaM String := do
  let suffix := name.map (" " ++ ·) |>.getD ""
  let article := if negative then "no" else "a"
  if ty.isAppOfArity ``SimpleGraph.Path 4 then
    let args := ty.getAppArgs
    return s!"{article} path{suffix} in {← atomText args[1]!} from {← atomText args[2]!} to {← atomText args[3]!}"
  if negative then
    if let some (singular, _) := scalarNouns? ty then
      return s!"no {singular}{suffix}"
  if let some description := scalarDescription? ty then
    return description ++ suffix
  let article := if negative then "no" else "an"
  return s!"{article} element{suffix} of {← atomText ty}"

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

/-- Recognize supported logical structure without unfolding mathematical constants.
Embedded implications stay inline; standalone implications introduce a block.
Quantifiers retain their block layout in either context. -/
partial def renderExpr (e : Expr) (sentenceEnd := false)
    (inlineContext := false) : MetaM String := do
  let e := e.consumeMData
  match e with
  | .letE _ _ value body _ => renderExpr (body.instantiate1 value) sentenceEnd inlineContext
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

/-- Render a supported unary predicate as a Mean definition. Others use a Lean def. -/
def renderDefinition (name : Name) (value : Expr) : MetaM String := do
  let nameStr ← nameText name
  match value.consumeMData with
  | .lam vertexName vertexSort graphLambda vertexInfo =>
    -- Mean's graph subject quantifies one fresh universe. Fixed or compound
    -- universe levels must retain their explicit Lean signature.
    let universeFits := match vertexSort with
      | .sort (.succ (.param _)) => true
      | _ => false
    if universeFits && vertexInfo.isImplicit then
      let vertexName ← freshName vertexName
      let result ← withLocalDecl vertexName vertexInfo vertexSort fun vertexType => do
        match graphLambda.instantiate1 vertexType with
        | .lam graphName graphTy body .default =>
          if graphTy.isAppOfArity ``SimpleGraph 1 && graphTy.getAppArgs[0]! == vertexType then
            let graphName ← freshName graphName
            withLocalDeclD graphName graphTy fun g => do
              let body := body.instantiate1 g
              if !(← isProp body) then return none
              let edgesName ← freshName `E
              let bodyText ← renderExpr body true
              -- Keep the explicit vertex name only when the rendered body uses it.
              let parts ← if ← mentionsName bodyText vertexName then
                pure s!" = ({← nameText vertexName}, {← nameText edgesName})"
                else pure ""
              return some s!"Definition:\n  a simple graph {← nameText graphName}{parts} is {nameStr} if\n{indented (indented (bodyText ++ "."))}"
          else return none
        | _ => return none
      if let some text := result then return text
  | _ => pure ()
  match value.consumeMData with
  | .lam n ty body .default =>
    let n ← freshName n
    let result ← withLocalDeclD n ty fun x => do
      let body := body.instantiate1 x
      if !(← isProp body) then return none
      let subject ← match scalarDescription? ty with
        | some description => pure s!"{description} {← nameText n}"
        | none => pure s!"an element {← nameText n} of {← atomText ty}"
      return some s!"Definition:\n  {subject} is {nameStr} if\n{indented (indented ((← renderExpr body true) ++ "."))}"
    if let some text := result then return text
  | _ => pure ()
  return s!"def {nameStr} : {← leanText (← inferType value)} :=\n{indented (← leanText value)}"

/-- Return text only after checking its meaning. -/
def renderChecked (e : Expr) : TermElabM String := do
  let text ← renderExpr e
  RoundTrip.checkText e text
  return text

private def showTerm (t : Syntax) (compare : Bool) : Command.CommandElabM Unit :=
  Command.runTermElabM fun _ => do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let after ← renderChecked e
  if compare then
    logInfo s!"\n{← leanText e}\n-> MEAN\n{after}"
  else logInfo after

private def showDeclaration (declaration : Syntax) (compare : Bool) : Command.CommandElabM Unit :=
  Command.liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo declaration
  let info ← getConstInfo n
  withLevelNames info.levelParams do
    match info with
    | .defnInfo d =>
      let text ← renderDefinition n d.value
      RoundTrip.checkText d.value text true
      if compare then
        let before := s!"def {← nameText n} : {← leanText info.type} :=\n{indented (← leanText d.value)}"
        logInfo s!"\n{before}\n-> MEAN\n{text}"
      else logInfo text
    | _ =>
      let text ← renderChecked info.type
      let context := if info.levelParams.isEmpty then "" else
        "-- Universe parameters: " ++ String.intercalate ", " (info.levelParams.map toString) ++ "\n"
      if compare then
        logInfo s!"\n{context}-- Statement of {n}\n{← leanText info.type}\n-> MEAN\n{text}"
      else logInfo s!"{context}-- Statement of {n}\n{text}"

elab "#mean_term " t:term : command => showTerm t false
elab "#mean_term_compare " t:term : command => showTerm t true
elab "#mean " declaration:ident : command => showDeclaration declaration false
elab "#mean_compare " declaration:ident : command => showDeclaration declaration true

end Mean.Render
