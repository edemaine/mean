import Mean.RoundTrip

/-! An independent renderer of elaborated expressions, with checked text round trips.
Import this module and use `#mean declaration` or `#mean_term proposition`.
No declarations are added by the checker. -/

namespace Mean.Render
open Lean Meta Elab Term

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

private def atomText (e : Expr) : MetaM String := do
  let text ← leanText e
  if e.isFVar || e.isConst || e.isLit then return text
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
  sentenceTail (← leanText e) ending

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
private def witnessText (ty : Expr) (name : Option String) : MetaM String := do
  let suffix := name.map (" " ++ ·) |>.getD ""
  if ty.isAppOfArity ``SimpleGraph.Path 4 then
    let args := ty.getAppArgs
    return s!"a path{suffix} in {← atomText args[1]!} from {← atomText args[2]!} to {← atomText args[3]!}"
  if let some description := scalarDescription? ty then
    return description ++ suffix
  return s!"an element{suffix} of {← atomText ty}"

/-- Parentheses preserve binder scope and the right associativity of connectives. -/
private def groupOperand (e : Expr) (parent : Name) (left : Bool) (text : String) : String :=
  let e := e.consumeMData
  let grouped := e.isForall || e.isAppOfArity ``Exists 2 ||
    (parent == ``And && e.isAppOfArity ``Or 2) ||
    (left && e.isAppOfArity parent 2)
  if grouped then "(" ++ text ++ ")" else text

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
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
      let op := e.getAppFn.constName!
      let args := e.getAppArgs
      let left := groupOperand args[0]! op true (← renderExpr args[0]! false true)
      let right := groupOperand args[1]! op false (← renderExpr args[1]! sentenceEnd true)
      let word := if op == ``And then "and" else "or"
      return ← sentenceTail s!"{left} {word} {right}" sentenceEnd
    if e.isAppOfArity ``Exists 2 then
      let args := e.getAppArgs
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
        let description ← witnessText ty (if used then some witnessName else none)
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
      let result ← withLocalDecl vertexName vertexInfo vertexSort fun vertex => do
        match graphLambda.instantiate1 vertex with
        | .lam graphName graphTy body .default =>
          if graphTy.isAppOfArity ``SimpleGraph 1 && graphTy.getAppArgs[0]! == vertex then
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
