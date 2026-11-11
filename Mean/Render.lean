import Mean.RoundTrip

/-! An independent renderer of elaborated expressions, with checked text round trips.
Import this module and use `#mean declaration` or `#mean_term proposition`.
No declarations are added by the checker. -/

register_option mean.renderProperties : Bool := {
  defValue := false
  descr := "Render Mean property, type, finite sum, and function phrases inside expressions"
}

register_option mean.renderFunctions : Bool := {
  defValue := true
  descr := "Render function expressions in the Mean view, except where native notation binds them"
}

namespace Mean.Render
open Lean Meta Elab Term

-- These delaborators run only for the Mean view, leaving ordinary Lean output intact.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Fin]
def delabIndices : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  guard <| (← getExpr).isAppOfArity ``Fin 1
  let bound ← withAppArg delab
  `(the type of indices in [0, $bound))

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

/-- Unexpanders for binder notation (such as set builders and `∃!`) need a
native lambda to recognize their syntax. Protect those argument positions while
allowing function phrases elsewhere, including deeper inside their bodies. -/
private partial def nativeBinderOptions (env : Environment) (e : Expr)
    (pos : Lean.SubExpr.Pos := .root)
    (options : Lean.PrettyPrinter.Delaborator.OptionsPerPos := {}) :
    Lean.PrettyPrinter.Delaborator.OptionsPerPos :=
  match e with
  | .app f argument =>
    let head := f.getAppFn
    let options := if argument.consumeMData.isLambda && head.isConst &&
        !(Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute.getValues env head.constName!).isEmpty then
      options.insertAt (pos.push 1) `mean.renderFunctions (.ofBool false)
    else options
    nativeBinderOptions env argument (pos.push 1) (nativeBinderOptions env f (pos.push 0) options)
  | .lam _ ty body _ | .forallE _ ty body _ =>
    nativeBinderOptions env body (pos.push 1) (nativeBinderOptions env ty (pos.push 0) options)
  | .letE _ ty value body _ =>
    nativeBinderOptions env body (pos.push 2)
      (nativeBinderOptions env value (pos.push 1) (nativeBinderOptions env ty (pos.push 0) options))
  | .mdata _ e => nativeBinderOptions env e pos options
  | .proj _ _ e => nativeBinderOptions env e (pos.push 0) options
  | _ => options

/-- Ordinary Lean is the fallback, always delaborated in the current local context. -/
private def leanText (e : Expr) : MetaM String := do
  withOptions (fun opts => opts.setBool `pp.coercions.types true |>.setBool `pp.funBinderTypes true) do
    if mean.renderProperties.get (← getOptions) then
      let delab : Lean.PrettyPrinter.Delaborator.Delab := do
        let options := nativeBinderOptions (← getEnv)
          (← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr)
        withReader (fun ctx => { ctx with optionsPerPos := ctx.optionsPerPos.merge options })
          Lean.PrettyPrinter.Delaborator.delab
      let text := (← Lean.PrettyPrinter.ppExprWithInfos e (delab := delab)).fmt.pretty
      -- Mean output is reparsed. Restore proof terms when native printing
      -- would replace them with the non-reconstructible omission token.
      if text.contains '⋯' then
        return ← withOptions (fun opts => opts.setBool `pp.proofs true) do
          pure (← Lean.PrettyPrinter.ppExprWithInfos e (delab := delab)).fmt.pretty
      return text
    return (← Meta.ppExpr e).pretty

/-- Translate Mean phrases recursively even inside otherwise ordinary Lean syntax. -/
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

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app]
def delabValueCoercion : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  guard <| !(pp.explicit.get (← getOptions))
  let e ← getExpr
  let .const name _ := e.getAppFn | failure
  let some info ← Meta.getCoeFnInfo? name | failure
  guard <| info.type == .coe && e.getAppNumArgs == info.numArgs
  let ty ← inferType e
  let value ← withNaryArg info.coercee delab
  if let some (singular, _) := scalarNouns? ty then
    let .ok noun := Parser.runParserCategory (← getEnv) `meanScalar singular | failure
    let noun : TSyntax `meanScalar := ⟨noun⟩
    if ty.isConstOf ``Int then `($value as an $noun:meanScalar)
    else `($value as a $noun:meanScalar)
  else
    let target ← withType delab
    `($value as $target)

private def scalarDescription? (ty : Expr) : Option String := do
  let (singular, _) ← scalarNouns? ty
  return (if ty.isConstOf ``Int then "an " else "a ") ++ singular

/-- Preserve type aliases; specialize only an explicit `Fin` application. -/
private def indexDomainText? (ty : Expr) : MetaM (Option String) := do
  unless ty.isAppOfArity ``Fin 1 do return none
  let bound := ty.getAppArgs[0]!
  if bound.isAppOfArity ``List.length 2 || bound.isAppOfArity ``Array.size 2 then
    return some s!"into {← atomText bound.getAppArgs[1]!}"
  return some s!"in [0, {← propertyText bound})"

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Finset.sum]
def delabSum : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  guard <| !(pp.explicit.get (← getOptions))
  let e ← getExpr
  guard <| e.isAppOfArity ``Finset.sum 5
  let args := e.getAppArgs
  guard args[4]!.isLambda
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i =>
    return ((⟨i⟩ : Ident), ← delab)
  if args[3]!.isAppOfArity ``Finset.univ 2 then
    if let some domain ← indexDomainText? args[0]! then
      let .ok stx := Parser.runParserCategory (← getEnv) `meanIndexDomain domain | failure
      let domain : TSyntax `meanIndexDomain := ⟨stx⟩
      `(the sum over indices $i:ident $domain:meanIndexDomain of $body)
    else
      let ty ← withNaryArg 0 delab
      let ty ← if args[0]!.isConst || args[0]!.isFVar then pure ty else `(($ty))
      `(the sum over elements $i:ident of $ty of $body)
  else
    let s ← withNaryArg 3 delab
    let s ← if args[3]!.isConst || args[3]!.isFVar then pure s else `(($s))
    `(the sum over $i:ident in $s of $body)

private def collectionElementsText (ty : Expr) : MetaM String := do
  if let some (_, plural) := scalarNouns? ty then return plural
  return s!"{← typeAtomText ty} elements"

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.List, delab app.Set]
def delabCollections : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  let e ← getExpr
  let isSet := e.isAppOfArity ``Set 1
  guard <| isSet || e.isAppOfArity ``List 1
  let ty := e.getAppArgs[0]!
  if let some (_, plural) := scalarNouns? ty then
    let .ok noun := Parser.runParserCategory (← getEnv) `meanScalarPlural plural
      | failure
    let noun : TSyntax `meanScalarPlural := ⟨noun⟩
    if isSet then `(the type of sets of $noun:meanScalarPlural)
    else `(the type of lists of $noun:meanScalarPlural)
  else
    let item ← withAppArg delab
    let item ← if ty.isConst || ty.isFVar || ty.isLit then pure item
      else `(($item))
    if isSet then `(the type of sets of $item:term elements)
    else `(the type of lists of $item:term elements)

/-- Only explicit, nondependent arrows admit the simple from/to description.
Inspect the type expression without unfolding user-defined aliases. -/
private partial def functionTypeParts? (ty : Expr) : Option (List Expr × Expr) := do
  let .forallE name domain result .default := ty.consumeMData | none
  if result.hasLooseBVars || publicParameterName name then none
  else if result.consumeMData.isForall then
    let (domains, codomain) ← functionTypeParts? result
    some (domain :: domains, codomain)
  else some ([domain], result)

/-- Function signatures already establish a type context, so descriptions need
neither a `the type of` introducer nor an extra grouping layer. -/
private def functionEndpointText (ty : Expr) (result := false) : MetaM String := do
  if let some domain ← indexDomainText? ty then return s!"indices {domain}"
  if ty.isAppOfArity ``List 1 then
    return s!"lists of {← collectionElementsText ty.getAppArgs[0]!}"
  if ty.isAppOfArity ``Set 1 then
    return s!"sets of {← collectionElementsText ty.getAppArgs[0]!}"
  if result then subjectTypeText ty else typeAtomText ty

private def functionSignatureText? (ty : Expr) : MetaM (Option String) := do
  let some (domains, codomain) := functionTypeParts? ty | return none
  let domains ← domains.mapM (fun domain => functionEndpointText domain)
  return some s!"from {String.intercalate " and " domains} to {← functionEndpointText codomain true}"

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
  if let some domain ← indexDomainText? ty then
    return s!"{modifier.getD "an"} index{suffix} {domain}"
  if ty.isAppOfArity ``List 1 then
    return s!"{modifier.getD "a"} list{suffix} of {← collectionElementsText ty.getAppArgs[0]!}"
  if ty.isAppOfArity ``Set 1 then
    return s!"{modifier.getD "a"} set{suffix} of {← collectionElementsText ty.getAppArgs[0]!}"
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

/-- Shared noun vocabulary, with the appropriate indefinite article kept separate. -/
private def witnessDescription (ty : Expr) (name : Option String) : MetaM (String × String) := do
  let suffix := name.map (" " ++ ·) |>.getD ""
  if (← isClass? ty).isSome then
    return ("an", s!"instance{suffix} of typeclass {← subjectTypeText ty}")
  if ← isProp ty then
    return ("a", s!"proof{suffix} that {← atomText ty}")
  if let some domain ← indexDomainText? ty then
    return ("an", s!"index{suffix} {domain}")
  if ty.isAppOfArity ``SimpleGraph.Path 4 then
    let args := ty.getAppArgs
    return ("a", s!"path{suffix} in {← atomText args[1]!} from {← atomText args[2]!} to {← atomText args[3]!}")
  if ty.isAppOfArity ``List 1 then
    return ("a", s!"list{suffix} of {← collectionElementsText ty.getAppArgs[0]!}")
  if ty.isAppOfArity ``Set 1 then
    return ("a", s!"set{suffix} of {← collectionElementsText ty.getAppArgs[0]!}")
  if let some signature ← functionSignatureText? ty then
    return ("a", s!"function{suffix} {signature}")
  if let some (singular, _) := scalarNouns? ty then
    return (if ty.isConstOf ``Int then "an" else "a", singular ++ suffix)
  return ("an", s!"element{suffix} of {← typeAtomText ty}")

private def witnessText (ty : Expr) (name : Option String) (negative := false) : MetaM String := do
  let (article, noun) ← witnessDescription ty name
  return s!"{if negative then "no" else article} {noun}"

/-- Lean represents these quantifiers as applications to predicates. Their
function types alone do not distinguish them from generic unary predicates. -/
private def isExistential (e : Expr) : Bool :=
  e.isAppOfArity ``Exists 2 || e.isAppOfArity ``ExistsUnique 2

private def almostEveryView? (e : Expr) : Option (Expr × Expr × Expr) := do
  guard <| e.isAppOfArity ``Filter.Eventually 3
  let args := e.getAppArgs
  let filter := args[2]!.consumeMData
  guard <| filter.isAppOfArity ``MeasureTheory.ae 5
  return (args[0]!, args[1]!, filter.getAppArgs[4]!)

private def isQuantifier (e : Expr) : Bool :=
  e.isForall || isExistential e || (almostEveryView? e).isSome

private def negatedExists? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Not 1 then
    let body := e.getAppArgs[0]!.consumeMData
    if body.isAppOfArity ``Exists 2 then some body else none
  else none

/-- Rendering substitutes local lets; grouping must inspect the same outer form. -/
private partial def inlineLets (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ value body _ => inlineLets (body.instantiate1 value)
  | e => e

private partial def subjectListSyntax (stx : Syntax) : Bool :=
  if stx.isOfKind choiceKind then stx.getArgs.any subjectListSyntax
  else match stx with
    | `($_:term and $_:term $[and $_:term]* are $_:meanAdjective)
    | `($_:term and $_:term $[and $_:term]* are not $_:meanAdjective) => true
    | _ => false

/-- Parentheses preserve binder scope, connective precedence, and associativity. -/
private def groupOperand (e : Expr) (parent : Name) (left : Bool) (text : String) : MetaM String := do
  let e := inlineLets e
  let subjects ← if parent == ``And || parent == ``Or then do
    match Parser.runParserCategory (← getEnv) `term text with
    | .ok stx => pure (subjectListSyntax stx)
    | .error _ => pure false
  else pure false
  let grouped := subjects || isQuantifier e || (negatedExists? e).isSome ||
    (parent == ``And && e.isAppOfArity ``Or 2) ||
    e.isAppOfArity ``Iff 2 ||
    (left && e.isAppOfArity parent 2)
  return if grouped then "(" ++ text ++ ")" else text

/-- Collect only the right spine: left-associated connectives retain their grouping. -/
private partial def connectiveClauses (e : Expr) (op : Name) : List Expr :=
  let e := inlineLets e
  if e.isAppOfArity op 2 then
    let args := e.getAppArgs
    args[0]! :: connectiveClauses args[1]! op
  else [e]

/-- Independent inverse vocabulary plus named predicates with subject lists.
Subjects are the trailing explicit arguments, after implicit parameters. -/
private def adjectiveView? (e : Expr) : MetaM (Option (List Expr × String)) := do
  if e.isAppOfArity ``Not 1 then return none
  unless ← isProp e do return none
  let explicit := pp.explicit.get (← getOptions)
  let vocabulary : List (Name × Nat × String) := [
    (``Nonempty, 1, "nonempty"),
    (``IsEmpty, 1, "empty"),
    (``Finite, 1, "finite"),
    (``Infinite, 1, "infinite"),
    (``Countable, 1, "countable"),
    (``Function.Injective, 3, "injective"),
    (``Function.Surjective, 3, "surjective"),
    (``Function.Bijective, 3, "bijective"),
    (``REPred, 3, "recursively enumerable"),
    (``ComputablePred, 3, "computable"),
    (``Computable, 5, "computable")]
  for (predicate, arity, word) in vocabulary do
    if e.isAppOfArity predicate arity && !explicit then
      return some ([e.getAppArgs[arity - 1]!], word)
  -- A named predicate has trailing explicit arguments after implicit parameters.
  -- Inspect binder information rather than guessing from its spelling.
  let head := e.getAppFn
  unless head.isConst || head.isFVar do return none
  let args := e.getAppArgs
  if args.isEmpty then return none
  let headType ← inferType head
  -- A polymorphic value operation can return a proposition when specialized
  -- to `Prop` (e.g. `id`, `iInf`, or a coercion). It is not thereby a predicate.
  -- Inspect the codomain with formal parameters, before applying actual args.
  let declaredPredicate ← forallTelescopeReducing headType fun _ result => do
    return (← whnf result) == mkSort .zero
  unless declaredPredicate do return none
  let mut ty := headType
  let mut subjects : List Expr := []
  for i in [:args.size] do
    let .forallE _ _ body bi ← whnf ty | return none
    if bi == .default then
      subjects := subjects ++ [args[i]!]
    else unless subjects.isEmpty do return none
    ty := body.instantiate1 args[i]!
  if subjects.isEmpty then return none
  if subjects.length > 1 then
    -- Keep native relation notation such as =, ≤, ∈, and ⊆. Only a plain
    -- prefix application needs the named predicate wording.
    if explicit then return none
    let .ok native := Parser.runParserCategory (← getEnv) `term (← leanText e) | return none
    unless native.isOfKind ``Parser.Term.app do return none
  let text ← propertyText (if explicit then e.getBoundedAppFn subjects.length else head)
  -- A bare polymorphic function prints with `@`; ordinary predicate wording
  -- should infer its implicit arguments from the subject instead.
  let text := if !explicit && text.startsWith "@" then (text.drop 1).toString else text
  let predicate ← match Parser.runParserCategory (← getEnv) `term text with
    | .ok stx => pure (if stx.isIdent then text else "(" ++ text ++ ")")
    | .error _ => pure ("(" ++ text ++ ")")
  return some (subjects, predicate)

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

private def closureName? (e : Expr) (arity : Nat) : Option String :=
  if e.isAppOfArity ``Relation.ReflTransGen arity then some "reflexive transitive" else
  if e.isAppOfArity ``Relation.TransGen arity then some "transitive" else
  if e.isAppOfArity ``Relation.ReflGen arity then some "reflexive" else
  if e.isAppOfArity ``Relation.SymmGen arity then some "symmetric" else
  if e.isAppOfArity ``Relation.EqvGen arity then some "equivalence" else none

private def isRelationOperator (e : Expr) : Bool :=
  (closureName? e 2).isSome || e.isAppOfArity ``Relation.Comp 5

/-- Describe operators recursively without unfolding or simplifying their meaning. -/
private partial def relationOperatorText (e : Expr) : MetaM String := do
  let e := e.consumeMData
  let argumentText (r : Expr) : MetaM String := do
    let text ← relationOperatorText r
    return if r.isConst || r.isFVar then text else "(" ++ text ++ ")"
  if let some name := closureName? e 2 then
    let predicate ← argumentText e.getAppArgs[1]!
    let heading := s!"the {name} closure of"
    return if predicate.contains '\n' then s!"{heading}\n{indented predicate}"
      else s!"{heading} {predicate}"
  if e.isAppOfArity ``Relation.Comp 5 then
    let args := e.getAppArgs
    let first ← argumentText args[3]!
    let second ← argumentText args[4]!
    return if first.contains '\n' || second.contains '\n' then
      s!"the composition of\n{indented first}\nfollowed by\n{indented second}"
      else s!"the composition of {first} followed by {second}"
  propertyText e

/-- Recognize supported logical structure without unfolding mathematical constants.
Embedded implications stay inline; standalone implications introduce a block.
Quantifiers retain their block layout in either context. -/
partial def renderExpr (e : Expr) (sentenceEnd := false)
    (inlineContext := false) : MetaM String := do
  let e := inlineLets e
  match e with
  | .lam n ty body bi =>
    functionText n ty body bi (fun body => renderExpr body sentenceEnd)
  | .forallE n ty body bi =>
    if bi == .default && (← isProp ty) && !body.hasLooseBVars && (← isProp e) then
      let premise ← renderExpr ty false true
      let premise := if (inlineLets ty).isForall then "(" ++ premise ++ ")" else premise
      let conclusion ← renderExpr body sentenceEnd inlineContext
      let conclusion := if (inlineLets body).isAppOfArity ``Iff 2 then
        "(" ++ conclusion ++ ")" else conclusion
      let text := if inlineContext then
        s!"if {premise} then {conclusion}"
      else
        s!"if {premise} then\n{indented conclusion}"
      return ← sentenceTail text sentenceEnd
    if bi == .default && (← isProp e) then
      let n ← freshName n
      withLocalDecl n bi ty fun x => do
        let renderQuantified (heading : String) (body : Expr) : MetaM String := do
          let body := inlineLets body
          if let .forallE _ premise conclusion .default := body then
            -- Keep a proof binder when its proof is used by the conclusion.
            if (← isProp premise) && !conclusion.hasLooseBVars then
              let condition ← renderExpr premise false true
              let condition := if isQuantifier (inlineLets premise) ||
                  (negatedExists? (inlineLets premise)).isSome then
                "(" ++ condition ++ ")" else condition
              let rest ← renderExpr conclusion sentenceEnd
              return s!"{heading} where {condition}:\n{indented rest}"
          return s!"{heading}:\n{indented (← renderExpr body sentenceEnd)}"
        let renderSingle : MetaM String := do
          let body := inlineLets (body.instantiate1 x)
          if !(pp.explicit.get (← getOptions)) then
            if let .forallE _ premise conclusion .default := body then
              let premise := inlineLets premise
              if premise.isAppOfArity ``Membership.mem 5 && !conclusion.hasLooseBVars then
                let args := premise.getAppArgs
                if args[4]! == x then
                  let collection ← atomText args[3]!
                  return ← renderQuantified s!"for every {← nameText n} ∈ {collection}" conclusion
          let (_, noun) ← witnessDescription ty (some (← nameText n))
          renderQuantified s!"for every {noun}" body
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
              renderQuantified s!"for all {binding}" (body₂.instantiate1 y)
          else renderSingle
        | _ => renderSingle
    else leafText e sentenceEnd
  | _ =>
    -- Structural forms take precedence over the open-ended predicate fallback.
    let negativeRelation := e.isAppOfArity ``Not 1
    let relation := if negativeRelation then e.getAppArgs[0]!.consumeMData else e
    if ((closureName? relation 4).isSome || relation.isAppOfArity ``Relation.Comp 7) &&
        !(pp.explicit.get (← getOptions)) then
      let args := relation.getAppArgs
      let copula := if negativeRelation then "is not related to" else "is related to"
      let operatorText ← relationOperatorText (relation.getBoundedAppFn 2)
      let text := s!"{← atomText args[args.size - 2]!} {copula} {← atomText args[args.size - 1]!} by {operatorText}"
      return ← sentenceTail text sentenceEnd
    if isRelationOperator e && !(pp.explicit.get (← getOptions)) then
      return ← sentenceTail (← relationOperatorText e) sentenceEnd
    if let some (ty, predicate, measure) := almostEveryView? e then
      let suggested := match predicate.consumeMData with
        | .lam n _ _ _ => n
        | _ => `x
      let n ← freshName suggested
      return ← withLocalDeclD n ty fun x => do
        let body := inlineLets (predicate.beta #[x])
        let used := body.containsFVar x.fvarId!
        let name ← if used then pure (some (← nameText n)) else pure none
        let (_, noun) ← witnessDescription ty name
        let canonical ← withoutModifyingState do
          try
            let volume ← mkAppOptM ``MeasureTheory.volume #[some ty, none]
            isDefEq measure volume
          catch _ => pure false
        let measureText ← if canonical then pure ""
          else pure s!" with respect to {← atomText measure}"
        let heading := s!"for almost every {noun}{measureText}"
        if let .forallE _ premise conclusion .default := body then
          if (← isProp premise) && !conclusion.hasLooseBVars then
            let condition ← renderExpr premise false true
            let condition := if isQuantifier (inlineLets premise) ||
                (negatedExists? (inlineLets premise)).isSome then
              "(" ++ condition ++ ")" else condition
            return s!"{heading} where {condition}:\n{indented (← renderExpr conclusion sentenceEnd)}"
        return s!"{heading}:\n{indented (← renderExpr body sentenceEnd)}"
    if e.isAppOfArity ``Set.ofPred 2 then
      let args := e.getAppArgs
      let ty := args[0]!
      let predicate := args[1]!
      let suggested := match predicate.consumeMData with
        | .lam n _ _ _ => n
        | _ => `x
      let n ← freshName suggested
      return ← withLocalDeclD n ty fun x => do
        let body := predicate.beta #[x]
        let used := (inlineLets body).containsFVar x.fvarId!
        let suffix ← if used then pure s!" {← nameText n}" else pure ""
        return s!"the set of elements{suffix} of {← subjectTypeText ty} such that\n{indented (← renderExpr body sentenceEnd)}"
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
      let op := e.getAppFn.constName!
      let word := if op == ``And then "and" else "or"
      let clauses := connectiveClauses e op
      let texts ← clauses.mapIdxM fun i clause => do
        let last := i + 1 == clauses.length
        let text ← renderExpr clause (last && sentenceEnd) true
        groupOperand clause op (!last) text
      let flat := String.intercalate s!" {word} " texts
      let width := Lean.Std.Format.getWidth (← getOptions)
      let separator := if flat.contains '\n' || flat.length > width then s!" {word}\n" else s!" {word} "
      return ← sentenceTail (String.intercalate separator texts) sentenceEnd
    if e.isAppOfArity ``Iff 2 then
      let op := e.getAppFn.constName!
      let args := e.getAppArgs
      let left ← groupOperand args[0]! op true (← renderExpr args[0]! false true)
      let right ← groupOperand args[1]! op false (← renderExpr args[1]! sentenceEnd true)
      return ← sentenceTail s!"{left} if and only if {right}" sentenceEnd
    let negative := negatedExists? e
    let existential := negative.getD e
    let isUnique := existential.isAppOfArity ``ExistsUnique 2
    if isExistential existential then
      let args := existential.getAppArgs
      let ty := args[0]!
      let predicate := args[1]!
      let suggested := match predicate with
        | .lam n _ _ _ => n
        | _ => `witness
      let n ← freshName suggested
      return ← withLocalDeclD n ty fun x => do
        let body := (predicate.beta #[x]).consumeMData
        let used := body.containsFVar x.fvarId!
        let witnessName ← nameText n
        let name := if used then some witnessName else none
        let heading ← if isUnique then do
          let (_, noun) ← witnessDescription ty name
          pure s!"there is a unique {noun}"
        else do
          pure s!"there is {← witnessText ty name negative.isSome}"
        if body.isConstOf ``True then return ← sentenceTail heading sentenceEnd
        return s!"{heading} such that\n{indented (← renderExpr body sentenceEnd)}"
    let negativeAdjective := e.isAppOfArity ``Not 1
    let positive := if negativeAdjective then e.getAppArgs[0]! else e
    -- A negated quantifier without dedicated wording stays Lean. Do not turn
    -- its predicate argument into an adjective subject either.
    if negativeAdjective && isQuantifier positive then return ← leafText e sentenceEnd
    if let some (subjects, adjective) ← adjectiveView? positive then
      let texts ← subjects.mapM fun subject => do
        let rendered ← renderExpr subject false true
        if (unsignedNumeral? subject).isSome && !(pp.explicit.get (← getOptions)) then
          pure rendered
        else if rendered == (← propertyText subject) then atomText subject true
        else pure ("(" ++ rendered ++ ")")
      let copula := if subjects.length == 1 then "is" else "are"
      let copula := copula ++ if negativeAdjective then " not" else ""
      return ← sentenceTail s!"{String.intercalate " and " texts} {copula} {adjective}" sentenceEnd
    leafText e sentenceEnd

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Set.ofPred]
def delabSetComprehension : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  guard <| (← getExpr).isAppOfArity ``Set.ofPred 2
  let text ← renderExpr (← getExpr)
  let .ok stx := Parser.runParserCategory (← getEnv) `term text | failure
  return ⟨stx⟩

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab lam]
def delabFunction : Delab := do
  guard <| mean.renderProperties.get (← getOptions)
  guard <| ← getPPOption mean.renderFunctions.get
  -- Share the renderer, including binding scope and recursive body wording,
  -- when Lean's fallback encounters a function inside an application or type.
  let text ← renderExpr (← getExpr)
  let .ok stx := Parser.runParserCategory (← getEnv) `term text | failure
  return ⟨stx⟩

/-- Follow the declaration's public parameter names, which may differ from its
lambda variable names. Anonymous arrow types leave the original spelling alone. -/
private partial def declarationBinders (signatureType value : Expr) : Expr :=
  match signatureType.consumeMData, value.consumeMData with
  | .forallE publicName domain result _, .lam name _ body bi =>
    .lam (if publicParameterName publicName then publicName else name) domain
      (declarationBinders result body) bi
  | _, _ => value

/-- Keep all explicit predicate arguments in scope together, including dependent
domains. Group a common type without inventing a plural of a user-defined name. -/
private partial def predicateSubjectsText? (value : Expr) : MetaM (Option (String × String)) :=
  go value []
where
  go (value : Expr) (subjects : List (Name × Expr)) : MetaM (Option (String × String)) := do
    match value.consumeMData with
    | .lam suggested ty body .default =>
      let n ← freshName suggested
      withLocalDeclD n ty fun x => go (body.instantiate1 x) (subjects ++ [(n, ty)])
    | _ =>
      if subjects.length < 2 || !(← isProp value) then return none
      let bodyText ← renderExpr value true
      let (_, ty) := subjects.head!
      let text ← if subjects.all (fun (_, domain) => domain == ty) then do
        let names ← subjects.mapM (fun (n, _) => nameText n)
        let names := String.intercalate " and " names
        if let some (_, plural) := scalarNouns? ty then
          pure s!"{plural} {names}"
        else if let some domain ← indexDomainText? ty then
          pure s!"indices {names} {domain}"
        else pure s!"elements {names} of {← subjectTypeText ty}"
      else do
        let descriptions ← subjects.mapM (fun (n, ty) => subjectText ty (some n) .default)
        pure (String.intercalate " and " descriptions)
      return some (text, bodyText)

/-- Prefer predicate subjects; other values use named definitions. -/
def renderDefinition (name : Name) (signatureType value : Expr) (abbreviation := false) : TermElabM String := do
  let value := declarationBinders signatureType value
  let nameStr ← nameText name
  let clause := if abbreviation then "Abbreviation" else "Definition"
  if (← whnf signatureType).isSort then
    let article := if ['a', 'e', 'i', 'o', 'u'].contains (nameStr.toLower.toList.headD ' ') then
      "an" else "a"
    return s!"{clause}:\n  {article} {nameStr} is\n{indented (indented ((← witnessText value none) ++ "."))}"
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
  if let some (subjects, bodyText) ← predicateSubjectsText? value then
    return s!"{clause}:\n  {subjects} are {nameStr} if\n{indented (indented (bodyText ++ "."))}"
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
