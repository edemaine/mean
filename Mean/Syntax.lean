import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Countable.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Computability.RE
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.Determinant
import Lean

/-! # Mean: compositional controlled mathematical syntax inside Lean.

A trailing `%` marks internal helper syntax in Mean. These forms connect the
surface grammar to binding rules and disappear during macro expansion; authors
need not write them. This is a naming convention, not enforced privacy.
-/

/-- Expose the vertex type carried by a mathlib graph's type parameter as `G.V`. -/
abbrev SimpleGraph.V {α : Type*} (_ : SimpleGraph α) := α

namespace Mean

/-- Inductive declarations retain Lean's binder and constructor notation;
constructor types may contain Mean type phrases. -/
syntax "Inductive " ident bracketedBinder* " : " term " where" Lean.Parser.Command.ctor* : command
macro_rules
  | `(command| Inductive $name:ident $binders:bracketedBinder* : $ty:term where $ctors:ctor*) =>
    `(command| inductive $name $binders* : $ty where $ctors*)


/-! Logical connectives use Lean's usual precedence: `and` binds tighter than
`or`; both associate to the right. `if and only if` has the precedence and
nonassociativity of `↔`. An `if … then …` without `else` is implication.
Lean's ordinary `if … then … else …` remains available. -/
syntax:35 term:36 " and " term:35 : term
syntax:30 term:31 " or " term:30 : term
-- Backtrack unless the complete phrase matches, preserving ordinary `if` blocks.
syntax:20 term:21 atomic(" if " "and " "only " "if ") term:21 : term
syntax:25 "if" term "then" term:25 : term
macro_rules
  | `($p:term and $q:term) => `(And $p $q)
  | `($p:term or $q:term) => `(Or $p $q)
  | `($p:term if and only if $q:term) => `(Iff $p $q)
  | `(if $premise:term then $conclusion:term) =>
      `(∀ (_ : ($premise : Prop)), ($conclusion : Prop))

/-! Adjectives share one application rule. New adjectives implement
`adjectivePredicate%` with their Lean predicate; Lean checks the subject's type. -/
declare_syntax_cat meanAdjective
syntax "nonempty" : meanAdjective
syntax "empty" : meanAdjective
syntax "a" "nonempty" "type" : meanAdjective
syntax "an" "empty" "type" : meanAdjective
syntax "a" "nonempty" "list" : meanAdjective
syntax "an" "empty" "list" : meanAdjective
syntax "a" "nonempty" "set" : meanAdjective
syntax "an" "empty" "set" : meanAdjective
syntax "finite" : meanAdjective
syntax "infinite" : meanAdjective
syntax "countable" : meanAdjective
syntax "injective" : meanAdjective
syntax "surjective" : meanAdjective
syntax "bijective" : meanAdjective
syntax "recursively" "enumerable" : meanAdjective
syntax "computable" : meanAdjective
syntax (priority := low) ident : meanAdjective
syntax "(" term ")" : meanAdjective
syntax "adjectivePredicate%" meanAdjective : term
syntax "adjectiveOn%" meanAdjective "of" term : term
syntax:50 term:51 " is " meanAdjective : term
syntax:50 term:51 " is " "not " meanAdjective : term
-- Backtrack to logical `and` unless a complete subject list fits. Longer lists
-- can compete with outer conjunctions; parentheses make the boundary explicit.
syntax:50 term:51 atomic(" and " term:51 (" and " term:51)* " are ") meanAdjective : term
syntax:50 term:51 atomic(" and " term:51 (" and " term:51)* " are ") "not " meanAdjective : term

syntax:50 term:51 " satisfies " meanAdjective : term
syntax:50 term:51 " does " "not " "satisfy " meanAdjective : term
syntax:50 term:51 atomic(" and " term:51 (" and " term:51)* " satisfy ") meanAdjective : term
-- Stop before the negating `do`, rather than parsing a Lean do-block argument.
def predicateSubjectBeforeDo : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "term" `term (isPseudoKind := true))
    (Lean.Parser.withForbidden "do" (Lean.Parser.termParser 51))
syntax:50 term:51 atomic(" and " predicateSubjectBeforeDo (" and " predicateSubjectBeforeDo)*
  " do " "not " "satisfy ") meanAdjective : term

/-! Logarithms retain their base and argument explicitly. -/
/-- The natural logarithm, using the standard mathematical name. -/
noncomputable abbrev ln (x : Real) : Real := Real.log x

def logarithmWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "log " (includeIdent := true) >> Lean.Parser.nonReservedSymbol "base "
syntax:max logarithmWords term:arg " of " term:arg : term
macro_rules
  | `(log base $base:term of $value:term) => `(Real.logb $base $value)

/-! General set and geometry expressions use contextual words after `the`. -/
def imageWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "image "
def complementWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "complement "
def concatenationWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "concatenation "
def lengthWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "length "
def underWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "under "
def euclideanSpaceWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "real " >> Lean.Parser.nonReservedSymbol "Euclidean " >>
    Lean.Parser.nonReservedSymbol "space "
def dimensionWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "dimension "
def isometryTypeWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "bijective " >> Lean.Parser.nonReservedSymbol "affine " >>
    Lean.Parser.nonReservedSymbol "isometries "
def overWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "over "
def linearPartWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "linear " >> Lean.Parser.nonReservedSymbol "part "
def determinantWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "determinant "
def bisectorWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "perpendicular " >> Lean.Parser.nonReservedSymbol "bisector "
def reflectionWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "reflection "
def acrossWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "across "
syntax:max "the " imageWord "of " term:arg ppSpace underWord term:arg : term
syntax:max "the " complementWord "of " term:arg : term
syntax:max "the " concatenationWord "of " term:arg " and " term:arg : term
syntax:max "the " lengthWord "of " term:arg : term
syntax:max "the " "set " "of " "all " "elements " "of " term:arg : term
syntax:max "the " "set " term:arg : term
syntax:max "the " euclideanSpaceWords "of " dimensionWord term:arg : term
syntax:max "the " "type " "of " isometryTypeWords "from " term:arg " to " term:arg ppSpace overWord term:arg : term
syntax:max "the " linearPartWords "of " term:arg : term
syntax:max "the " determinantWord "of " term:arg : term
syntax:max "the " bisectorWords "of " term:arg " and " term:arg : term
syntax:max "the " reflectionWord acrossWord term:arg : term
macro_rules
  | `(the image of $s:term under $f:term) => `(Set.image $f $s)
  | `(the complement of $s:term) => `(Compl.compl ($s : Set _))
  | `(the concatenation of $xs:term and $ys:term) => `(Fin.append $xs $ys)
  | `(the length of $xs:term) => `(List.length $xs)
  | `(the set of all elements of $ty:term) => `((Set.univ : Set $ty))
  | `(the set $value:term) => `(($value : Set _))
  | `(the real Euclidean space of dimension $d:term) => `(EuclideanSpace Real (Fin $d))
  | `(the type of bijective affine isometries from $source:term to $target:term over $k:term) =>
      `(AffineIsometryEquiv $k $source $target)
  | `(the linear part of $f:term) => `(($f).linear)
  | `(the determinant of $f:term) => `(($f).det)
  | `(the perpendicular bisector of $p:term and $q:term) => `(AffineSubspace.perpBisector $p $q)
  | `(the reflection across $s:term) => `(EuclideanGeometry.reflection $s)

/-! Relation operators remain relations; relatedness applies them in order. -/
def closureWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "reflexive " >>
  Lean.Parser.nonReservedSymbol "transitive " >>
  Lean.Parser.nonReservedSymbol "closure "
def transitiveClosureWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "transitive " >> Lean.Parser.nonReservedSymbol "closure "
def reflexiveClosureWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "reflexive " >> Lean.Parser.nonReservedSymbol "closure "
def symmetricClosureWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "symmetric " >> Lean.Parser.nonReservedSymbol "closure "
def equivalenceClosureWords : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "equivalence " >> Lean.Parser.nonReservedSymbol "closure "
def compositionWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "composition "
def followedWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "followed "
def relatedWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "related "
syntax:max "the " closureWords "of " term:arg : term
syntax:max "the " transitiveClosureWords "of " term:arg : term
syntax:max "the " reflexiveClosureWords "of " term:arg : term
syntax:max "the " symmetricClosureWords "of " term:arg : term
syntax:max "the " equivalenceClosureWords "of " term:arg : term
syntax:max "the " compositionWord "of " term:arg followedWord "by " term:arg : term
syntax:50 term:51 atomic(" is " relatedWord "to ") term:51 " by " term:51 : term
syntax:50 term:51 atomic(" is " "not " relatedWord "to ") term:51 " by " term:51 : term
macro_rules
  | `(the reflexive transitive closure of $r:term) => `(Relation.ReflTransGen $r)
  | `(the transitive closure of $r:term) => `(Relation.TransGen $r)
  | `(the reflexive closure of $r:term) => `(Relation.ReflGen $r)
  | `(the symmetric closure of $r:term) => `(Relation.SymmGen $r)
  | `(the equivalence closure of $r:term) => `(Relation.EqvGen $r)
  | `(the composition of $r:term followed by $s:term) => `(Relation.Comp $r $s)

/-- Infer the application without a Prop expectation, so Boolean coercions do
not silently turn an arbitrary function into a predicate. -/
private def checkedPredicateApplication (p : Lean.Term) (args : Array Lean.Term) :
    Lean.Elab.Term.TermElabM Lean.Expr := do
  let application ← Lean.Elab.Term.elabTerm (← `($p $args*)) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless ← Lean.Meta.isProp application do
    Lean.throwErrorAt p "expected a proposition-valued predicate"
  return application

elab "adjectiveApply%" p:term "of" x:term : term =>
  checkedPredicateApplication p #[x]

elab "relationApply%" p:term "of" "[" xs:term,* "]" : term =>
  checkedPredicateApplication p xs.getElems

/-- Predicate computability concerns an indicator function; other functions use
`Computable` directly. Inspect the codomain without unfolding the subject. -/
elab "computableOn%" t:term : term => do
  let subject ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType subject)
  let .forallE name domain body bi := ty
    | Lean.throwErrorAt t "expected a function or predicate"
  let isPredicate ← Lean.Meta.withLocalDecl name bi domain fun x => do
    let result ← Lean.Meta.whnf (body.instantiate1 x)
    return result == Lean.mkSort .zero
  Lean.Meta.mkAppM (if isPredicate then ``ComputablePred else ``Computable) #[subject]

/-- Bare emptiness adjectives infer the domain; explicit nouns check it.
List forms preserve equality or inequality with nil directly. -/
elab "emptinessOn%" adjective:meanAdjective "of" t:term : term => do
  let (isNonempty, listExpected) : Bool × Option Bool ← match adjective with
    | `(meanAdjective| nonempty) => pure (true, none)
    | `(meanAdjective| empty) => pure (false, none)
    | `(meanAdjective| a nonempty type) => pure (true, some false)
    | `(meanAdjective| an empty type) => pure (false, some false)
    | `(meanAdjective| a nonempty list) => pure (true, some true)
    | `(meanAdjective| an empty list) => pure (false, some true)
    | _ => Lean.throwErrorAt adjective "expected an emptiness adjective"
  let subject ← Lean.Elab.Term.elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType subject)
  if ty.isSort && listExpected != some true then
    Lean.Meta.mkAppM (if isNonempty then ``Nonempty else ``IsEmpty) #[subject]
  else if ty.isAppOfArity ``List 1 && listExpected != some false then
    let nil ← Lean.Meta.mkAppOptM ``List.nil #[some ty.getAppArgs[0]!]
    Lean.Meta.mkAppM (if isNonempty then ``Ne else ``Eq) #[subject, nil]
  else
    Lean.throwErrorAt t (match listExpected with
      | some true => "expected a list"
      | some false => "expected a type"
      | none => "expected a type or list")

macro_rules
  | `($subject:term satisfies $predicate:meanAdjective) =>
      `($subject is $predicate)
  | `($subject:term does not satisfy $predicate:meanAdjective) =>
      `($subject is not $predicate)
  | `($x:term and $y:term $[and $zs:term]* satisfy $predicate:meanAdjective) =>
      `($x and $y $[and $zs]* are $predicate)
  | `($x:term and $y:term $[and $zs:term]* do not satisfy $predicate:meanAdjective) =>
      `($x and $y $[and $zs]* are not $predicate)
  | `($x:term is related to $y:term by $r:term) =>
      `(relationApply% $r of [$x, $y])
  | `($x:term is not related to $y:term by $r:term) =>
      `(Not (relationApply% $r of [$x, $y]))
  | `($x:term and $y:term $[and $zs:term]* are $predicate:meanAdjective) => do
      let args := #[x, y] ++ zs
      `(relationApply% (adjectivePredicate% $predicate) of [$args,*])
  | `($x:term and $y:term $[and $zs:term]* are not $predicate:meanAdjective) => do
      let args := #[x, y] ++ zs
      `(Not (relationApply% (adjectivePredicate% $predicate) of [$args,*]))
  | `($subject:term is $adjective:meanAdjective) =>
      `(adjectiveOn% $adjective of $subject)
  | `($subject:term is not $adjective:meanAdjective) =>
      `(Not (adjectiveOn% $adjective of $subject))
  | `(adjectiveOn% computable of $subject:term) => `(computableOn% $subject)
  | `(adjectiveOn% nonempty of $subject:term) => `(emptinessOn% nonempty of $subject)
  | `(adjectiveOn% empty of $subject:term) => `(emptinessOn% empty of $subject)
  | `(adjectiveOn% a nonempty type of $subject:term) => `(emptinessOn% a nonempty type of $subject)
  | `(adjectiveOn% an empty type of $subject:term) => `(emptinessOn% an empty type of $subject)
  | `(adjectiveOn% a nonempty list of $subject:term) => `(emptinessOn% a nonempty list of $subject)
  | `(adjectiveOn% an empty list of $subject:term) => `(emptinessOn% an empty list of $subject)
  | `(adjectiveOn% $adjective:meanAdjective of $subject:term) =>
      `(adjectiveApply% (adjectivePredicate% $adjective) of $subject)
  | `(adjectivePredicate% nonempty) => `(Nonempty)
  | `(adjectivePredicate% empty) => `(IsEmpty)
  | `(adjectivePredicate% a nonempty set) => `(Set.Nonempty)
  | `(adjectivePredicate% an empty set) => `(fun (s : Set _) => s = ∅)
  | `(adjectivePredicate% finite) => `(Finite)
  | `(adjectivePredicate% infinite) => `(Infinite)
  | `(adjectivePredicate% countable) => `(Countable)
  | `(adjectivePredicate% injective) => `(Function.Injective)
  | `(adjectivePredicate% surjective) => `(Function.Surjective)
  | `(adjectivePredicate% bijective) => `(Function.Bijective)
  | `(adjectivePredicate% recursively enumerable) => `(REPred)
  | `(adjectivePredicate% $predicate:ident) => `($predicate)
  | `(adjectivePredicate% ($predicate:term)) => `($predicate)

/-- Quantifiers share predicate application, including ordered subject lists. -/
private def qualifierCondition (names : Array Lean.Ident) (predicate : Lean.TSyntax `meanAdjective) :
    Lean.MacroM (Lean.TSyntax `term) := do
  if names.size == 1 then
    `(adjectiveOn% $predicate of $(names[0]!))
  else
    let args : Array (Lean.TSyntax `term) := names.map (fun name => ⟨name.raw⟩)
    `(relationApply% (adjectivePredicate% $predicate) of [$args,*])

private inductive RestrictionMode where
  | implication
  | conjunction

/-- Universal and almost-everywhere restrictions imply their body; existential
restrictions conjoin with it. No body is distinct from an explicit `True` body. -/
private def restrictedBody (mode : RestrictionMode) (conditions : Array (Lean.TSyntax `term))
    (body : Option (Lean.TSyntax `term)) : Lean.MacroM (Lean.TSyntax `term) := do
  let mut result := body
  for condition in conditions.reverse do
    let next ← match result with
      | none => pure condition
      | some body => match mode with
        | .implication => `(∀ (_ : ($condition : Prop)), ($body : Prop))
        | .conjunction => `($condition ∧ ($body : Prop))
    result := some next
  match result with
  | some body => pure body
  | none => `(True)

/-! Properties share both surface forms; each noun supplies its interpretation.
Lean lexes `G's` as one identifier, so the possessive rule removes that suffix. -/
declare_syntax_cat meanProperty
syntax "edge" "set" : meanProperty
syntax "vertex" "type" : meanProperty
syntax "propertyOf%" meanProperty "of" term:arg : term
-- Bind above comparisons but below arithmetic, so printing groups property operands.
syntax:60 "the " meanProperty " of " term:arg : term
def possessiveOwner : Lean.Parser.Parser :=
  Lean.Parser.identNoAntiquot >> Lean.Parser.checkStackTop
    (fun stx => stx.getId.toString.endsWith "'s") "possessive identifier such as G's"
syntax:max (name := possessiveProperty) possessiveOwner meanProperty : term

/-- Recover the name shared by possessive property and neighbor phrases. -/
private def possessiveName (owner : Lean.Syntax) : Lean.MacroM (Lean.TSyntax `ident) := do
  let .str namePrefix last := owner.getId
    | Lean.Macro.throwErrorAt owner "expected a possessive identifier such as G's"
  unless last.length > 2 do
    Lean.Macro.throwErrorAt owner "expected a name before 's"
  return Lean.mkIdentFrom owner (.str namePrefix (last.dropEnd 2).toString)

@[macro possessiveProperty]
def expandPossessiveProperty : Lean.Macro := fun stx => do
  let owner ← possessiveName stx[0]
  let property : Lean.TSyntax `meanProperty := ⟨stx[1]⟩
  `(propertyOf% $property of $owner:ident)

macro_rules
  | `(the $property:meanProperty of $owner:term) =>
      `(propertyOf% $property of $owner)
  | `(propertyOf% edge set of $g:term) => `(SimpleGraph.edgeSet $g)
  | `(propertyOf% vertex type of $g:term) => `(SimpleGraph.V $g)

/-! Vertex-relative properties share one interpretation per set kind.
Surface variants place the vertex before the ambient graph. -/
declare_syntax_cat meanVertexSet
syntax "neighbor" "set" : meanVertexSet
syntax "incidence" "set" : meanVertexSet
syntax "vertexSetOf%" meanVertexSet "at" term:arg "in" term:arg : term
macro_rules
  | `(vertexSetOf% neighbor set at $v:term in $g:term) => `(SimpleGraph.neighborSet $g $v)
  | `(vertexSetOf% incidence set at $v:term in $g:term) => `(SimpleGraph.incidenceSet $g $v)

declare_syntax_cat meanVertexProperty
syntax meanVertexSet "of" : meanVertexProperty
syntax "set" "of" "neighbors" "of" : meanVertexProperty
syntax "set" "of" "edges" "incident" "to" : meanVertexProperty
syntax "vertexPropertyOf%" meanVertexProperty term:arg "in" term:arg : term
syntax:60 "the " meanVertexProperty ppSpace term:arg " in " term:arg : term
macro_rules
  | `(the $property:meanVertexProperty $v:term in $g:term) =>
      `(vertexPropertyOf% $property $v in $g)
  | `(vertexPropertyOf% $kind:meanVertexSet of $v:term in $g:term) =>
      `(vertexSetOf% $kind at $v in $g)
  | `(vertexPropertyOf% set of neighbors of $v:term in $g:term) =>
      `(vertexSetOf% neighbor set at $v in $g)
  | `(vertexPropertyOf% set of edges incident to $v:term in $g:term) =>
      `(vertexSetOf% incidence set at $v in $g)

syntax:max (name := possessiveVertexSet) possessiveOwner meanVertexSet "in" term:arg : term
@[macro possessiveVertexSet]
def expandPossessiveVertexSet : Lean.Macro := fun stx => do
  let v ← possessiveName stx[0]
  let kind : Lean.TSyntax `meanVertexSet := ⟨stx[1]⟩
  let g : Lean.TSyntax `term := ⟨stx[3]⟩
  `(vertexSetOf% $kind at $v:ident in $g)

syntax:max (name := possessiveNeighbors)
  "the" "set" "of" possessiveOwner "neighbors" "in" term:arg : term
@[macro possessiveNeighbors]
def expandPossessiveNeighbors : Lean.Macro := fun stx => do
  let v ← possessiveName stx[3]
  let g : Lean.TSyntax `term := ⟨stx[6]⟩
  `(vertexSetOf% neighbor set at $v:ident in $g)

/-- Keep the sentence's period out of Lean's field-completion parser. -/
def sentenceBody : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "." Lean.Parser.termParser

private def predicateVerbs : Array String := #["is", "are", "satisfies", "satisfy"]

private def subjectContext (ctx : Lean.Parser.CacheableParserContext) :
    Lean.Parser.CacheableParserContext :=
  if ctx.forbiddenTks.contains "and" then ctx
  else { ctx with forbiddenTks := ctx.forbiddenTks.filter (· == ".") ++ predicateVerbs }

/-- Definitions end a subject type at their predicate verb; function lists end it at `and`.
Parentheses disable these delimiters inside a compound type. -/
def subjectType : Lean.Parser.Parser :=
  Lean.Parser.adaptCacheableContext subjectContext
    Lean.Parser.termParser

/-- Collection descriptions end their element type at the explicit plural noun. -/
def listElementType : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "elements" Lean.Parser.termParser

/-- Function domains and results stop before the surrounding phrase's separators.
Parentheses retain ordinary Lean types containing these tokens. -/
declare_syntax_cat meanFunctionEndpoint
syntax term : meanFunctionEndpoint

def functionDomain : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["and", "to"]
    (Lean.Parser.categoryParser `meanFunctionEndpoint 0)

def functionResult : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens (#["and", "to"] ++ predicateVerbs)
    (Lean.Parser.categoryParser `meanFunctionEndpoint 0)

declare_syntax_cat meanFunctionSignature
syntax "from" functionDomain ("and" functionDomain)* "to" functionResult : meanFunctionSignature

/-- A nested signature owns its internal `and` and `to` separators.
Its result parser restores the outer delimiters. -/
private def signatureParser (category : Lean.Name) : Lean.Parser.Parser :=
  Lean.Parser.adaptCacheableContext
    (fun ctx => { ctx with forbiddenTks := ctx.forbiddenTks.filter (fun tk => tk != "and" && tk != "to") })
    (Lean.Parser.categoryParser category 0)

def functionSignature : Lean.Parser.Parser := signatureParser `meanFunctionSignature

declare_syntax_cat meanEmbeddingSignature
syntax "from " functionDomain " to " functionResult : meanEmbeddingSignature
def embeddingSignature : Lean.Parser.Parser := signatureParser `meanEmbeddingSignature
def embeddingWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "embedding "
syntax:max "an " embeddingWord embeddingSignature : term
syntax:max "an " "injective " "function " embeddingSignature : term

syntax "functionType%" functionSignature : term
syntax "functionEndpointType%" meanFunctionEndpoint : term
macro_rules
  | `(an embedding $signature:meanEmbeddingSignature) =>
      `(an injective function $signature)
  | `(an injective function from $domain:meanFunctionEndpoint to $result:meanFunctionEndpoint) =>
      `(Function.Embedding (functionEndpointType% $domain) (functionEndpointType% $result))
  | `(functionEndpointType% $ty:term) => `($ty)
  | `(functionType% from $domain:meanFunctionEndpoint $[and $domains:meanFunctionEndpoint]*
        to $result:meanFunctionEndpoint) => do
      let mut result ← `(functionEndpointType% $result)
      for domain in domains.reverse do
        result ← `((functionEndpointType% $domain) → $result)
      `((functionEndpointType% $domain) → $result)

/-! One scalar noun-to-type mapping serves subjects and all quantifiers.
Plural domains delegate to their singular noun through `scalarDomainType%`. -/
declare_syntax_cat meanScalar
syntax "natural" "number" : meanScalar
syntax "integer" : meanScalar
syntax "rational" "number" : meanScalar
syntax "real" "number" : meanScalar
syntax "complex" "number" : meanScalar
syntax "boolean" : meanScalar
syntax "scalarType%" meanScalar : term

macro_rules
  | `(scalarType% natural number) => `(Nat)
  | `(scalarType% integer) => `(Int)
  | `(scalarType% rational number) => `(Rat)
  | `(scalarType% real number) => `(Real)
  | `(scalarType% complex number) => `(Complex)
  | `(scalarType% boolean) => `(Bool)

/-- Treat a bare trailing decimal point as sentence punctuation in a typed
scalar operand. Decimal fractions, exponents, and ordinary Lean terms retain
their normal parsing. The numeral node preserves its original source range. -/
def scalarOperandFn (normalFn : Lean.Parser.ParserFn) : Lean.Parser.ParserFn :=
  fun ctx s =>
    if ctx.forbiddenTks.contains "." && (ctx.get s.pos).isDigit then
      let digits := Lean.Parser.takeDigitsFn Char.isDigit "decimal number" true ctx s
      let following := ctx.get (ctx.next digits.pos)
      if !digits.hasError && ctx.get digits.pos == '.' &&
          !following.isDigit && following != 'e' && following != 'E' && following != '.' then
        Lean.Parser.mkNodeToken Lean.numLitKind s.pos true ctx digits
      else normalFn ctx s
    else normalFn ctx s

-- Preserve Lean's term formatter and parenthesizer for the operand.
def scalarOperand : Lean.Parser.Parser :=
  Lean.Parser.withFn scalarOperandFn (Lean.Parser.termParser Lean.Parser.argPrec)

-- Scalar descriptions annotate values independently of definitions and binders.
syntax:max "the" meanScalar ppSpace scalarOperand : term
syntax:max "the" meanScalar "-" scalarOperand : term
macro_rules
  | `(the $noun:meanScalar $value:term) => `(($value : scalarType% $noun))
  | `(the $noun:meanScalar - $value:term) => `((-$value : scalarType% $noun))

/-- Request a checked Lean coercion, rather than a type annotation alone.
The source is inferred independently so its arithmetic keeps its original type. -/
syntax:70 term:70 " as " "a " meanScalar : term
syntax:70 term:70 " as " "an " meanScalar : term
syntax:70 term:70 " as " term:71 : term
macro_rules
  | `($value:term as a $noun:meanScalar) => `((↑($value) : scalarType% $noun))
  | `($value:term as an $noun:meanScalar) => `((↑($value) : scalarType% $noun))
  | `($value:term as $ty:term) => `((↑($value) : $ty))

declare_syntax_cat meanScalarDomain
syntax meanScalar : meanScalarDomain
declare_syntax_cat meanScalarPlural
syntax "natural" "numbers" : meanScalarPlural
syntax "integers" : meanScalarPlural
syntax "rational" "numbers" : meanScalarPlural
syntax "real" "numbers" : meanScalarPlural
syntax "complex" "numbers" : meanScalarPlural
syntax "booleans" : meanScalarPlural
syntax meanScalarPlural : meanScalarDomain
syntax "scalarDomainType%" meanScalarDomain : term

macro_rules
  | `(scalarDomainType% $noun:meanScalar) => `(scalarType% $noun)
  | `(scalarDomainType% natural numbers) => `(scalarType% natural number)
  | `(scalarDomainType% integers) => `(scalarType% integer)
  | `(scalarDomainType% rational numbers) => `(scalarType% rational number)
  | `(scalarDomainType% real numbers) => `(scalarType% real number)
  | `(scalarDomainType% complex numbers) => `(scalarType% complex number)
  | `(scalarDomainType% booleans) => `(scalarType% boolean)

/-! Lists and sets share element descriptions, retaining custom type names
and using familiar scalar plurals. -/
declare_syntax_cat meanListElements
syntax meanScalarPlural : meanListElements
syntax "functions " functionSignature : meanListElements
syntax listElementType ppSpace "elements" : meanListElements
syntax "listType%" meanListElements : term
macro_rules
  | `(listType% $plural:meanScalarPlural) => do
      let domain ← `(meanScalarDomain| $plural:meanScalarPlural)
      `(List (scalarDomainType% $domain))
  | `(listType% functions $signature:meanFunctionSignature) => `(List (functionType% $signature))
  | `(listType% $ty:term elements) => `(List $ty)

syntax "setType%" meanListElements : term
macro_rules
  | `(setType% $plural:meanScalarPlural) => do
      let domain ← `(meanScalarDomain| $plural:meanScalarPlural)
      `(Set (scalarDomainType% $domain))
  | `(setType% functions $signature:meanFunctionSignature) => `(Set (functionType% $signature))
  | `(setType% $ty:term elements) => `(Set $ty)

/-! Index ranges are types, not real intervals or sets. The lower endpoint must
be zero; the upper endpoint is exclusive, including when it is zero. -/
declare_syntax_cat meanIndexRange
syntax "[" num ", " term ")" : meanIndexRange
syntax "indices " meanIndexRange : term
macro_rules
  | `(indices [$lower:num, $upper:term)) => do
      unless lower.getNat == 0 do
        Lean.Macro.throwErrorAt lower "index ranges must start at 0"
      `(Fin $upper)

declare_syntax_cat meanIndexDomain
syntax "in " meanIndexRange : meanIndexDomain
syntax "into " subjectType : meanIndexDomain
syntax "indexType%" meanIndexDomain : term

/-- Valid element indices for lists and arrays, preserving the exact collection. -/
elab "indexIntoType%" t:term : term => do
  let collection ← Lean.Elab.Term.elabTerm t none
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType collection)
  let bound ← if ty.isAppOfArity ``List 1 then
      Lean.Meta.mkAppM ``List.length #[collection]
    else if ty.isAppOfArity ``Array 1 then
      Lean.Meta.mkAppM ``Array.size #[collection]
    else Lean.throwErrorAt t "expected a list or array"
  Lean.Meta.mkAppM ``Fin #[bound]

macro_rules
  | `(indexType% in $range:meanIndexRange) => `(indices $range)
  | `(indexType% into $collection:term) => `(indexIntoType% $collection)

/-! Type descriptions name collections of possible values. Bindings use the
singular noun phrases declared below, including when their name is omitted. -/
declare_syntax_cat meanTypeDescription
syntax meanScalarPlural : meanTypeDescription
syntax "lists " "of " meanListElements : meanTypeDescription
syntax "sets " "of " meanListElements : meanTypeDescription
syntax "indices " meanIndexDomain : meanTypeDescription
syntax meanTypeDescription : meanFunctionEndpoint
syntax "describedType%" meanTypeDescription : term
syntax:max "the " "type " "of " meanTypeDescription : term
macro_rules
  | `(functionEndpointType% $description:meanTypeDescription) => `(describedType% $description)
  | `(the type of $description:meanTypeDescription) => `(describedType% $description)
  | `(describedType% $plural:meanScalarPlural) => do
      let domain ← `(meanScalarDomain| $plural:meanScalarPlural)
      `(scalarDomainType% $domain)
  | `(describedType% lists of $items:meanListElements) => `(listType% $items)
  | `(describedType% sets of $items:meanListElements) => `(setType% $items)
  | `(describedType% indices $domain:meanIndexDomain) => `(indexType% $domain)

/-! Sums and indexed unions share index descriptions. Their bodies stop
before comparisons and logical connectives. -/
def aggregateDomain : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "of" Lean.Parser.termParser

declare_syntax_cat meanAggregateIndex
syntax "indices" ident (" and " ident)? meanIndexDomain : meanAggregateIndex
syntax "elements " ident (" and " ident)? " of " aggregateDomain : meanAggregateIndex
syntax meanScalarPlural ppSpace ident (" and " ident)? : meanAggregateIndex
syntax ident " in " aggregateDomain : meanAggregateIndex
def unionWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "union "
def intersectionWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "intersection "
syntax:60 "the " "sum " "over " meanAggregateIndex " of " term:60 : term
syntax:60 "the " unionWord "over " meanAggregateIndex " of" ppLine term:60 : term
syntax:60 "the " intersectionWord "over " meanAggregateIndex " of" ppLine term:60 : term

private def aggregateBinder (binding : Lean.TSyntax `meanAggregateIndex) :
    Lean.MacroM (Lean.Ident × Option Lean.Ident × Lean.Term) := do
  match binding with
  | `(meanAggregateIndex| indices $i:ident $[and $j:ident]? $domain:meanIndexDomain) =>
      pure (i, j, ← `(indexType% $domain))
  | `(meanAggregateIndex| elements $i:ident $[and $j:ident]? of $ty:term) => pure (i, j, ty)
  | `(meanAggregateIndex| $plural:meanScalarPlural $i:ident $[and $j:ident]?) => do
      let domain ← `(meanScalarDomain| $plural:meanScalarPlural)
      pure (i, j, ← `(scalarDomainType% $domain))
  | _ => Lean.Macro.throwUnsupported

private def typedAggregate (op : Lean.Term) (binding : Lean.TSyntax `meanAggregateIndex)
    (body : Lean.Term) : Lean.MacroM Lean.Term := do
  let (i, j, ty) ← aggregateBinder binding
  if let some j := j then
    -- Resolve the shared domain before either index can shadow its free names.
    `(let sharedType := $ty
      $op (fun ($i : sharedType) => $op (fun ($j : sharedType) => $body)))
  else
    `($op (fun ($i : $ty) => $body))

macro_rules
  | `(the sum over $i:ident in $s:term of $body:term) =>
      `(Finset.sum $s (fun $i => $body))
  | `(the sum over $binding:meanAggregateIndex of $body:term) => do
      typedAggregate (← `(Finset.sum Finset.univ)) binding body
  | `(the union over $i:ident in $s:term of $body:term) =>
      `(⋃ $i:ident ∈ $s, $body)
  | `(the union over $binding:meanAggregateIndex of $body:term) => do
      typedAggregate (← `(Set.iUnion)) binding body
  | `(the intersection over $i:ident in $s:term of $body:term) =>
      `(⋂ $i:ident ∈ $s, $body)
  | `(the intersection over $binding:meanAggregateIndex of $body:term) => do
      typedAggregate (← `(Set.iInter)) binding body

/-- The word `typeclass` requires a class application, including proposition-valued classes. -/
elab "typeclassType%" t:term : term => do
  let ty ← Lean.Elab.Term.elabType t
  unless (← Lean.Meta.isClass? ty).isSome do
    Lean.throwErrorAt t "expected a typeclass application"
  return ty

declare_syntax_cat meanWitnessNoun
syntax "element" (ppSpace ident)? " of " term : meanWitnessNoun
syntax "type" (ppSpace ident)? : meanWitnessNoun
syntax "proof" (ppSpace ident)? " that " term : meanWitnessNoun
syntax meanScalar (ppSpace ident)? : meanWitnessNoun
syntax "path" (ppSpace ident)? " in " term " from " term " to " term : meanWitnessNoun
syntax "list" (ppSpace ident)? " of " meanListElements : meanWitnessNoun
syntax "set" (ppSpace ident)? " of " meanListElements : meanWitnessNoun
syntax "index" (ppSpace ident)? meanIndexDomain : meanWitnessNoun
syntax "function" (ppSpace ident)? functionSignature : meanWitnessNoun
syntax "injective" "function" (ppSpace ident)? embeddingSignature : meanWitnessNoun
syntax "instance" (ppSpace ident)? " of " "typeclass" term : meanWitnessNoun

private def nounBinding (noun : Lean.TSyntax `meanWitnessNoun) :
    Lean.MacroM (Option Lean.Ident × Lean.TSyntax `term) :=
  match noun with
    | `(meanWitnessNoun| element $[$x:ident]? of $ty:term) => pure (x, ty)
    | `(meanWitnessNoun| type $[$x:ident]?) => do pure (x, ← `(Type))
    | `(meanWitnessNoun| proof $[$x:ident]? that $p:term) => do
        pure (x, ← `(($p : Prop)))
    | `(meanWitnessNoun| $scalar:meanScalar $[$x:ident]?) => do
        pure (x, ← `(scalarType% $scalar))
    | `(meanWitnessNoun| list $[$x:ident]? of $items:meanListElements) => do
        pure (x, ← `(listType% $items))
    | `(meanWitnessNoun| set $[$x:ident]? of $items:meanListElements) => do
        pure (x, ← `(setType% $items))
    | `(meanWitnessNoun| index $[$x:ident]? $domain:meanIndexDomain) => do
        pure (x, ← `(indexType% $domain))
    | `(meanWitnessNoun| function $[$x:ident]? $signature:meanFunctionSignature) => do
        pure (x, ← `(functionType% $signature))
    | `(meanWitnessNoun| injective function $[$x:ident]? $signature:meanEmbeddingSignature) => do
        pure (x, ← `(an injective function $signature))
    | `(meanWitnessNoun| instance $[$x:ident]? of typeclass $ty:term) => do
        pure (x, ← `(typeclassType% $ty))
    | `(meanWitnessNoun| path $[$x:ident]? in $g:term from $u:term to $v:term) => do
        pure (x, ← `(SimpleGraph.Path $g $u $v))
    | _ => Lean.Macro.throwErrorAt noun "unsupported quantified noun"

/-! Subjects specify bindings, independently of the definition clause.
New subject forms implement `functionOn%`, shared by functions and predicates. -/
/-- Subject nouns keep predicate verbs outside their type expressions. -/
def subjectNoun : Lean.Parser.Parser :=
  Lean.Parser.adaptCacheableContext subjectContext
    (Lean.Parser.categoryParser `meanWitnessNoun 0)

declare_syntax_cat meanSubject
syntax "a" "simple" "graph" (ppSpace ident)? : meanSubject
syntax "a" "simple" "graph" (ppSpace ident)? "=" "(" ident "," ident ")" : meanSubject
syntax "a" subjectNoun : meanSubject
syntax "an" subjectNoun : meanSubject
syntax "an" "implicit" subjectNoun : meanSubject
syntax "a" "strictly" "implicit" subjectNoun : meanSubject

/-- Omitted names are hygienic: they cannot capture references in the user's body. -/
private def parameterName (name : Option (Lean.TSyntax `ident)) : Lean.MacroM (Lean.TSyntax `ident) :=
  match name with
  | some name => pure name
  | none => `(ident| _anonymousParameter)

/-- Keep binder separators out of an unparenthesized element type. -/
def functionSubject : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "and" (Lean.Parser.categoryParser `meanSubject 0)

-- Internal composition point: subject bindings scoped over a value.
syntax "functionOn%" meanSubject "=>" term : term
syntax "functionOver%" functionSubject ("and" functionSubject)* "=>" term : term
syntax "predicateOn%" meanSubject "=>" term : term
syntax "the" "function" "mapping" functionSubject (" and " functionSubject)*
  " to" ppIndent(ppLine term) : term
syntax "the" "function" ":" term "mapping" functionSubject (" and " functionSubject)*
  " to" ppIndent(ppLine term) : term
syntax:max "the " "type " "of " "functions " functionSignature : term

macro_rules
  | `(the type of functions $signature:meanFunctionSignature) => `(functionType% $signature)
  | `(the function mapping $subject:meanSubject $[and $subjects:meanSubject]* to $body:term) =>
      `(functionOver% $subject $[and $subjects]* => $body)
  | `(the function : $ty:term mapping $subject:meanSubject $[and $subjects:meanSubject]* to $body:term) =>
      `(((functionOver% $subject $[and $subjects]* => $body) : $ty))
  | `(functionOver% $subject:meanSubject $[and $subjects:meanSubject]* => $body:term) => do
      let mut body := body
      for subject in subjects.reverse do
        body ← `(functionOn% $subject => $body)
      `(functionOn% $subject => $body)
  | `(predicateOn% $subject:meanSubject => $body:term) =>
      `(functionOn% $subject => ($body : Prop))
  | `(functionOn% a simple graph $[$g:ident]? => $body:term) => do
      let g ← parameterName g
      `(fun {Vertex : Type*} ($g : SimpleGraph Vertex) => $body)
  | `(functionOn% a simple graph $[$g:ident]? = ($vs:ident, $es:ident) => $body:term) => do
      let g ← parameterName g
      let names := [g.getId, vs.getId, es.getId]
      unless names.eraseDups.length == names.length do
        Lean.Macro.throwErrorAt g
          "the graph, vertex type, and edge set must have distinct names"
      `(fun {$vs : Type*} ($g : SimpleGraph $vs) =>
          let $es := SimpleGraph.edgeSet $g
          $body)
  | `(functionOn% a $noun:meanWitnessNoun => $body:term) =>
      `(functionOn% an $noun => $body)
  | `(functionOn% an $noun:meanWitnessNoun => $body:term) => do
      let (name, ty) ← nounBinding noun
      let name ← parameterName name
      if let `(meanWitnessNoun| instance $[$_:ident]? of typeclass $_:term) := noun then
        `(fun [$name : $ty] => $body)
      else
        `(fun ($name : $ty) => $body)
  | `(functionOn% an implicit $noun:meanWitnessNoun => $body:term) => do
      let (name, ty) ← nounBinding noun
      let name ← parameterName name
      `(fun {$name : $ty} => $body)
  | `(functionOn% a strictly implicit $noun:meanWitnessNoun => $body:term) => do
      let (name, ty) ← nounBinding noun
      let name ← parameterName name
      `(fun ⦃$name : $ty⦄ => $body)

/-! English inductive declarations share subject binding with functions. -/
def inductiveSubject : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["and", "with", "indexed", "to", ";", "."]
    (Lean.Parser.categoryParser `meanSubject 0)
declare_syntax_cat meanConstructorInputs
syntax inductiveSubject ("and" inductiveSubject)* : meanConstructorInputs
def constructorElementType : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["and", "to", ";", "."] Lean.Parser.termParser
syntax "two" "elements" "of" constructorElementType : meanConstructorInputs
def constructorInputs : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["to", ";", "."] (Lean.Parser.categoryParser `meanConstructorInputs 0)
declare_syntax_cat meanConstructorClause
def constructorResult : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #[";", "."] Lean.Parser.termParser
syntax ident ("from" constructorInputs)? ("to" constructorResult)? : meanConstructorClause
syntax "Inductive" "type" ident
  ("parameterized" "by" inductiveSubject ("and" inductiveSubject)*)?
  (atomic("with" "values" "in") sentenceBody)?
  "with" "constructors" ":" ppIndent(ppLine sepBy(meanConstructorClause, ";")) "." : command
syntax "Inductive" "family" ident
  ("parameterized" "by" inductiveSubject ("and" inductiveSubject)*)?
  "indexed" "by" inductiveSubject ("and" inductiveSubject)*
  (atomic("with" "values" "in") sentenceBody)?
  "with" "constructors" ":" ppIndent(ppLine sepBy(meanConstructorClause, ";")) "." : command

/-- Extract typed binders through the existing function-subject extension hook. -/
private partial def subjectBinders (subject : Lean.TSyntax `meanSubject) :
    Lean.MacroM (Array (Lean.TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut expanded ← `(functionOn% $subject => True)
  for _ in [:100] do
    if let `(fun $binders* => $_:term) := expanded then
      return ← binders.mapM fun binder => do
        if binder.raw.isOfKind ``Lean.Parser.Term.typeAscription then
          let `(($name:ident : $ty:term)) := binder.raw
            | Lean.Macro.throwErrorAt binder "expected a named typed binder"
          return ⟨← Lean.Elab.Term.expandSimpleBinderWithType ty name.raw⟩
        else
          pure ⟨binder.raw⟩
    let some next ← Lean.expandMacro? expanded
      | Lean.Macro.throwErrorAt subject "expected a subject introducing typed binders"
    expanded := ⟨next⟩
  Lean.Macro.throwErrorAt subject "subject expansion did not terminate"

def signatureSubject : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "meanSubject" `meanSubject (isPseudoKind := true))
    (Lean.Parser.withForbiddens #["and", ":"] (Lean.Parser.categoryParser `meanSubject 0))

syntax "with" signatureSubject (" and " signatureSubject)* ":" ppLine term : term
def parameterWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "parameter "
def parametersWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "parameters "
syntax "with" "implicit" "type" parameterWord ident ":" ppLine term : term
syntax "with" "implicit" "type" parametersWord ident (" and " ident)+ ":" ppLine term : term
macro_rules
  | `(with $first:meanSubject $[and $rest:meanSubject]* : $body:term) => do
      let binders ← (#[first] ++ rest).foldlM
        (fun acc subject => return acc ++ (← subjectBinders subject)) #[]
      `(∀ $binders:bracketedBinder*, $body)
  | `(with implicit type parameter $name:ident : $body:term) =>
      `(∀ {$name:ident : Type}, $body)
  | `(with implicit type parameters $first:ident $[and $rest:ident]* : $body:term) =>
      `(∀ {$first:ident $rest:ident* : Type}, $body)

private def inductiveBinderNames (binders : Array (Lean.TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    Array (Lean.TSyntax `term) :=
  binders.flatMap fun binder =>
    -- Instance binders are [name : type]; other typed binders contain an identifier list.
    if binder.raw.isOfKind ``Lean.Parser.Term.instBinder then
      #[⟨binder.raw[1][0]⟩]
    else binder.raw[1].getArgs.map (fun name => ⟨name⟩)

private def englishInductive (name : Lean.Ident) (parameters idxs : Array (Lean.TSyntax `meanSubject))
    (sort : Option Lean.Term) (clauses : Array (Lean.TSyntax `meanConstructorClause)) :
    Lean.MacroM (Lean.TSyntax `command) := do
  let parameters ← parameters.foldlM (fun acc subject => return acc ++ (← subjectBinders subject)) #[]
  let idxs ← idxs.foldlM (fun acc subject => return acc ++ (← subjectBinders subject)) #[]
  let mut result ← match sort with
    | some sort => pure sort
    | none => `(Type)
  if !idxs.isEmpty then result ← `(∀ $idxs:bracketedBinder*, $result)
  let args := inductiveBinderNames parameters
  let defaultResult ← `(@$name $args*)
  let mut ctorSyntax : Array (Lean.TSyntax ``Lean.Parser.Command.ctor) := #[]
  for clause in clauses do
    let `(meanConstructorClause| $ctor:ident $[from $inputs:meanConstructorInputs]? $[to $target:term]?) := clause
      | Lean.Macro.throwUnsupported
    if !idxs.isEmpty && target.isNone then
      Lean.Macro.throwErrorAt clause "indexed constructors require an explicit to result"
    let mut ty := target.getD defaultResult
    if let some inputs := inputs then
      let binders ← match inputs with
        | `(meanConstructorInputs| $first:meanSubject $[and $rest:meanSubject]*) =>
          (#[first] ++ rest).foldlM (fun acc subject => return acc ++ (← subjectBinders subject)) #[]
        | `(meanConstructorInputs| two elements of $domain:term) => do
          let subject ← `(meanSubject| an element of $domain)
          pure ((← subjectBinders subject) ++ (← subjectBinders subject))
        | _ => Lean.Macro.throwUnsupported
      ty ← `(∀ $binders:bracketedBinder*, $ty)
    ctorSyntax := ctorSyntax.push (← `(Lean.Parser.Command.ctor| | $ctor:ident : $ty))
  `(command| inductive $name $parameters:bracketedBinder* : $result where $ctorSyntax:ctor*)

macro_rules
  | `(command| Inductive type $name:ident
      $[parameterized by $first:meanSubject $[and $rest:meanSubject]*]?
      $[with values in $sort:term]? with constructors: $clauses:meanConstructorClause;* .) =>
    englishInductive name (first.toArray ++ rest.getD #[]) #[] sort clauses.getElems
  | `(command| Inductive family $name:ident
      $[parameterized by $first:meanSubject $[and $rest:meanSubject]*]?
      indexed by $idx:meanSubject $[and $idxs:meanSubject]*
      $[with values in $sort:term]? with constructors: $clauses:meanConstructorClause;* .) =>
    englishInductive name (first.toArray ++ rest.getD #[]) (#[idx] ++ idxs) sort clauses.getElems

/-- The declaration checker preserves the actual printed command when renaming. -/
def inductiveDeclarationName? (stx : Lean.Syntax) : Option Lean.Ident :=
  match stx with
  | `(command| Inductive $name:ident $_:bracketedBinder* : $_:term where $_:ctor*) => some name
  | `(command| Inductive type $name:ident $[parameterized by $_:meanSubject $[and $_:meanSubject]*]?
      $[with values in $_:term]? with constructors: $_:meanConstructorClause;* .) => some name
  | `(command| Inductive family $name:ident $[parameterized by $_:meanSubject $[and $_:meanSubject]*]?
      indexed by $_:meanSubject $[and $_:meanSubject]*
      $[with values in $_:term]? with constructors: $_:meanConstructorClause;* .) => some name
  | _ => none

/-! Multiple predicate subjects share function binding semantics. Plural nouns
group names of the same type; mixed subjects keep their individual descriptions. -/
declare_syntax_cat meanPredicateSubjects
syntax functionSubject "and" functionSubject ("and" functionSubject)* : meanPredicateSubjects
syntax "elements" ident "and" ident ("and" ident)* "of" subjectType : meanPredicateSubjects
syntax meanScalarPlural ident "and" ident ("and" ident)* : meanPredicateSubjects
syntax "indices" ident "and" ident ("and" ident)* meanIndexDomain : meanPredicateSubjects
syntax "predicateOver%" meanPredicateSubjects "=>" term : term
macro_rules
  | `(predicateOver% $first:meanSubject and $second:meanSubject $[and $rest:meanSubject]* => $body:term) =>
      `(functionOver% $first and $second $[and $rest]* => ($body : Prop))
  | `(predicateOver% elements $x:ident and $y:ident $[and $zs:ident]* of $ty:term => $body:term) => do
      -- Elaborate the common domain outside all the new bindings, so a name
      -- cannot capture a reference to an outer type in a later argument.
      let names : Array (Lean.TSyntax ``Lean.Parser.Term.funBinder) :=
        (#[x, y] ++ zs).map (fun name => ⟨name.raw⟩)
      let mut signature ← `(Prop)
      for _ in [:names.size] do
        signature ← `($ty → $signature)
      let predicate ← `(fun $names* => ($body : Prop))
      `(($predicate : $signature))
  | `(predicateOver% $noun:meanScalarPlural $x:ident and $y:ident $[and $zs:ident]* => $body:term) =>
      `(predicateOver% elements $x and $y $[and $zs]* of (describedType% $noun:meanScalarPlural) => $body)
  | `(predicateOver% indices $x:ident and $y:ident $[and $zs:ident]* $domain:meanIndexDomain => $body:term) =>
      `(predicateOver% elements $x and $y $[and $zs]* of (indexType% $domain) => $body)

/-! The definition clause knows nothing about graphs or other subject types. -/
syntax "Definition" ":" meanPredicateSubjects
  "satisfy" ident "if" sentenceBody "." : command
syntax "Abbreviation" ":" meanPredicateSubjects
  "satisfy" ident "if" sentenceBody "." : command
syntax "Definition" ":" meanSubject
  "satisfies" ident "if" sentenceBody "." : command
syntax "Abbreviation" ":" meanSubject
  "satisfies" ident "if" sentenceBody "." : command
syntax "Definition" ":" meanPredicateSubjects
  "are" ident "if" sentenceBody "." : command
syntax "Abbreviation" ":" meanPredicateSubjects
  "are" ident "if" sentenceBody "." : command
syntax "Definition" ":" meanSubject
  "is" ident "if" sentenceBody "." : command
syntax "Definition" ":" ident "is" sentenceBody "." : command
syntax "Abbreviation" ":" meanSubject
  "is" ident "if" sentenceBody "." : command
syntax "Abbreviation" ":" ident "is" sentenceBody "." : command

macro_rules
  | `(command| Definition: $subjects:meanPredicateSubjects satisfy $name:ident if $body:term .) =>
      `(command| Definition: $subjects are $name if $body .)
  | `(command| Abbreviation: $subjects:meanPredicateSubjects satisfy $name:ident if $body:term .) =>
      `(command| Abbreviation: $subjects are $name if $body .)
  | `(command| Definition: $subject:meanSubject satisfies $name:ident if $body:term .) =>
      `(command| Definition: $subject is $name if $body .)
  | `(command| Abbreviation: $subject:meanSubject satisfies $name:ident if $body:term .) =>
      `(command| Abbreviation: $subject is $name if $body .)
  | `(command| Definition: $subjects:meanPredicateSubjects are $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOver% $subjects => $body)
  | `(command| Abbreviation: $subjects:meanPredicateSubjects are $name:ident if $body:term .) =>
      `(command| abbrev $name:ident := predicateOver% $subjects => $body)
  | `(command| Definition: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOn% $subject => $body)
  | `(command| Definition: $name:ident is $value:term .) =>
      `(command| def $name:ident := $value)
  | `(command| Abbreviation: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| abbrev $name:ident := predicateOn% $subject => $body)
  | `(command| Abbreviation: $name:ident is $value:term .) =>
      `(command| abbrev $name:ident := $value)

/-! Theorem statements reuse ordinary terms, including all Mean propositions.
The separate statement category also supports rendering without a proof. -/
declare_syntax_cat meanTheoremStatement
syntax "Theorem" ident ":" term : meanTheoremStatement
syntax meanTheoremStatement "Proof" ":" term : command

macro_rules
  | `(command| Theorem $name:ident : $statement:term Proof: $proofTerm:term) =>
      `(command| theorem $name:ident : $statement := $proofTerm)

syntax "Axiom" Lean.Parser.Command.declId ":" term : command
syntax "unsafe" "Axiom" Lean.Parser.Command.declId ":" term : command

open Lean.Parser.Command in
macro_rules
  | `(command| Axiom $name:declId : $ty:term) =>
      `(command| axiom $name:declId : $ty)
  | `(command| unsafe Axiom $name:declId : $ty:term) =>
      `(command| unsafe axiom $name:declId : $ty)

-- Lemmas share theorem semantics; examples use Lean's anonymous declaration form.
macro "Lemma" name:ident ":" statement:term "Proof" ":" proofTerm:term : command =>
  `(command| Theorem $name:ident : $statement Proof: $proofTerm)

macro "Example" ":" statement:term "Proof" ":" proofTerm:term : command =>
  `(command| example : $statement := $proofTerm)

/-! Quantified bindings are independent of both the definition and its subject.
New domains implement `forallOver%`, shared by `for all` and `for every`. -/
declare_syntax_cat meanQuantified
syntax meanScalarDomain ident ("and" ident)? : meanQuantified
syntax ident "and" ident "in" term : meanQuantified
syntax "vertices" ident "and" ident "of" term : meanQuantified
syntax "forallOver%" meanQuantified "=>" term : term
syntax "forallSatisfying%" meanQuantified "with" meanAdjective "=>" term : term
/-- A restriction belongs to the quantifier, outside its domain description.
Parentheses allow type ascriptions and nested quantifiers in the condition. -/
def quantifiedBinding : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["where", "satisfying"] (Lean.Parser.categoryParser `meanQuantified 0)
def quantifiedCondition : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "term" `term (isPseudoKind := true))
    (Lean.Parser.withForbidden ":" Lean.Parser.termParser)
syntax ident "∈" quantifiedCondition : meanQuantified
def supersetWord : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "superset " (includeIdent := true)
syntax supersetWord ident "of" quantifiedCondition : meanQuantified
syntax ident "⊇" quantifiedCondition : meanQuantified
syntax "set" ident "⊇" quantifiedCondition : meanQuantified
syntax "for" "every" quantifiedBinding ":" term : term
syntax "for" "all" quantifiedBinding ":" term : term
syntax "for" "every" quantifiedBinding "where" quantifiedCondition ":" term : term
syntax "for" "all" quantifiedBinding "where" quantifiedCondition ":" term : term
syntax "for" "every" quantifiedBinding "satisfying" meanAdjective
  ("where" quantifiedCondition)? ":" term : term
syntax "for" "all" quantifiedBinding "satisfying" meanAdjective
  ("where" quantifiedCondition)? ":" term : term

macro_rules
  | `(for every $binding:meanQuantified satisfying $predicate:meanAdjective
        $[where $condition:term]? : $body:term) => do
      let body ← restrictedBody .implication condition.toArray (some body)
      `(forallSatisfying% $binding with $predicate => $body)
  | `(for all $binding:meanQuantified satisfying $predicate:meanAdjective
        $[where $condition:term]? : $body:term) =>
      `(for every $binding satisfying $predicate $[where $condition]? : $body)
  | `(for every $binding:meanQuantified where $condition:term : $body:term) => do
      let body ← restrictedBody .implication #[condition] (some body)
      `(forallOver% $binding => $body)
  | `(for all $binding:meanQuantified where $condition:term : $body:term) =>
      `(for every $binding where $condition : $body)
  | `(for every $binding:meanQuantified : $body:term) =>
      `(forallOver% $binding => $body)
  | `(for all $binding:meanQuantified : $body:term) =>
      `(forallOver% $binding => $body)
  | `(forallOver% $domain:meanScalarDomain $x:ident $[and $y:ident]? => $body:term) => do
      match y with
      | some y => `(∀ ($x : scalarDomainType% $domain) ($y : scalarDomainType% $domain), $body)
      | none => `(∀ ($x : scalarDomainType% $domain), $body)
  | `(forallOver% $u:ident and $v:ident in $ty:term => $body:term) =>
      `(∀ ($u : $ty) ($v : $ty), $body)
  | `(forallOver% superset $x:ident of $collection:term => $body:term) =>
      `(∀ ($x:ident : Set _), $collection ⊆ $x:ident → ($body : Prop))
  | `(forallOver% $x:ident ⊇ $collection:term => $body:term) =>
      `(forallOver% superset $x of $collection => $body)
  | `(forallOver% set $x:ident ⊇ $collection:term => $body:term) =>
      `(forallOver% superset $x of $collection => $body)
  | `(forallOver% $x:ident ∈ $collection:term => $body:term) =>
      `(∀ ($x:ident : _), $x:ident ∈ $collection → $body)
  | `(forallOver% vertices $u:ident and $v:ident of $g:term => $body:term) =>
      `(forallOver% $u:ident and $v:ident in SimpleGraph.V $g => $body)

/-! Quantification is independent of its noun description.
`witnessBinding` supplies shared noun meanings; `existsOver%` handles articles.
Positive and negative existence share the noun and optional condition. -/
-- Universal and existential quantifiers share noun meanings and binding scope.
-- Prefer the existing scalar-domain grammar where both forms match.
syntax (priority := low) meanWitnessNoun : meanQuantified

private def witnessBinding (noun : Lean.TSyntax `meanWitnessNoun) :
    Lean.MacroM (Lean.Ident × Lean.TSyntax `term) := do
  let (name, ty) ← nounBinding noun
  let name ← match name with
    | some name => pure name
    | none => `(ident| existentialWitness)
  return (name, ty)

/-- Walk only the domain expansion, ending at a fresh marker rather than the
user's body. Named explicit binders are subjects; arrows retain restrictions.
Consequently a `forallOver%` extension automatically supports qualifiers. -/
private partial def qualifyForall (stx marker : Lean.Term) (predicate : Lean.TSyntax `meanAdjective)
    (body : Lean.Term) (names : Array Lean.Ident := #[]) : Lean.MacroM Lean.Term := do
  if stx.raw == marker.raw then
    if names.isEmpty then Lean.Macro.throwErrorAt stx "expected a named quantified subject"
    let condition ← qualifierCondition names predicate
    return ← restrictedBody .implication #[condition] (some body)
  -- Expand aliases (including forall's shared-type shorthand) before inspecting binders.
  if let some expanded ← Lean.expandMacro? stx then
    return ← qualifyForall ⟨expanded⟩ marker predicate body names
  match stx with
  | `(∀ $binders*, $rest) =>
    let mut names := names
    for binder in binders do
      let binder := binder.raw
      if binder.isIdent then
        names := names.push ⟨binder⟩
      else if binder.isOfKind ``Lean.Parser.Term.explicitBinder then
        for name in binder[1].getArgs do
          if name.isIdent then names := names.push ⟨name⟩
    let rest ← qualifyForall rest marker predicate body names
    `(∀ $binders*, $rest)
  | `($condition → $rest) => do
    let rest ← qualifyForall rest marker predicate body names
    `($condition → $rest)
  | `(($inner : $ty)) => do
    let inner ← qualifyForall inner marker predicate body names
    `(($inner : $ty))
  | `(($inner)) => do
    let inner ← qualifyForall inner marker predicate body names
    `(($inner))
  | _ => Lean.Macro.throwErrorAt stx "expected forallOver% to introduce quantified bindings"

macro_rules
  | `(forallSatisfying% $binding:meanQuantified with $predicate:meanAdjective => $body:term) => do
      let marker ← `(quantifiedBodyMarker)
      let domain ← `(forallOver% $binding => $marker)
      qualifyForall domain marker predicate body

/-! Almost-everywhere quantification uses one witness domain and a measure.
An omitted measure uses the domain's canonical `volume`. -/
def almostEveryBinding : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["with", "where", "satisfying"]
    (Lean.Parser.categoryParser `meanWitnessNoun 0)
def almostEveryMeasure : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "term" `term (isPseudoKind := true))
    (Lean.Parser.withForbiddens #[":", "where", "satisfying"] Lean.Parser.termParser)
syntax "for " "almost " "every " almostEveryBinding
  (" satisfying " meanAdjective)?
  (" with " "respect " "to " almostEveryMeasure)?
  (" where " quantifiedCondition)? ":" ppIndent(ppLine term) : term
-- Also accept the qualifier after an explicitly specified measure.
syntax "for " "almost " "every " almostEveryBinding
  " with " "respect " "to " almostEveryMeasure " satisfying " meanAdjective
  (" where " quantifiedCondition)? ":" ppIndent(ppLine term) : term
macro_rules
  | `(for almost every $noun:meanWitnessNoun with respect to $measure:term
        satisfying $predicate:meanAdjective $[where $condition:term]? : $body:term) =>
      `(for almost every $noun satisfying $predicate with respect to $measure
        $[where $condition]? : $body)
  | `(for almost every $noun:meanWitnessNoun $[satisfying $predicate:meanAdjective]?
        $[with respect to $measure:term]? $[where $condition:term]? : $body:term) => do
      let (name, ty) ← witnessBinding noun
      let measure ← match measure with
        | some measure => pure measure
        | none => `(MeasureTheory.volume)
      let qualifier ← match predicate with
        | some predicate => do
            pure (some (← qualifierCondition #[name] predicate))
        | none => pure none
      let body ← restrictedBody .implication (qualifier.toArray ++ condition.toArray)
        (some (← `(($body : Prop))))
      `(Filter.Eventually (fun ($name : $ty) => $body) (MeasureTheory.ae $measure))

/-- A set comprehension owns its element name and proposition. The type stops
at `such that`; parentheses protect those words inside a compound type. -/
def setComprehensionType : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "such" Lean.Parser.termParser
syntax "the " "set " "of " "elements" (ppSpace ident)? " of " setComprehensionType
  " such " "that" ppIndent(ppLine term) : term
def setComprehensionSignature : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "such" functionSignature
syntax "the " "set " "of " "functions" (ppSpace ident)? setComprehensionSignature
  " such " "that" ppIndent(ppLine term) : term

private def setComprehension (name : Option Lean.Ident) (ty body : Lean.Term) : Lean.MacroM Lean.Term := do
  let name ← parameterName name
  `(Set.ofPred (fun ($name : $ty) => ($body : Prop)))

macro_rules
  | `(the set of elements $[$x:ident]? of $ty:term such that $body:term) =>
      setComprehension x ty body
  | `(the set of functions $[$x:ident]? $signature:meanFunctionSignature such that $body:term) => do
      setComprehension x (← `(functionType% $signature)) body

macro_rules
  | `(forallOver% $binding:meanQuantified => $body:term) => do
      let `(meanQuantified| $noun:meanWitnessNoun) := binding
        | Lean.Macro.throwUnsupported
      let (name, ty) ← witnessBinding noun
      `(∀ ($name:ident : $ty), $body)

declare_syntax_cat meanWitness
syntax "a" meanWitnessNoun : meanWitness
syntax "an" meanWitnessNoun : meanWitness

/-- A type declaration describes an unnamed value without introducing one. -/
syntax "anonymousType%" meanWitness : term
syntax "anonymousNounType%" meanWitnessNoun : term
elab "typeExpression%" t:term : term => Lean.Elab.Term.elabType t
macro "we " "have " description:meanWitness : term => `(anonymousType% $description)
macro_rules
  | `(anonymousType% a $noun:meanWitnessNoun) => `(anonymousNounType% $noun)
  | `(anonymousType% an $noun:meanWitnessNoun) => `(anonymousNounType% $noun)
  | `(anonymousNounType% $noun:meanWitnessNoun) => do
      let (name, ty) ← nounBinding noun
      if let some name := name then
        Lean.Macro.throwErrorAt name "expected an anonymous type description; omit the name"
      `(typeExpression% $ty)

/-- Retain the sentence period outside element, function, and index descriptions. -/
def typeWitness : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "." (Lean.Parser.categoryParser `meanWitness 0)

syntax "Definition" ":" "a" ident "is" typeWitness "." : command
syntax "Definition" ":" "an" ident "is" typeWitness "." : command
syntax "Abbreviation" ":" "a" ident "is" typeWitness "." : command
syntax "Abbreviation" ":" "an" ident "is" typeWitness "." : command
macro_rules
  | `(command| Definition: a $name:ident is $description:meanWitness .) =>
      `(command| def $name := anonymousType% $description)
  | `(command| Definition: an $name:ident is $description:meanWitness .) =>
      `(command| def $name := anonymousType% $description)
  | `(command| Abbreviation: a $name:ident is $description:meanWitness .) =>
      `(command| abbrev $name := anonymousType% $description)
  | `(command| Abbreviation: an $name:ident is $description:meanWitness .) =>
      `(command| abbrev $name := anonymousType% $description)

syntax "existsWitness%" meanWitnessNoun "=>" term : term
syntax "uniqueWitness%" meanWitnessNoun "=>" term : term
syntax "existsOver%" meanWitness "=>" term : term
syntax "satisfyingWitness%" meanWitnessNoun "with" meanAdjective ("such" "that" term)? : term
syntax "there" "is" meanWitness "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "a" "unique" meanWitnessNoun "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "exactly" "one" meanWitnessNoun "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "no" meanWitnessNoun "satisfying" meanAdjective ("such" "that" term)? : term
macro_rules
  | `(satisfyingWitness% $noun:meanWitnessNoun with $predicate:meanAdjective $[such that $body:term]?) => do
      let (name, ty) ← witnessBinding noun
      let condition ← qualifierCondition #[name] predicate
      let body ← restrictedBody .conjunction #[condition] body
      `(fun ($name:ident : $ty) => $body)
  | `(there is $description:meanWitness satisfying $predicate:meanAdjective $[such that $body:term]?) => do
      let noun ← match description with
        | `(meanWitness| a $noun:meanWitnessNoun) => pure noun
        | `(meanWitness| an $noun:meanWitnessNoun) => pure noun
        | _ => Lean.Macro.throwUnsupported
      `(Exists (satisfyingWitness% $noun with $predicate $[such that $body]?))
  | `(there is a unique $noun:meanWitnessNoun satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(there is exactly one $noun satisfying $predicate $[such that $body]?)
  | `(there is exactly one $noun:meanWitnessNoun satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(ExistsUnique (satisfyingWitness% $noun with $predicate $[such that $body]?))
  | `(there is no $noun:meanWitnessNoun satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(Not (Exists (satisfyingWitness% $noun with $predicate $[such that $body]?)))

syntax "there" "is" "a" "unique" meanWitnessNoun ("such" "that" term)? : term
syntax "there" "is" "exactly" "one" meanWitnessNoun ("such" "that" term)? : term
syntax "there" "is" "no" meanWitnessNoun ("such" "that" term)? : term
syntax "there" "is" meanWitness ("such" "that" term)? : term

def boundedCollection : Lean.Parser.Parser :=
  Lean.Parser.withAntiquot (Lean.Parser.mkAntiquot "term" `term (isPseudoKind := true))
    (Lean.Parser.withForbidden "such" Lean.Parser.termParser)
def subsetWord : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "subset "
declare_syntax_cat meanBoundedWitness
syntax ident "∈" boundedCollection : meanBoundedWitness
syntax ident "⊆" boundedCollection : meanBoundedWitness
syntax "boundedWitness%" meanBoundedWitness "=>" term : term
syntax "satisfyingBoundedWitness%" meanBoundedWitness "with" meanAdjective ("such" "that" term)? : term
syntax "there" "is" meanBoundedWitness "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "exactly" "one" meanBoundedWitness "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "a" "unique" meanBoundedWitness "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "no" meanBoundedWitness "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "a" subsetWord ident "of" boundedCollection "satisfying" meanAdjective ("such" "that" term)? : term
syntax "there" "is" "no" subsetWord ident "of" boundedCollection "satisfying" meanAdjective ("such" "that" term)? : term
macro_rules
  | `(satisfyingBoundedWitness% $binding:meanBoundedWitness with $predicate:meanAdjective $[such that $body:term]?) => do
      let name ← match binding with
        | `(meanBoundedWitness| $x:ident ∈ $_:term) => pure x
        | `(meanBoundedWitness| $x:ident ⊆ $_:term) => pure x
        | _ => Lean.Macro.throwUnsupported
      let condition ← qualifierCondition #[name] predicate
      let body ← restrictedBody .conjunction #[condition] body
      `(boundedWitness% $binding => $body)
  | `(there is $binding:meanBoundedWitness satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(Exists (satisfyingBoundedWitness% $binding with $predicate $[such that $body]?))
  | `(there is exactly one $binding:meanBoundedWitness satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(ExistsUnique (satisfyingBoundedWitness% $binding with $predicate $[such that $body]?))
  | `(there is a unique $binding:meanBoundedWitness satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(there is exactly one $binding:meanBoundedWitness satisfying $predicate $[such that $body]?)
  | `(there is no $binding:meanBoundedWitness satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(Not (Exists (satisfyingBoundedWitness% $binding with $predicate $[such that $body]?)))
  | `(there is a subset $x:ident of $s:term satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(there is $x:ident ⊆ $s satisfying $predicate $[such that $body]?)
  | `(there is no subset $x:ident of $s:term satisfying $predicate:meanAdjective $[such that $body:term]?) =>
      `(there is no $x:ident ⊆ $s satisfying $predicate $[such that $body]?)

syntax "there" "is" meanBoundedWitness ("such" "that" term)? : term
syntax "there" "is" "exactly" "one" meanBoundedWitness ("such" "that" term)? : term
syntax "there" "is" "a" "unique" meanBoundedWitness ("such" "that" term)? : term
syntax "there" "is" "no" meanBoundedWitness ("such" "that" term)? : term
syntax "there" "is" "a" subsetWord ident "of" boundedCollection ("such" "that" term)? : term
syntax "there" "is" "no" subsetWord ident "of" boundedCollection ("such" "that" term)? : term
macro_rules
  | `(boundedWitness% $x:ident ∈ $s:term => $body:term) =>
      `(fun ($x:ident : _) => $x:ident ∈ $s ∧ ($body : Prop))
  | `(boundedWitness% $x:ident ⊆ $s:term => $body:term) =>
      `(fun ($x:ident : _) => $x:ident ⊆ $s ∧ ($body : Prop))
  | `(there is $binding:meanBoundedWitness $[such that $body:term]?) => do
      `(Exists (boundedWitness% $binding => $(body.getD (← `(True)))))
  | `(there is exactly one $binding:meanBoundedWitness $[such that $body:term]?) => do
      `(ExistsUnique (boundedWitness% $binding => $(body.getD (← `(True)))))
  | `(there is a unique $binding:meanBoundedWitness $[such that $body:term]?) =>
      `(there is exactly one $binding:meanBoundedWitness $[such that $body]?)
  | `(there is no $binding:meanBoundedWitness $[such that $body:term]?) => do
      `(Not (Exists (boundedWitness% $binding => $(body.getD (← `(True))))))
  | `(there is a subset $x:ident of $s:term $[such that $body:term]?) =>
      `(there is $x:ident ⊆ $s $[such that $body]?)
  | `(there is no subset $x:ident of $s:term $[such that $body:term]?) =>
      `(there is no $x:ident ⊆ $s $[such that $body]?)

macro_rules
  | `(there is a unique $description:meanWitnessNoun
        $[such that $condition:term]?) =>
      `(there is exactly one $description:meanWitnessNoun $[such that $condition:term]?)
  | `(there is exactly one $description:meanWitnessNoun
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(uniqueWitness% $description => $condition)
  | `(uniqueWitness% $noun:meanWitnessNoun => $body:term) => do
      let (name, ty) ← witnessBinding noun
      `(∃! ($name:ident : $ty), ($body : Prop))
  | `(there is no $description:meanWitnessNoun
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(¬ (existsWitness% $description => $condition))
  | `(existsOver% a $description:meanWitnessNoun => $body:term) =>
      `(existsWitness% $description => $body)
  | `(existsOver% an $description:meanWitnessNoun => $body:term) =>
      `(existsWitness% $description => $body)
  | `(there is $description:meanWitness
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(existsOver% $description => $condition)
  | `(existsWitness% $noun:meanWitnessNoun => $body:term) => do
      let (name, ty) ← witnessBinding noun
      `(∃ ($name:ident : $ty), $body)

/-- Neither `V` nor `E` needs to occur in the definition body.
`V` already occurs in the generated type `G : SimpleGraph V`, so only `E`
needs an unused-variable exemption. Keep all other diagnostics. -/
@[unused_variables_ignore_fn]
def ignoreUnusedEdgeSet : Lean.Linter.IgnoreFunction := fun binder stack _ =>
  stack.any fun (parent, _) =>
    match parent with
    | `(meanSubject| a simple graph $[$_:ident]? = ($_:ident, $es:ident)) =>
        binder.getRange? == es.raw.getRange?
    | _ => false

/-! Case-based definitions preserve the full function signature. -/
def caseDiscriminant : Lean.Parser.Parser := quantifiedCondition
def caseReturnWitness : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "by" (Lean.Parser.categoryParser `meanWitness 0)
declare_syntax_cat meanFunctionCase
syntax ident ident* "gives" constructorResult : meanFunctionCase
syntax "Definition" ":" ident "maps" functionSubject ("and" functionSubject)*
  "to" caseReturnWitness "by" "cases" "on" caseDiscriminant ":"
  ppIndent(ppLine sepBy1(meanFunctionCase, ";")) "." : command
syntax "Abbreviation" ":" ident "maps" functionSubject ("and" functionSubject)*
  "to" caseReturnWitness "by" "cases" "on" caseDiscriminant ":"
  ppIndent(ppLine sepBy1(meanFunctionCase, ";")) "." : command
syntax "caseValue%" functionSubject ("and" functionSubject)*
  "to" caseReturnWitness "by" "cases" "on" caseDiscriminant ":"
  sepBy1(meanFunctionCase, ";") : term

private def caseBody (discriminant : Lean.Term) (clauses : Array (Lean.TSyntax `meanFunctionCase)) :
    Lean.MacroM Lean.Term := do
  let mut alts : Array (Lean.TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for clause in clauses do
    let `(meanFunctionCase| $ctor:ident $args:ident* gives $body:term) := clause
      | Lean.Macro.throwUnsupported
    let args : Array Lean.Term := args.map (fun arg => ⟨arg.raw⟩)
    alts := alts.push ⟨(← `(Lean.Parser.Term.matchAltExpr| | .$ctor:ident $args* => $body)).raw⟩
  `(match $discriminant:term with $alts:matchAlt*)

private def caseDefinition (name : Lean.Ident) (subjects : Array (Lean.TSyntax `meanSubject))
    (result : Lean.TSyntax `meanWitness) (discriminant : Lean.Term)
    (clauses : Array (Lean.TSyntax `meanFunctionCase)) (abbreviation : Bool) :
    Lean.MacroM (Lean.TSyntax `command) := do
  let binders ← subjects.foldlM (fun acc subject => return acc ++ (← subjectBinders subject)) #[]
  let body ← caseBody discriminant clauses
  if abbreviation then
    `(command| abbrev $name $binders:bracketedBinder* : anonymousType% $result := $body)
  else
    `(command| def $name $binders:bracketedBinder* : anonymousType% $result := $body)

macro_rules
  | `(command| Definition: $name:ident maps $first:meanSubject $[and $rest:meanSubject]*
      to $result:meanWitness by cases on $discriminant:term : $clauses:meanFunctionCase;* .) =>
    caseDefinition name (#[first] ++ rest) result discriminant clauses.getElems false
  | `(command| Abbreviation: $name:ident maps $first:meanSubject $[and $rest:meanSubject]*
      to $result:meanWitness by cases on $discriminant:term : $clauses:meanFunctionCase;* .) =>
    caseDefinition name (#[first] ++ rest) result discriminant clauses.getElems true
  | `(caseValue% $first:meanSubject $[and $rest:meanSubject]* to $result:meanWitness
      by cases on $discriminant:term : $clauses:meanFunctionCase;*) => do
    let body ← caseBody discriminant clauses.getElems
    `(functionOver% $first $[and $rest]* => (($body : anonymousType% $result)))


end Mean

export Mean (ln)
