import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Countable.Defs
import Lean

/-! # Mean: compositional controlled mathematical syntax inside Lean.

A trailing `%` marks internal helper syntax in Mean. These forms connect the
surface grammar to binding rules and disappear during macro expansion; authors
need not write them. This is a naming convention, not enforced privacy.
-/

/-- Expose the vertex type carried by a mathlib graph's type parameter as `G.V`. -/
abbrev SimpleGraph.V {α : Type*} (_ : SimpleGraph α) := α

namespace Mean

/-! Logical connectives use Lean's usual precedence: `and` binds tighter than
`or`; both associate to the right. An `if … then …` without `else` is implication.
Lean's ordinary `if … then … else …` remains available. -/
syntax:35 term:36 " and " term:35 : term
syntax:30 term:31 " or " term:30 : term
syntax:25 "if" term "then" term:25 : term
macro_rules
  | `($p:term and $q:term) => `(And $p $q)
  | `($p:term or $q:term) => `(Or $p $q)
  | `(if $premise:term then $conclusion:term) =>
      `(∀ (_ : ($premise : Prop)), ($conclusion : Prop))

/-! Adjectives share one application rule. New adjectives implement
`adjectivePredicate%` with their Lean predicate; Lean checks the subject's type. -/
declare_syntax_cat meanAdjective
syntax "nonempty" : meanAdjective
syntax "empty" : meanAdjective
syntax "finite" : meanAdjective
syntax "infinite" : meanAdjective
syntax "countable" : meanAdjective
syntax "injective" : meanAdjective
syntax "surjective" : meanAdjective
syntax "bijective" : meanAdjective
syntax "adjectivePredicate%" meanAdjective : term
syntax:50 term:51 " is " meanAdjective : term
macro_rules
  | `($subject:term is $adjective:meanAdjective) =>
      `((adjectivePredicate% $adjective) $subject)
  | `(adjectivePredicate% nonempty) => `(Nonempty)
  | `(adjectivePredicate% empty) => `(IsEmpty)
  | `(adjectivePredicate% finite) => `(Finite)
  | `(adjectivePredicate% infinite) => `(Infinite)
  | `(adjectivePredicate% countable) => `(Countable)
  | `(adjectivePredicate% injective) => `(Function.Injective)
  | `(adjectivePredicate% surjective) => `(Function.Surjective)
  | `(adjectivePredicate% bijective) => `(Function.Bijective)

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

/-- The definition's `is` ends an unparenthesized subject type. -/
def subjectType : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "is" Lean.Parser.termParser

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

declare_syntax_cat meanScalarDomain
syntax meanScalar : meanScalarDomain
syntax "natural" "numbers" : meanScalarDomain
syntax "integers" : meanScalarDomain
syntax "rational" "numbers" : meanScalarDomain
syntax "real" "numbers" : meanScalarDomain
syntax "complex" "numbers" : meanScalarDomain
syntax "booleans" : meanScalarDomain
syntax "scalarDomainType%" meanScalarDomain : term

macro_rules
  | `(scalarDomainType% $noun:meanScalar) => `(scalarType% $noun)
  | `(scalarDomainType% natural numbers) => `(scalarType% natural number)
  | `(scalarDomainType% integers) => `(scalarType% integer)
  | `(scalarDomainType% rational numbers) => `(scalarType% rational number)
  | `(scalarDomainType% real numbers) => `(scalarType% real number)
  | `(scalarDomainType% complex numbers) => `(scalarType% complex number)
  | `(scalarDomainType% booleans) => `(scalarType% boolean)

/-! Subjects specify bindings, independently of the definition clause.
New subject forms implement `predicateOn%`; the definition command is unchanged. -/
declare_syntax_cat meanSubject
syntax "a" "simple" "graph" ident : meanSubject
syntax "a" "simple" "graph" ident "=" "(" ident "," ident ")" : meanSubject
syntax "an" "element" ident "of" subjectType : meanSubject
syntax "a" meanScalar ident : meanSubject
syntax "an" meanScalar ident : meanSubject

-- Internal composition point: subject bindings scoped over a proposition.
syntax "predicateOn%" meanSubject "=>" term : term

macro_rules
  | `(predicateOn% a simple graph $g:ident => $body:term) =>
      `(fun {Vertex : Type*} ($g : SimpleGraph Vertex) => ($body : Prop))
  | `(predicateOn% a simple graph $g:ident = ($vs:ident, $es:ident) => $body:term) => do
      let names := [g.getId, vs.getId, es.getId]
      unless names.eraseDups.length == names.length do
        Lean.Macro.throwErrorAt g
          "the graph, vertex type, and edge set must have distinct names"
      `(fun {$vs : Type*} ($g : SimpleGraph $vs) =>
          let $es := SimpleGraph.edgeSet $g
          ($body : Prop))
  | `(predicateOn% an element $x:ident of $ty:term => $body:term) =>
      `(fun ($x : $ty) => ($body : Prop))
  | `(predicateOn% a $noun:meanScalar $x:ident => $body:term) =>
      `(predicateOn% an element $x of (scalarType% $noun) => $body)
  | `(predicateOn% an $noun:meanScalar $x:ident => $body:term) =>
      `(predicateOn% an element $x of (scalarType% $noun) => $body)

/-! The definition clause knows nothing about graphs or other subject types. -/
syntax "Definition" ":" meanSubject
  "is" ident "if" sentenceBody "." : command

macro_rules
  | `(command| Definition: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOn% $subject => $body)

/-! Theorem statements reuse ordinary terms, including all Mean propositions.
The separate statement category also supports rendering without a proof. -/
declare_syntax_cat meanTheoremStatement
syntax "Theorem" ident ":" term : meanTheoremStatement
syntax meanTheoremStatement "Proof" ":" term : command

macro_rules
  | `(command| Theorem $name:ident : $statement:term Proof: $proof:term) =>
      `(command| theorem $name:ident : $statement := $proof)

-- Lemmas share theorem semantics; examples use Lean's anonymous declaration form.
macro "Lemma" name:ident ":" statement:term "Proof" ":" proof:term : command =>
  `(command| Theorem $name:ident : $statement Proof: $proof)

macro "Example" ":" statement:term "Proof" ":" proof:term : command =>
  `(command| example : $statement := $proof)

/-! Quantified bindings are independent of both the definition and its subject.
New domains implement `forallOver%`, shared by `for all` and `for every`. -/
declare_syntax_cat meanQuantified
syntax meanScalarDomain ident ("and" ident)? : meanQuantified
syntax ident "and" ident "in" term : meanQuantified
syntax "vertices" ident "and" ident "of" term : meanQuantified
syntax "forallOver%" meanQuantified "=>" term : term
syntax "for" "every" meanQuantified ":" term : term
syntax "for" "all" meanQuantified ":" term : term

macro_rules
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
  | `(forallOver% vertices $u:ident and $v:ident of $g:term => $body:term) =>
      `(forallOver% $u:ident and $v:ident in SimpleGraph.V $g => $body)

/-! Existential quantification is independent of its witness description.
New noun phrases implement `existsWitness%`; `existsOver%` handles articles.
Positive and negative existence share the noun and optional condition. -/
declare_syntax_cat meanWitnessNoun
syntax "element" (ppSpace ident)? "of" term : meanWitnessNoun
syntax meanScalar (ppSpace ident)? : meanWitnessNoun
syntax "path" (ppSpace ident)? "in" term "from" term "to" term : meanWitnessNoun

declare_syntax_cat meanWitness
syntax "a" meanWitnessNoun : meanWitness
syntax "an" meanWitnessNoun : meanWitness

syntax "existsWitness%" meanWitnessNoun "=>" term : term
syntax "existsOver%" meanWitness "=>" term : term
syntax "there" "is" "no" meanWitnessNoun ("such" "that" term)? : term
syntax "there" "is" meanWitness ("such" "that" term)? : term

macro_rules
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
  | `(existsWitness% element $[$x:ident]? of $ty:term => $body:term) => do
      let witness ← match x with
        | some name => pure name
        | none => `(ident| existentialWitness)
      `(∃ ($witness:ident : $ty), $body)
  | `(existsWitness% $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of (scalarType% $noun) => $body)
  | `(existsWitness% path $[$p:ident]? in $g:term from $u:term to $v:term
        => $body:term) =>
      `(existsOver% an element $[$p:ident]? of SimpleGraph.Path $g $u $v => $body)

/-- Neither `V` nor `E` needs to occur in the definition body.
`V` already occurs in the generated type `G : SimpleGraph V`, so only `E`
needs an unused-variable exemption. Keep all other diagnostics. -/
@[unused_variables_ignore_fn]
def ignoreUnusedEdgeSet : Lean.Linter.IgnoreFunction := fun binder stack _ =>
  stack.any fun (parent, _) =>
    match parent with
    | `(meanSubject| a simple graph $_:ident = ($_:ident, $es:ident)) =>
        binder.getRange? == es.raw.getRange?
    | _ => false

end Mean
