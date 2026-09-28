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

/-- Keep the sentence's period out of Lean's field-completion parser. -/
def sentenceBody : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "." Lean.Parser.termParser

/-- The definition's `is` ends an unparenthesized subject type. -/
def subjectType : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "is" Lean.Parser.termParser

/-! Subjects specify bindings, independently of the definition clause.
New subject forms implement `predicateOn%`; the definition command is unchanged. -/
declare_syntax_cat meanSubject
syntax "a" "simple" "graph" ident : meanSubject
syntax "a" "simple" "graph" ident "=" "(" ident "," ident ")" : meanSubject
syntax "an" "element" ident "of" subjectType : meanSubject
syntax "a" "natural" "number" ident : meanSubject
syntax "an" "integer" ident : meanSubject
syntax "a" "rational" "number" ident : meanSubject
syntax "a" "real" "number" ident : meanSubject
syntax "a" "complex" "number" ident : meanSubject
syntax "a" "boolean" ident : meanSubject

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
  | `(predicateOn% a natural number $n:ident => $body:term) =>
      `(predicateOn% an element $n of Nat => $body)
  | `(predicateOn% an integer $x:ident => $body:term) =>
      `(predicateOn% an element $x of Int => $body)
  | `(predicateOn% a rational number $x:ident => $body:term) =>
      `(predicateOn% an element $x of Rat => $body)
  | `(predicateOn% a real number $x:ident => $body:term) =>
      `(predicateOn% an element $x of Real => $body)
  | `(predicateOn% a complex number $x:ident => $body:term) =>
      `(predicateOn% an element $x of Complex => $body)
  | `(predicateOn% a boolean $x:ident => $body:term) =>
      `(predicateOn% an element $x of Bool => $body)

/-! The definition clause knows nothing about graphs or other subject types. -/
syntax "Definition" ":" meanSubject
  "is" ident "if" sentenceBody "." : command

macro_rules
  | `(command| Definition: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOn% $subject => $body)

/-! Scalar domains used by universal quantifiers. `scalarType%` translates a noun
phrase to its Lean type; binding and quantifier wording are independent. -/
declare_syntax_cat meanScalarDomain
syntax "natural" "number" : meanScalarDomain
syntax "natural" "numbers" : meanScalarDomain
syntax "integer" : meanScalarDomain
syntax "integers" : meanScalarDomain
syntax "rational" "number" : meanScalarDomain
syntax "rational" "numbers" : meanScalarDomain
syntax "real" "number" : meanScalarDomain
syntax "real" "numbers" : meanScalarDomain
syntax "complex" "number" : meanScalarDomain
syntax "complex" "numbers" : meanScalarDomain
syntax "boolean" : meanScalarDomain
syntax "booleans" : meanScalarDomain
syntax "scalarType%" meanScalarDomain : term

macro_rules
  | `(scalarType% natural number) => `(Nat)
  | `(scalarType% natural numbers) => `(Nat)
  | `(scalarType% integer) => `(Int)
  | `(scalarType% integers) => `(Int)
  | `(scalarType% rational number) => `(Rat)
  | `(scalarType% rational numbers) => `(Rat)
  | `(scalarType% real number) => `(Real)
  | `(scalarType% real numbers) => `(Real)
  | `(scalarType% complex number) => `(Complex)
  | `(scalarType% complex numbers) => `(Complex)
  | `(scalarType% boolean) => `(Bool)
  | `(scalarType% booleans) => `(Bool)

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
      | some y => `(∀ ($x : scalarType% $domain) ($y : scalarType% $domain), $body)
      | none => `(∀ ($x : scalarType% $domain), $body)
  | `(forallOver% $u:ident and $v:ident in $ty:term => $body:term) =>
      `(∀ ($u : $ty) ($v : $ty), $body)
  | `(forallOver% vertices $u:ident and $v:ident of $g:term => $body:term) =>
      `(forallOver% $u:ident and $v:ident in SimpleGraph.V $g => $body)

/-! Existential quantification is independent of its witness description.
New noun phrases implement `existsWitness%`; `existsOver%` handles articles.
Positive and negative existence share the noun and optional condition. -/
declare_syntax_cat meanWitnessNoun
syntax "element" (ppSpace ident)? "of" term : meanWitnessNoun
syntax "natural" "number" (ppSpace ident)? : meanWitnessNoun
syntax "integer" (ppSpace ident)? : meanWitnessNoun
syntax "rational" "number" (ppSpace ident)? : meanWitnessNoun
syntax "real" "number" (ppSpace ident)? : meanWitnessNoun
syntax "complex" "number" (ppSpace ident)? : meanWitnessNoun
syntax "boolean" (ppSpace ident)? : meanWitnessNoun
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
  | `(existsWitness% natural number $[$n:ident]? => $body:term) =>
      `(existsOver% an element $[$n:ident]? of Nat => $body)
  | `(existsWitness% integer $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of Int => $body)
  | `(existsWitness% rational number $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of Rat => $body)
  | `(existsWitness% real number $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of Real => $body)
  | `(existsWitness% complex number $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of Complex => $body)
  | `(existsWitness% boolean $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of Bool => $body)
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
