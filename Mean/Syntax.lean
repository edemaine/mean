import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

/-- Keep the sentence's period out of Lean's field-completion parser. -/
def sentenceBody : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "." Lean.Parser.termParser

/-! Subjects specify bindings, independently of the definition clause.
New subject forms implement `predicateOn%`; the definition command is unchanged. -/
declare_syntax_cat meanSubject
syntax "a" "simple" "graph" ident : meanSubject
syntax "a" "simple" "graph" ident "=" "(" ident "," ident ")" : meanSubject
syntax "an" "element" ident "of" term : meanSubject
syntax "a" "natural" "number" ident : meanSubject

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

/-! The definition clause knows nothing about graphs or other subject types. -/
syntax "Definition" ":" meanSubject
  "is" ident "if" sentenceBody "." : command

macro_rules
  | `(command| Definition: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOn% $subject => $body)

/-! Quantified bindings are independent of both the definition and its subject.
New domains implement `forallOver%`, shared by `for all` and `for every`. -/
declare_syntax_cat meanQuantified
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
  | `(forallOver% $u:ident and $v:ident in $ty:term => $body:term) =>
      `(∀ ($u : $ty) ($v : $ty), $body)
  | `(forallOver% vertices $u:ident and $v:ident of $g:term => $body:term) =>
      `(forallOver% $u:ident and $v:ident in SimpleGraph.V $g => $body)

/-! Existential quantification is independent of its witness description.
New noun phrases implement `existsOver%`, without changing `there is`. -/
declare_syntax_cat meanWitness
syntax "an" "element" (ppSpace ident)? "of" term : meanWitness
syntax "a" "natural" "number" (ppSpace ident)? : meanWitness
syntax "a" "path" (ppSpace ident)? "in" term "from" term "to" term : meanWitness

syntax "existsOver%" meanWitness "=>" term : term
syntax "there" "is" meanWitness ("such" "that" term)? : term

macro_rules
  | `(there is $description:meanWitness
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(existsOver% $description => $condition)
  | `(existsOver% an element $[$x:ident]? of $ty:term => $body:term) => do
      let witness ← match x with
        | some name => pure name
        | none => `(ident| existentialWitness)
      `(∃ ($witness:ident : $ty), $body)
  | `(existsOver% a natural number $[$n:ident]? => $body:term) =>
      `(existsOver% an element $[$n:ident]? of Nat => $body)
  | `(existsOver% a path $[$p:ident]? in $g:term from $u:term to $v:term
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
