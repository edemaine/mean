import Examples.MeanToLean
import Mean

-- The input may be ordinary Lean, with no Mean macros in its source.
def ordinaryPreconnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ _p : G.Path u v, True

/--
info: Definition:
  a simple graph G is ordinaryPreconnected if
    for all vertices u and v of G:
      there is a path in G from u to v.
-/
#guard_msgs in
#mean ordinaryPreconnected

#mean_compare ordinaryPreconnected
#mean_compare preconnectedViaVertices
#mean_compare zeroLengthLinked
#mean_compare edgeless
#mean_compare zero
#mean_compare zeroViaType
#mean_compare boundsPairSums

-- The explicit subject is retained when the body names the vertex type.
def inhabitedVertices {V : Type*} (G : SimpleGraph V) : Prop := Nonempty V ∧ G = G
#mean_compare inhabitedVertices

-- Fixed and compound universes cannot be generalized to a Mean graph subject.
def smallGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ _p : G.Path u v, True
#mean_compare smallGraph

def compoundGraph.{u, v} {V : Type (max u v)} (G : SimpleGraph V) : Prop :=
  ∀ x y : V, ∃ _p : G.Path x y, True
#mean_compare compoundGraph

def boolPredicate (b : Bool) : Prop := b = true
#mean_compare boolPredicate

#mean_term_compare ∃ n : Nat, ∃ m : Nat, m = n + 1
#mean_term_compare ∃ _n : Nat, True
#mean_term_compare ∃ x : Bool, x = true
#mean_term_compare ∃ _n : Nat, False

section
variable {V : Type*} (G : SimpleGraph V) (u v : V)
#mean_term_compare ∃ p : G.Path u v, p.val.length = 0
end

-- Unsupported shapes retain explicit Lean, without losing their assumptions.
def withAssumption (n : Nat) (h : n > 0) : Prop := n ≥ 1 ∧ h = h
#mean_compare withAssumption
#mean_compare preconnected_iff_mathlib_preconnected

-- Names colliding with Mean keywords, shadowing, and unnamed binders.
#mean_term_compare ∀ («a» : Nat) («graph» : Nat), ∃ «path» : Nat, «path» = «a» + «graph»
#mean_term_compare ∃ _n : Nat, ∃ _n : Nat, _n = 0

-- Preservation of nontrivial binder dependencies and fallback expressions.
#mean_term_compare ∀ n : Nat, ∀ i : Fin n, i.val < n
#mean_term_compare ∀ n m : Nat, (n = m → m = n)
#mean_term_compare ∀ n m : Nat, (n = m ∧ m = n) ∨ n ≠ m

-- Grouping preserves the expression, including left-associated connectives.
section
variable (P Q R : Prop)
#mean_term_compare (P ∨ Q) ∧ R
#mean_term_compare P ∨ (Q ∧ R)
#mean_term_compare (P ∧ Q) ∧ R
#mean_term_compare (P ∨ Q) ∨ R
#mean_term_compare (P → Q) → R
#mean_term_compare P → Q → R
#mean_term_compare P ∧ (Q → R)
#mean_term_compare (∃ n : Nat, n = 0) ∧ P
#mean_term_compare P → ∃ n : Nat, n = 0 ∧ Q
end

#mean_compare zeroOrPositive

-- The checker must reject changed meaning even when the printed text parses.
open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(∃ n : Nat, n = 0)) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let rejected ← try
    Mean.RoundTrip.checkText original "there is a natural number n such that n = 1"
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed predicate"

-- Reject turning a fixed Type 0 graph parameter into a universe-polymorphic one.
open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``smallGraph).value!
  let rejected ← try
    Mean.RoundTrip.checkText original
      "Definition: a simple graph G is smallGraph if for all vertices x and y of G: there is a path in G from x to y." true
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed universe signature"
