import Examples.MeanToLean
import Mean

-- Theorem rendering checks the statement and omits the proof.
theorem ordinaryNatTrans3 (x y z w : Nat) (h : x = y ∧ z = y ∧ z = w) : x = w := by
  exact h.1.trans (h.2.1.symm.trans h.2.2)

#mean_compare ordinaryNatTrans3
#mean_compare TheoremExamples.zeroExists
#mean_compare TheoremExamples.edgeSubsetSelf
#mean_compare TheoremExamples.natAddZero

/--
info: Theorem TheoremExamples.zeroExists:
  there is a natural number n such that
    n = 0
-/
#guard_msgs in
#mean TheoremExamples.zeroExists

open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``TheoremExamples.zeroExists).type
  let rejected ← try
    Mean.RoundTrip.checkText original "Theorem changed: False" `meanTheoremStatement
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed theorem statement"

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
#mean_compare zeroLengthLinked
#mean_compare edgeless
#mean_compare zero
#mean_compare boundsPairSums

-- The explicit subject is retained when the body names the vertex type.
def inhabitedVertices {V : Type*} (_G : SimpleGraph V) : Prop := Nonempty V
#mean_compare inhabitedVertices

def emptyVertices {V : Type*} (_G : SimpleGraph V) : Prop := IsEmpty V
#mean_compare emptyVertices

section
variable {T : Sort u} (P : Prop) (n : Nat)
#mean_term_compare Nonempty T
#mean_term_compare IsEmpty T
#mean_term_compare Nonempty T ∧ P
#mean_term_compare IsEmpty T → P
#mean_term_compare Nonempty (Fin n)
#mean_term_compare IsEmpty (Fin n)
end

-- Fixed and compound universes cannot be generalized to a Mean graph subject.
def smallGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ _p : G.Path u v, True
#mean_compare smallGraph

def compoundGraph.{u, v} {V : Type (max u v)} (G : SimpleGraph V) : Prop :=
  ∀ x y : V, ∃ _p : G.Path x y, True
#mean_compare compoundGraph

def truthy (b : Bool) : Prop := b = true
#mean_compare truthy

#mean_term_compare ∃ n : Nat, ∃ m : Nat, m = n + 1
#mean_term_compare ∃ _n : Nat, True
#mean_term_compare ∃ x : Bool, x = true
#mean_term_compare ∃ _x : Bool, True
-- Regression check: an existential with body False must not render as "there is no".
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
      "Definition: a simple graph G is smallGraph if for all vertices x and y of G: there is a path in G from x to y." `command
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed universe signature"

-- Standard Int vocabulary, including unnamed witnesses.
def intZero (x : Int) : Prop := x = 0
#mean_compare intZero
#mean_term_compare ∃ x : Int, x = 0
#mean_term_compare ∃ _x : Int, True

-- Standard Rat vocabulary, including unnamed witnesses.
def ratZero (x : Rat) : Prop := x = 0
#mean_compare ratZero
#mean_term_compare ∃ x : Rat, x = 0
#mean_term_compare ∃ _x : Rat, True

-- Standard Real vocabulary, including unnamed witnesses.
def realZero (x : Real) : Prop := x = 0
#mean_compare realZero
#mean_term_compare ∃ x : Real, x = 0
#mean_term_compare ∃ _x : Real, True

-- Standard Complex vocabulary, including unnamed witnesses.
def complexZero (x : Complex) : Prop := x = 0
#mean_compare complexZero
#mean_term_compare ∃ x : Complex, x = 0
#mean_term_compare ∃ _x : Complex, True

#mean_term_compare ∀ x : Nat, x = x
#mean_term_compare ∀ x y : Nat, x = y

#mean_term_compare ∀ x : Int, x = x
#mean_term_compare ∀ x y : Int, x = y

#mean_term_compare ∀ x : Rat, x = x
#mean_term_compare ∀ x y : Rat, x = y

#mean_term_compare ∀ x : Real, x = x
#mean_term_compare ∀ x y : Real, x = y

#mean_term_compare ∀ x : Complex, x = x
#mean_term_compare ∀ x y : Complex, x = y

#mean_term_compare ∀ x : Bool, x = x
#mean_term_compare ∀ x y : Bool, x = y

-- Negated existence; a False existential body must stay positive existence.
#mean_compare hasNoSmallerSquare
#mean_term_compare ¬ ∃ x : Real, x * x < 0
#mean_term_compare ¬ ∃ _x : Int, True
#mean_term_compare ¬ ∃ _x : Empty, True
#mean_term_compare ∃ _x : Empty, False
#mean_term_compare ¬ ∃ _x : Int, False
#mean_term_compare ¬ ∃ x : Int, ¬ ∃ y : Int, x = y
section
variable {T : Type*} (P : T → Prop) (Q : Prop)
#mean_term_compare (¬ ∃ x : T, P x) ∧ Q
#mean_term_compare Q ∨ (¬ ∃ x : T, P x)
#mean_term_compare (¬ ∃ x : T, P x) → Q
end
section
variable {V : Type*} (G : SimpleGraph V) (u v : V)
#mean_term_compare ¬ ∃ _p : G.Path u v, True
#mean_term_compare ¬ ∃ p : G.Path u v, p.val.length = 0
end

-- Type and function adjectives use the same rendering rule.
section
variable {T : Sort u} {A : Sort v} {B : Sort w} (f : A → B)
#mean_term_compare Finite T
#mean_term_compare Infinite T
#mean_term_compare Countable T
#mean_term_compare Function.Injective f
#mean_term_compare Function.Surjective f
#mean_term_compare Function.Bijective f
#mean_term_compare Function.Injective f ∧ Function.Surjective f
#mean_term_compare Finite T → Countable T
#mean_term_compare Function.Injective (fun x : Nat => x + 1)
end
#mean_compare oneToOne

-- Properties render inside ordinary expressions as well as on their own.
section
variable {V : Type*} (G H : SimpleGraph V) (u v : V)
#mean_term_compare G.edgeSet
#mean_term_compare G.V
#mean_term_compare G.neighborSet u
#mean_term_compare G.incidenceSet u
#mean_term_compare (G ⊔ H).neighborSet u
#mean_term_compare v ∈ G.neighborSet u
#mean_term_compare G.edgeSet ⊆ H.edgeSet
#mean_term_compare G.edgeSet ∪ H.edgeSet
#mean_term_compare G.neighborSet u ∩ H.neighborSet v
#mean_term_compare Set.Nonempty G.edgeSet
#mean_term_compare (G ⊔ H).edgeSet = G.edgeSet ∪ H.edgeSet
#mean_term_compare Nonempty G.V
#mean_term_compare G.edgeSet = ∅ ∧ H.edgeSet = ∅
end
