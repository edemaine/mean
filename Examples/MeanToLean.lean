import Mean.Syntax

-- English connectives match Lean's precedence and associativity exactly.
example (P Q R : Prop) : (P and Q or R) = ((P ∧ Q) ∨ R) := rfl
example (P Q R : Prop) : (P or Q and R) = (P ∨ (Q ∧ R)) := rfl
example (P Q R : Prop) : (P and Q and R) = (P ∧ (Q ∧ R)) := rfl
example (P Q R : Prop) : ((P or Q) and R) = ((P ∨ Q) ∧ R) := rfl
example (P Q R : Prop) : (if P then Q and R) = (P → Q ∧ R) := rfl
example (P Q R : Prop) : (if P then if Q then R) = (P → Q → R) := rfl
example (P Q R : Prop) : (if (if P then Q) then R) = ((P → Q) → R) := rfl

-- Ordinary Lean conditionals with else still select a value or proposition.
example : (if true then 1 else 2) = 1 := rfl
example (P Q R : Prop) [Decidable P] : (if P then Q else R) = ite P Q R := rfl

Definition:
  a natural number n is zeroOrPositive if
    n = 0 or (if n ≠ 0 then n > 0).

example (n : Nat) : zeroOrPositive n = (n = 0 ∨ (n ≠ 0 → n > 0)) := rfl

Definition:
  a simple graph G is preconnectedViaVertices if
    for all vertices u and v of G:
      there is a path in G from u to v.

Definition:
  a simple graph G = (V, E) is preconnected if
    for every u and v in V:
      there is a path in G from u to v.

-- Neither explicitly named component needs to be referenced in the body.
-- #guard_msgs ensures this declaration produces no unused-variable warnings.
#guard_msgs in
Definition:
  a simple graph G = (V, E) is preconnectedWithNamedParts if
    for all vertices u and v of G:
      there is a path in G from u to v.

example {V : Type*} (G : SimpleGraph V) :
    preconnectedWithNamedParts G = preconnected G := rfl

-- Lean checks that the readable definition has exactly this meaning.
example {V : Type*} (G : SimpleGraph V) :
    preconnected G = (∀ u v : V, ∃ _p : G.Path u v, True) := rfl

-- Both graph subjects and both quantifier forms have exactly the same meaning.
example {V : Type*} (G : SimpleGraph V) :
    preconnectedViaVertices G = preconnected G := rfl

example {V : Type*} (G : SimpleGraph V) : G.V = V := rfl

-- A named witness is bound in the optional condition.
example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (there is a path _p in G from u to v) =
    (∃ _p : G.Path u v, True) := rfl

example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (there is a path p in G from u to v such that p.val.length = 0) =
    (∃ p : G.Path u v, p.val.length = 0) := rfl

-- The clause can also use surrounding variables without naming the path.
example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (there is a path in G from u to v such that u = v) =
    (∃ _p : G.Path u v, u = v) := rfl

-- The generated anonymous witness must not capture a surrounding variable.
example {V : Type*} (G : SimpleGraph V) (u v : V) (existentialWitness : Nat) :
    (there is a path in G from u to v such that existentialWitness = 0) =
    (∃ _p : G.Path u v, existentialWitness = 0) := rfl

-- The same existential grammar works with unrelated witness descriptions.
example : (there is a natural number n such that n = 0) =
    (∃ n : Nat, n = 0) := rfl

example : (there is a natural number) = (∃ _n : Nat, True) := rfl

example {α : Type*} (P : α → Prop) :
    (there is an element x of α such that P x) = (∃ x : α, P x) := rfl

example {α : Type*} : (there is an element of α) = (∃ _x : α, True) := rfl

-- Nested existential clauses preserve the scope of both witnesses.
example :
    (there is a natural number n such that
      there is a natural number m such that m = n + 1) =
    (∃ n : Nat, ∃ m : Nat, m = n + 1) := rfl

-- The same optional clause composes with the definition and universal quantifier.
Definition:
  a simple graph G is zeroLengthLinked if
    for all vertices u and v of G:
      there is a path p in G from u to v such that (p.val.length = 0).

example {V : Type*} (G : SimpleGraph V) :
    zeroLengthLinked G = (∀ u v : V, ∃ p : G.Path u v, p.val.length = 0) := rfl

-- Graph-relative quantification also works in ordinary Lean, with no Mean subject.
example {V : Type*} (G : SimpleGraph V)
    (h : for all vertices x and y of G: there is a path in G from x to y) :
    preconnected G := h

-- Every/all and explicit/graph-relative domains compose independently.
example {V : Type*} (G : SimpleGraph V) :
    (for every vertices x and y of G: there is a path in G from x to y) =
    (for all x and y in V: there is a path in G from x to y) := rfl

-- The same definition clause works for subjects unrelated to graphs.
Definition:
  a natural number n is zero if (n = 0).

Definition:
  an element n of Nat is zeroViaType if (n = 0).

example (n : Nat) : zero n = (n = 0) := rfl
example : zero = zeroViaType := rfl

-- A non-graph subject can contain a Mean quantifier too.
Definition:
  a natural number n is boundsPairSums if
    for all x and y in Nat: x + y ≤ n.

example (n : Nat) : boundsPairSums n = (∀ x y : Nat, x + y ≤ n) := rfl

-- The generated definition can be used in ordinary Lean proofs.
theorem preconnected_iff_mathlib_preconnected {V : Type*} (G : SimpleGraph V) :
    preconnected G ↔ G.Preconnected := by
  constructor
  · intro h u v
    obtain ⟨p, _⟩ := h u v
    exact p.val.reachable
  · intro h u v
    exact (h u v).elim_path fun p => ⟨p, trivial⟩

-- Mathlib's Connected additionally requires at least one vertex.
theorem preconnected_iff_mathlib_connected {V : Type*} [Nonempty V]
    (G : SimpleGraph V) : preconnected G ↔ G.Connected := by
  constructor
  · intro h
    exact ⟨(preconnected_iff_mathlib_preconnected G).mp h⟩
  · intro h
    exact (preconnected_iff_mathlib_preconnected G).mpr h.preconnected

-- Renaming every bound name does not change the meaning.
Definition:
  a simple graph H = (W, F) is linked if
    for every x and y in W:
      there is a path in H from x to y.

example {V : Type*} (G : SimpleGraph V) : linked G = preconnected G := rfl

-- E is actually bound to G.edgeSet, and ordinary Lean is allowed in the body.
Definition:
  a simple graph G = (V, E) is edgeless if
    E = ∅.

example {V : Type*} (G : SimpleGraph V) : edgeless G = (G.edgeSet = ∅) := rfl

-- The two phrase forms can also be used independently of the command.
example {V : Type*} (G : SimpleGraph V)
    (h : for every u and v in V: there is a path in G from u to v) :
    preconnected G := h

-- Empty graphs satisfy the user's pairwise-path definition vacuously.
example (G : SimpleGraph Empty) : preconnected G := by
  intro u
  exact Empty.elim u

example (G : SimpleGraph Empty) : ¬ G.Connected := by
  intro h
  obtain ⟨v⟩ := h.nonempty
  exact Empty.elim v

-- A one-vertex graph needs only the zero-length path.
example (G : SimpleGraph Unit) : preconnected G := by
  apply (preconnected_iff_mathlib_preconnected G).mpr
  intro u v
  have h : u = v := Subsingleton.elim u v
  subst v
  exact SimpleGraph.Reachable.refl u

-- Two isolated vertices are a counterexample to preconnectedness.
example : ¬ preconnected (⊥ : SimpleGraph Bool) := by
  intro h
  have hf := (preconnected_iff_mathlib_preconnected _).mp h false true
  have heq : false = true := SimpleGraph.reachable_bot.mp hf
  cases heq

/-- error: the graph, vertex type, and edge set must have distinct names -/
#guard_msgs in
Definition:
  a simple graph G = (V, G) is ambiguous if True.
