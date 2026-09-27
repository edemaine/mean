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

Definition:
  a boolean x is trueBoolean if x = true.

example (x : Bool) : trueBoolean x = (x = true) := rfl

example : (there is a boolean x such that x = true) =
    (∃ x : Bool, x = true) := rfl

example : (there is a boolean) = (∃ _x : Bool, True) := rfl

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

Definition:
  an integer x is intZeroFromMean if (x = 0).

example (x : Int) : intZeroFromMean x = (x = 0) := rfl
example : (there is an integer x such that x = 0) =
    (∃ x : Int, x = 0) := rfl
example : (there is an integer) = (∃ _x : Int, True) := rfl

Definition:
  a rational number x is ratZeroFromMean if (x = 0).

example (x : Rat) : ratZeroFromMean x = (x = 0) := rfl
example : (there is a rational number x such that x = 0) =
    (∃ x : Rat, x = 0) := rfl
example : (there is a rational number) = (∃ _x : Rat, True) := rfl

Definition:
  a real number x is realZeroFromMean if (x = 0).

example (x : Real) : realZeroFromMean x = (x = 0) := rfl
example : (there is a real number x such that x = 0) =
    (∃ x : Real, x = 0) := rfl
example : (there is a real number) = (∃ _x : Real, True) := rfl

Definition:
  a complex number x is complexZeroFromMean if (x = 0).

example (x : Complex) : complexZeroFromMean x = (x = 0) := rfl
example : (there is a complex number x such that x = 0) =
    (∃ x : Complex, x = 0) := rfl
example : (there is a complex number) = (∃ _x : Complex, True) := rfl

example : (for every natural number x: x = x) = (∀ x : Nat, x = x) := rfl
example : (for all natural numbers x and y: x = y) = (∀ x y : Nat, x = y) := rfl

example : (for every integer x: x = x) = (∀ x : Int, x = x) := rfl
example : (for all integers x and y: x = y) = (∀ x y : Int, x = y) := rfl

example : (for every rational number x: x = x) = (∀ x : Rat, x = x) := rfl
example : (for all rational numbers x and y: x = y) = (∀ x y : Rat, x = y) := rfl

example : (for every real number x: x = x) = (∀ x : Real, x = x) := rfl
example : (for all real numbers x and y: x = y) = (∀ x y : Real, x = y) := rfl

example : (for every complex number x: x = x) = (∀ x : Complex, x = x) := rfl
example : (for all complex numbers x and y: x = y) = (∀ x y : Complex, x = y) := rfl

example : (for every boolean x: x = x) = (∀ x : Bool, x = x) := rfl
example : (for all booleans x and y: x = y) = (∀ x y : Bool, x = y) := rfl

-- Negative existence shares witness vocabulary and negates the whole existential.
example : (there is no real number x such that x * x < 0) =
    (¬ ∃ x : Real, x * x < 0) := rfl
example {T : Type*} : (there is no element of T) = (¬ ∃ _x : T, True) := rfl
example {T : Type*} (P : T → Prop) :
    (there is no element x of T such that P x) = (¬ ∃ x : T, P x) := rfl
example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (there is no path in G from u to v) = (¬ ∃ _p : G.Path u v, True) := rfl
example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (there is no path p in G from u to v such that p.val.length = 0) =
    (¬ ∃ p : G.Path u v, p.val.length = 0) := rfl

-- An empty domain distinguishes negated existence from an existential of False.
example : there is no element of Empty := by rintro ⟨x, _⟩; cases x
example : ¬ (∃ _x : Empty, False) := by rintro ⟨_, h⟩; exact h

Definition:
  a real number x is hasNoSmallerSquare if
    there is no real number y such that y * y < x.
example (x : Real) : hasNoSmallerSquare x = (¬ ∃ y : Real, y * y < x) := rfl

example : (there is no natural number) = (¬ ∃ _x : Nat, True) := rfl

example : (there is no integer) = (¬ ∃ _x : Int, True) := rfl

example : (there is no rational number) = (¬ ∃ _x : Rat, True) := rfl

example : (there is no real number) = (¬ ∃ _x : Real, True) := rfl

example : (there is no complex number) = (¬ ∃ _x : Complex, True) := rfl

example : (there is no boolean) = (¬ ∃ _x : Bool, True) := rfl
