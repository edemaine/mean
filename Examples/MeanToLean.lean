import Mean.Syntax

-- Named values and function construction are independent syntax forms.
namespace ValueExamples

Definition: double is the function mapping a natural number n to 2 * n.
example : double = (fun n : Nat => 2 * n) := rfl
example : double 7 = 14 := rfl

Definition: answer is the integer 42.
example : answer = (42 : Int) := rfl

-- Typed values reuse scalar vocabulary; the numeral need not be parenthesized.
Definition: naturalAnswer is the natural number 42.
Definition: negativeAnswer is the integer -42.
Definition: rationalAnswer is the rational number 42.
Definition: realAnswer is the real number 42.
Definition: complexAnswer is the complex number 42.
Definition: booleanAnswer is the boolean true.
Definition: decimalAnswer is the rational number 1.5.
Definition: negativeDecimalAnswer is the rational number -1.5.
Definition: exponentAnswer is the real number 42.e2.
Definition: underscoreAnswer is the integer 1_000.
Definition: hexAnswer is the integer 0x2a.
Definition: computedAnswer is the integer (2 + 3).
example : naturalAnswer = (42 : Nat) := rfl
example : negativeAnswer = (-42 : Int) := rfl
example : rationalAnswer = (42 : Rat) := rfl
example : realAnswer = (42 : Real) := rfl
example : complexAnswer = (42 : Complex) := rfl
example : booleanAnswer = true := rfl
example : decimalAnswer = (1.5 : Rat) := rfl
example : negativeDecimalAnswer = (-1.5 : Rat) := rfl
example : exponentAnswer = (42.e2 : Real) := rfl
example : underscoreAnswer = (1000 : Int) := rfl
example : hexAnswer = (42 : Int) := rfl
example : computedAnswer = (2 + 3 : Int) := rfl
example (n : Int) : (the integer (2 * n)) = 2 * n := rfl
example : (the integer 42) = (42 : Int) := rfl
example : (the integer -42) = (-42 : Int) := rfl
example : (the integer 2 + 3) = (5 : Int) := rfl
example : (the boolean false) = false := rfl

Definition: add is the function mapping a natural number n to
  the function mapping a natural number m to n + m.
example : add = (fun n m : Nat => n + m) := rfl

-- Each subject supplies a successive argument, with earlier names in scope.
Definition: addCurried is the function mapping a natural number n and a natural number m to n + m.
example : addCurried = add := rfl
Definition: mixedSum is the function mapping a natural number n and an integer z to n + z.
example : mixedSum = (fun (n : Nat) (z : Int) => n + z) := rfl
Definition: sumThree is the function mapping a natural number x and
  a natural number y and a natural number z to x + y + z.
example : sumThree = (fun x y z : Nat => x + y + z) := rfl
Definition: constantInteger is the function : Nat → Bool → Int mapping
  a natural number _n and a boolean _b to (0).
example : constantInteger = (fun (_n : Nat) (_b : Bool) => (0 : Int)) := rfl

Definition: integerDouble is the function mapping an integer n to 2 * n.
Definition: rationalDouble is the function mapping a rational number x to 2 * x.
Definition: realDouble is the function mapping a real number x to 2 * x.
Definition: complexDouble is the function mapping a complex number z to 2 * z.
Definition: booleanIdentity is the function mapping a boolean b to b.
example : integerDouble = (fun n : Int => 2 * n) := rfl
example : rationalDouble = (fun x : Rat => 2 * x) := rfl
example : realDouble = (fun x : Real => 2 * x) := rfl
example : complexDouble = (fun z : Complex => 2 * z) := rfl
example : booleanIdentity = (fun b : Bool => b) := rfl

-- The body may be a proposition, a dependent function, or ordinary Lean.
Definition: isZero is the function mapping a natural number n to (n = 0).
example : isZero = (fun n : Nat => n = 0) := rfl
Definition: indexValue is the function mapping a natural number n to
  the function mapping an element i of (Fin n) to i.val.
example : indexValue = (fun (n : Nat) (i : Fin n) => i.val) := rfl
Definition: indexCurried is the function mapping a natural number n and
  an element i of (Fin n) to i.val.
example : indexCurried = indexValue := rfl
example : (the function : (n : Nat) → Fin n → Nat mapping
    a natural number n and an element i of (Fin n) to i.val) = indexValue := rfl
Definition: zeroInteger is the function : Nat → Int mapping a natural number _n to (0).
example : zeroInteger = (fun _n : Nat => (0 : Int)) := rfl

-- Implicit subjects preserve Lean's calling convention and dependent inference.
Definition: implicitAdd is the function mapping a natural number n and
  an implicit natural number m to n + m.
example : implicitAdd 3 (m := 4) = 7 := rfl
example : implicitAdd = (fun (n : Nat) {m : Nat} => n + m) := rfl
Definition: implicitIndex is the function mapping an implicit natural number n and
  an element i of (Fin n) to i.val.
example : implicitIndex (2 : Fin 3) = 2 := rfl
Definition: implicitIntegerNext is the function mapping an implicit integer x to (x + 1).
example : implicitIntegerNext (x := 4) = (5 : Int) := rfl
Definition: implicitConstant is the function : Nat → {_m : Nat} → Int mapping
  a natural number _n and an implicit natural number _m to (0).
example : implicitConstant 3 (_m := 4) = (0 : Int) := rfl
example : (the function mapping an implicit integer x and a boolean b to
    if b then x else -x) = (fun {x : Int} (b : Bool) => if b then x else -x) := rfl

-- Strict implicit arguments are inferred when a later explicit argument is supplied.
Definition: strictIndex is the function mapping a strictly implicit natural number n and
  an element i of Fin n to i.val.
example : strictIndex (2 : Fin 3) = 2 := rfl
Definition: strictConstant is the function : ⦃n : Nat⦄ → Fin n → Int mapping
  a strictly implicit natural number n and an element _i of Fin n to (0).
example : strictConstant (2 : Fin 3) = (0 : Int) := rfl
Definition: strictAdd is the function mapping a natural number n and
  a strictly implicit natural number m to n + m.
example : strictAdd 3 = (fun ⦃m : Nat⦄ => 3 + m) := rfl
example : strictAdd 3 (m := 4) = 7 := rfl
example : (the function mapping a strictly implicit integer x and a boolean b to
    if b then x else -x) = (fun ⦃x : Int⦄ (b : Bool) => if b then x else -x) := rfl
Definition: strictIdentity is the function mapping a strictly implicit element T of Type and
  an element x of T to x.
example : strictIdentity 3 = (3 : Nat) := rfl

-- The optional type constrains the entire function, including nested bodies.
example : (the function : Nat → Int mapping a natural number _n to 0) =
    (fun _n : Nat => (0 : Int)) := rfl
example : (the function : Nat → Prop mapping a natural number n to n = 0) =
    (fun n : Nat => n = 0) := rfl
example : (the function : (n : Nat) → Fin n → Nat mapping a natural number n to
    the function : Fin n → Nat mapping an element i of (Fin n) to i.val) =
    (fun (n : Nat) (i : Fin n) => i.val) := rfl
example : (the function : Nat → Int mapping a natural number n to n) 3 = (3 : Int) := rfl

-- Parentheses delimit the function body in an application or adjective subject.
example : (the function mapping a natural number n to 2 * n) 3 = 6 := rfl
example : ((the function mapping a natural number n to n + 1) is injective) =
    Function.Injective (fun n : Nat => n + 1) := rfl

section
variable {T : Sort u} (offset : Nat)
example : (the function mapping an implicit element _x of T and an element y of T to y) =
    (fun {_x : T} (y : T) => y) := rfl
example : (the function mapping a strictly implicit element _x of T and an element y of T to y) =
    (fun ⦃_x : T⦄ (y : T) => y) := rfl
example : (the function mapping an implicit element S of Sort u and an element x of S to x) =
    (fun {S : Sort u} (x : S) => x) := rfl
example : (the function mapping an implicit element V of Type and an element G of SimpleGraph V to G) =
    (fun {V : Type} (G : SimpleGraph V) => G) := rfl
Definition: implicitIdentityOnT is the function mapping an implicit element x of T to x.
example (x : T) : implicitIdentityOnT (x := x) = x := rfl
-- Typed-element subjects may precede other subjects; parentheses delimit type conjunctions.
example : (the function mapping an element x of T and a natural number _n to x) =
    (fun (x : T) (_n : Nat) => x) := rfl
example : (the function mapping an element _x of T and an element y of T to y) =
    (fun (_x : T) (y : T) => y) := rfl
example (P Q : Prop) : (the function mapping an element h of (P and Q) and a boolean _b to h) =
    (fun (h : P ∧ Q) (_b : Bool) => h) := rfl
example : (the function mapping a natural number _n and a natural number _n to _n) =
    (fun (_x : Nat) (y : Nat) => y) := rfl
example : (the function : T → T mapping an element x of T to x) = (fun x : T => x) := rfl
Definition: identityOnT is the function mapping an element x of T to x.
Definition: shifted is the function mapping a natural number n to n + offset.
example : identityOnT = (fun x : T => x) := rfl
example : shifted offset = (fun n : Nat => n + offset) := rfl
-- A binder shadows the surrounding variable with the same name.
example : (the function mapping a natural number offset to offset + 1) =
    (fun n : Nat => n + 1) := rfl
end

Definition: graphVertices is the function mapping a simple graph G to G.V.
example {V : Type*} (G : SimpleGraph V) : graphVertices G = V := rfl
Definition: graphEdges is the function mapping a simple graph G = (V, E) to E.
example {V : Type*} (G : SimpleGraph V) : graphEdges G = G.edgeSet := rfl
Definition: adjacent is the function mapping a simple graph G = (V, E) and
  an element u of V and an element v of V to s(u, v) ∈ E.
example {V : Type*} (G : SimpleGraph V) : adjacent G = (fun u v : V => s(u, v) ∈ G.edgeSet) := rfl

end ValueExamples

namespace ProofExamples
section
variable (P Q : Prop)
-- These definitions deliberately test functions returning proofs.
set_option linter.defProp false in
Definition: identity is the function mapping a proof h that P to h.
set_option linter.defProp false in
Definition: implicitIdentity is the function mapping an implicit proof h that P to h.
set_option linter.defProp false in
Definition: strictIdentity is the function mapping a strictly implicit proof h that P and
  a proof _eq that h = h to h.
example (h : P) : identity P h = h := rfl
example (h : P) : implicitIdentity P (h := h) = h := rfl
example (h : P) : strictIdentity P (h := h) rfl = h := rfl
example : (the function mapping a proof h that (P and Q) and a boolean _b to h) =
    (fun (h : P ∧ Q) (_b : Bool) => h) := rfl
-- Generic element syntax remains accepted for propositions.
example : (the function mapping an element h of P to h) = identity P := rfl
end
Definition: a proof h that True is reflexive if h = h.
example : reflexive True.intro := rfl
Definition: zero is the function : True → Int mapping a proof _h that True to (0).
example : zero True.intro = (0 : Int) := rfl
end ProofExamples

namespace AbbreviationExamples
Abbreviation: Natural is Nat.
Abbreviation: answer is the integer 42.
Abbreviation: a natural number n is zero if (n = 0).
Abbreviation: double is the function mapping a natural number n to 2 * n.
Abbreviation: zeroInteger is the function : Nat → Int mapping a natural number _n to (0).
Abbreviation: a simple graph G is pathLinked if
  for all vertices u and v of G: there is a path in G from u to v.

-- Overload and instance synthesis must see through the generated abbreviations.
example : (7 : Natural) = (7 : Nat) := rfl
example (n : Nat) : Decidable (zero n) := inferInstance
example : answer = (42 : Int) := rfl
example : double = (fun n : Nat => 2 * n) := rfl
example : zeroInteger = (fun _n : Nat => (0 : Int)) := rfl
example {V : Type*} (G : SimpleGraph V) :
    pathLinked G = (∀ u v : V, ∃ _p : G.Path u v, True) := rfl

-- Unsupported binder forms must retain `abbrev` in the Lean fallback too.
abbrev inhabitedValue [inst : Inhabited Nat] : Nat := @default Nat inst
end AbbreviationExamples

-- Proof witnesses share named, unnamed, positive, and negative existential forms.
example (P : Prop) : (there is a proof that P) = (∃ _h : P, True) := rfl
example (P : Prop) : (there is a proof h that P such that h = h) =
    (∃ h : P, h = h) := rfl
example (P : Prop) : (there is no proof that P) = (¬ ∃ _h : P, True) := rfl
example (P : Prop) : (there is no proof h that P such that h = h) =
    (¬ ∃ h : P, h = h) := rfl
example (P Q : Prop) : (there is a proof that (P and Q)) = (∃ _h : P ∧ Q, True) := rfl
example (P : Prop) (existentialWitness : Nat) :
    (there is a proof that P such that existentialWitness = 0) =
    (∃ _h : P, existentialWitness = 0) := rfl
example (n : Nat) : (there is a proof h that n > 0 such that h = h) =
    (∃ h : n > 0, h = h) := rfl
example (P : Prop) : (there is an element of P) = (there is a proof that P) := rfl

-- Statements reuse Mean propositions; proofs remain ordinary Lean terms or tactics.
namespace TheoremExamples

Theorem natTrans3:
  for all natural numbers x and y:
    for all natural numbers z and w:
      if x = y and z = y and z = w then x = w
Proof: by
  intro x y z w ⟨hxy, hzy, hzw⟩
  exact hxy.trans (hzy.symm.trans hzw)

Theorem zeroExists:
  there is a natural number n such that n = 0
Proof:
  ⟨0, rfl⟩

example : ∀ x y z w : Nat, x = y ∧ z = y ∧ z = w → x = w := natTrans3
example : ∃ n : Nat, n = 0 := zeroExists

Lemma natAddZero:
  for every natural number n:
    n + 0 = n
Proof: by
  intro n
  rfl

Example:
  for every natural number n:
    n + 0 = n
Proof: natAddZero

Example:
  there is a natural number n such that n = 0
Proof: by
  exact zeroExists

section
variable {V : Type*} (G : SimpleGraph V)

Lemma edgeSubsetSelf:
  the edge set of G ⊆ the edge set of G
Proof: by
  intro e he
  exact he

example : G.edgeSet ⊆ G.edgeSet := edgeSubsetSelf G

Example:
  the edge set of G ⊆ the edge set of G
Proof: edgeSubsetSelf G
end

end TheoremExamples

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

-- Type inhabitation is preserved directly, including universes and precedence.
example {T : Sort u} : (T is nonempty) = Nonempty T := rfl
example {T : Sort u} : (T is empty) = IsEmpty T := rfl
example {T : Sort u} (P : Prop) : (T is nonempty and P) = (Nonempty T ∧ P) := rfl
example {T : Sort u} (P : Prop) : (if T is empty then P) = (IsEmpty T → P) := rfl
example (n : Nat) : ((Fin n) is nonempty) = Nonempty (Fin n) := rfl
example (n : Nat) : ((Fin n) is empty) = IsEmpty (Fin n) := rfl

Definition:
  a simple graph G is hasVertices if G.V is nonempty.
Definition:
  a simple graph G is hasNoVertices if G.V is empty.
example {V : Type*} (G : SimpleGraph V) : hasVertices G = Nonempty V := rfl
example {V : Type*} (G : SimpleGraph V) : hasNoVertices G = IsEmpty V := rfl

-- Adjectives share application syntax while retaining distinct Lean predicates.
example {T : Sort u} : (T is finite) = Finite T := rfl
example {T : Sort u} : (T is infinite) = Infinite T := rfl
example {T : Sort u} : (T is countable) = Countable T := rfl
example {A : Sort u} {B : Sort v} (f : A → B) :
    (f is injective) = Function.Injective f := rfl
example {A : Sort u} {B : Sort v} (f : A → B) :
    (f is surjective) = Function.Surjective f := rfl
example {A : Sort u} {B : Sort v} (f : A → B) :
    (f is bijective) = Function.Bijective f := rfl
example {A B : Type*} (f : A → B) :
    (f is injective and f is surjective) = (Function.Injective f ∧ Function.Surjective f) := rfl
Definition:
  an element f of (Nat → Nat) is oneToOne if f is injective.
example (f : Nat → Nat) : oneToOne f = Function.Injective f := rfl

-- Property phrases share their meaning across definite and possessive forms.
section
variable {V : Type*} (G H : SimpleGraph V) (u : V)
example : (the edge set of G) = G.edgeSet := rfl
example : (G's edge set) = G.edgeSet := rfl
example : (the vertex type of G) = G.V := rfl
example : (G's vertex type) = G.V := rfl
example : (the set of neighbors of u in G) = G.neighborSet u := rfl
example : (the neighbor set of u in G) = G.neighborSet u := rfl
example : (the set of u's neighbors in G) = G.neighborSet u := rfl
example : (the set of edges incident to u in G) = G.incidenceSet u := rfl
example : (the incidence set of u in G) = G.incidenceSet u := rfl
example : (the set of neighbors of u in (G ⊔ H)) = (G ⊔ H).neighborSet u := rfl
example : (u's neighbor set in G) = G.neighborSet u := rfl
example : (u's incidence set in G) = G.incidenceSet u := rfl
example : (the edge set of (G ⊔ H)) = (G ⊔ H).edgeSet := rfl
example : (G's edge set = ∅ and H's edge set = ∅) =
    (G.edgeSet = ∅ ∧ H.edgeSet = ∅) := rfl
example : (the vertex type of G is nonempty) = Nonempty G.V := rfl
end

Definition:
  a simple graph G is hasNoEdges if the edge set of G = ∅.
Definition:
  a simple graph G is hasNoEdgesPossessive if G's edge set = ∅.
example {V : Type*} (G : SimpleGraph V) : hasNoEdges G = (G.edgeSet = ∅) := rfl
example {V : Type*} (G : SimpleGraph V) : hasNoEdges G = hasNoEdgesPossessive G := rfl
