import Examples.MeanToLean
import Mean

-- Break a whole connective chain together, preserving grouping and binder scope.
section
variable (P Q R S : Prop) (u v w : Nat)
/-- info: P and Q and R -/
#guard_msgs in
set_option format.width 13 in
#mean_term P ∧ Q ∧ R
/--
info: P and
Q and
R
-/
#guard_msgs in
set_option format.width 12 in
#mean_term P ∧ Q ∧ R
/--
info: P and
Q and
R and
S
-/
#guard_msgs in
set_option format.width 16 in
#mean_term P ∧ Q ∧ R ∧ S
/--
info: P and
(for every natural number n:
  n = n) and
Q
-/
#guard_msgs in
#mean_term P ∧ (∀ n : Nat, n = n) ∧ Q
/-- info: u and v are BinaryPredicateExamples.Adjacent -/
#guard_msgs in
set_option format.width 12 in
#mean_term BinaryPredicateExamples.Adjacent u v
/-- info: P or Q or R -/
#guard_msgs in
set_option format.width 11 in
#mean_term P ∨ Q ∨ R
/--
info: P or
Q or
R
-/
#guard_msgs in
set_option format.width 10 in
#mean_term P ∨ Q ∨ R
/--
info: P or
(there is a natural number n such that
  n = n) or
Q
-/
#guard_msgs in
#mean_term P ∨ (∃ n : Nat, n = n) ∨ Q
section
set_option format.width 16
#mean_term_compare P ∧ Q ∧ R ∧ S
#mean_term_compare ((P ∧ Q) ∧ R) ∧ S
#mean_term_compare P ∧ (Q ∨ R) ∧ S
#mean_term_compare (P ∧ Q ∧ R ∧ S) ∨ Q
#mean_term_compare P ↔ Q ∧ R ∧ S
#mean_term_compare P ∧ BinaryPredicateExamples.Adjacent u v ∧ BinaryPredicateExamples.ternary u v w
#mean_term_compare P ∧ (let condition := Q ∧ R; condition) ∧ S
#mean_term_compare P ∨ Q ∨ R ∨ S ∨ P
#mean_term_compare ((P ∨ Q) ∨ R) ∨ S
#mean_term_compare P ∨ (Q ∧ R) ∨ S
#mean_term_compare P ∨ (Q ∧ R ∧ S) ∨ Q
#mean_term_compare P ↔ Q ∨ R ∨ S ∨ P
#mean_term_compare P ∨ BinaryPredicateExamples.Adjacent u v ∨ BinaryPredicateExamples.ternary u v w
#mean_term_compare P ∨ (let condition := Q ∨ R; condition) ∨ S
end
#mean_term_compare P ∧ (∀ n : Nat, n = n) ∧ Q
#mean_term_compare P ∧ ∀ n : Nat, n = n ∧ Q
#mean_term_compare P ∨ (∃ n : Nat, n = n) ∨ Q
#mean_term_compare P ∨ ∃ n : Nat, n = n ∨ Q
end

section
variable (A : Type u) (R S : A → A → Prop) (x y : A) (P : Prop)
/-- info: x is related to y by the transitive closure of R -/
#guard_msgs in
#mean_term Relation.TransGen R x y
/-- info: the composition of R followed by S -/
#guard_msgs in
#mean_term Relation.Comp R S
#mean_term_compare Relation.TransGen R
#mean_term_compare Relation.ReflGen R
#mean_term_compare Relation.SymmGen R
#mean_term_compare Relation.EqvGen R
#mean_term_compare Relation.ReflTransGen R
#mean_term_compare Relation.TransGen R x y
#mean_term_compare Relation.ReflGen R x y
#mean_term_compare Relation.SymmGen R x y
#mean_term_compare Relation.EqvGen R x y
#mean_term_compare ¬ Relation.TransGen R x y
#mean_term_compare ¬ Relation.ReflGen R x y
#mean_term_compare ¬ Relation.SymmGen R x y
#mean_term_compare ¬ Relation.EqvGen R x y
#mean_term_compare P ∧ Relation.TransGen R x y
#mean_term_compare Relation.ReflGen R x y ∧ P
#mean_term_compare P ∨ ¬ Relation.EqvGen R x y
#mean_term_compare Relation.Comp R S
#mean_term_compare Relation.Comp R S x y
#mean_term_compare ¬ Relation.Comp R S x y
#mean_term_compare P ∧ Relation.Comp R S x y
#mean_term_compare Relation.EqvGen (Relation.TransGen R) x y
#mean_term_compare Relation.Comp (Relation.ReflGen R) (Relation.SymmGen S) x y
#mean_term_compare Relation.TransGen (Relation.Comp R S) x y
#mean_term_compare some (fun u v : A => Relation.Comp R S u v)
end
section
variable (A : Type u) (B : Type v) (C : Type w)
variable (R : A → B → Prop) (S : B → C → Prop) (x : A) (z : C)
#mean_term_compare Relation.Comp R S x z
#mean_term_compare ∃ y : B, R x y ∧ S y z
end
#mean_term_compare Relation.SymmGen (fun x y : Nat => x < y) 0 1
#mean_term_compare Relation.Comp (fun x y : Nat => x + 1 = y) (fun x y : Nat => x < y) 0 2
#mean_term_compare Relation.TransGen (Relation.Comp (fun x y : Nat => x + 1 = y) (fun x y : Nat => x < y))

-- Closure kinds and relation-composition order are part of the checked meaning.
open Lean Meta Elab Term in
run_elab do
  let ty ← elabType (← `(Nat → Nat → Prop))
  withLocalDeclD `R ty fun r => do
    withLocalDeclD `S ty fun s => do
      let x := mkNatLit 0
      let y := mkNatLit 1
      let probes := [
        (← mkAppM ``Relation.TransGen #[r, x, y],
          "0 is related to 1 by the reflexive transitive closure of R"),
        (← mkAppM ``Relation.ReflGen #[r, x, y],
          "0 is related to 1 by the transitive closure of R"),
        (← mkAppM ``Relation.SymmGen #[r, x, y],
          "0 is related to 1 by the equivalence closure of R"),
        (← mkAppM ``Relation.EqvGen #[r, x, y],
          "0 is related to 1 by the symmetric closure of R"),
        (← mkAppM ``Relation.Comp #[r, s, x, y],
          "0 is related to 1 by the composition of S followed by R")]
      for (original, text) in probes do
        let rejected ← withoutModifyingState do
          try
            Mean.RoundTrip.checkText original text
            pure false
          catch _ => pure true
        unless rejected do throwError "relation operator rendering changed closure kind or composition order"

section
variable (A : Type u) (R : A → A → Prop) (x y z : A) (P Q : Prop)
/-- info: x is related to y by the reflexive transitive closure of R -/
#guard_msgs in
#mean_term Relation.ReflTransGen R x y
#mean_term_compare Relation.ReflTransGen R x y
#mean_term_compare ¬ Relation.ReflTransGen R x y
#mean_term_compare Relation.ReflTransGen R x x
#mean_term_compare P ∧ Relation.ReflTransGen R x y
#mean_term_compare Relation.ReflTransGen R x y ∧ P
#mean_term_compare P ∨ ¬ Relation.ReflTransGen R x y
#mean_term_compare Relation.ReflTransGen R x y ↔ Q
#mean_term_compare Relation.ReflTransGen R x y → Relation.ReflTransGen R y z
#mean_term_compare Relation.ReflTransGen R x y ∧ Relation.ReflTransGen R y z
#mean_term_compare ∀ t : A, Relation.ReflTransGen R x t
#mean_term_compare some (fun u v : A => Relation.ReflTransGen R u v)
end
#mean_term_compare Relation.ReflTransGen (fun x y : Nat => x + 1 = y) 0 3
#mean_term_compare Relation.ReflTransGen (fun x y : Nat => x < y) 0 3

-- Do not replace reflexive–transitive closure by one step, or reverse it.
open Lean Elab Term in
run_elab do
  let ty ← elabType (← `(Nat → Nat → Prop))
  Lean.Meta.withLocalDeclD `R ty fun r => do
    let x := mkNatLit 0
    let y := mkNatLit 1
    let original ← Lean.Meta.mkAppM ``Relation.ReflTransGen #[r, x, y]
    for text in [
        "0 and 1 are R",
        "1 is related to 0 by the reflexive transitive closure of R"] do
      let rejected ← withoutModifyingState do
        try
          Mean.RoundTrip.checkText original text
          pure false
        catch _ => pure true
      unless rejected do throwError "relation closure rendering changed steps or direction"

section
open BinaryPredicateExamples
variable (u v w : Nat) (z : Int) (P Q R : Prop) (S : Set Nat)
variable (b : Bool)
/-- info: u and v are Adjacent -/
#guard_msgs in
#mean_term Adjacent u v
#mean_term_compare Adjacent u v
#mean_term_compare ¬ Adjacent u v
#mean_term_compare ordered u z
#mean_term_compare same u v
#mean_term_compare dependent u (0 : Fin (u + 1))
#mean_term_compare Adjacent (u + 1) (v * 2)
#mean_term_compare P ∧ Adjacent u v
#mean_term_compare Adjacent u v ∧ P
#mean_term_compare Adjacent u v ∧ Adjacent v w
#mean_term_compare (Adjacent u v ∧ P) ∨ Q
#mean_term_compare P ∨ ¬ Adjacent u v
#mean_term_compare Adjacent u v ↔ P
#mean_term_compare Adjacent u v → ¬ Adjacent v u
#mean_term_compare iffRelated (P ∧ Q) R
#mean_term_compare ternary u v w
#mean_term_compare ¬ ternary u v w
#mean_term_compare four u v w 0
#mean_term_compare mixedTernary u z b
#mean_term_compare sameThree u v w
#mean_term_compare P ∧ Q ∧ ternary u v w
#mean_term_compare ternary u v w ∧ P
#mean_term_compare P ∨ ¬ ternary u v w
#mean_term_compare Adjacent u v ∧ ternary u v w
#mean_term_compare (ternary u v w ∧ P) ∧ Q
#mean_term_compare ternary u v w ↔ P
#mean_term_compare u = v
#mean_term_compare u ≠ v
#mean_term_compare u ≤ v
#mean_term_compare u ∈ S
#mean_term_compare P ∧ Q ∧ R
end
section
variable (A : Sort u) (x y : A) (r : A → A → Prop)
#mean_term_compare BinaryPredicateExamples.same x y
#mean_term_compare r x y
end

open Lean Elab Term in
run_elab do
  for term in [
      ← `(0 and 1 are BinaryPredicateExamples.booleanRelation),
      ← `(0 and 1 are BinaryPredicateExamples.ternary)] do
    let rejected ← withoutModifyingState do
      try
        discard <| withoutErrToSorry <| elabTerm term none
        synthesizeSyntheticMVarsNoPostponing
        pure false
      catch _ => pure true
    unless rejected do throwError "accepted a non-proposition-valued binary predicate"
  let original ← elabTerm (← `(BinaryPredicateExamples.ordered 1 (2 : Int))) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  for text in [
      "2 and 1 are BinaryPredicateExamples.ordered",
      "1 and 2 are not BinaryPredicateExamples.ordered"] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkText original text
        pure false
      catch _ => pure true
    unless rejected do throwError "binary predicate rendering changed argument order or polarity"

-- Parentheses delimit a predicate argument list inside an outer conjunction.
section
open BinaryPredicateExamples
variable (P Q : Prop) (u v w : Nat)
/-- info: P and (u and v are Adjacent) -/
#guard_msgs in
#mean_term P ∧ Adjacent u v
/-- info: (u and v are Adjacent) and (u and v and w are ternary) -/
#guard_msgs in
#mean_term Adjacent u v ∧ ternary u v w
end

#mean_compare CustomCoercionExamples.wrap
/--
info: the function mapping a natural number n to
  n as CustomCoercionExamples.Foo
-/
#guard_msgs in
#mean_term fun (n : Nat) => (n : CustomCoercionExamples.Foo)
section
open CustomCoercionExamples
variable (n : Nat) (A : Type u) (x : A)
/-- info: x as Box A -/
#guard_msgs in
#mean_term (x : Box A)
#mean_term_compare (n : Foo)
#mean_term_compare ((n + 1 : Nat) : Foo)
#mean_term_compare ((n : Foo) : Bar)
#mean_term_compare some (n : Foo)
#mean_term_compare (n : Foo) = (n : Foo)
#mean_term_compare (x : Box A)
#mean_term_compare ((fun n : Nat => n + 1) : Box (Nat → Nat))
end
section
variable (A B : Type u) [Coe A B] (x : A)
#mean_term_compare (x : B)
end

open Lean Elab Term in
run_elab do
  let invalid ← withoutModifyingState do
    try
      discard <| withoutErrToSorry <| elabTerm
        (← `((fun n : Nat => n) as CustomCoercionExamples.Foo)) none
      synthesizeSyntheticMVarsNoPostponing
      pure false
    catch _ => pure true
  unless invalid do throwError "accepted an unavailable custom coercion"

section
open MeasureTheory
variable (A : Type u) [MeasurableSpace A] (μ ν : Measure A) (p q : A → Prop)
#mean_term_compare ∀ᵐ x ∂μ, p x
#mean_term_compare ∀ᵐ x ∂(μ + ν), p x
#mean_term_compare ∀ᵐ x ∂μ, p x → q x
#mean_term_compare ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x ∧ q y
#mean_term_compare (∀ᵐ x ∂μ, p x) ∧ True
#mean_term_compare (∀ᵐ x ∂μ, p x) → False
#mean_term_compare ¬ ∀ᵐ x ∂μ, p x
#mean_term_compare ∀ x : A, (∀ᵐ y ∂μ, p y) → p x
#mean_term_compare ∀ᵐ _x ∂μ, True
#mean_term_compare ∀ᵐ x ∂μ, ∃! y : A, x = y
-- Ordinary filter quantifiers must not be mistaken for measure quantifiers.
variable (F : Filter A)
#mean_term_compare ∀ᶠ x in F, p x
end
section
open MeasureTheory
variable (A : Type u) [MeasureSpace A] (p : A → Prop) (μ : Measure A)
/--
info: for almost every element x of A:
  x is p
-/
#guard_msgs in
#mean_term ∀ᵐ x, p x
#mean_term_compare ∀ᵐ x, p x
#mean_term_compare ∀ᵐ x ∂μ, p x
#mean_term_compare ∀ᵐ x, p x → x = x
#mean_term_compare ∀ᵐ x, ∃! y : A, x = y
end

open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(fun (A : Type) [MeasurableSpace A]
    (μ ν : MeasureTheory.Measure A) (p : A → Prop) => ∀ᵐ x ∂μ, p x)) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText original
        "the function mapping an element A of Type and an instance of typeclass MeasurableSpace A and an element μ of MeasureTheory.Measure A and an element ν of MeasureTheory.Measure A and a function p from A to Prop to for almost every element x of A with respect to ν: p x"
      pure false
    catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed almost-everywhere measure"

section
variable (z : Int) (n m : Nat) (q : Rat) (x : Real) (i : Fin 3)
variable (p : Fin 3 → Int)
/-- info: p i as a real number -/
#guard_msgs in
#mean_term (p i : Real)
/-- info: n as an integer -/
#guard_msgs in
#mean_term (n : Int)
#mean_term_compare (p i : Real)
#mean_term_compare (z : Real)
#mean_term_compare (n : Int)
#mean_term_compare (q : Real)
#mean_term_compare (x : Complex)
#mean_term_compare (i : Nat)
#mean_term_compare ((z + 1 : Int) : Real)
#mean_term_compare ((n - m : Nat) : Int)
#mean_term_compare ((-z : Int) : Real)
#mean_term_compare ((n : Int) : Real)
#mean_term_compare (z : Real) + 1
#mean_term_compare (z : Real) ≤ 1
#mean_term_compare some (z : Real)
end

-- The source arithmetic must not be reinterpreted in the target type.
open Lean Elab Term in
run_elab do
  let subtraction ← elabTerm (← `(fun n m : Nat => ((n - m : Nat) : Int))) none
  synthesizeSyntheticMVarsNoPostponing
  let subtraction ← instantiateMVars subtraction
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText subtraction
        "the function mapping a natural number n and a natural number m to (n as an integer) - (m as an integer)"
      pure false
    catch _ => pure true
  unless rejected do throwError "coercion rendering changed natural-number subtraction"
  let invalid ← withoutModifyingState do
    try
      discard <| withoutErrToSorry <| elabTerm (← `((fun n : Nat => n) as a real number)) none
      synthesizeSyntheticMVarsNoPostponing
      pure false
    catch _ => pure true
  unless invalid do throwError "accepted an unavailable scalar coercion"

/--
info: the set of elements n of ℕ such that
  n > 0 and n < 3
-/
#guard_msgs in
#mean_term {n : Nat | n > 0 ∧ n < 3}
#mean_compare SetComprehensionExamples.zeros
#mean_term_compare {n : Nat | n > 0 ∧ n < 3}
#mean_term_compare {_n : Nat | True}
#mean_term_compare {_n : Nat | False}
#mean_term_compare {«a» : Nat | «a» = 0}
#mean_term_compare {S : Set Nat | 0 ∈ S}
#mean_term_compare some {n : Nat | n > 0}
#mean_term_compare {f : Nat → Nat | f 0 = 0}
section
variable (A : Type u) (p : A → Prop) (n : Nat) (S : Set Nat)
#mean_term_compare {x : A | p x}
#mean_term_compare Set.ofPred p
#mean_term_compare n ∈ {m : Nat | m > 0}
#mean_term_compare {n : Nat | n > 0} ∪ S
#mean_term_compare {n : Nat | n > 0} = S
#mean_term_compare ({n : Nat | n > 0}, n)
end

open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `({n : Nat | n > 0})) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText original "the set of elements n of ℕ such that n = 0"
      pure false
    catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed set condition"
  let ordinary := (← Lean.Meta.ppExpr original).pretty
  unless (ordinary.splitOn "{").length > 1 do
    throwError "Mean set comprehension leaked into the ordinary Lean view: {ordinary}"

/-- info: the type of sets of natural numbers -/
#guard_msgs in
#mean_term Set Nat
/-- info: there is a set of natural numbers -/
#guard_msgs in
#mean_term ∃ _S : Set Nat, True
#mean_compare SetPhraseExamples.Family
#mean_compare SetPhraseExamples.reflexive
#mean_term_compare Set Nat
#mean_term_compare Set SetPhraseExamples.Point
#mean_term_compare Set (Nat → Bool)
#mean_term_compare Set (Set Nat)
#mean_term_compare fun (S : Set Nat) => S
#mean_term_compare fun {S : Set Int} => S
#mean_term_compare fun ⦃S : Set Bool⦄ => S
#mean_term_compare ∀ S : Set Int, 0 ∈ S → 0 ∈ S
#mean_term_compare ∃ T : Set SetPhraseExamples.Point, T = ∅
#mean_term_compare ¬ ∃ _S : Set Nat, True
#mean_term_compare ∃! S : Set Nat, S = ∅
#mean_term_compare fun (f : Set Nat → Set Int) => f
#mean_term_compare fun (f : List Nat → Set Nat → Bool) => f
#mean_term_compare fun (S : Finset Nat) => S
-- An alias for a set keeps its declared type name.
#mean_term_compare fun (S : SetPhraseExamples.Family) => S

section
variable (A : Type u)
#mean_term_compare Set A
#mean_term_compare fun (S : Set A) => S
end

-- The renderer must not substitute `Finset` for an arbitrary set.
open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(Set Nat)) none
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText original "Finset Nat"
      pure false
    catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a finite collection for Set"

section
variable (P Q : Prop) (p : Nat → Prop) (S : Set Prop) (r : {_q : Prop // True})
variable (s t : Set Nat) (n : Nat) [Decidable P]
/-- info: id P -/
#guard_msgs in
#mean_term id P
/-- info: ⨅ (i : ℕ), p i -/
#guard_msgs in
#mean_term ⨅ i : Nat, p i
/-- info: r as Prop -/
#guard_msgs in
#mean_term (r : Prop)
#mean_term_compare id P
#mean_term_compare ⨅ i : Nat, p i
#mean_term_compare ⨆ i : Nat, p i
#mean_term_compare sInf S
#mean_term_compare sSup S
#mean_term_compare (r : Prop)
#mean_term_compare Classical.choice (show Nonempty Prop from ⟨P⟩)
#mean_term_compare n ≠ 0
#mean_term_compare n ∉ s
#mean_term_compare s ⊆ t
#mean_term_compare if P then Q else True
end

/--
info: there is a unique natural number n such that
  n = 0
-/
#guard_msgs in
#mean_term ∃! n : Nat, n = 0
/-- info: there is a unique index in [0, 1) -/
#guard_msgs in
#mean_term ∃! _i : Fin 1, True
#mean_term_compare ∃! n : Nat, n = 0
#mean_term_compare ∃! _i : Fin 1, True
#mean_term_compare ∃! _n : Nat, False
#mean_term_compare ∃! xs : List Nat, xs = []
#mean_term_compare ∃! f : Nat → Nat, f 0 = 0
#mean_term_compare (∃! n : Nat, n = 0) ∧ False
#mean_term_compare False ∨ (∃! n : Nat, n = 0)
#mean_term_compare (∃! n : Nat, n = 0) ↔ True
#mean_term_compare (∃! _n : Nat, True) → False
#mean_term_compare (∃! n : Nat, n = 0) → False
#mean_term_compare ∀ n : Nat, (∃! m : Nat, m = n) → n = n
#mean_term_compare ¬ ∃! n : Nat, n = 0
section
variable (Point : Type) (P : Point → Prop)
#mean_term_compare ∃! t : Point, P t
#mean_term_compare ExistsUnique P
end

-- Quantifier applications and ordinary predicates on predicates have the same
-- type shape. Structural dispatch must win without banning function subjects.
open Lean Meta Elab Term in
run_elab do
  let predicateType ← elabType (← `(Nat → Prop))
  let higherType ← elabType (← `((Nat → Prop) → Prop))
  withLocalDeclD `p predicateType fun p => do
    withLocalDeclD `acceptsPredicate higherType fun acceptsPredicate => do
      for explicit in [false, true] do
        withOptions (fun opts => opts.setBool `pp.explicit explicit) do
          for (name, heading) in [
              (``Exists, "there is a natural number"),
              (``ExistsUnique, "there is a unique natural number")] do
            let e ← mkAppM name #[p]
            let text ← Mean.Render.renderChecked e
            unless text.startsWith heading do
              throwError "quantifier reached generic predicate rendering: {text}"
          let e ← mkAppM ``ExistsUnique #[p]
          let text ← Mean.Render.renderChecked (mkNot e)
          unless (text.splitOn " is not ").length == 1 do
            throwError "negated quantifier reached generic predicate rendering: {text}"
          let text ← Mean.Render.renderChecked (mkApp acceptsPredicate p)
          unless text == "p is acceptsPredicate" do
            throwError "ordinary predicate on predicates lost adjective wording: {text}"

open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(∃! n : Nat, n = 0)) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  for text in [
      "there is a natural number n such that n = 0",
      "there is exactly one natural number n such that n = 1"] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkText original text
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted changed unique existence"

section
variable (Point : Type) (P : Set Point) (Adjacent : Point → Point → Prop) (p q : Point)
#mean_term_compare Relation.ReflTransGen
  (fun («a» b : Point) => «a» ∈ P ∧ b ∈ P ∧ Adjacent «a» b) p q
end
#mean_term_compare List.map (fun n : Nat => n + 1) [1, 2]
#mean_term_compare some (fun n : Nat => n + 1)
#mean_term_compare some (fun _n : Nat => (0 : Int))
#mean_term_compare (some (fun n : Nat => n + 1), some (fun b : Bool => b))
#mean_term_compare some (fun (n : Nat) (i : Fin n) => i)
#mean_term_compare (some (fun {n : Nat} => n) : Option ({_n : Nat} → Nat))
#mean_term_compare (some (fun ⦃n : Nat⦄ => n) : Option (⦃_n : Nat⦄ → Nat))
#mean_term_compare some (fun [inst : Inhabited Nat] => @default Nat inst)
#mean_term_compare some (let f := fun n : Nat => n + 1; f)
#mean_term_compare Subtype (fun n : Nat => n > 0 ∧ n < 3)
#mean_term_compare {n : Nat | n > 0 ∧ n < 3}
#mean_term_compare some (∃! n : Nat, n = 0)
section
variable (n : Nat)
#mean_term_compare (some (fun n : Nat => n + 1), n)
end

-- Ordinary Lean output stays ordinary; nested Mean functions must be visible.
open Lean Elab Term in
run_elab do
  let e ← elabTerm (← `(Relation.ReflTransGen (fun x y : Nat => x = y) 0 1)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let text ← Mean.Render.renderChecked e
  unless (text.splitOn "the function mapping").length > 1 do
    throwError "nested function kept its Lean syntax: {text}"
  let ordinary := (← Lean.Meta.ppExpr e).pretty
  unless (ordinary.splitOn "fun ").length > 1 do
    throwError "Mean function wording leaked into ordinary Lean output: {ordinary}"
  for (term, marker) in [
      (← `({n : Nat | n > 0}), "the set of elements"),
      (← `(some (∃! n : Nat, n = 0)), "∃!")] do
    let e ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let text ← Mean.Render.renderChecked (← instantiateMVars e)
    unless (text.splitOn marker).length > 1 do
      throwError "set-comprehension or native unique-existence wording was lost: {text}"

section
variable (Point : Type) (P : Set Point)
/--
info: for every element p of Point where p ∈ P:
  p ∈ P
-/
#guard_msgs in
#mean_term ∀ p : Point, p ∈ P → p ∈ P
#mean_term_compare ∀ p : Point, p ∈ P → p ∈ P
#mean_term_compare ∀ p : Point, p ∈ P → ∀ q : Point, q ∈ P → p = q → q = p
end
section
variable (xs : List Nat) (P Q : Nat → Prop)
#mean_term_compare ∀ n m : Nat, n ≤ m → n ≤ m
#mean_term_compare ∀ i : Fin xs.length, xs[i] > 0 → xs[i] ≥ 1
#mean_term_compare ∀ f : Nat → Nat, f 0 = 0 → f 0 ≤ 1
#mean_term_compare ∀ n : Nat, (∀ m : Nat, n ≤ m) → n = 0
#mean_term_compare ∀ n : Nat, (∃ m : Nat, n = m) → n = n
#mean_term_compare ∀ n : Nat, (P n ↔ Q n) → P n → Q n
-- Proofs referenced in the conclusion must remain explicit binders.
#mean_term_compare ∀ n : Nat, ∀ h : n > 0, h = h
#mean_term_compare ∀ n : Nat, ∀ h : P n, h = h → h = h
end

open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(∀ n : Nat, n > 0 → n ≥ 1)) none
  for text in [
      "for every natural number n: n ≥ 1",
      "for every natural number n where n = 0: n ≥ 1"] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkText original text
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted a changed quantifier restriction"

/--
info: Definition:
  elements «a» and b of PredicateExamples.Point are PredicateExamples.adjacent if
    (the sum over indices i in [0, 3) of |«a» i - b i| = 1).
-/
#guard_msgs in
#mean PredicateExamples.adjacent
#mean_compare PredicateExamples.adjacent
#mean_compare PredicateExamples.ordered
#mean_compare PredicateExamples.equalIntegers
#mean_compare PredicateExamples.sameIndex
#mean_compare PredicateExamples.below
#mean_compare PredicateExamples.reflexivePair
#mean_compare PredicateExamples.positivePair
#mean_compare PredicateExamples.ignoresSecond
#mean_compare PredicateExamples.mixed

-- The declaration checker rejects changes to argument order, names, and kind.
open Lean Elab Term in
run_elab do
  for (name, text) in [
      (``PredicateExamples.below,
        "Definition: an index i in [0, n) and a natural number n are changed if i.val < n."),
      (``PredicateExamples.ignoresSecond,
        "Definition: natural numbers x and z are changed if x = x."),
      (``PredicateExamples.equalIntegers,
        "Definition: integers x and y are changed if x = y.")] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted changed predicate arguments"

/--
info: the function mapping a function «a» from indices in [0, 3) to ℤ and a function b from indices in [0, 3) to ℤ to
  the sum over indices i in [0, 3) of |«a» i - b i| = 1
-/
#guard_msgs in
#mean_term fun («a» b : Fin 3 → Int) => (∑ i : Fin 3, |«a» i - b i|) = 1
#mean_term_compare fun («a» b : Fin 3 → Int) => (∑ i : Fin 3, |«a» i - b i|) = 1
section
variable (f : Fin 3 → Nat) (xs : List Nat) (ys : Array Nat)
variable (α : Type u) [Fintype α] (g : α → Int) (s : Finset Nat)
#mean_term_compare ∑ i : Fin 3, (f i + 1)
#mean_term_compare (∑ i : Fin 3, f i) + 1
#mean_term_compare 2 * (∑ i : Fin 3, f i)
#mean_term_compare (∑ i : Fin 3, f i) = 1 ∧ True
#mean_term_compare ∑ i : Fin 0, i.val
#mean_term_compare ∑ i : Fin xs.length, xs[i]
#mean_term_compare ∑ i : Fin ys.size, ys[i]
#mean_term_compare ∑ x : α, g x
#mean_term_compare ∑ i ∈ s, (i + 1)
#mean_term_compare ∑ i ∈ s with i > 0, i
#mean_term_compare ∑ i : Fin 3, ∑ j : Fin 3, (f i + f j)
#mean_term_compare ∑ i ∈ s, ∑ j ∈ Finset.range i, (i + j)
#mean_term_compare ∑ h : Fin 2 → Bool, if h 0 then 1 else 0
#mean_term_compare fun (i : Nat) => (∑ i : Fin 3, f i) + i
#mean_term_compare fun (f : Fin 3 → Int) => (∑ i : Fin 3, f i) < 0
end

#mean_compare FunctionEndpointExamples.Point
#mean_compare FunctionEndpointExamples.Reindexer
#mean_compare FunctionEndpointExamples.Consumer
#mean_compare FunctionEndpointExamples.Curried
/--
info: Abbreviation:
  a FunctionEndpointExamples.Point is
    a function from indices in [0, 3) to ℤ.
-/
#guard_msgs in
#mean FunctionEndpointExamples.Point
/--
info: the function mapping a function f from indices in [0, 3) to lists of natural numbers and a boolean b to
  (f 0, b)
-/
#guard_msgs in
#mean_term fun (f : Fin 3 → List Nat) (b : Bool) => (f 0, b)
#mean_term_compare fun (f : Fin 3 → List Nat) (b : Bool) => (f 0, b)
#mean_term_compare fun (f : Nat → Fin 3 → Int) => f
#mean_term_compare fun (f : List (Nat → Nat) → List Nat) => f
#mean_term_compare fun (f : (Nat → Nat) → Fin 3) => f
section
variable (xs : List Nat) (ys : Array Nat) (A : Type u)
#mean_term_compare fun (f : Fin xs.length → Int) => f
#mean_term_compare fun (f : Nat → Fin ys.size) => f
#mean_term_compare fun (f : List A → Prop) => f
#mean_term_compare ∃ _f : Fin xs.length → Nat, True
end

open Lean Elab Term in
run_elab do
  for (name, text) in [
      (``FunctionEndpointExamples.Point,
        "Abbreviation: a changed is a function from indices in [0, 4) to ℤ."),
      (``FunctionEndpointExamples.Reindexer,
        "Abbreviation: a changed is a function from indices in [0, 3) to indices in [0, 5)."),
      (``FunctionEndpointExamples.Curried,
        "Abbreviation: a changed is a function from (Nat × Fin 3) to integers.")] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted a changed function signature"

#mean_compare TypeDeclarationExamples.Point
#mean_compare TypeDeclarationExamples.Prototile
#mean_compare TypeDeclarationExamples.PrototileDef
#mean_compare TypeDeclarationExamples.Direction
#mean_compare TypeDeclarationExamples.Index
#mean_compare TypeDeclarationExamples.Integer
#mean_compare TypeDeclarationExamples.Boolean
#mean_compare TypeDeclarationExamples.Map
#mean_compare TypeDeclarationExamples.Coordinate
#mean_compare TypeDeclarationExamples.Trivial
#mean_compare TypeDeclarationExamples.Instance
#mean_compare TypeDeclarationExamples.Universe
#mean_compare TypeDeclarationExamples.ViaUniverse
#mean_compare TypeDeclarationExamples.NamedArrow
#mean_compare TypeDeclarationExamples.ImplicitArrow
#mean_compare TypeDeclarationExamples.Position
#mean_compare TypeDeclarationExamples.Route
/--
info: Abbreviation:
  a TypeDeclarationExamples.Prototile is
    a list of TypeDeclarationExamples.Point elements.
-/
#guard_msgs in
#mean TypeDeclarationExamples.Prototile
/--
info: Definition:
  a TypeDeclarationExamples.Index is
    an index in [0, 4).
-/
#guard_msgs in
#mean TypeDeclarationExamples.Index

-- Check the elaborated declaration, including its kind, type, value, and names.
open Lean Elab Term in
run_elab do
  for (name, text, reason) in [
      (``TypeDeclarationExamples.Prototile,
        "Definition: a changed is a list of TypeDeclarationExamples.Point elements.",
        "Mean round-trip changed the declaration's abbreviation status"),
      (``TypeDeclarationExamples.PrototileDef,
        "Abbreviation: a changed is a list of TypeDeclarationExamples.Point elements.",
        "Mean round-trip changed the declaration's abbreviation status"),
      (``TypeDeclarationExamples.Direction,
        "Abbreviation: a changed is an index in [0, 5).",
        "Mean round-trip check failed: rendered text changed the expression"),
      (``TypeDeclarationExamples.NamedArrow,
        "Abbreviation: a changed is a function from Nat to Nat.",
        "Mean round-trip changed a named parameter"),
      (``TypeDeclarationExamples.ImplicitArrow,
        "Abbreviation: a changed is an element of ((n : Nat) → Fin n).",
        "Mean round-trip changed function argument implicitness")] do
    let message ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure "accepted"
      catch ex => ex.toMessageData.toString
    unless message == reason do
      throwError "expected type-declaration rejection '{reason}', got: {message}"
  for text in [
      "Abbreviation: a changed is a list xs of natural numbers.",
      "Abbreviation: a changed is an element of (7 : Nat)."] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition ``ListTypeExamples.Naturals text
        pure false
      catch _ => pure true
    unless rejected do throwError "accepted an invalid type description"

#mean_compare ListTypeExamples.Naturals
/-- info: the type of lists of natural numbers -/
#guard_msgs in
#mean_term List Nat
/-- info: the type of lists of TypeNounExamples.Token elements -/
#guard_msgs in
#mean_term List TypeNounExamples.Token
/-- info: the type of lists of (ℕ → ℕ) elements -/
#guard_msgs in
#mean_term List (Nat → Nat)
#mean_term_compare List TypeNounExamples.Token
section
variable (A : Type u) (n : Nat)
#mean_term_compare List A
#mean_term_compare List (List A)
#mean_term_compare List (Fin n)
#mean_term_compare List (List Nat)
#mean_term_compare List (Nat → Nat)
#mean_term_compare List Nat → Nat
#mean_term_compare Nat × List Int
#mean_term_compare fun (f : List Nat → Nat) => f []
end

open Lean Elab Term in
run_elab do
  for text in ["a list of natural numbers", "an index in [0, 3)",
      "lists of natural numbers", "indices in [0, 3)"] do
    match Parser.runParserCategory (← getEnv) `term text with
    | .ok _ => throwError "context-only noun phrase parsed as a type expression: {text}"
    | .error _ => pure ()
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkDefinition ``ListTypeExamples.Naturals
        "Abbreviation: changed is the type of lists of integers."
      pure false
    catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed list element type"

#mean_compare IndexExamples.Four
#mean_compare IndexExamples.value
#mean_compare IndexExamples.lookup
#mean_compare IndexExamples.arrayLookup
#mean_compare IndexExamples.implicitValue
#mean_compare IndexExamples.strictValue
#mean_compare IndexExamples.first
/--
info: the function mapping a list xs of natural numbers and an index i into xs to
  xs[i]
-/
#guard_msgs in
#mean_term fun (xs : List Nat) (i : Fin xs.length) => xs[i]
section
variable (n m : Nat) (xs : List Nat) (ys : Array Nat)
#mean_term_compare Fin n
#mean_term_compare Fin (n + m)
#mean_term_compare Fin 0
#mean_term_compare Fin 1
#mean_term_compare Fin 4
#mean_term_compare fun (i : Fin n) => i.val
#mean_term_compare fun {i : Fin n} => i.val
#mean_term_compare fun ⦃i : Fin n⦄ => i.val
#mean_term_compare fun (i : Fin (n + m)) => i.val
#mean_term_compare fun (i : Fin xs.length) => xs[i]
#mean_term_compare fun {i : Fin xs.length} => xs[i]
#mean_term_compare fun ⦃i : Fin ys.size⦄ => ys[i]
#mean_term_compare fun (i : Fin (xs ++ xs).length) => i.val
#mean_term_compare fun (_i : IndexExamples.Four) => true
#mean_term_compare ∀ i : Fin n, i.val < n
#mean_term_compare ∀ i : Fin xs.length, xs[i] = xs[i]
#mean_term_compare ∃ i : Fin ys.size, ys[i] = 3
#mean_term_compare ∃ _i : Fin n, True
#mean_term_compare ¬ ∃ _i : Fin 0, True
#mean_term_compare ∀ i j : Fin n, i = j ∨ i ≠ j
#mean_term_compare fun (xs : List (Fin n)) => xs
end
#mean_term_compare fun (xs : List Rat) => xs
#mean_term_compare fun {xs : List Real} => xs
#mean_term_compare fun ⦃xs : List Complex⦄ => xs
#mean_term_compare ∃ _xs : List Bool, True

-- Reject changed index bounds, collection types, and scalar element types.
open Lean Elab Term in
run_elab do
  for text in ["indices [1, 4)", "indexIntoType% (3 : Nat)"] do
    let rejected ← withoutModifyingState do
      try
        let .ok stx := Parser.runParserCategory (← getEnv) `term text
          | throwError "unparseable test input"
        let _ ← withoutErrToSorry <| elabTerm stx none
        pure false
      catch _ => pure true
    unless rejected do throwError "accepted invalid index description: {text}"
  for (name, text) in [
      (``IndexExamples.value,
        "Definition: changed is the function mapping a natural number n and an index i in [0, n + 1) to i.val."),
      (``IndexExamples.lookup,
        "Definition: changed is the function mapping a list xs of natural numbers and an index i into xs.reverse to xs.reverse[i]."),
      (``IndexExamples.lookup,
        "Definition: changed is the function mapping a list xs of integers and an index i into xs to xs[i].")] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure false
      catch _ => pure true
    unless rejected do throwError "accepted a changed index/list definition"

-- Function values render independently of named definitions.
#mean_compare ValueExamples.double

/--
info: Definition:
  ValueExamples.double is
    the function mapping a natural number n to
      2 * n.
-/
#guard_msgs in
#mean ValueExamples.double

#mean_compare ValueExamples.answer

/--
info: Definition:
  ValueExamples.answer is
    the integer 42.
-/
#guard_msgs in
#mean ValueExamples.answer

#mean_compare ValueExamples.naturalAnswer
#mean_compare ValueExamples.negativeAnswer
#mean_compare ValueExamples.rationalAnswer
#mean_compare ValueExamples.realAnswer
#mean_compare ValueExamples.complexAnswer
#mean_compare ValueExamples.booleanAnswer
#mean_compare ValueExamples.decimalAnswer
#mean_compare ValueExamples.negativeDecimalAnswer
#mean_compare ValueExamples.exponentAnswer
#mean_compare ValueExamples.underscoreAnswer
#mean_compare ValueExamples.hexAnswer
#mean_compare ValueExamples.computedAnswer
#mean_compare ValueExamples.add
#mean_compare ValueExamples.integerDouble
#mean_compare ValueExamples.rationalDouble
#mean_compare ValueExamples.realDouble
#mean_compare ValueExamples.complexDouble
#mean_compare ValueExamples.booleanIdentity
#mean_compare ValueExamples.indexValue
#mean_compare ValueExamples.zeroInteger

/--
info: Definition:
  ValueExamples.zeroInteger is
    the function : ℕ → ℤ mapping a natural number _n to
      (0).
-/
#guard_msgs in
#mean ValueExamples.zeroInteger

#mean_compare ValueExamples.identityOnT
#mean_compare ValueExamples.shifted

/--
info: Definition:
  ValueExamples.shifted is
    the function mapping a natural number offset and a natural number n to
      n + offset.
-/
#guard_msgs in
#mean ValueExamples.shifted

#mean_compare ValueExamples.mixedSum
#mean_compare ValueExamples.sumThree
#mean_compare ValueExamples.constantInteger
#mean_compare ValueExamples.implicitAdd
#mean_compare ValueExamples.implicitIndex
#mean_compare ValueExamples.implicitIntegerNext
#mean_compare ValueExamples.implicitConstant
#mean_compare ValueExamples.implicitIdentityOnT
#mean_compare ValueExamples.strictIndex
#mean_compare ValueExamples.strictConstant
#mean_compare ValueExamples.strictAdd
#mean_compare ValueExamples.strictIdentity
#mean_compare ProofExamples.identity
#mean_compare ProofExamples.implicitIdentity
#mean_compare ProofExamples.strictIdentity
#mean_compare ProofExamples.reflexive
#mean_compare ProofExamples.zero
#mean_compare AbbreviationExamples.Natural
#mean_compare AbbreviationExamples.answer
#mean_compare AbbreviationExamples.zero
#mean_compare AbbreviationExamples.double
#mean_compare AbbreviationExamples.zeroInteger
#mean_compare AbbreviationExamples.pathLinked
#mean_compare AbbreviationExamples.inhabitedValue
/--
info: Abbreviation:
  AbbreviationExamples.answer is
    the integer 42.
-/
#guard_msgs in
#mean AbbreviationExamples.answer
#mean_compare ValueExamples.graphEdges
#mean_compare TypeNounExamples.indexReflexive
#mean_compare TypeNounExamples.emptyList
#mean_compare TypeNounExamples.copyList
#mean_compare TypeNounExamples.polymorphicCopy
#mean_compare TypeNounExamples.implicitLength
#mean_compare TypeNounExamples.strictLength
#mean_compare TypeNounExamples.diagonal
#mean_compare TypeNounExamples.diagonalZero
#mean_compare TypeNounExamples.implicitApply
#mean_compare TypeNounExamples.strictApply
#mean_compare BinderExamples.anonymousNatural
#mean_compare BinderExamples.constantPredicate
#mean_compare BinderExamples.constantGraph
#mean_compare BinderExamples.inhabitedCarrier
#mean_compare BinderExamples.defaultValue
#mean_compare BinderExamples.chosenValue
#mean_compare BinderExamples.namedUnused
#mean_compare BinderExamples.namedImplicit
#mean_compare BinderExamples.namedStrict
#mean_compare BinderExamples.differentNames
#mean_compare BinderExamples.aliasWithName
#mean_compare BinderExamples.namedCallback
/--
info: Definition:
  BinderExamples.namedUnused is
    the function mapping a natural number n to
      true.
-/
#guard_msgs in
#mean BinderExamples.namedUnused
/--
info: Definition:
  BinderExamples.differentNames is
    the function mapping a natural number input to
      input.
-/
#guard_msgs in
#mean BinderExamples.differentNames
/--
info: the function mapping an instance of typeclass Inhabited ℕ to
  true
-/
#guard_msgs in
#mean_term fun [Inhabited Nat] => true
/--
info: the function mapping an instance of typeclass Fact True to
  true
-/
#guard_msgs in
#mean_term fun [Fact True] => true
#mean_term_compare fun (_ : Nat) => true
#mean_term_compare fun (_n : Nat) => true
#mean_term_compare fun [Inhabited Nat] => true
#mean_term_compare fun [inst : Inhabited Nat] => let _ := inst; true
#mean_term_compare fun [Fact True] => true
#mean_term_compare ∃ _inst : Inhabited Nat, True
#mean_term_compare ∃ inst : Inhabited Nat, inst.default = 7
#mean_term_compare ¬ ∃ _inst : Inhabited Nat, True
#mean_term_compare fun [Inhabited Nat] =>
  let first := inferInstanceAs (Inhabited Nat)
  fun [Inhabited Nat] => @default Nat first

-- Declaration checks preserve named arguments as well as types and values.
open Lean Elab Term in
run_elab do
  for (name, text, reason) in [
      (``BinderExamples.namedUnused,
        "Definition: changed is the function mapping a natural number to true.",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.namedUnused,
        "Definition: changed is the function mapping a natural number m to true.",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.namedImplicit,
        "Definition: changed is the function mapping an implicit natural number and a natural number n to n.",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.namedStrict,
        "Definition: changed is the function mapping a strictly implicit natural number and a natural number n to n.",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.differentNames,
        "Definition: changed is the function mapping a natural number n to n.",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.chosenValue,
        "Definition: changed is the function mapping an implicit element A of Type u and an instance of typeclass Inhabited A to (default : A).",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.chosenValue,
        "Definition: changed is the function mapping an implicit element A of Type u and an element inst of Inhabited A to @default A inst.",
        "Mean round-trip changed function argument implicitness"),
      (``BinderExamples.namedCallback,
        "Definition: changed is the function mapping a function f from Nat to Nat to f (0).",
        "Mean round-trip changed a named parameter"),
      (``BinderExamples.namedUnused,
        "Definition: changed is the function mapping an instance of typeclass Nat to true.",
        "expected a typeclass application")] do
    let message ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure "accepted"
      catch ex => ex.toMessageData.toString
    unless message == reason do
      throwError "expected binder rejection '{reason}', got: {message}"
/--
info: Definition:
  an index i in [0, 3) is TypeNounExamples.indexReflexive if
    i = i.
-/
#guard_msgs in
#mean TypeNounExamples.indexReflexive
/--
info: Definition:
  a list xs of TypeNounExamples.Token elements is TypeNounExamples.emptyList if
    xs = [].
-/
#guard_msgs in
#mean TypeNounExamples.emptyList
/--
info: the function mapping a function f from ℕ and ℕ to ℕ and a natural number n to
  f n n
-/
#guard_msgs in
#mean_term fun (f : Nat → Nat → Nat) (n : Nat) => f n n
#mean_term_compare fun (xs : List Nat) (i : Fin xs.length) => xs[i]
#mean_term_compare fun (fs : List (Nat → Nat)) => fs.length
#mean_term_compare fun (f : Nat × Nat → Nat) => f (0, 0)
#mean_term_compare fun (f : (Nat → Nat) → Nat) => f Nat.succ
#mean_term_compare fun (_f : (n : Nat) → Fin n) => true
#mean_term_compare fun (_f : {n : Nat} → Fin n) => true
#mean_term_compare fun (f : TypeNounExamples.Endomap) => f
section
universe u
#mean_term_compare fun {A : Type u} (f : A → A) => f
end
#mean_term_compare ∃ xs : List TypeNounExamples.Token, xs = []
#mean_term_compare ∃ _xs : List TypeNounExamples.Token, True
#mean_term_compare ¬ ∃ xs : List TypeNounExamples.Token, xs = []
#mean_term_compare ¬ ∃ _xs : List TypeNounExamples.Token, True
#mean_term_compare ∃ f : Int → Int → TypeNounExamples.Token, f = f
#mean_term_compare ∃ _f : Nat → Nat, True
#mean_term_compare ¬ ∃ f : Nat → Nat, f 0 = 0
#mean_term_compare ¬ ∃ _f : Nat → Nat, True

-- Universal noun phrases recurse into dependent domains and logical structure.
/--
info: for every function q from ℕ to Prop where 0 is q:
  there is a function r from ℕ to ℕ such that
    for every natural number n:
      n is q if and only if (r n) is q
-/
#guard_msgs in
#mean_term ∀ q : Nat → Prop, q 0 → ∃ r : Nat → Nat, ∀ n : Nat, q n ↔ q (r n)
#mean_term_compare ∀ q : Nat → Prop, q 0 → ∃ r : Nat → Nat, ∀ n : Nat, q n ↔ q (r n)
#mean_term_compare ∀ f : Nat → Nat → Nat, f 0 0 = 0
#mean_term_compare ∀ xs : List Nat, ∀ i : Fin xs.length, xs[i] = xs[i]
#mean_term_compare ∀ f : (n : Nat) → Fin n, f 1 = f 1
#mean_term_compare ∀ f : {n : Nat} → Fin n, f (n := 1) = f (n := 1)
#mean_term_compare ∀ x : TypeNounExamples.Token, x = x
#mean_term_compare ∀ f : TypeNounExamples.Endomap, f = f
#mean_term_compare ∀ inst : Inhabited Nat, inst.default = 0
#mean_term_compare ∀ P : Prop, P ↔ P
section
variable {V : Type*} (G : SimpleGraph V) (u v : V)
#mean_term_compare ∀ p : G.Path u v, p = p
end
section
variable {A : Sort u} (P Q R : Prop)
#mean_term_compare ∀ x : A, x = x
#mean_term_compare ∀ h : P, h = h
#mean_term_compare P ↔ Q
#mean_term_compare (P ↔ Q) ↔ R
#mean_term_compare P ↔ (Q ↔ R)
#mean_term_compare (P ↔ Q) ∧ R
#mean_term_compare P ∧ (Q ↔ R)
#mean_term_compare (P ↔ Q) ∨ R
#mean_term_compare P ∨ (Q ↔ R)
#mean_term_compare P ∧ Q ↔ R
#mean_term_compare P ↔ Q ∨ R
#mean_term_compare (P → Q) ↔ R
#mean_term_compare P ↔ (Q → R)
#mean_term_compare P → (Q ↔ R)
#mean_term_compare (P ↔ Q) → R
#mean_term_compare P → (let S := Q; S ↔ R)
#mean_term_compare (let S := P; S ↔ Q) ∧ R
#mean_term_compare (∀ x : A, x = x) ↔ P
#mean_term_compare P ↔ (∃ x : A, x = x)
end

-- Noun phrases preserve element types, currying, and parameter implicitness.
open Lean Elab Term in
run_elab do
  for (name, text, reason) in [
      (``TypeNounExamples.emptyList,
        "Definition: a list xs of Int elements is changed if xs = [].",
        "Mean round-trip check failed: rendered text changed the expression"),
      (``TypeNounExamples.diagonal,
        "Definition: changed is the function mapping a function f from (Nat × Nat) to Nat and a natural number n to f (n, n).",
        "Mean round-trip check failed: rendered text changed the expression"),
      (``TypeNounExamples.diagonal,
        "Definition: changed is the function mapping an implicit function f from Nat and Nat to Nat and a natural number n to f n n.",
        "Mean round-trip changed function argument implicitness")] do
    let message ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinition name text
        pure "accepted"
      catch ex => ex.toMessageData.toString
    unless message == reason do
      throwError "expected noun-phrase rejection '{reason}', got: {message}"

#mean_term_compare fun n : Nat => 2 * n
#mean_term_compare fun n : Nat => fun i : Fin n => i.val
#mean_term_compare fun «a» : Nat => fun «graph» : Nat => «a» + «graph»
#mean_term_compare fun _n : Nat => fun _n : Nat => _n
-- Ordinary implicit binders join the function phrase without changing inference.
#mean_term_compare fun n : Nat => fun {m : Nat} => n + m
/--
info: the function mapping a natural number n and an implicit natural number m to
  n + m
-/
#guard_msgs in
#mean_term fun (n : Nat) {m : Nat} => n + m
#mean_term_compare fun {n : Nat} (i : Fin n) => i.val
#mean_term_compare fun {n : Nat} (m : Nat) {k : Nat} => n + m + k
-- Strict implicit subjects preserve delayed inference, including trailing binders.
#mean_term_compare fun n : Nat => fun ⦃m : Nat⦄ => n + m
/--
info: the function mapping a strictly implicit natural number n and an index i in [0, n) to
  i as a natural number
-/
#guard_msgs in
#mean_term fun ⦃n : Nat⦄ (i : Fin n) => i.val
#mean_term_compare fun ⦃n : Nat⦄ (m : Nat) {k : Nat} => n + m + k
-- Instance parameters use typeclass search and preserve explicitly supplied names.
#mean_term_compare fun (n : Nat) [inst : Inhabited Nat] => n + @default Nat inst
#mean_term_compare fun _n : Nat => (0 : Int)
section
variable {T : Sort u}
#mean_term_compare fun x : T => x
#mean_term_compare fun (_x : T) (y : T) => y
#mean_term_compare fun {_x : T} (y : T) => y
#mean_term_compare fun ⦃_x : T⦄ (y : T) => y
#mean_term_compare fun (h : True and True) (_b : Bool) => h
end

/--
info: the function mapping a natural number n and a proof h that n > 0 to
  h
-/
#guard_msgs in
#mean_term fun (n : Nat) (h : n > 0) => h

section
variable (P Q : Prop) (n : Nat)
#mean_term_compare fun (h : P ∧ Q) => h
#mean_term_compare fun (h : P) ⦃_eq : h = h⦄ => h
#mean_term_compare ∃ _h : P, True
#mean_term_compare ∃ h : P, h = h
#mean_term_compare ¬ ∃ _h : P, True
#mean_term_compare ¬ ∃ h : P, h = h
#mean_term_compare ∃ _h : P, False
#mean_term_compare ∃ _h : P ∧ Q, True
#mean_term_compare ∃ h : n > 0, h = h
#mean_term_compare (∃ _h : P, True) ∧ Q
#mean_term_compare (¬ ∃ _h : P, True) → Q
end

-- The type Prop contains propositions, rather than proofs of one proposition.
#mean_term_compare fun (P : Prop) => P

open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``ValueExamples.double).value!
  let rejected ← try
    Mean.RoundTrip.checkDefinitionValue original
      "Definition: changed is the function mapping a natural number n to 3 * n."
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted a changed function definition"

open Lean Elab Term in
run_elab do
  -- An unannotated numeral must not inherit its type from the original definition.
  for (name, text) in [
      (``ValueExamples.answer, "Definition: changed is (42)."),
      (``ValueExamples.answer, "Definition: changed is the natural number 42."),
      (``ValueExamples.answer, "Definition: changed is the integer true."),
      (``ValueExamples.zeroInteger,
        "Definition: changed is the function mapping a natural number _n to (0)."),
      (``ValueExamples.zeroInteger,
        "Definition: changed is the function : Int → Int mapping a natural number _n to (0).") ] do
    let original := (← getConstInfo name).value!
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinitionValue original text
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted a changed inferred type"

open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``ValueExamples.implicitAdd).value!
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkDefinitionValue original
        "Definition: changed is the function mapping a natural number n and a natural number m to n + m."
      pure false
    catch _ => pure true
  unless rejected do throwError "round-trip checker accepted erased argument implicitness"

open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``ValueExamples.double).value!
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkDefinitionValue original
        "Definition: changed is the function mapping a proof n that Nat to 2 * n."
      pure false
    catch _ => pure true
  unless rejected do throwError "proof parameter accepted a non-proposition"
  let original ← elabTerm (← `(∃ n : Nat, n = 0)) none
  let rejected ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText original
        "there is a proof n that Nat such that n = 0"
      pure false
    catch _ => pure true
  unless rejected do throwError "proof witness accepted a non-proposition"

open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``ValueExamples.strictIndex).value!
  -- Definitional equality alone cannot distinguish these calling conventions.
  for modifier in ["an implicit", "a"] do
    let rejected ← withoutModifyingState do
      try
        Mean.RoundTrip.checkDefinitionValue original
          s!"Definition: changed is the function mapping {modifier} natural number n and an element i of Fin n to i.val."
        pure false
      catch _ => pure true
    unless rejected do throwError "round-trip checker accepted changed strict implicitness"

section
@[irreducible] private def auditIrreducible : Int := 42
private def auditFunction := Nat.succ

-- Deliberately give a command an honest-looking label but the wrong expansion.
local syntax "auditMisleadingAbbreviation" : term
local macro_rules
  | `(auditMisleadingAbbreviation) => `((42 : Int))
local macro_rules
  | `(command| Abbreviation: $name:ident is auditMisleadingAbbreviation .) =>
      `(command| def $name := (42 : Int))

open Lean Elab Term in
run_elab do
  let constantsBefore := (← getEnv).constants.toList.length
  -- This passes the expression-only check, so rejection must inspect the declaration.
  let original := (← getConstInfo ``AbbreviationExamples.answer).value!
  Mean.RoundTrip.checkDefinitionValue original
    "Abbreviation: changed is auditMisleadingAbbreviation." true
  for (name, text, reason) in [
      (``AbbreviationExamples.answer, "Definition: changed is the integer 42.", "abbreviation status"),
      (``ValueExamples.answer, "Abbreviation: changed is the integer 42.", "abbreviation status"),
      (``AbbreviationExamples.answer, "Abbreviation: changed is auditMisleadingAbbreviation.",
        "abbreviation status"),
      (``auditIrreducible, "Definition: changed is the integer 42.", "reducibility")] do
    let message ← try
      Mean.RoundTrip.checkDefinition name text
      pure "accepted"
    catch ex => ex.toMessageData.toString
    unless message == s!"Mean round-trip changed the declaration's {reason}" do
      throwError "expected rejection for {reason}, got: {message}"
  -- A constant and its eta-expanded lambda are definitionally equal, even if
  -- implicitness changes. Compare the declaration's type as well as its value.
  let changedFunction :=
    "Definition: changed is the function mapping an implicit natural number n to Nat.succ n."
  Mean.RoundTrip.checkDefinitionValue (← getConstInfo ``auditFunction).value! changedFunction
  let message ← try
    Mean.RoundTrip.checkDefinition ``auditFunction changedFunction
    pure "accepted"
  catch ex => ex.toMessageData.toString
  unless message == "Mean round-trip changed function argument implicitness" do
    throwError "expected rejection for changed function implicitness, got: {message}"
  Mean.RoundTrip.checkDefinition ``AbbreviationExamples.answer
    "Abbreviation: changed is the integer 42."
  -- The checker supplies the original universes without relying on renderer state.
  Mean.RoundTrip.checkDefinition ``ValueExamples.identityOnT
    "Definition: changed is the function mapping an implicit element T of Sort u and an element x of T to x."
  unless (← getEnv).constants.toList.length == constantsBefore do
    throwError "declaration round trip leaked temporary declarations"
end

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

-- An actual axiom must remain distinct from an imported theorem without its proof.
axiom ordinaryAxiom : True
/--
info: -- Statement of ordinaryAxiom
True
-/
#guard_msgs in
#mean ordinaryAxiom

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
  a simple graph G = (V, E) is ordinaryPreconnected if
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

set_option linter.checkUnivs false in
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

-- Additional explicit parameters and hypotheses share a predicate subject list.
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

open Lean Elab Term in
run_elab do
  let original ← elabTerm (← `(True ↔ False)) none
  let rejected ← try
    Mean.RoundTrip.checkText original "if True then False"
    pure false
  catch _ => pure true
  unless rejected do throwError "round-trip checker accepted implication for equivalence"

-- Reject turning a fixed Type 0 graph parameter into a universe-polymorphic one.
open Lean Elab Term in
run_elab do
  let original := (← getConstInfo ``smallGraph).value!
  let rejected ← try
    Mean.RoundTrip.checkDefinitionValue original
      "Definition: a simple graph G is smallGraph if for all vertices x and y of G: there is a path in G from x to y."
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
variable (n : Nat) (p : Nat → Prop) (f : Nat → Nat) (P Q : Prop) (r : Prop → Prop)
/-- info: n is p -/
#guard_msgs in
#mean_term p n
/-- info: n is not p -/
#guard_msgs in
#mean_term ¬ p n
/--
info: (the function mapping a natural number k to
  k is not p) is recursively enumerable
-/
#guard_msgs in
#mean_term REPred (fun k : Nat => ¬ p k)
#mean_term_compare PredicateExamples.FooPred n
#mean_term_compare ¬ PredicateExamples.FooPred n
#mean_term_compare PredicateExamples.accepts n
#mean_term_compare PredicateExamples.BoolPred n
#mean_term_compare PredicateExamples.relates n 0
#mean_term_compare p n
#mean_term_compare ¬ p n
#mean_term_compare ¬ ¬ p n
#mean_term_compare p n ∧ ¬ p (n + 1)
#mean_term_compare (p n ↔ ¬ p n) → p n
#mean_term_compare r (P ∧ Q)
#mean_term_compare ¬ r (P ↔ Q)
#mean_term_compare ¬ (P ∧ Q)
#mean_term_compare REPred p
#mean_term_compare ¬ REPred p
#mean_term_compare Computable f
#mean_term_compare ¬ Computable f
#mean_term_compare ComputablePred p
#mean_term_compare ¬ ComputablePred p
#mean_term_compare REPred (fun n : Nat => ¬ p n)
#mean_term_compare ComputablePred (fun n : Nat => ¬ p n)
#mean_term_compare Computable (fun n : Nat => n + 1)
#mean_term_compare Function.Injective (fun n : Nat => n + 1)
#mean_term_compare ¬ Function.Injective (fun n : Nat => n + 1)
#mean_term_compare ¬ Finite Nat
end
section
variable {A : Sort u} (p : A → Prop) (x : A)
#mean_term_compare p x
#mean_term_compare ¬ p x
#mean_term_compare PredicateExamples.accepts x
end
#mean_term_compare fun [Inhabited Nat] =>
  let first := inferInstanceAs (Inhabited Nat)
  fun [Inhabited Nat] => @PredicateExamples.classified first 7
#mean_term_compare fun [Primcodable Nat] =>
  let first := inferInstanceAs (Primcodable Nat)
  fun [Primcodable Nat] (p : Nat → Prop) => ¬ @REPred Nat first p

-- Generic adjective syntax refuses Boolean-valued functions, and the checker
-- rejects changed predicate polarity.
open Lean Elab Term in
run_elab do
  let invalid ← withoutModifyingState do
    try
      let _ ← withoutErrToSorry <| elabTerm (← `(7 is PredicateExamples.BoolPred)) none
      synthesizeSyntheticMVarsNoPostponing
      pure false
    catch _ => pure true
  unless invalid do throwError "accepted a Boolean function as a predicate"
  let original ← elabTerm (← `(PredicateExamples.FooPred 7)) none
  let changed ← withoutModifyingState do
    try
      Mean.RoundTrip.checkText original "7 is not PredicateExamples.FooPred"
      pure false
    catch _ => pure true
  unless changed do throwError "round-trip checker accepted changed predicate polarity"

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
