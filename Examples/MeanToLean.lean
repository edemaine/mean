import Mean.Syntax
import Mathlib.MeasureTheory.Measure.Module

namespace AlmostEveryExamples

open MeasureTheory

section
variable (A : Type u) [MeasurableSpace A] (μ ν : Measure A) (p q : A → Prop)
example : (for almost every element x of A with respect to μ: p x) =
    (∀ᵐ x ∂μ, p x) := rfl
example : (for almost every element x of A with respect to μ where p x: q x) =
    (∀ᵐ x ∂μ, p x → q x) := rfl
example : (for almost every element x of A with respect to μ:
    for almost every element y of A with respect to ν: p x ∧ q y) =
    (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x ∧ q y) := rfl
example (existentialWitness : A) :
    (for almost every element of A with respect to μ: p existentialWitness) =
    (∀ᵐ _x ∂μ, p existentialWitness) := rfl
example : (for almost every element x of A with respect to (μ + ν): p x) =
    (∀ᵐ x ∂(μ + ν), p x) := rfl
end

section
variable (A : Type u) [MeasureSpace A] (p : A → Prop)
example : (for almost every element x of A: p x) = (∀ᵐ x, p x) := rfl
example : (for almost every element x of A where p x: x = x) =
    (∀ᵐ x, p x → x = x) := rfl
example : (for almost every element x of A: there is a unique element y of A such that y = x) =
    (∀ᵐ x, ∃! y : A, y = x) := rfl
end

end AlmostEveryExamples

namespace ScalarCoercionExamples

example (z : Int) : (z as a real number) = (z : Real) := rfl
example (n : Nat) : (n as an integer) = (n : Int) := rfl
example (q : Rat) : (q as a real number) = (q : Real) := rfl
example (x : Real) : (x as a complex number) = (x : Complex) := rfl
example (i : Fin 3) : (i as a natural number) = i.val := rfl
example (z : Int) : ((z + 1) as a real number) = ((z + 1 : Int) : Real) := rfl
example (n m : Nat) : ((n - m) as an integer) = ((n - m : Nat) : Int) := rfl
example (z : Int) : (-z as a real number) = ((-z : Int) : Real) := rfl
example (n : Nat) : ((n as an integer) as a real number) = ((n : Int) : Real) := rfl
example (z : Int) : (z as a real number) + 1 = (z : Real) + 1 := rfl
example (z : Int) : (z as a real number) ≤ 1 ↔ (z : Real) ≤ 1 := Iff.rfl
example (p : Fin 3 → Int) (i : Fin 3) : (p i as a real number) = (p i : Real) := rfl
example (z : Int) : some (z as a real number) = some (z : Real) := rfl

end ScalarCoercionExamples

namespace SetComprehensionExamples

Definition: zeros is the set of elements n of Nat such that (n = 0).
example : zeros = {n : Nat | n = 0} := rfl
example (A : Type u) (p : A → Prop) :
    (the set of elements x of A such that p x) = {x : A | p x} := rfl
example : (the set of elements of Nat such that True) = (Set.univ : Set Nat) := rfl
example : (the set of elements of Nat such that False) = (∅ : Set Nat) := rfl
example (x : Nat) : ((the set of elements x of Nat such that x > 0), x) =
    ({n : Nat | n > 0}, x) := rfl
example (_anonymousParameter : Nat) :
    (the set of elements of Nat such that _anonymousParameter = 0) =
    {_n : Nat | _anonymousParameter = 0} := rfl
example : (the set of elements «a» of Nat such that «a» = 0) = {n : Nat | n = 0} := rfl
example : (the set of elements S of (the type of sets of natural numbers) such that 0 ∈ S) =
    {S : Set Nat | 0 ∈ S} := rfl
example : some (the set of elements n of Nat such that n > 0) = some {n : Nat | n > 0} := rfl
example (S : Set Nat) : (the set of elements n of Nat such that n > 0) ∪ S =
    {n : Nat | n > 0} ∪ S := rfl
example (n : Nat) : (n ∈ (the set of elements m of Nat such that m > 0)) =
    (n ∈ {m : Nat | m > 0}) := rfl
example : (the set of elements f of (Nat → Nat) such that f 0 = 0) =
    {f : Nat → Nat | f 0 = 0} := rfl

end SetComprehensionExamples

namespace SetPhraseExamples

abbrev Point := Fin 3 → Int
Abbreviation: a Family is a set of Point elements.
Definition: a set S of Point elements is reflexive if S = S.

example : Family = Set Point := rfl
example : reflexive = (fun S : Set Point => S = S) := rfl
example : (the type of sets of natural numbers) = Set Nat := rfl
example (A : Type u) : (the type of sets of A elements) = Set A := rfl
example : (the type of sets of (Nat → Bool) elements) = Set (Nat → Bool) := rfl
example : (the function mapping a set S of natural numbers to S) =
    (fun S : Set Nat => S) := rfl
example : (the function mapping an implicit set S of integers to S) =
    (fun {S : Set Int} => S) := rfl
example : (the function mapping a strictly implicit set S of booleans to S) =
    (fun ⦃S : Set Bool⦄ => S) := rfl
example : (for every set S of integers where 0 ∈ S: 0 ∈ S) =
    (∀ S : Set Int, 0 ∈ S → 0 ∈ S) := rfl
example : (there is a set T of Point elements such that T = ∅) =
    (∃ T : Set Point, T = ∅) := rfl
example : (there is no set of natural numbers) = (¬ ∃ _S : Set Nat, True) := rfl
example : (there is a unique set S of natural numbers such that S = ∅) =
    (∃! S : Set Nat, S = ∅) := rfl
example (existentialWitness : Set Nat) :
    (there is a set of natural numbers such that existentialWitness = ∅) =
    (∃ _S : Set Nat, existentialWitness = ∅) := rfl
example : (the function mapping a function f from sets of Point elements
    to sets of natural numbers to f) = (fun f : Set Point → Set Nat => f) := rfl
example : (the function mapping a function f from lists of Point elements and
    sets of Point elements to booleans to f) =
    (fun f : List Point → Set Point → Bool => f) := rfl

end SetPhraseExamples

namespace UniqueExistenceExamples

example (A : Type*) (p : A → Prop) :
    (there is a unique element x of A such that p x) =
    (there is exactly one element x of A such that p x) := rfl
example : (there is a unique integer n such that n = 0) = (∃! n : Int, n = 0) := rfl
example : (there is a unique index in [0, 1)) = (∃! _i : Fin 1, True) := rfl
example (existentialWitness : Nat) :
    (there is a unique natural number such that existentialWitness = 0) =
    (∃! _n : Nat, existentialWitness = 0) := rfl

example (A : Type*) (p : A → Prop) :
    (there is exactly one element x of A such that p x) = (∃! x : A, p x) := rfl
example : (there is exactly one natural number n such that n = 0) = (∃! n : Nat, n = 0) := rfl
example : (there is exactly one index in [0, 1)) = (∃! _i : Fin 1, True) := rfl
example : (there is exactly one natural number such that False) = (∃! _n : Nat, False) := rfl
example : (there is exactly one list xs of natural numbers such that xs = []) =
    (∃! xs : List Nat, xs = []) := rfl
example : (there is exactly one function f from Nat to Nat such that f 0 = 0) =
    (∃! f : Nat → Nat, f 0 = 0) := rfl
example (P : Prop) : (there is exactly one proof h that P such that h = h) =
    (∃! h : P, h = h) := rfl
example (existentialWitness : Nat) :
    (there is exactly one natural number such that existentialWitness = 0) =
    (∃! _n : Nat, existentialWitness = 0) := rfl

end UniqueExistenceExamples

namespace RestrictedQuantifierExamples

example (A : Type*) (P : Set A) :
    (for every element p of A where p ∈ P: p ∈ P) =
    (∀ p : A, p ∈ P → p ∈ P) := rfl
example : (for all natural numbers n and m where n ≤ m: n ≤ m) =
    (∀ n m : Nat, n ≤ m → n ≤ m) := rfl
example (xs : List Nat) : (for every index i into xs where xs[i] > 0: xs[i] ≥ 1) =
    (∀ i : Fin xs.length, xs[i] > 0 → xs[i] ≥ 1) := rfl
example : (for every function f from Nat to Nat where f 0 = 0: f 0 ≤ 1) =
    (∀ f : Nat → Nat, f 0 = 0 → f 0 ≤ 1) := rfl
example (P : Prop) : (for every proof h that P where h = h: h = h) =
    (∀ h : P, h = h → h = h) := rfl
example : (for every natural number n where (for every natural number m: n ≤ m): n = 0) =
    (∀ n : Nat, (∀ m : Nat, n ≤ m) → n = 0) := rfl
example : (for every natural number n where (there is a natural number m such that n = m): n = n) =
    (∀ n : Nat, (∃ m : Nat, n = m) → n = n) := rfl
example (P Q : Nat → Prop) :
    (for every natural number n where P n if and only if Q n: P n → Q n) =
    (∀ n : Nat, (P n ↔ Q n) → P n → Q n) := rfl
example (A : Type*) (P : Set A) :
    (for every element p of A where p ∈ P:
      for every element q of A where q ∈ P: p = q → q = p) =
    (∀ p : A, p ∈ P → ∀ q : A, q ∈ P → p = q → q = p) := rfl
example (n : Nat) : (for every natural number n where n > 0: n ≥ 1) =
    (∀ n : Nat, n > 0 → n ≥ 1) := rfl

end RestrictedQuantifierExamples

namespace SumExamples

example («a» b : Fin 3 → Int) :
    (the sum over indices i in [0, 3) of |«a» i - b i| = 1) =
    ((∑ i : Fin 3, |«a» i - b i|) = 1) := rfl
example (f : Fin 3 → Nat) :
    (the sum over indices i in [0, 3) of f i + 1) =
    (∑ i : Fin 3, (f i + 1)) := rfl
example (f : Fin 3 → Nat) :
    (the sum over indices i in [0, 3) of f i) + 1 =
    (∑ i : Fin 3, f i) + 1 := rfl
example (xs : List Nat) :
    (the sum over indices i into xs of xs[i]) = (∑ i : Fin xs.length, xs[i]) := rfl
example (xs : Array Nat) :
    (the sum over indices i into xs of xs[i]) = (∑ i : Fin xs.size, xs[i]) := rfl
example (α : Type*) [Fintype α] (f : α → Int) :
    (the sum over elements x of α of f x) = (∑ x : α, f x) := rfl
example (s : Finset Nat) :
    (the sum over i in s of i + 1) = (∑ i ∈ s, (i + 1)) := rfl
example (i : Nat) (f : Fin 3 → Nat) :
    (the sum over indices i in [0, 3) of f i) + i = (∑ i : Fin 3, f i) + i := rfl

end SumExamples

namespace IndexExamples

example (n : Nat) : indices [0, n) = Fin n := rfl
example : indices [0, 0) = Fin 0 := rfl
example : indices [0, 1) = Fin 1 := rfl
example (n m : Nat) : indices [0, n + m) = Fin (n + m) := rfl
example (n : Nat) : (the type of indices in [0, n)) = Fin n := rfl
example : (the type of indices in [0, 0)) = Fin 0 := rfl
example (xs : List Nat) : (the type of indices into xs) = Fin xs.length := rfl
example (xs : Array Nat) : (the type of indices into xs) = Fin xs.size := rfl

Abbreviation: Four is indices [0, 4).
Definition: value is the function mapping a natural number n and
  an index i in [0, n) to i.val.
Definition: lookup is the function mapping a list xs of natural numbers and
  an index i into xs to xs[i].
Definition: arrayLookup is the function mapping an element xs of Array Nat and
  an index i into xs to xs[i].
Definition: implicitValue is the function mapping a natural number n and
  an implicit index i in [0, n) to i.val.
Definition: strictValue is the function mapping a natural number n and
  a strictly implicit index i in [0, n) to i.val.
Definition: an index i in [0, 4) is first if (i.val = 0).

example : value = (fun (n : Nat) (i : Fin n) => i.val) := rfl
example : lookup = (fun (xs : List Nat) (i : Fin xs.length) => xs[i]) := rfl
example : arrayLookup = (fun (xs : Array Nat) (i : Fin xs.size) => xs[i]) := rfl
example (xs : List Nat) (i : Fin xs.length) : lookup (xs := xs) (i := i) = xs[i] := rfl
example : implicitValue = (fun (n : Nat) {i : Fin n} => i.val) := rfl
example : strictValue = (fun (n : Nat) ⦃i : Fin n⦄ => i.val) := rfl
example : (the function mapping an index in [0, 3) to true) =
    (fun (_ : Fin 3) => true) := rfl
example (xs : List Nat) : (the function mapping an index into xs to true) =
    (fun (_ : Fin xs.length) => true) := rfl
example (xs : List Nat) : (the function mapping an implicit index i into xs to i.val) =
    (fun {i : Fin xs.length} => i.val) := rfl
example (xs : Array Nat) : (the function mapping a strictly implicit index i into xs to i.val) =
    (fun ⦃i : Fin xs.size⦄ => i.val) := rfl
example (n : Nat) : (for every index i in [0, n): i.val < n) =
    (∀ i : Fin n, i.val < n) := rfl
example (xs : List Nat) : (for every index i into xs: xs[i] = xs[i]) =
    (∀ i : Fin xs.length, xs[i] = xs[i]) := rfl
example (xs : Array Nat) : (there is an index i into xs such that xs[i] = 3) =
    (∃ i : Fin xs.size, xs[i] = 3) := rfl
example (n : Nat) : (there is an index in [0, n)) = (∃ _i : Fin n, True) := rfl
example : (there is no index in [0, 0)) = (¬ ∃ _i : Fin 0, True) := rfl
example (xs : List Nat) (ys : List (Fin xs.length)) :
    (for every index i into xs: i ∈ ys) = (∀ i : Fin xs.length, i ∈ ys) := rfl

-- Natural scalar plurals preserve types; custom nouns retain the element form.
example : (the function mapping a list xs of natural numbers to xs) =
    (fun xs : List Nat => xs) := rfl
example : (the function mapping an implicit list xs of integers to xs) =
    (fun {xs : List Int} => xs) := rfl
example : (the function mapping a strictly implicit list xs of booleans to xs) =
    (fun ⦃xs : List Bool⦄ => xs) := rfl
example : (for every list xs of rational numbers: xs = xs) =
    (∀ xs : List Rat, xs = xs) := rfl
example : (there is a list of real numbers) = (∃ _xs : List Real, True) := rfl
example : (there is no list xs of complex numbers such that xs = []) =
    (¬ ∃ xs : List Complex, xs = []) := rfl

end IndexExamples

namespace ListTypeExamples

Abbreviation: Naturals is the type of lists of natural numbers.
example : Naturals = List Nat := rfl
example (A : Type u) : (the type of lists of A elements) = List A := rfl
example (A : Type u) :
    (the type of lists of (the type of lists of A elements) elements) = List (List A) := rfl
example : (the type of lists of (Nat → Nat) elements) = List (Nat → Nat) := rfl
example : (the type of lists of (the type of lists of natural numbers) elements) = List (List Nat) := rfl
example (n : Nat) : (the type of lists of (indices [0, n)) elements) = List (Fin n) := rfl
example : (the type of lists of natural numbers → Nat) = (List Nat → Nat) := rfl
example : (Nat × the type of lists of integers) = (Nat × List Int) := rfl
example : (the function mapping a function f from (the type of lists of natural numbers) to Nat to f []) =
    (fun f : List Nat → Nat => f []) := rfl
example : (the type of natural numbers) = Nat := rfl
example : (the type of integers) = Int := rfl
example : (the type of booleans) = Bool := rfl

end ListTypeExamples

namespace TypeDeclarationExamples

abbrev Point := Fin 3 → Int
Abbreviation: a Prototile is a list of Point elements.
Definition: a PrototileDef is a list of Point elements.
Abbreviation: a Direction is an index in [0, 4).
Definition: an Index is an index in [0, 4).
Abbreviation: an Integer is an integer.
Definition: a Boolean is a boolean.
Abbreviation: a Map is a function from Nat to Nat.
Abbreviation: a Coordinate is an element of (Fin 3).
Definition: a Trivial is a proof that True.
Abbreviation: an Instance is an instance of typeclass Inhabited Nat.
Abbreviation: a Universe is an element of Type.
def ViaUniverse : Universe := Nat
abbrev NamedArrow := (input : Nat) → Nat
abbrev ImplicitArrow := {n : Nat} → Fin n

example : Prototile = List Point := rfl
example : PrototileDef = List Point := rfl
example : Direction = Fin 4 := rfl
example : Index = Fin 4 := rfl
example : Integer = Int := rfl
example : Boolean = Bool := rfl
example : Map = (Nat → Nat) := rfl
example : Coordinate = Fin 3 := rfl
example : Trivial = True := rfl
example : Instance = Inhabited Nat := rfl
example : Universe = Type := rfl
example : ViaUniverse = Nat := rfl
example (f : NamedArrow) : f (input := 3) = f 3 := rfl

section
variable (xs : List Nat)
Abbreviation: a Position is an index into xs.
example : Position xs = Fin xs.length := rfl
end

section
variable {V : Type u} (G : SimpleGraph V) (u v : V)
Abbreviation: a Route is a path in G from u to v.
example : Route G u v = G.Path u v := rfl
end

end TypeDeclarationExamples

namespace FunctionEndpointExamples

Abbreviation: a Point is a function from indices in [0, 3) to ℤ.
Abbreviation: a Reindexer is a function from indices in [0, 3) to indices in [0, 4).
Definition: a Consumer is a function from lists of natural numbers to ℤ.
Abbreviation: a Curried is a function from natural numbers and indices in [0, 3) to integers.

example : Point = (Fin 3 → Int) := rfl
example : Reindexer = (Fin 3 → Fin 4) := rfl
example : Consumer = (List Nat → Int) := rfl
example : Curried = (Nat → Fin 3 → Int) := rfl
example : (the function mapping a function f from natural numbers to integers to f) =
    (fun f : Nat → Int => f) := rfl
example : (the function mapping a function f from indices in [0, 3) to lists of natural numbers and
    a boolean b to (f 0, b)) = (fun (f : Fin 3 → List Nat) (b : Bool) => (f 0, b)) := rfl
example : (the function mapping a function f from lists of (Nat → Nat) elements to ℕ to f) =
    (fun f : List (Nat → Nat) → Nat => f) := rfl
example : (the function mapping a function f from (Nat → Nat) to indices in [0, 3) to f) =
    (fun f : (Nat → Nat) → Fin 3 => f) := rfl
example (xs : List Nat) : (the function mapping a function f from indices into xs to ℤ to f) =
    (fun f : Fin xs.length → Int => f) := rfl
example (xs : Array Nat) : (the function mapping a function f from ℕ to indices into xs to f) =
    (fun f : Nat → Fin xs.size => f) := rfl
example (A : Type u) : (the function mapping a function f from lists of A elements to Prop to f) =
    (fun f : List A → Prop => f) := rfl
example : (the function mapping a function f from (the type of indices in [0, 3)) to ℤ to f) =
    (fun f : Fin 3 → Int => f) := rfl

end FunctionEndpointExamples

namespace PredicateExamples

abbrev Point := Fin 3 → Int
Definition: elements «a» and b of Point are adjacent if
  (the sum over indices i in [0, 3) of |«a» i - b i| = 1).
Definition: natural numbers x and y and z are ordered if x ≤ y ∧ y ≤ z.
Abbreviation: integers x and y are equalIntegers if x = y.
Definition: indices i and j in [0, 3) are sameIndex if i = j.
Definition: a natural number n and an index i in [0, n) are below if i.val < n.
Definition: an element T of Type and an element x of T are reflexivePair if x = x.
Definition: a natural number n and a proof h that n > 0 are positivePair if n ≥ 1 ∧ h = h.
Definition: a natural number x and a natural number y are ignoresSecond if x = x.
Definition: a function f from ℕ and ℕ to ℕ and a boolean b are mixed if f 0 0 = 0 ∧ b = true.

example : adjacent = (fun («a» b : Point) => (∑ i : Fin 3, |«a» i - b i|) = 1) := rfl
example : ordered = (fun x y z : Nat => x ≤ y ∧ y ≤ z) := rfl
example : equalIntegers = (fun x y : Int => x = y) := rfl
example : sameIndex = (fun i j : Fin 3 => i = j) := rfl
example : below = (fun (n : Nat) (i : Fin n) => i.val < n) := rfl
example : reflexivePair = (fun (T : Type) (x : T) => x = x) := rfl
example : positivePair = (fun (n : Nat) (h : n > 0) => n ≥ 1 ∧ h = h) := rfl
example : ignoresSecond (x := 0) (y := 5) := rfl
example : mixed = (fun (f : Nat → Nat → Nat) (b : Bool) => f 0 0 = 0 ∧ b = true) := rfl

-- A grouped type is elaborated before any of its names shadow the context.
section
variable (T : Type)
Definition: elements T and x of T are shadowType if T = x.
example : shadowType T = (fun x y : T => x = y) := rfl
end

-- Predicate types, not spelling conventions, determine generic `is` wording.
def FooPred (n : Nat) : Prop := n = 0
def accepts {A : Sort u} (x : A) : Prop := x = x
def BoolPred (n : Nat) : Bool := n == 0
def relates (n m : Nat) : Prop := n = m
def classified [inst : Inhabited Nat] (n : Nat) : Prop := n = inst.default

example (n : Nat) : (n is FooPred) = FooPred n := rfl
example (n : Nat) : (n is not FooPred) = (¬ FooPred n) := rfl
example {A : Sort u} (x : A) : (x is accepts) = accepts x := rfl
example {A : Sort u} (p : A → Prop) (x : A) : (x is p) = p x := rfl
example {A : Sort u} (p : A → Prop) (x : A) : (x is not p) = (¬ p x) := rfl
example (P Q : Prop) (p : Prop → Prop) : ((P and Q) is not p) = (¬ p (P ∧ Q)) := rfl
example (n m : Nat) : (n is (relates m)) = relates m n := rfl
example (T : Type*) : (T is not finite) = (¬ Finite T) := rfl
example (f : Nat → Nat) : (f is computable) = Computable f := rfl
example (p : Nat → Prop) : (p is computable) = ComputablePred p := rfl
example (p : Nat → Prop) : (p is not computable) = (¬ ComputablePred p) := rfl
example (p : Nat → Prop) : (p is recursively enumerable) = REPred p := rfl
example (p : Nat → Prop) : (p is not recursively enumerable) = (¬ REPred p) := rfl
example (p : Nat → Prop) :
    ((the function mapping a natural number n to n is not p) is recursively enumerable) =
      REPred (fun n : Nat => ¬ p n) := rfl
example : ((the function mapping a natural number n to n + 1) is computable) =
    Computable (fun n : Nat => n + 1) := rfl

end PredicateExamples

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

namespace TypeNounExamples
universe u
-- These ordinary Lean definitions need no English vocabulary registration.
def Token := Fin 3
def Endomap := Nat → Nat

Definition: an element i of Fin 3 is indexReflexive if i = i.
example : indexReflexive = (fun i : Fin 3 => i = i) := rfl
Definition: a list xs of Token elements is emptyList if xs = [].
example : emptyList = (fun xs : List Token => xs = []) := rfl
Definition: copyList is the function mapping a list xs of Token elements to xs.
example : copyList = (fun xs : List Token => xs) := rfl
Definition: polymorphicCopy is the function mapping an implicit element A of Type u and
  a list xs of A elements to xs.
example : @polymorphicCopy = (fun {A : Type u} (xs : List A) => xs) := rfl
Definition: implicitLength is the function mapping an implicit list xs of Token elements and
  a natural number n to xs.length + n.
example : @implicitLength = (fun {xs : List Token} (n : Nat) => xs.length + n) := rfl
Definition: strictLength is the function mapping a strictly implicit list xs of Token elements and
  a natural number n to xs.length + n.
example : strictLength = (fun ⦃xs : List Token⦄ (n : Nat) => xs.length + n) := rfl
example : (the function mapping a list xs of Nat elements and
    an element i of Fin xs.length to xs[i]) =
    (fun (xs : List Nat) (i : Fin xs.length) => xs[i]) := rfl
example (n : Nat) : (the function mapping a list xs of (Fin n) elements to xs) =
    (fun xs : List (Fin n) => xs) := rfl
example : (the function mapping a list fs of (Nat → Nat) elements to fs.length) =
    (fun fs : List (Nat → Nat) => fs.length) := rfl

Definition: diagonal is the function mapping a function f from Nat and Nat to Nat and
  a natural number n to f n n.
example : diagonal = (fun (f : Nat → Nat → Nat) (n : Nat) => f n n) := rfl
Definition: a function f from Nat and Nat to Nat is diagonalZero if (f 0 0 = 0).
example : diagonalZero = (fun f : Nat → Nat → Nat => f 0 0 = 0) := rfl
Definition: implicitApply is the function mapping an implicit function f from Nat to Nat and
  a natural number n to f n.
example : @implicitApply = (fun {f : Nat → Nat} (n : Nat) => f n) := rfl
Definition: strictApply is the function mapping a strictly implicit function f from Nat to Nat and
  a natural number n to f n.
example : strictApply = (fun ⦃f : Nat → Nat⦄ (n : Nat) => f n) := rfl
example : (the function mapping a function f from (Nat × Nat) to Nat to f (0, 0)) =
    (fun f : Nat × Nat → Nat => f (0, 0)) := rfl
example : (the function mapping a function f from (Nat → Nat) to Nat to f Nat.succ) =
    (fun f : (Nat → Nat) → Nat => f Nat.succ) := rfl

example : (there is a list xs of Token elements such that xs = []) =
    (∃ xs : List Token, xs = []) := rfl
example : (there is a list of Token elements) = (∃ _xs : List Token, True) := rfl
example : (there is no list of Token elements) = (¬ ∃ _xs : List Token, True) := rfl
example : (there is no list xs of Token elements such that xs = []) =
    (¬ ∃ xs : List Token, xs = []) := rfl
example : (there is a function f from Int and Int to Token such that f = f) =
    (∃ f : Int → Int → Token, f = f) := rfl
example : (there is a function from Nat to Nat) = (∃ _f : Nat → Nat, True) := rfl
example : (there is no function from Nat to Nat) = (¬ ∃ _f : Nat → Nat, True) := rfl
example : (there is no function f from Nat to Nat such that f 0 = 0) =
    (¬ ∃ f : Nat → Nat, f 0 = 0) := rfl
-- Anonymous descriptions leave surrounding variables in scope.
example (xs : List Token) : (there is a list of Token elements such that xs = xs) =
    (∃ _ys : List Token, xs = xs) := rfl
end TypeNounExamples

namespace BinderExamples
universe u

-- Every parameter noun supports a hygienic omitted name and the same binder kinds.
example : (the function mapping a natural number and an implicit integer and
    a strictly implicit boolean to true) =
    (fun (_ : Nat) {_ : Int} ⦃_ : Bool⦄ => true) := rfl
example : (the function mapping an element of Nat and an implicit element of Bool and
    a strictly implicit element of Int to true) =
    (fun (_ : Nat) {_ : Bool} ⦃_ : Int⦄ => true) := rfl
example : (the function mapping a proof that True and an implicit proof that True and
    a strictly implicit proof that True to true) =
    (fun (_ : True) {_ : True} ⦃_ : True⦄ => true) := rfl
example : (the function mapping a list of Nat elements and an implicit list of Bool elements and
    a strictly implicit list of Int elements to true) =
    (fun (_ : List Nat) {_ : List Bool} ⦃_ : List Int⦄ => true) := rfl
example : (the function mapping a function from Nat to Nat and
    an implicit function from Int to Int and a strictly implicit function from Bool to Bool to true) =
    (fun (_ : Nat → Nat) {_ : Int → Int} ⦃_ : Bool → Bool⦄ => true) := rfl
example (_anonymousParameter : Nat) :
    (the function mapping a natural number and a natural number to _anonymousParameter) =
    (fun (_ _ : Nat) => _anonymousParameter) := rfl

Definition: anonymousNatural is the function mapping a natural number to true.
example : anonymousNatural 7 = true := rfl
Definition: a natural number is constantPredicate if True.
example (n : Nat) : constantPredicate n := True.intro
Definition: a simple graph is constantGraph if True.
example (G : SimpleGraph Nat) : constantGraph G := True.intro
Definition: a simple graph = (V, E) is inhabitedCarrier if V is nonempty.
example {V : Type*} (G : SimpleGraph V) : inhabitedCarrier G = Nonempty V := rfl

Definition: defaultValue is the function mapping an implicit element A of Type u and
  an instance of typeclass Inhabited A to (default : A).
example : defaultValue (A := Nat) = 0 := rfl
Definition: chosenValue is the function mapping an implicit element A of Type u and
  an instance inst of typeclass Inhabited A to @default A inst.
example : chosenValue (A := Nat) (inst := ⟨7⟩) = 7 := rfl
example : (the function mapping an instance of typeclass Fact True to true) =
    (fun [Fact True] => true) := rfl
example : (there is an instance of typeclass Inhabited Nat) =
    (∃ _inst : Inhabited Nat, True) := rfl
example : (there is an instance inst of typeclass Inhabited Nat such that inst.default = 7) =
    (∃ inst : Inhabited Nat, inst.default = 7) := rfl
example : (there is no instance of typeclass Inhabited Nat) =
    (¬ ∃ _inst : Inhabited Nat, True) := rfl

-- Public parameter names survive even when unused or different from lambda names.
def namedUnused (n : Nat) : Bool := let _ := n; true
def namedImplicit {ignored : Nat} (n : Nat) : Nat := let _ := ignored; n
def namedStrict ⦃ignored : Nat⦄ (n : Nat) : Nat := let _ := ignored; n
def differentNames : (input : Nat) → Nat := fun n => n
def aliasWithName : (input : Nat) → Nat := Nat.succ
def namedCallback (f : (input : Nat) → Nat) : Nat := f (input := 0)
example : namedUnused (n := 7) = true := rfl
example : namedImplicit (ignored := 7) (n := 3) = 3 := rfl
example : namedStrict (ignored := 7) (n := 3) = 3 := rfl
example : differentNames (input := 7) = 7 := rfl
example : aliasWithName (input := 7) = 8 := rfl
example : namedCallback (f := fun n => n) = 0 := rfl
end BinderExamples

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

-- Universal nouns share witness types; later domains can depend on earlier names.
example : (for every function q from Nat to Prop:
    if q 0 then there is a function r from Nat to Nat such that
      for every natural number n: q n if and only if q (r n)) =
    (∀ q : Nat → Prop, q 0 → ∃ r : Nat → Nat, ∀ n : Nat, q n ↔ q (r n)) := rfl
example : (for all list xs of Nat elements:
    for every element i of Fin xs.length: xs[i] = xs[i]) =
    (∀ xs : List Nat, ∀ i : Fin xs.length, xs[i] = xs[i]) := rfl
example (A : Sort u) : (for every element x of A: x = x) = (∀ x : A, x = x) := rfl
example (P : Prop) : (for every proof h that P: h = h) = (∀ h : P, h = h) := rfl
example : (for every instance inst of typeclass Inhabited Nat: inst.default = 0) =
    (∀ inst : Inhabited Nat, inst.default = 0) := rfl
example {V : Type*} (G : SimpleGraph V) (u v : V) :
    (for all path p in G from u to v: p = p) = (∀ p : G.Path u v, p = p) := rfl
example : (for every function from Nat and Nat to Nat: True) =
    (∀ _f : Nat → Nat → Nat, True) := rfl
example (existentialWitness : Nat) :
    (for every element of Bool: existentialWitness = 0) =
    (∀ _b : Bool, existentialWitness = 0) := rfl

-- English connectives match Lean's precedence and associativity exactly.
example (P Q R : Prop) : (P and Q or R) = ((P ∧ Q) ∨ R) := rfl
example (P Q R : Prop) : (P or Q and R) = (P ∨ (Q ∧ R)) := rfl
example (P Q R : Prop) : (P and Q and R) = (P ∧ (Q ∧ R)) := rfl
example (P Q R : Prop) : ((P or Q) and R) = ((P ∨ Q) ∧ R) := rfl
example (P Q R : Prop) : (if P then Q and R) = (P → Q ∧ R) := rfl
example (P Q R : Prop) : (if P then if Q then R) = (P → Q → R) := rfl
example (P Q R : Prop) : (if (if P then Q) then R) = ((P → Q) → R) := rfl
example (P Q R : Prop) : (P and Q if and only if R) = ((P ∧ Q) ↔ R) := rfl
example (P Q R : Prop) : (P if and only if Q or R) = (P ↔ (Q ∨ R)) := rfl
example (P Q R : Prop) : ((P if and only if Q) if and only if R) = ((P ↔ Q) ↔ R) := rfl
example (P Q R : Prop) : (P if and only if (Q if and only if R)) = (P ↔ (Q ↔ R)) := rfl
example (P Q R : Prop) : ((if P then Q) if and only if R) = ((P → Q) ↔ R) := rfl
example (P Q R : Prop) : (if P then (Q if and only if R)) = (P → (Q ↔ R)) := rfl

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
