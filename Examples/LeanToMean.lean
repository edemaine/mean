import Examples.MeanToLean
import Mean

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
  an element i of Fin 3 is TypeNounExamples.indexReflexive if
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
info: for every function q from ℕ to Prop:
  if 0 is q then
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
info: the function mapping a strictly implicit natural number n and an element i of Fin n to
  (↑i : ℕ)
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

-- Additional explicit parameters and hypotheses use nested function expressions.
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
