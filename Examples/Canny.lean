/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file Canny.LICENSE.

Upstream source: [LeanCanny/Abstract.lean](https://github.com/edemaine/lean-canny/blob/6b758a2abff2b2ef69d245dad37505f9fb790921/LeanCanny/Abstract.lean)
Upstream license: [Apache 2.0](https://github.com/edemaine/lean-canny/blob/6b758a2abff2b2ef69d245dad37505f9fb790921/LICENSE)

Adapted for Mean's Lean/mathlib 4.35.0. Binder names a, b are replaced
by p, q (or p₁, p₂) because Mean reserves a. See Canny.mean and Canny.compare
for checked renderings. Inductive types retain native signatures; consult the
source below for their constructors.

Changes from upstream: replace CSLib Frontier's generated encodings and
machine-based complexity definitions with the explicitly declared Background
interfaces below. Their intended meanings are documented, not implemented or
verified here. This adaptation is a rendering example, not a verification of
complexity bounds or equivalence with CSLib Frontier. Replace all seven bridge
proofs with sorry, as in Wang. Preserve the abstract's mathematical syntax,
solution sets, encoded-language construction, and theorem statements relative
to these interfaces. No newer toolchain or CSLib dependency is required.
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Path
import Examples.Wang

noncomputable section
namespace LeanCanny.Abstract

/-! ## Shared formulas and real solution sets -/

/-- Integer polynomial expressions use constants, variables, addition, and
multiplication. In dimension `n`, variables are the indices `Fin n`. -/
inductive Term (n : ℕ) where
  | const : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
#mean_compare Term

/-- Evaluate an integer polynomial expression at a real assignment `x`. -/
def Term.eval {n : ℕ} (x : Fin n → ℝ) : Term n → ℝ
  | .const z => z
  | .var i => x i
  | .add p q => p.eval x + q.eval x
  | .mul p q => p.eval x * q.eval x
#mean_compare Term.eval

/-- A Boolean formula compares polynomial expressions with zero, using equality
or strict inequality, and combines these assertions by negation, conjunction,
and disjunction. ETR existentially quantifies all occurring variables;
connectivity treats them as coordinates of the described space. -/
inductive Formula (n : ℕ) where
  | false : Formula n
  | eqZero : Term n → Formula n
  | ltZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
#mean_compare Formula

/-- A formula describes a solution set in `ℝⁿ`, represented by `Fin n → ℝ`.
Negation, conjunction, and disjunction give complement, intersection, and union. -/
def Formula.solutionSet {n : ℕ} : Formula n → Set (Fin n → ℝ)
  | .false => ∅
  | .eqZero t => {x | t.eval x = 0}
  | .ltZero t => {x | t.eval x < 0}
  | .not p => p.solutionSetᶜ
  | .and p q => p.solutionSet ∩ q.solutionSet
  | .or p q => p.solutionSet ∪ q.solutionSet
#mean_compare Formula.solutionSet

/-! ## Background interfaces (not implementations)

These declarations stand in for CSLib Frontier. The encoding interfaces are
injective, but their bit layout and size bounds are not checked in this example.
The class interfaces carry no machine semantics or closure properties here.
Consult the pinned upstream abstract for the actual generated encodings and
machine-based classes. -/
namespace Background
/-- Intended: unary dimension encoding. -/
axiom encUnary : ℕ ↪ List Bool
/-- Intended: the upstream framed pair encoding. -/
axiom encPair {α β : Type} : (α ↪ List Bool) → (β ↪ List Bool) → (α × β ↪ List Bool)
/-- Intended: the upstream framed list encoding. -/
axiom encList {α : Type} : (α ↪ List Bool) → (List α ↪ List Bool)
/-- Binary words encode themselves. -/
abbrev encBits : List Bool ↪ List Bool := Function.Embedding.refl _
/-- Intended: one uniform deterministic machine decides the language in polynomial space. -/
axiom PSPACE {α : Type} : (α ↪ List Bool) → Set (Set α)
/-- Intended: C₀P is P; each successor is strict-majority polynomial time
with one fixed oracle from the preceding level. -/
axiom CountingLevel : ℕ → {α : Type} → (α ↪ List Bool) → Set (Set α)
/-- Intended: an encoding-relative, total polynomial-time many-one reduction. -/
axiom PolyTimeReducible {α β : Type} :
  (α ↪ List Bool) → (β ↪ List Bool) → Set α → Set β → Prop
end Background

/-- Intended: flat constructor stream, with binary integers and unary Fin indices. -/
axiom encTerm (n : ℕ) : Term n ↪ List Bool
#mean_compare encTerm

/-- Intended: the corresponding formula stream reusing encTerm. -/
axiom encFormula (n : ℕ) : Formula n ↪ List Bool
#mean_compare encFormula

/-! ## ∃ℝ -/

/-- ETR consists of the encodings of real-satisfiable formulas. -/
def ETR : Set (List Bool) :=
  ⋃ n, {p : Formula n | p.solutionSet.Nonempty}.image (encFormula n)
#mean_compare ETR

set_option warn.sorry false in
/-- Theorem (Canny, 1988): existential real satisfiability is decidable in deterministic
polynomial space, including rejection of malformed binary inputs. -/
theorem etr_in_PSPACE : ETR ∈ Background.PSPACE Background.encBits :=
  sorry
#mean_compare etr_in_PSPACE

set_option warn.sorry false in
/-- Theorem (OpenAI, 2026): ETR belongs to the fixed counting level C₂₆P,
with the same encoded language used in the PSPACE theorem above. -/
theorem etr_in_CountingLevel :
    ETR ∈ Background.CountingLevel 26 Background.encBits :=
  sorry
#mean_compare etr_in_CountingLevel

/-- The class ∃ℝ consists of binary languages reducible to ETR in polynomial time.
A reduction is a polynomial-time algorithm on all input strings that preserves
yes/no answers; the background library's `PolyTimeReducible` includes its time bound. -/
def ExistsReal : Set (Set (List Bool)) :=
  {L | Background.PolyTimeReducible Background.encBits
    Background.encBits L ETR}
#mean_compare ExistsReal

set_option warn.sorry false in
/-- Corollary (Canny, 1988): every problem in ∃ℝ is decidable in deterministic
polynomial space. -/
theorem existsReal_subset_PSPACE :
    ExistsReal ⊆ Background.PSPACE Background.encBits :=
  sorry
#mean_compare existsReal_subset_PSPACE

set_option warn.sorry false in
/-- Corollary (OpenAI, 2026): every problem in ∃ℝ belongs to that same fixed
counting level. -/
theorem existsReal_subset_CountingLevel :
    ExistsReal ⊆ Background.CountingLevel 26 Background.encBits :=
  sorry
#mean_compare existsReal_subset_CountingLevel

/-! ## ∃∀ℝ -/

/-- The ∃∀ℝ solution set contains the existential assignments `x` of length `r`
for which every universal assignment `y` of length `s` satisfies `p`.
`Fin.addCases` concatenates the tuples, with the existential coordinates first.
Either block may be empty; nonemptiness of this set expresses ∃∀ℝ truth. -/
def Formula.existsForallSolutionSet {r s : ℕ} (p : Formula (r + s)) : Set (Fin r → ℝ) :=
  {x | ∀ y : Fin s → ℝ, Fin.addCases x y ∈ p.solutionSet}
#mean_compare Formula.existsForallSolutionSet

/-- The language ∃∀ℝ consists of true existential-universal real sentences.
It uses the same formula encoding as ETR and records the unary existential block
length. The union allows all finite block sizes; unused coordinates do not affect
truth. Every other word is rejected. -/
def ExistsForallReal : Set (List Bool) :=
  ⋃ r, ⋃ s, {p : Formula (r + s) | p.existsForallSolutionSet.Nonempty}.image (fun p =>
    Background.encPair Background.encUnary Background.encBits
      (r, encFormula (r + s) p))
#mean_compare ExistsForallReal

set_option warn.sorry false in
/-- Theorem (OpenAI, 2026): ∃∀ℝ belongs to CH.
This formalization supplies the fixed level C₆₀P, independent of variable counts,
polynomial degrees, and coefficient magnitudes. -/
theorem existsForallReal_in_CountingLevel :
    ExistsForallReal ∈ Background.CountingLevel 60 Background.encBits :=
  sorry
#mean_compare existsForallReal_in_CountingLevel

/-! ## Whole-space connectivity -/

/-- Connected formulas describe connected solution sets in `ℝⁿ`, allowing the
empty set (Mathlib's root-level `IsPreconnected`). -/
def ConnectedFormulas (n : ℕ) : Set (Formula n) :=
  {p | _root_.IsPreconnected p.solutionSet}
#mean_compare ConnectedFormulas

/-- Whole-space connectivity applies the input encoding to connected formulas. -/
def ConnectedLanguage : Set (List Bool) :=
  ⋃ n, (ConnectedFormulas n).image (fun p =>
    Background.encPair Background.encUnary Background.encBits
      (n, encFormula n p))
#mean_compare ConnectedLanguage

set_option warn.sorry false in
/-- Theorem (Canny, 1988): connectivity of an integer semialgebraic set is in PSPACE,
including singular and unbounded sets and accepting the empty set. -/
theorem connectedLanguage_in_PSPACE :
    ConnectedLanguage ∈ Background.PSPACE Background.encBits :=
  sorry
#mean_compare connectedLanguage_in_PSPACE

/-! ## Point reachability -/

/-- Reachable endpoint pairs describe two unique points joined by a continuous
path inside the solution set of `p`. Mathlib's root-level `Path x y` is a
continuous map from `[0,1]` with endpoints `x` and `y`. The endpoints may be
irrational; each endpoint formula must have a singleton solution set. -/
def ReachableEndpoints {n : ℕ} (p : Formula n) : Set (Formula n × Formula n) :=
  {(p₁, p₂) | ∃ x y, p₁.solutionSet = {x} ∧ p₂.solutionSet = {y} ∧
    ∃ γ : _root_.Path x y, ∀ t, γ t ∈ p.solutionSet}
#mean_compare ReachableEndpoints

/-- Reachability applies the input encoding to reachable endpoint pairs. -/
def ReachableLanguage : Set (List Bool) :=
  ⋃ n, ⋃ p : Formula n, (ReachableEndpoints p).image (fun (p₁, p₂) =>
    Background.encPair Background.encUnary
      (Background.encList Background.encBits)
      (n, [encFormula n p, encFormula n p₁, encFormula n p₂]))
#mean_compare ReachableLanguage

set_option warn.sorry false in
/-- Theorem (Canny, 1988): path connectivity between two formula-described points
in an integer semialgebraic set is in PSPACE, including endpoint validation. -/
theorem reachableLanguage_in_PSPACE :
    ReachableLanguage ∈ Background.PSPACE Background.encBits :=
  sorry
#mean_compare reachableLanguage_in_PSPACE

end LeanCanny.Abstract
