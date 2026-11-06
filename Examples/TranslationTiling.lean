/-
Adapted from the formal abstract for "Tiling 3D by Translates of a Single
Polycube is Undecidable" by Erik Demaine and Stefan Langerman.

Upstream source: [TranslationTiling/Abstract.lean](https://github.com/edemaine/translation-tiling-paper/blob/2c69feb2cf4b6c45a46e5cbe18838ede30f9a08f/lean/TranslationTiling/Abstract.lean)
Upstream license: no project-wide license is declared in the pinned TranslationTiling repository.
Upstream source: [LeanWang/Abstract.lean](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LeanWang/Abstract.lean)
Upstream license: the imported Wang example retains [Apache 2.0](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LICENSE) in Wang.LICENSE.

Changes from upstream: import Examples.Wang instead of LeanWang.CoRE, and use
LeanWang.Abstract.CoREComplete instead of LeanWang.CoREComplete in the two
completeness statements. This uses
natural-number source predicates rather than arbitrary encoded source types;
these are equivalent formulations here, but are not definitionally identical.
Escape `a` as `«a»` because Mean reserves `a`; replace the four AbstractBridge
proofs with `sorry`; add checked before/after comparisons. All eight original
definitions/abbreviations and four theorem declarations are retained.
Mean and both pinned upstream projects use Lean/mathlib 4.35.0.
-/
import Mathlib.Computability.Halting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Examples.Wang

/-!
# Translation tiling: a formal abstract

Project: https://edemaine.github.io/translation-tiling-paper/
See TranslationTiling.mean for Mean output and TranslationTiling.compare for
paired Lean/Mean comparisons. Unsupported constructions remain Lean, with the
same checked round trip.
-/

/-!
# The 3D tiling problem

A *prototile* is a finite list of points of `ℤ³`. It *tiles space* if `ℤ³` can be
partitioned into translates of it: there is a set `T` of translation vectors such
that every point of `ℤ³` lies in exactly one translate `t + P` with `t ∈ T`.

We show that deciding whether a *connected* prototile tiles is co-r.e.-complete,
both for `ℤ³` and for the solid body in `ℝ³` (union of unit cubes, arbitrary real
translations). The proofs invoke `TranslationTiling.AbstractBridge`, which connects
the statements to the rest of the project.
-/

namespace TranslationTiling.Abstract

/-- A point of `ℤ³`. -/
abbrev Point := Fin 3 → ℤ
#mean_compare Point

/-- A prototile: a finite set of points of `ℤ³`, given as a list. -/
abbrev Prototile := List Point
#mean_compare Prototile

/-- Two points are adjacent when their `ℓ¹` distance is one. -/
def Adjacent («a» b : Point) : Prop :=
  ∑ i, |«a» i - b i| = 1
#mean_compare Adjacent

/-- `P` is (face-)connected: any two of its points are joined by a path of
adjacent points inside `P`. -/
def Connected (P : Prototile) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (fun «a» b => «a» ∈ P ∧ b ∈ P ∧ Adjacent «a» b) p q
#mean_compare Connected

/-! ### Tiling `ℤ³` -/

/-- `P` tiles `ℤ³`: for some set `T` of translations, every point `x` lies in exactly
one translate `t + P` with `t ∈ T`, i.e., for exactly one `t ∈ T` we have `x - t ∈ P`. -/
def Tiles (P : Prototile) : Prop :=
  ∃ T : Set Point, ∀ x : Point, ∃! t : Point, t ∈ T ∧ x - t ∈ P
#mean_compare Tiles

set_option warn.sorry false in
/-- **Main theorem.** Deciding whether a connected prototile in `ℤ³` tiles space is
co-r.e.-complete: the non-tilers are recursively enumerable, and every co-r.e.
problem many-one reduces (computably) to it. -/
theorem tiling_coRE_complete : LeanWang.Abstract.CoREComplete fun P => Connected P ∧ Tiles P := sorry
#mean_compare tiling_coRE_complete

set_option warn.sorry false in
/-- **Corollary.** No algorithm decides whether a connected prototile in `ℤ³`
tiles space. (Mathlib notions only.) -/
theorem tiling_undecidable : ¬ ComputablePred fun P => Connected P ∧ Tiles P := sorry
#mean_compare tiling_undecidable

/-! ### Tiling `ℝ³` -/

/-- A point of `ℝ³`. -/
abbrev RealPoint := Fin 3 → ℝ
#mean_compare RealPoint

/-- The solid body of a prototile: the union of the unit cubes `p + [0, 1]³`, `p ∈ P`. -/
def Solid (P : Prototile) : Set RealPoint :=
  {x | ∃ p ∈ P, ∀ i, p i ≤ x i ∧ x i ≤ p i + 1}
#mean_compare Solid

/-- The solid body of `P` tiles `ℝ³` by translations: for some set `T ⊆ ℝ³` of
(arbitrary real) translations, almost every point `x` of `ℝ³` lies in exactly one
translate `t + Solid P` with `t ∈ T`. -/
def RealTiles (P : Prototile) : Prop :=
  ∃ T : Set RealPoint, ∀ᵐ x ∂MeasureTheory.volume, ∃! t : RealPoint, t ∈ T ∧ x - t ∈ Solid P
#mean_compare RealTiles

set_option warn.sorry false in
/-- Deciding whether the solid body of a connected prototile tiles `ℝ³` by arbitrary
real translations is co-r.e.-complete. -/
theorem real_tiling_coRE_complete : LeanWang.Abstract.CoREComplete fun P => Connected P ∧ RealTiles P := sorry
#mean_compare real_tiling_coRE_complete

set_option warn.sorry false in
/-- No algorithm decides whether a connected prototile tiles `ℝ³` by arbitrary
real translations. (Mathlib notions only.) -/
theorem real_tiling_undecidable : ¬ ComputablePred fun P => Connected P ∧ RealTiles P := sorry
#mean_compare real_tiling_undecidable

end TranslationTiling.Abstract
