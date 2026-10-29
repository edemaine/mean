/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file Wang.LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1

Upstream source: [LeanWang/Abstract.lean](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LeanWang/Abstract.lean)
Upstream license: [Apache 2.0](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LICENSE)

Changes from upstream: import Mean; escape the binder
`a` as `«a»` because Mean reserves `a`; add checked before/after comparisons;
replace the two upstream theorem proofs with `sorry` rather than importing
AbstractBridge. Comparisons check the original definitions and theorem statements.
Mean and the upstream project both use Lean/mathlib 4.35.0.
-/
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List
import Mean

/-!
# Wang tiling: a formal abstract

See Wang.mean for generated Mean output, Wang.compare for Lean/Mean comparisons,
and Wang.LICENSE for the upstream Apache 2.0 license.
Unsupported constructions remain Lean, with the same checked round trip.
-/

namespace LeanWang.Abstract

/-
A Wang tile is a unit square with a color on each of its north, south, east,
and west edges (rotation/reflection forbidden). We represent this as a
function assigning a natural-number color to each direction.
Here `Direction` is the type `Fin 4`, whose elements are {0, 1, 2, 3},
which we alias to {n, s, e, w}. Thus `t n` is the north color of Wang tile `t`.
-/
abbrev Direction := Fin 4
#mean_compare Direction
abbrev n : Direction := 0
#mean_compare n
abbrev s : Direction := 1
#mean_compare s
abbrev e : Direction := 2
#mean_compare e
abbrev w : Direction := 3
#mean_compare w
abbrev Tile := Direction → ℕ
#mean_compare Tile

/--
A finite collection of Wang tiles tiles the plane if translated copies cover
the integer grid with equal colors on touching edges.
Here `List Tile` represents the collection using a list rather than a set
so that algorithms can process it easily; duplicates are harmless.
The value `t x y` is the Wang tile placed at cell `(x, y)`.
-/
def TilesPlane (T : List Tile) : Prop :=
  ∃ t : ℤ → ℤ → Tile, ∀ x y,
    t x y ∈ T ∧
    t x y e = t (x + 1) y w ∧
    t x y n = t x (y + 1) s

#mean_compare TilesPlane

/--
A problem is co-RE if an algorithm halts exactly on its no-instances,
which is equivalent to saying that the complement of the problem is RE
(an algorithm halts exactly on its yes-instances).
Mathlib's `REPred` defines RE.
-/
def CoRE {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  REPred (fun «a» => ¬ p «a»)

#mean_compare CoRE

/--
A problem is co-RE-complete if it is co-RE and every co-RE problem reduces to
it by a total computable map preserving answers. Natural numbers encode source
inputs; `Computable r` means an always-halting algorithm computes `r`, and
`q n ↔ p (r n)` says that the map preserves yes- and no-answers.
-/
def CoREComplete {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  CoRE p ∧
  ∀ q : ℕ → Prop, CoRE q →
    ∃ r : ℕ → α, Computable r ∧ ∀ n, q n ↔ p (r n)

#mean_compare CoREComplete

set_option warn.sorry false in
/--
Main theorem: Wang tiling is co-RE-complete. In particular, there is an
algorithm that halts exactly when the given Wang tiles do not tile the plane.
-/
theorem coRE_complete : CoREComplete TilesPlane := sorry
#mean_compare coRE_complete

set_option warn.sorry false in
/--
Main corollary: Wang tiling is undecidable, i.e., no always-halting algorithm
correctly decides whether a given finite collection of Wang tiles
tiles the plane. Mathlib's `ComputablePred` defines decidability.
-/
theorem undecidable : ¬ ComputablePred TilesPlane := sorry
#mean_compare undecidable

end LeanWang.Abstract
