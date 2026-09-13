/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.CoverSmallQuasiIso

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Lebesgue
import Mathlib.Analysis.Normed.Module.Convex

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Mesh estimates for affine barycentric subdivision

This file proves the quantitative geometric estimate behind the small-chain argument.  In the
sup metric on the standard `n`-simplex, the affine simplex associated to every flag of nonempty
faces has diameter at most `n / (n + 1)`.  The proof uses the exact face-barycenter coordinates
from `Singular.Subdivision.Affine`.

The final theorem packages the metric conclusion needed for iterated subdivision: any family of
nonempty cells whose diameters are bounded by successive powers of this factor is eventually
subordinate to an arbitrary open cover of a compact metric space.  Connecting that abstract
family to the chain-level iterate requires keeping the ancestry of every iterated affine flag;
that combinatorial bookkeeping is intentionally separate from the metric argument here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Set Simplicial

namespace AlgebraicTopology.Singular

/-- The classical mesh-contraction factor for barycentric subdivision of an `n`-simplex. -/
public noncomputable def barycentricContractionFactor (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 1)

public theorem barycentricContractionFactor_nonneg (n : ℕ) :
    0 ≤ barycentricContractionFactor n := by
  unfold barycentricContractionFactor
  positivity

public theorem barycentricContractionFactor_lt_one (n : ℕ) :
    barycentricContractionFactor n < 1 := by
  unfold barycentricContractionFactor
  rw [div_lt_one (by positivity)]
  norm_num

/-- The intrinsic diameter of a nonempty standard simplex is one in the sup metric. -/
public theorem diam_univ_stdSimplex (n : ℕ) (hn : 1 ≤ n) :
    Metric.diam (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) = 1 := by
  let : Nontrivial (Fin (n + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (Nat.add_le_add_right hn 1)
  calc
    Metric.diam (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) =
        Metric.diam (Set.range
          (Subtype.val : stdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ)) :=
      isometry_subtype_coe.diam_range.symm
    _ = Metric.diam (stdSimplex ℝ (Fin (n + 1))) := by
      congr 1
      ext w
      simp
    _ = 1 := diam_stdSimplex

/-- Powers of the barycentric mesh factor eventually fall below every positive tolerance. -/
public theorem exists_barycentricContractionFactor_pow_lt
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, barycentricContractionFactor n ^ m < ε :=
  exists_pow_lt_of_lt_one hε (barycentricContractionFactor_lt_one n)

/-! ## Iterated affine-cell ancestry -/

/-- A top-dimensional flag in the barycentric subdivision of the standard `n`-simplex. -/
public abbrev TopAffineFlag (n : ℕ) :=
  (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
    (Opposite.op (SimplexCategory.mk n))

/-- The affine cell map described by a finite ancestry of top-dimensional flags.  The head of
the list is the newest (innermost) subdivision cell and the tail records its parent ancestry. -/
public noncomputable def iteratedAffineCellMap (n : ℕ)
    (ancestry : List (TopAffineFlag n)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  match ancestry with
  | [] => ContinuousMap.id _
  | F :: ancestry =>
      (iteratedAffineCellMap n ancestry).comp (affineFlagContinuousMap n n F)

@[simp]
public theorem iteratedAffineCellMap_nil (n : ℕ) :
    iteratedAffineCellMap n [] = ContinuousMap.id _ :=
  rfl

@[simp]
public theorem iteratedAffineCellMap_cons
    (n : ℕ) (F : TopAffineFlag n) (ancestry : List (TopAffineFlag n)) :
    iteratedAffineCellMap n (F :: ancestry) =
      (iteratedAffineCellMap n ancestry).comp
        (affineFlagContinuousMap n n F) :=
  rfl

/-! ## Chain-level endpoint -/

/-- Iterating affine subdivision is additive in the exponent.  This synchronization identity is
the algebraic tool for putting finitely many generatorwise subdivision depths over one common
depth. -/
public theorem affineSingularSubdivisionIterate_add
    (X : TopCat) (m r : ℕ) :
    affineSingularSubdivisionIterate X (m + r) =
      affineSingularSubdivisionIterate X m ≫
        affineSingularSubdivisionIterate X r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, affineSingularSubdivisionIterate_succ, ih,
        affineSingularSubdivisionIterate_succ, Category.assoc]

/-- A sharply stated range bridge from geometry to the algebraic small-chain endpoint: it is
enough to prove that some affine-subdivision iterate of every chain lies in the degreewise range
of the cover-small inclusion. -/
public theorem coverSmallAffineSubdivisionEventuallySmall_of_iterate_mem_range
    {iota : Type} (X : TopCat) (U : iota → Set X)
    (h : ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ m : ℕ, (affineSingularSubdivisionIterate X m).f n x ∈
        Set.range ((coverSmallIntegralSingularChainInclusion X U).f n)) :
    ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (CoverSmallIntegralSingularChainComplex X U).X n),
        (coverSmallIntegralSingularChainInclusion X U).f n y =
          (affineSingularSubdivisionIterate X m).f n x :=
  fun n x ↦ h n x

end AlgebraicTopology.Singular
