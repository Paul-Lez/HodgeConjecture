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

public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularCoverSmallQuasiIso

import HodgeConjecture.Lemmas.AlgebraicTopology.SingularOpenCoverLebesgue
import Mathlib.Analysis.Normed.Module.Convex

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Mesh estimates for affine barycentric subdivision

This file proves the quantitative geometric estimate behind the small-chain argument.  In the
sup metric on the standard `n`-simplex, the affine simplex associated to every flag of nonempty
faces has diameter at most `n / (n + 1)`.  The proof uses the exact face-barycenter coordinates
from `SingularAffineSubdivision`.

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

/-- Arithmetic estimate for barycenters of two nested nonempty faces. -/
public theorem inv_natCast_sub_inv_natCast_le_barycentricContractionFactor
    (n a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n + 1) :
    |(a : ℝ)⁻¹ - (b : ℝ)⁻¹| ≤ barycentricContractionFactor n := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (b : ℝ) ≤ n + 1 := by exact_mod_cast hb
  have hB : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one (haR.trans habR)
  have h_inv_ab : (b : ℝ)⁻¹ ≤ (a : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) habR
  rw [abs_of_nonneg (sub_nonneg.mpr h_inv_ab)]
  have ha_one : (a : ℝ)⁻¹ ≤ 1 := by
    simpa using (inv_anti₀ (by norm_num : (0 : ℝ) < 1) haR)
  have hb_N : (n + 1 : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ :=
    inv_anti₀ hB hbR
  have hfactor : barycentricContractionFactor n =
      1 - (n + 1 : ℝ)⁻¹ := by
    unfold barycentricContractionFactor
    field_simp
    ring
  rw [hfactor]
  linarith

/-- If a face acquires a new vertex, then its barycenter coordinate at that vertex is bounded by
the barycentric mesh factor. -/
public theorem inv_natCast_le_barycentricContractionFactor_of_two_le
    (n b : ℕ) (hn : 1 ≤ n) (hb₂ : 2 ≤ b) :
    (b : ℝ)⁻¹ ≤ barycentricContractionFactor n := by
  have hb₂R : (2 : ℝ) ≤ b := by exact_mod_cast hb₂
  have hnR : (2 : ℝ) ≤ n + 1 := by
    exact_mod_cast (Nat.add_le_add_right hn 1)
  have hbhalf : (b : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hb₂R
  have hNhalf : (n + 1 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hnR
  have hfactor : barycentricContractionFactor n =
      1 - (n + 1 : ℝ)⁻¹ := by
    unfold barycentricContractionFactor
    field_simp
    ring
  rw [hfactor]
  have hhalf : (2 : ℝ)⁻¹ ≤ 1 - (n + 1 : ℝ)⁻¹ := by
    norm_num at hNhalf ⊢
    linarith
  exact hbhalf.trans hhalf

/-- Barycenters of two nested nonempty faces of the standard `n`-simplex are at distance at
most `n / (n + 1)` in the sup metric. -/
public theorem dist_nonemptyFiniteChainBarycenter_le
    (n : ℕ) (hn : 1 ≤ n)
    (A B : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) (hAB : A ≤ B) :
    dist (nonemptyFiniteChainBarycenter A)
      (nonemptyFiniteChainBarycenter B) ≤ barycentricContractionFactor n := by
  classical
  change dist (nonemptyFiniteChainBarycenter A : Fin (n + 1) → ℝ)
      (nonemptyFiniteChainBarycenter B : Fin (n + 1) → ℝ) ≤ _
  rw [dist_pi_le_iff (barycentricContractionFactor_nonneg n)]
  intro i
  rw [Real.dist_eq, nonemptyFiniteChainBarycenter_apply,
    nonemptyFiniteChainBarycenter_apply]
  by_cases hiA : ULift.up i ∈ A.finset
  · have hiB : ULift.up i ∈ B.finset := hAB hiA
    rw [if_pos hiA, if_pos hiB]
    apply inv_natCast_sub_inv_natCast_le_barycentricContractionFactor
    · exact A.nonempty.card_pos
    · exact Finset.card_le_card hAB
    · simpa using B.finset.card_le_univ
  · by_cases hiB : ULift.up i ∈ B.finset
    · rw [if_neg hiA, if_pos hiB, zero_sub, abs_neg,
        abs_of_nonneg (by positivity)]
      apply inv_natCast_le_barycentricContractionFactor_of_two_le n
        B.finset.card hn
      have hss : A.finset ⊂ B.finset :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hAB, ?_⟩
      · exact (Finset.card_lt_card hss).trans_le' A.nonempty.card_pos
      · intro heq
        exact hiA (heq.symm ▸ hiB)
    · simp [hiA, hiB, barycentricContractionFactor_nonneg]

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

/-- Abstract eventual-smallness theorem for iterated cells.  Once a concrete subdivision model
supplies nonempty cells with the displayed power-law diameter bound, a single depth works for all
cells and makes each of them lie in one member of any open cover. -/
public theorem exists_depth_for_diameter_controlled_cells_subordinate
    {X α ι : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (n : ℕ) (U : ι → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (cell : ℕ → α → Set X)
    (hcell : ∀ m a, (cell m a).Nonempty)
    (hdiam : ∀ m a, Metric.diam (cell m a) ≤
      barycentricContractionFactor n ^ m) :
    ∃ m : ℕ, ∀ a : α, ∃ i : ι, cell m a ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hUopen hUcover
  obtain ⟨m, hm⟩ := exists_barycentricContractionFactor_pow_lt n hδ
  refine ⟨m, fun a ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcell m a
  obtain ⟨i, hi⟩ := hball x (Set.mem_univ x)
  refine ⟨i, fun y hy ↦ hi ?_⟩
  rw [Metric.mem_ball]
  exact (Metric.dist_le_diam_of_mem
    (isCompact_univ.isBounded.subset (Set.subset_univ _)) hy hx).trans_lt
      ((hdiam m a).trans_lt hm)

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
