/-
Copyright 2026 The Formal Conjectures Authors.

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
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineMesh

/-!
# AffineMesh, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineMesh`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits PartialOrder Set Simplicial
namespace AlgebraicTopology.Singular

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

end AlgebraicTopology.Singular
end
end
