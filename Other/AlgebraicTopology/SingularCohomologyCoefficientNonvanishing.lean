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

public import Other.AlgebraicTopology.SingularCoefficientBaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Nonvanishing under rational-to-complex singular coefficient change

This file records the nonvanishing consequences of the rational-to-complex base-change
theorem for singular homology.  They do not require a finite-dimensionality assumption.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- A nonzero complex singular cohomology class pairs nontrivially with the complexification
of some rational homology class.  This is stronger than mere nonvanishing of rational homology:
the rational cycle retains a nonzero period against the given complex class. -/
theorem exists_rationalHomologyClass_complex_pairing_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ z : Homology ℚ X n, alpha (qToCHomology X n z) ≠ 0 := by
  let alpha' : Module.Dual ℂ ((CChains X).homology n) := alpha
  have halpha' : alpha' ≠ 0 := halpha
  obtain ⟨w, hw⟩ : ∃ w : (CChains X).homology n, alpha' w ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_ne_iff] at hall
    apply halpha'
    ext w
    exact hall w
  by_contra hall
  simp only [not_exists, not_ne_iff] at hall
  have hzero : ∀ w : (CChains X).homology n, alpha' w = 0 := by
    intro w
    apply (qToCHomology_isBaseChange X n).inductionOn w
      (fun v => alpha' v = 0)
    · exact map_zero alpha'
    · intro z
      exact hall z
    · intro s v hv
      rw [map_smul, hv, smul_zero]
    · intro v₁ v₂ hv₁ hv₂
      rw [map_add, hv₁, hv₂, add_zero]
  exact hw (hzero w)

/-- A nonzero complex singular cohomology class forces some rational homology class to
remain nonzero after extending its coefficients to `ℂ`. -/
theorem exists_rationalHomologyClass_qToC_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ z : Homology ℚ X n, qToCHomology X n z ≠ 0 := by
  obtain ⟨z, hz⟩ :=
    exists_rationalHomologyClass_complex_pairing_ne_zero X n alpha halpha
  exact ⟨z, fun hzero => hz (by rw [hzero]; exact map_zero alpha)⟩

/-- Extending coefficients gives an injective map from rational to complex singular
cohomology, in every degree and without a finite-dimensionality hypothesis. -/
theorem rationalToComplexCohomologyMap_injective (X : TopCat) (n : ℕ) :
    Function.Injective (rationalToComplexCohomologyMap X n) := by
  intro beta₁ beta₂ hbeta
  ext z
  apply FaithfulSMul.algebraMap_injective ℚ ℂ
  calc
    algebraMap ℚ ℂ (beta₁ z) =
        rationalToComplexCohomologyMap X n beta₁ (qToCHomology X n z) := by
      exact ((qToCHomology_isBaseChange X n).toDual_comp_apply beta₁ z).symm
    _ = rationalToComplexCohomologyMap X n beta₂ (qToCHomology X n z) := by
      exact DFunLike.congr_fun hbeta (qToCHomology X n z)
    _ = algebraMap ℚ ℂ (beta₂ z) := by
      exact (qToCHomology_isBaseChange X n).toDual_comp_apply beta₂ z

/-- A nonzero complex singular cohomology class yields a rational singular cohomology
class whose coefficient extension is nonzero. -/
theorem exists_rationalCohomologyClass_image_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ beta : Cohomology ℚ X n,
      rationalToComplexCohomologyMap X n beta ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_rationalHomologyClass_qToC_ne_zero X n alpha halpha
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz (LinearMap.map_zero _)
  obtain ⟨beta, hbeta⟩ := Module.Projective.exists_dual_ne_zero ℚ hz0
  refine ⟨beta, ?_⟩
  intro himage
  have hzero : beta = 0 := by
    apply rationalToComplexCohomologyMap_injective X n
    rw [himage, map_zero]
  apply hbeta
  rw [hzero, LinearMap.zero_apply]

/-- In particular, nonvanishing of complex singular cohomology implies nonvanishing of
rational singular cohomology. -/
theorem exists_rationalCohomologyClass_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ beta : Cohomology ℚ X n, beta ≠ 0 := by
  obtain ⟨beta, hbeta⟩ :=
    exists_rationalCohomologyClass_image_ne_zero X n alpha halpha
  exact ⟨beta, fun hzero => hbeta (by rw [hzero, map_zero])⟩

end AlgebraicTopology.Singular
