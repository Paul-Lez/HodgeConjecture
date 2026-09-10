import Other.AlgebraicTopology.SingularCoefficientBaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

open CategoryTheory Limits
open AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

theorem test_exists_rationalHomologyClass_qToC_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ z : Homology ℚ X n, qToCHomology X n z ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w : Homology ℂ X n, alpha w ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_ne_iff] at hall
    apply halpha
    ext w
    exact hall w
  have hw0 : w ≠ 0 := by
    intro hwzero
    apply hw
    rw [hwzero, map_zero]
  by_contra hall
  simp only [not_exists, not_ne_iff] at hall
  have hzero : ∀ w : Homology ℂ X n, w = 0 := by
    intro w
    apply (qToCHomology_isBaseChange X n).inductionOn w (fun v => v = 0)
    · rfl
    · intro z
      exact hall z
    · intro s v hv
      rw [hv, smul_zero]
    · intro v₁ v₂ hv₁ hv₂
      rw [hv₁, hv₂, add_zero]
  exact hw0 (hzero w)

theorem test_exists_rationalCohomologyClass_image_ne_zero
    (X : TopCat) (n : ℕ) (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0) :
    ∃ beta : Cohomology ℚ X n,
      rationalToComplexCohomologyMap X n beta ≠ 0 := by
  obtain ⟨z, hz⟩ := test_exists_rationalHomologyClass_qToC_ne_zero X n alpha halpha
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz (LinearMap.map_zero _)
  obtain ⟨beta, hbeta⟩ := Module.Projective.exists_dual_ne_zero ℚ hz0
  refine ⟨beta, ?_⟩
  intro himage
  have heval : rationalToComplexCohomologyMap X n beta
      (qToCHomology X n z) = 0 := by
    rw [himage]
    rfl
  have hcast : algebraMap ℚ ℂ (beta z) = 0 := by
    calc
      algebraMap ℚ ℂ (beta z) =
          rationalToComplexCohomologyMap X n beta
            (qToCHomology X n z) := by
        exact ((qToCHomology_isBaseChange X n).toDual_comp_apply beta z).symm
      _ = 0 := heval
  apply hbeta
  apply FaithfulSMul.algebraMap_injective ℚ ℂ
  simpa only [map_zero] using hcast

end AlgebraicTopology.Singular
