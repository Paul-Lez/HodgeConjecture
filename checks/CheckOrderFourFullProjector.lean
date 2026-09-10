import Other.AlgebraicTopology.SingularOrderFourProjector

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def test_orderFourMinusPart (J : Module.End ℂ V) (v : V) : V :=
  (1 / 4 : ℂ) • (v + Complex.I • J v - J (J v) -
    Complex.I • J (J (J v)))

theorem test_map_orderFourMinusPart (J : Module.End ℂ V)
    (hJ : ∀ x, J (J (J (J x))) = x) (v : V) :
    J (test_orderFourMinusPart J v) =
      -Complex.I • test_orderFourMinusPart J v := by
  rw [test_orderFourMinusPart, map_smul, map_sub, map_sub, map_add,
    map_smul, map_smul, hJ]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

section Bilinear

variable {V₁ V₂ W : Type*}
  [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup W] [Module ℂ W]

theorem test_orderFourMinusPart_bilinear_left
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₁) (T : Module.End ℂ W)
    (hT : ∀ x y, T (B x y) = B (J x) y) (x : V₁) (y : V₂) :
    test_orderFourMinusPart T (B x y) =
      B (test_orderFourMinusPart J x) y := by
  rw [test_orderFourMinusPart, test_orderFourMinusPart]
  rw [hT, hT, hT, map_smul, map_sub, map_sub, map_add, map_smul]
  simp

theorem test_orderFourMinusPart_bilinear_right
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₂) (T : Module.End ℂ W)
    (hT : ∀ x y, T (B x y) = B x (J y)) (x : V₁) (y : V₂) :
    test_orderFourMinusPart T (B x y) =
      B x (test_orderFourMinusPart J y) := by
  rw [test_orderFourMinusPart, test_orderFourMinusPart]
  rw [hT, hT, hT, map_smul, map_sub, map_sub, map_add, map_smul]
  simp

end Bilinear

def test_continuousOrderFourMinusPart
    (X : TopCat) (n : ℕ) (f : X ⟶ X) (alpha : Cohomology ℚ X n) :
    Cohomology ℂ X n :=
  test_orderFourMinusPart (cohomologyMap ℂ n f)
    (rationalToComplexCohomologyMap X n alpha)

theorem test_continuousOrderFourMinusPart_ne_zero
    (X : TopCat) (n : ℕ) (f : X ⟶ X) (alpha : Cohomology ℚ X n)
    (hdelta : alpha - cohomologyMap ℚ n f (cohomologyMap ℚ n f alpha) ≠ 0) :
    test_continuousOrderFourMinusPart X n f alpha ≠ 0 := by
  let A := cohomologyMap ℚ n f
  let v := rationalToComplexCohomologyMap X n alpha
  have hnat₁ : cohomologyMap ℂ n f v =
      rationalToComplexCohomologyMap X n (A alpha) := by
    exact (rationalToComplexCohomologyMap_naturality f n alpha).symm
  have hnat₂ : cohomologyMap ℂ n f (cohomologyMap ℂ n f v) =
      rationalToComplexCohomologyMap X n (A (A alpha)) := by
    rw [hnat₁]
    exact (rationalToComplexCohomologyMap_naturality f n (A alpha)).symm
  have hnat₃ : cohomologyMap ℂ n f
        (cohomologyMap ℂ n f (cohomologyMap ℂ n f v)) =
      rationalToComplexCohomologyMap X n (A (A (A alpha))) := by
    rw [hnat₂]
    exact (rationalToComplexCohomologyMap_naturality f n (A (A alpha))).symm
  have hsum := rationalToComplex_add_I_smul_rationalToComplex_ne_zero X n
    (alpha - A (A alpha)) (A alpha - A (A (A alpha))) (by simpa [A] using hdelta)
  intro hzero
  have hquarter : (1 / 4 : ℂ) ≠ 0 := by norm_num
  have hn := smul_eq_zero.mp hzero |>.resolve_left hquarter
  apply hsum
  rw [map_sub, map_sub]
  change v - _ + Complex.I • (_ - _) = 0
  rw [← hnat₁, ← hnat₂, ← hnat₃]
  dsimp only [v] at hn ⊢
  rw [smul_sub]
  abel_nf at hn ⊢
  exact hn

end AlgebraicTopology.Singular
