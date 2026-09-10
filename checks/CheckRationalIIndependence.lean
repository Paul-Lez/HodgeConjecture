import Other.AlgebraicTopology.SingularComplexPeriods

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

universe u

section Linear

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def test_antiIComponent (T : Module.End ℂ V) : Module.End ℂ V :=
  LinearMap.id + Complex.I • T

@[simp]
theorem test_antiIComponent_apply (T : Module.End ℂ V) (x : V) :
    test_antiIComponent T x = x + Complex.I • T x := by
  rfl

theorem test_antiIComponent_eigen (T : Module.End ℂ V) (x : V)
    (hT : T (T x) = -x) :
    T (test_antiIComponent T x) =
      (-Complex.I) • test_antiIComponent T x := by
  rw [test_antiIComponent_apply, map_add, map_smul, hT]
  module
  rw [Complex.I_sq]
  norm_num

end Linear

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_rational_plus_I_smul_rational_ne_zero
    (X : TopCat) (n : ℕ)
    (alpha beta : Cohomology ℚ X n) (halpha : alpha ≠ 0) :
    rationalToComplexCohomologyMap X n alpha +
        Complex.I • rationalToComplexCohomologyMap X n beta ≠ 0 := by
  obtain ⟨z, hz⟩ : ∃ z : Homology ℚ X n, alpha z ≠ 0 := by
    simpa [LinearMap.ext_iff] using halpha
  intro hzero
  have hp := congrArg (complexCohomologyPeriod X n) hzero
  rw [map_add, map_smul, map_zero,
    complexCohomologyPeriod_rationalToComplex,
    complexCohomologyPeriod_rationalToComplex] at hp
  have heval := LinearMap.congr_fun hp z
  change algebraMap ℚ ℂ (alpha z) +
      Complex.I * algebraMap ℚ ℂ (beta z) = 0 at heval
  change (alpha z : ℂ) + Complex.I * (beta z : ℂ) = 0 at heval
  have hre := congrArg Complex.re heval
  have hre' : (alpha z : ℝ) = 0 := by
    simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ratCast_re, Complex.ratCast_im, zero_mul, one_mul, zero_sub, neg_zero, add_zero,
      Complex.zero_re] using hre
  apply hz
  exact_mod_cast hre'

def test_antiIContinuousComponent
    (X : TopCat) (n : ℕ) (f : X ⟶ X) :
    Module.End ℂ (Cohomology ℂ X n) :=
  test_antiIComponent (cohomologyMap ℂ n f)

theorem test_antiIContinuousComponent_ne_zero
    (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℚ X n) (halpha : alpha ≠ 0)
    (hnat : cohomologyMap ℂ n f
        (rationalToComplexCohomologyMap X n alpha) =
      rationalToComplexCohomologyMap X n (cohomologyMap ℚ n f alpha)) :
    test_antiIContinuousComponent X n f
        (rationalToComplexCohomologyMap X n alpha) ≠ 0 := by
  unfold test_antiIContinuousComponent test_antiIComponent
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply]
  rw [hnat]
  exact test_rational_plus_I_smul_rational_ne_zero X n alpha
    (cohomologyMap ℚ n f alpha) halpha

theorem test_antiIContinuousComponent_eigen
    (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℂ X n)
    (hsq : cohomologyMap ℂ n f (cohomologyMap ℂ n f alpha) = -alpha) :
    cohomologyMap ℂ n f (test_antiIContinuousComponent X n f alpha) =
      (-Complex.I) • test_antiIContinuousComponent X n f alpha :=
  test_antiIComponent_eigen (cohomologyMap ℂ n f) alpha hsq

end AlgebraicTopology.Singular
