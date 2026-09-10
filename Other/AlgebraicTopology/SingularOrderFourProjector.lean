/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularComplexPeriods
public import Other.AlgebraicTopology.SingularCoefficientNaturality
public import Other.AlgebraicTopology.SingularDegreeOneExternalFunctoriality
public import Other.LinearAlgebra.OrderFourEigenprojectors
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Order-four projectors in singular cohomology

This file specializes the elementary `i`/`-i` projectors to pullback by a continuous
self-map.  The key nonvanishing statement uses rational periods: if `v` is the
complexification of a nonzero rational class, then `v + i Jv` cannot vanish provided
pullback commutes with rational-to-complex coefficient extension.

The last section applies the projector in both factors of the canonical degree-`(1,1)`
external product.  It records both separate `-i` eigenvalue equations and the equivalent
single eigenvalue equation for the sum of the two factor actions.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A rational period and `i` times a rational period cannot cancel if the first class is
nonzero.  No finite-dimensionality hypothesis on singular homology is needed. -/
theorem rationalToComplex_add_I_smul_rationalToComplex_ne_zero
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
      Complex.ratCast_re, Complex.ratCast_im, zero_mul, one_mul, zero_sub,
      neg_zero, add_zero, Complex.zero_re] using hre
  apply hz
  exact_mod_cast hre'

/-- The pullback endomorphism on complex singular cohomology induced by a continuous
self-map. -/
def continuousCohomologyEnd (X : TopCat) (n : ℕ) (f : X ⟶ X) :
    Module.End ℂ (Cohomology ℂ X n) :=
  cohomologyMap ℂ n f

/-- The `-i` part of a complexified rational singular cohomology class for a continuous
self-map. -/
def continuousCMMinusPart (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℚ X n) : Cohomology ℂ X n :=
  LinearAlgebra.cmMinusPart (continuousCohomologyEnd X n f)
    (rationalToComplexCohomologyMap X n alpha)

/-- The continuous `-i` part of a nonzero rational class is nonzero. -/
theorem continuousCMMinusPart_ne_zero
    (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℚ X n) (halpha : alpha ≠ 0) :
    continuousCMMinusPart X n f alpha ≠ 0 := by
  have hsum := rationalToComplex_add_I_smul_rationalToComplex_ne_zero X n alpha
    (cohomologyMap ℚ n f alpha) halpha
  rw [continuousCMMinusPart, LinearAlgebra.cmMinusPart]
  change (1 / 2 : ℂ) •
      (rationalToComplexCohomologyMap X n alpha +
        Complex.I • cohomologyMap ℂ n f
          (rationalToComplexCohomologyMap X n alpha)) ≠ 0
  rw [← rationalToComplexCohomologyMap_naturality]
  intro hzero
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  exact hsum (smul_eq_zero.mp hzero |>.resolve_left hhalf)

/-- If pullback squares to `-1`, the continuous minus part is a `-i` eigenvector. -/
theorem cohomologyMap_continuousCMMinusPart
    (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℚ X n)
    (hsq : ∀ x : Cohomology ℂ X n,
      cohomologyMap ℂ n f (cohomologyMap ℂ n f x) = -x) :
    cohomologyMap ℂ n f (continuousCMMinusPart X n f alpha) =
      -Complex.I • continuousCMMinusPart X n f alpha := by
  exact LinearAlgebra.map_cmMinusPart_of_sq_neg_one
    (continuousCohomologyEnd X n f) hsq
    (rationalToComplexCohomologyMap X n alpha)

/-! ## The full projector assuming only order four -/

section FullOrderFour

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The spectral projector onto the `-i` eigenspace of an operator satisfying `J⁴ = 1`.
This four-term formula does not assume `J² = -1`. -/
def orderFourCMMinusPart (J : Module.End ℂ V) (v : V) : V :=
  (1 / 4 : ℂ) • (v + Complex.I • J v - J (J v) -
    Complex.I • J (J (J v)))

/-- The four-term projector is a `-i` eigenvector when `J` has order dividing four. -/
theorem map_orderFourCMMinusPart (J : Module.End ℂ V)
    (hJ : ∀ x, J (J (J (J x))) = x) (v : V) :
    J (orderFourCMMinusPart J v) =
      -Complex.I • orderFourCMMinusPart J v := by
  rw [orderFourCMMinusPart, map_smul, map_sub, map_sub, map_add,
    map_smul, map_smul, hJ]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

variable {V₁ V₂ W : Type*}
  [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup W] [Module ℂ W]

/-- An equivariant bilinear map commutes with the full order-four projector in its
first variable. -/
theorem orderFourCMMinusPart_bilinear_left
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₁) (T : Module.End ℂ W)
    (hT : ∀ x y, T (B x y) = B (J x) y) (x : V₁) (y : V₂) :
    orderFourCMMinusPart T (B x y) =
      B (orderFourCMMinusPart J x) y := by
  rw [orderFourCMMinusPart, orderFourCMMinusPart]
  rw [hT, hT, hT, map_smul, map_sub, map_sub, map_add, map_smul]
  simp

/-- An equivariant bilinear map commutes with the full order-four projector in its
second variable. -/
theorem orderFourCMMinusPart_bilinear_right
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₂) (T : Module.End ℂ W)
    (hT : ∀ x y, T (B x y) = B x (J y)) (x : V₁) (y : V₂) :
    orderFourCMMinusPart T (B x y) =
      B x (orderFourCMMinusPart J y) := by
  rw [orderFourCMMinusPart, orderFourCMMinusPart]
  rw [hT, hT, hT, map_smul, map_sub, map_sub, map_add, map_smul]
  simp

end FullOrderFour

/-- The full order-four `-i` projector applied to a complexified rational class. -/
def continuousOrderFourCMMinusPart
    (X : TopCat) (n : ℕ) (f : X ⟶ X) (alpha : Cohomology ℚ X n) :
    Cohomology ℂ X n :=
  orderFourCMMinusPart (cohomologyMap ℂ n f)
    (rationalToComplexCohomologyMap X n alpha)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonzero complex `i`-eigenclass for pullback forces a rational cohomology
class with nonzero odd part for the square of the same map.  This only uses that
rational homology is detected by its algebraic dual; no finite-dimensionality or
surjectivity of coefficient extension in cohomology is needed. -/
theorem exists_rationalCohomology_odd_of_complex_I_eigen
    (X : TopCat) (n : ℕ) (f : X ⟶ X)
    (alpha : Cohomology ℂ X n) (halpha : alpha ≠ 0)
    (heigen : cohomologyMap ℂ n f alpha = Complex.I • alpha) :
    ∃ beta : Cohomology ℚ X n,
      beta - cohomologyMap ℚ n f (cohomologyMap ℚ n f beta) ≠ 0 := by
  let T : Module.End ℚ (Homology ℚ X n) := homologyMap ℚ n f
  have hperiod : complexCohomologyPeriod X n alpha ≠ 0 :=
    complexCohomologyPeriod_ne_zero X n halpha
  obtain ⟨z, hz⟩ : ∃ z : Homology ℚ X n,
      alpha (qToCHomology X n z) ≠ 0 := by
    simpa [complexCohomologyPeriod, LinearMap.ext_iff] using hperiod
  have hfirst :
      alpha (qToCHomology X n (T z)) =
        Complex.I * alpha (qToCHomology X n z) := by
    have h := LinearMap.congr_fun heigen (qToCHomology X n z)
    change alpha (homologyMap ℂ n f (qToCHomology X n z)) =
      Complex.I * alpha (qToCHomology X n z) at h
    rw [qToCHomology_naturality] at h
    simpa only [T] using h
  have hsecond :
      alpha (qToCHomology X n (T (T z))) =
        -alpha (qToCHomology X n z) := by
    have h := LinearMap.congr_fun heigen (qToCHomology X n (T z))
    change alpha (homologyMap ℂ n f (qToCHomology X n (T z))) =
      Complex.I * alpha (qToCHomology X n (T z)) at h
    rw [qToCHomology_naturality] at h
    calc
      alpha (qToCHomology X n (T (T z))) =
          Complex.I * alpha (qToCHomology X n (T z)) := by
            simpa only [T] using h
      _ = Complex.I * (Complex.I * alpha (qToCHomology X n z)) := by
            rw [hfirst]
      _ = -alpha (qToCHomology X n z) := by
            rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hoddPeriod :
      alpha (qToCHomology X n (z - T (T z))) ≠ 0 := by
    rw [map_sub, map_sub, hsecond, sub_neg_eq_add]
    simpa [two_mul] using
      (mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) hz)
  have hoddHomology : z - T (T z) ≠ 0 := by
    intro hzero
    apply hoddPeriod
    rw [hzero, map_zero, map_zero]
  obtain ⟨beta, hbeta⟩ :=
    Module.Projective.exists_dual_ne_zero ℚ hoddHomology
  refine ⟨beta, ?_⟩
  intro hzero
  have heval := LinearMap.congr_fun hzero z
  simp only [LinearMap.sub_apply, cohomologyMap_apply] at heval
  apply hbeta
  rw [map_sub]
  exact heval

/-- The full order-four minus part is nonzero as soon as `alpha - J² alpha` is nonzero.
The proof again uses rational periods and works without finite-dimensionality. -/
theorem continuousOrderFourCMMinusPart_ne_zero
    (X : TopCat) (n : ℕ) (f : X ⟶ X) (alpha : Cohomology ℚ X n)
    (hdelta : alpha - cohomologyMap ℚ n f (cohomologyMap ℚ n f alpha) ≠ 0) :
    continuousOrderFourCMMinusPart X n f alpha ≠ 0 := by
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
    (alpha - A (A alpha)) (A alpha - A (A (A alpha)))
    (by simpa [A] using hdelta)
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

/-- The full order-four projected class has eigenvalue `-i`. -/
theorem cohomologyMap_continuousOrderFourCMMinusPart
    (X : TopCat) (n : ℕ) (f : X ⟶ X) (alpha : Cohomology ℚ X n)
    (hfour : ∀ x : Cohomology ℂ X n,
      cohomologyMap ℂ n f
        (cohomologyMap ℂ n f
          (cohomologyMap ℂ n f (cohomologyMap ℂ n f x))) = x) :
    cohomologyMap ℂ n f (continuousOrderFourCMMinusPart X n f alpha) =
      -Complex.I • continuousOrderFourCMMinusPart X n f alpha := by
  exact map_orderFourCMMinusPart (cohomologyMap ℂ n f) hfour
    (rationalToComplexCohomologyMap X n alpha)

section External

/-- Apply the `-i` projector in both variables of the canonical degree-`(1,1)` external
product. -/
def continuousCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1) :
    Cohomology ℂ (X ⊗ Y) 2 :=
  degreeOneExternalCohomologyBilinear ℂ X Y
    (continuousCMMinusPart X 1 f alpha)
    (continuousCMMinusPart Y 1 g beta)

/-- The projected external class is nonzero whenever both rational factor classes are
nonzero. -/
theorem continuousCMMinusExternalClass_ne_zero
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    continuousCMMinusExternalClass X Y f g alpha beta ≠ 0 := by
  exact degreeOneExternalCohomologyBilinear_ne_zero ℂ
    (continuousCMMinusPart X 1 f alpha)
    (continuousCMMinusPart Y 1 g beta)
    (continuousCMMinusPart_ne_zero X 1 f alpha halpha)
    (continuousCMMinusPart_ne_zero Y 1 g beta hbeta)

/-- Pullback by the first-factor self-map acts by `-i` on the doubly projected class. -/
theorem firstCohomologyMap_continuousCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hsqf : ∀ x : Cohomology ℂ X 1,
      cohomologyMap ℂ 1 f (cohomologyMap ℂ 1 f x) = -x) :
    cohomologyMap ℂ 2 (f ⊗ₘ 𝟙 Y)
        (continuousCMMinusExternalClass X Y f g alpha beta) =
      -Complex.I • continuousCMMinusExternalClass X Y f g alpha beta := by
  rw [continuousCMMinusExternalClass,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply,
    cohomologyMap_continuousCMMinusPart X 1 f alpha hsqf]
  simp

/-- Pullback by the second-factor self-map acts by `-i` on the doubly projected class. -/
theorem secondCohomologyMap_continuousCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hsqg : ∀ y : Cohomology ℂ Y 1,
      cohomologyMap ℂ 1 g (cohomologyMap ℂ 1 g y) = -y) :
    cohomologyMap ℂ 2 (𝟙 X ⊗ₘ g)
        (continuousCMMinusExternalClass X Y f g alpha beta) =
      -Complex.I • continuousCMMinusExternalClass X Y f g alpha beta := by
  rw [continuousCMMinusExternalClass,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply,
    cohomologyMap_continuousCMMinusPart Y 1 g beta hsqg]
  rfl

/-- Pullback on degree-two product cohomology by a self-map in the first factor. -/
def firstFactorCohomologyEnd (X Y : TopCat) (f : X ⟶ X) :
    Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2) :=
  cohomologyMap ℂ 2 (f ⊗ₘ 𝟙 Y)

/-- Pullback on degree-two product cohomology by a self-map in the second factor. -/
def secondFactorCohomologyEnd (X Y : TopCat) (g : Y ⟶ Y) :
    Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2) :=
  cohomologyMap ℂ 2 (𝟙 X ⊗ₘ g)

/-- The sum of the two factor pullbacks.  On a Hodge decomposition for a product of CM
elliptic curves, its eigenvalues distinguish the `(2,0)`, `(1,1)`, and `(0,2)` pieces. -/
def productCMSumEnd (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y) :
    Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2) :=
  firstFactorCohomologyEnd X Y f + secondFactorCohomologyEnd X Y g

/-- The doubly projected class has eigenvalue `-2i` for the sum of the factor actions. -/
theorem productCMSumEnd_continuousCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hsqf : ∀ x : Cohomology ℂ X 1,
      cohomologyMap ℂ 1 f (cohomologyMap ℂ 1 f x) = -x)
    (hsqg : ∀ y : Cohomology ℂ Y 1,
      cohomologyMap ℂ 1 g (cohomologyMap ℂ 1 g y) = -y) :
    productCMSumEnd X Y f g
        (continuousCMMinusExternalClass X Y f g alpha beta) =
      (-2 * Complex.I) • continuousCMMinusExternalClass X Y f g alpha beta := by
  rw [productCMSumEnd, firstFactorCohomologyEnd,
    secondFactorCohomologyEnd, LinearMap.add_apply,
    firstCohomologyMap_continuousCMMinusExternalClass X Y f g alpha beta hsqf,
    secondCohomologyMap_continuousCMMinusExternalClass X Y f g alpha beta hsqg]
  module

/-! ### External product using only the order-four relation -/

/-- Apply the full order-four `-i` projector in both external-product factors. -/
def continuousOrderFourCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1) :
    Cohomology ℂ (X ⊗ Y) 2 :=
  degreeOneExternalCohomologyBilinear ℂ X Y
    (continuousOrderFourCMMinusPart X 1 f alpha)
    (continuousOrderFourCMMinusPart Y 1 g beta)

/-- The doubly projected external class is literally obtained by applying the two
factor projectors to the unprojected external product of the complexified rational
classes.  This is the polynomial identity used to transfer filtration membership. -/
theorem iteratedProductProjector_externalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1) :
    orderFourCMMinusPart (firstFactorCohomologyEnd X Y f)
        (orderFourCMMinusPart (secondFactorCohomologyEnd X Y g)
          (degreeOneExternalCohomologyBilinear ℂ X Y
            (rationalToComplexCohomologyMap X 1 alpha)
            (rationalToComplexCohomologyMap Y 1 beta))) =
      continuousOrderFourCMMinusExternalClass X Y f g alpha beta := by
  let B := degreeOneExternalCohomologyBilinear ℂ X Y
  let J₁ := cohomologyMap ℂ 1 f
  let J₂ := cohomologyMap ℂ 1 g
  have hfirst : ∀ x y,
      firstFactorCohomologyEnd X Y f (B x y) = B (J₁ x) y := by
    intro x y
    dsimp only [firstFactorCohomologyEnd, B, J₁]
    rw [degreeOneExternalCohomologyBilinear_naturality,
      cohomologyMap_id, LinearMap.id_apply]
  have hsecond : ∀ x y,
      secondFactorCohomologyEnd X Y g (B x y) = B x (J₂ y) := by
    intro x y
    dsimp only [secondFactorCohomologyEnd, B, J₂]
    rw [degreeOneExternalCohomologyBilinear_naturality,
      cohomologyMap_id, LinearMap.id_apply]
  change orderFourCMMinusPart (firstFactorCohomologyEnd X Y f)
      (orderFourCMMinusPart (secondFactorCohomologyEnd X Y g)
        (B (rationalToComplexCohomologyMap X 1 alpha)
          (rationalToComplexCohomologyMap Y 1 beta))) =
    B (orderFourCMMinusPart J₁
        (rationalToComplexCohomologyMap X 1 alpha))
      (orderFourCMMinusPart J₂
        (rationalToComplexCohomologyMap Y 1 beta))
  rw [orderFourCMMinusPart_bilinear_right B J₂
    (secondFactorCohomologyEnd X Y g) hsecond]
  rw [orderFourCMMinusPart_bilinear_left B J₁
    (firstFactorCohomologyEnd X Y f) hfirst]

/-- The product operator `(J₁ - i)(J₂ - i)` which vanishes on the first Hodge
filtration once every filtered class has at least one `i`-eigen factor. -/
def productCMDoubleMinusEnd (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y) :
    Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2) :=
  (firstFactorCohomologyEnd X Y f -
      Complex.I • LinearMap.id).comp
    (secondFactorCohomologyEnd X Y g -
      Complex.I • LinearMap.id)

/-- On a simultaneous `(-i,-i)` eigenvector, `(J₁-i)(J₂-i)` is multiplication by
`-4`. -/
theorem productCMDoubleMinusEnd_of_joint_eigen
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (w : Cohomology ℂ (X ⊗ Y) 2)
    (hfirst : firstFactorCohomologyEnd X Y f w = -Complex.I • w)
    (hsecond : secondFactorCohomologyEnd X Y g w = -Complex.I • w) :
    productCMDoubleMinusEnd X Y f g w = (-4 : ℂ) • w := by
  have hinner :
      (secondFactorCohomologyEnd X Y g -
        Complex.I • (LinearMap.id :
          Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2))) w =
        (-2 * Complex.I) • w := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hsecond]
    module
  rw [productCMDoubleMinusEnd, LinearMap.comp_apply, hinner]
  change firstFactorCohomologyEnd X Y f ((-2 * Complex.I) • w) -
      Complex.I • ((-2 * Complex.I) • w) = (-4 : ℂ) • w
  rw [map_smul, hfirst]
  simp only [smul_smul]
  have hscalar :
      (-2 * Complex.I) * (-Complex.I) -
          Complex.I * (-2 * Complex.I) = (-4 : ℂ) := by
    ring_nf
    rw [Complex.I_sq]
    norm_num
  rw [← sub_smul, hscalar]

/-- The projector numerator `1 - J²` onto the odd part of an order-four action. -/
def cmOddPartEnd {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) : Module.End ℂ W :=
  LinearMap.id - T.comp T

/-- The odd numerator followed by `T - i` is `-4i` times the full
order-four `-i` projector.  This is a polynomial identity and does not
require an order-four hypothesis. -/
theorem cmOddPartEnd_sub_I_apply
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (w : W) :
    cmOddPartEnd T
        ((T - Complex.I • (LinearMap.id : Module.End ℂ W)) w) =
      (-4 * Complex.I) • orderFourCMMinusPart T w := by
  simp only [cmOddPartEnd, orderFourCMMinusPart, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.id_apply, LinearMap.smul_apply,
    map_sub, map_smul, smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-- An equivariant bilinear map commutes with the odd-part numerator in its
first variable. -/
theorem cmOddPartEnd_bilinear_left
    {V₁ V₂ W : Type*}
    [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup W] [Module ℂ W]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₁)
    (T : Module.End ℂ W) (hT : ∀ x y, T (B x y) = B (J x) y)
    (x : V₁) (y : V₂) :
    cmOddPartEnd T (B x y) = B (cmOddPartEnd J x) y := by
  simp only [cmOddPartEnd, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, hT, map_sub]

/-- An equivariant bilinear map commutes with the odd-part numerator in its
second variable. -/
theorem cmOddPartEnd_bilinear_right
    {V₁ V₂ W : Type*}
    [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup W] [Module ℂ W]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W) (J : Module.End ℂ V₂)
    (T : Module.End ℂ W) (hT : ∀ x y, T (B x y) = B x (J y))
    (x : V₁) (y : V₂) :
    cmOddPartEnd T (B x y) = B x (cmOddPartEnd J y) := by
  simp only [cmOddPartEnd, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, hT, map_sub]

/-- The odd-part numerator acts by `2` on a `-i` eigenvector. -/
theorem cmOddPartEnd_of_negI_eigen
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (w : W) (h : T w = -Complex.I • w) :
    cmOddPartEnd T w = (2 : ℂ) • w := by
  rw [cmOddPartEnd, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, h, map_smul, h, smul_smul]
  have hscalar : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
    ring_nf
    rw [Complex.I_sq]
  rw [hscalar, neg_one_smul, sub_neg_eq_add]
  module

/-- The corrected whole-degree-two CM detector.  The odd projectors remove the
`H²⊗H⁰` and `H⁰⊗H²` summands before `(J₁-i)(J₂-i)` detects the `(-i,-i)` part. -/
def productCMOddDoubleMinusEnd
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y) :
    Module.End ℂ (Cohomology ℂ (X ⊗ Y) 2) :=
  (cmOddPartEnd (firstFactorCohomologyEnd X Y f)).comp
    ((cmOddPartEnd (secondFactorCohomologyEnd X Y g)).comp
      (productCMDoubleMinusEnd X Y f g))

/-- On a pure external class, the corrected detector is `-16` times the two
full order-four minus projectors.  No order-four relation is needed for this
polynomial identity. -/
theorem productCMOddDoubleMinusEnd_externalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℂ X 1) (beta : Cohomology ℂ Y 1) :
    productCMOddDoubleMinusEnd X Y f g
        (degreeOneExternalCohomologyBilinear ℂ X Y alpha beta) =
      (-16 : ℂ) •
        degreeOneExternalCohomologyBilinear ℂ X Y
          (orderFourCMMinusPart (cohomologyMap ℂ 1 f) alpha)
          (orderFourCMMinusPart (cohomologyMap ℂ 1 g) beta) := by
  let B := degreeOneExternalCohomologyBilinear ℂ X Y
  let J₁ := cohomologyMap ℂ 1 f
  let J₂ := cohomologyMap ℂ 1 g
  let T₁ := firstFactorCohomologyEnd X Y f
  let T₂ := secondFactorCohomologyEnd X Y g
  have hfirst : ∀ x y, T₁ (B x y) = B (J₁ x) y := by
    intro x y
    dsimp only [T₁, B, J₁, firstFactorCohomologyEnd]
    rw [degreeOneExternalCohomologyBilinear_naturality,
      cohomologyMap_id, LinearMap.id_apply]
  have hsecond : ∀ x y, T₂ (B x y) = B x (J₂ y) := by
    intro x y
    dsimp only [T₂, B, J₂, secondFactorCohomologyEnd]
    rw [degreeOneExternalCohomologyBilinear_naturality,
      cohomologyMap_id, LinearMap.id_apply]
  have hdouble :
      productCMDoubleMinusEnd X Y f g (B alpha beta) =
        B ((J₁ - Complex.I • (LinearMap.id :
            Module.End ℂ (Cohomology ℂ X 1))) alpha)
          ((J₂ - Complex.I • (LinearMap.id :
            Module.End ℂ (Cohomology ℂ Y 1))) beta) := by
    simp only [productCMDoubleMinusEnd, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hsecond, map_sub, map_smul, hfirst, hfirst]
    simp only [map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply]
    module
  rw [productCMOddDoubleMinusEnd, LinearMap.comp_apply,
    LinearMap.comp_apply, hdouble]
  rw [cmOddPartEnd_bilinear_right B J₂ T₂ hsecond]
  rw [cmOddPartEnd_bilinear_left B J₁ T₁ hfirst]
  rw [cmOddPartEnd_sub_I_apply, cmOddPartEnd_sub_I_apply]
  simp only [LinearMap.smul_apply, map_smul, smul_smul]
  dsimp only [B, J₁, J₂]
  have hscalar :
      (-4 * Complex.I) * (-4 * Complex.I) = (-16 : ℂ) := by
    ring_nf
    rw [Complex.I_sq]
    norm_num
  rw [hscalar]

/-- The corrected detector is nonzero on the unprojected external product as
soon as each rational factor has nonzero odd part. -/
theorem productCMOddDoubleMinusEnd_externalRationalClass_ne_zero
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hdeltaAlpha :
      alpha - cohomologyMap ℚ 1 f (cohomologyMap ℚ 1 f alpha) ≠ 0)
    (hdeltaBeta :
      beta - cohomologyMap ℚ 1 g (cohomologyMap ℚ 1 g beta) ≠ 0) :
    productCMOddDoubleMinusEnd X Y f g
        (degreeOneExternalCohomologyBilinear ℂ X Y
          (rationalToComplexCohomologyMap X 1 alpha)
          (rationalToComplexCohomologyMap Y 1 beta)) ≠ 0 := by
  rw [productCMOddDoubleMinusEnd_externalClass]
  apply smul_ne_zero (by norm_num)
  exact degreeOneExternalCohomologyBilinear_ne_zero ℂ
    (continuousOrderFourCMMinusPart X 1 f alpha)
    (continuousOrderFourCMMinusPart Y 1 g beta)
    (continuousOrderFourCMMinusPart_ne_zero X 1 f alpha hdeltaAlpha)
    (continuousOrderFourCMMinusPart_ne_zero Y 1 g beta hdeltaBeta)

/-- The corrected detector acts by `-16` on every simultaneous `(-i,-i)`
eigenvector. -/
theorem productCMOddDoubleMinusEnd_of_joint_eigen
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (w : Cohomology ℂ (X ⊗ Y) 2)
    (hfirst : firstFactorCohomologyEnd X Y f w = -Complex.I • w)
    (hsecond : secondFactorCohomologyEnd X Y g w = -Complex.I • w) :
    productCMOddDoubleMinusEnd X Y f g w = (-16 : ℂ) • w := by
  rw [productCMOddDoubleMinusEnd, LinearMap.comp_apply, LinearMap.comp_apply,
    productCMDoubleMinusEnd_of_joint_eigen X Y f g w hfirst hsecond,
    map_smul, cmOddPartEnd_of_negI_eigen
      (secondFactorCohomologyEnd X Y g) w hsecond,
    map_smul, map_smul, cmOddPartEnd_of_negI_eigen
      (firstFactorCohomologyEnd X Y f) w hfirst]
  module

/-- In particular, the corrected detector does not kill a nonzero simultaneous
`(-i,-i)` eigenvector. -/
theorem productCMOddDoubleMinusEnd_ne_zero_of_joint_eigen
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (w : Cohomology ℂ (X ⊗ Y) 2) (hw : w ≠ 0)
    (hfirst : firstFactorCohomologyEnd X Y f w = -Complex.I • w)
    (hsecond : secondFactorCohomologyEnd X Y g w = -Complex.I • w) :
    productCMOddDoubleMinusEnd X Y f g w ≠ 0 := by
  rw [productCMOddDoubleMinusEnd_of_joint_eigen X Y f g w hfirst hsecond]
  exact smul_ne_zero (by norm_num) hw

/-- The full order-four projected external class is nonzero whenever each rational
factor has a nonzero anti-invariant part for the square of its CM action. -/
theorem continuousOrderFourCMMinusExternalClass_ne_zero
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hdeltaAlpha :
      alpha - cohomologyMap ℚ 1 f (cohomologyMap ℚ 1 f alpha) ≠ 0)
    (hdeltaBeta :
      beta - cohomologyMap ℚ 1 g (cohomologyMap ℚ 1 g beta) ≠ 0) :
    continuousOrderFourCMMinusExternalClass X Y f g alpha beta ≠ 0 := by
  exact degreeOneExternalCohomologyBilinear_ne_zero ℂ
    (continuousOrderFourCMMinusPart X 1 f alpha)
    (continuousOrderFourCMMinusPart Y 1 g beta)
    (continuousOrderFourCMMinusPart_ne_zero X 1 f alpha hdeltaAlpha)
    (continuousOrderFourCMMinusPart_ne_zero Y 1 g beta hdeltaBeta)

/-- The first factor action has eigenvalue `-i` on the full order-four external
projector. -/
theorem firstCohomologyMap_continuousOrderFourCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hfourf : ∀ x : Cohomology ℂ X 1,
      cohomologyMap ℂ 1 f
        (cohomologyMap ℂ 1 f
          (cohomologyMap ℂ 1 f (cohomologyMap ℂ 1 f x))) = x) :
    cohomologyMap ℂ 2 (f ⊗ₘ 𝟙 Y)
        (continuousOrderFourCMMinusExternalClass X Y f g alpha beta) =
      -Complex.I •
        continuousOrderFourCMMinusExternalClass X Y f g alpha beta := by
  rw [continuousOrderFourCMMinusExternalClass,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply,
    cohomologyMap_continuousOrderFourCMMinusPart X 1 f alpha hfourf]
  simp

/-- The second factor action has eigenvalue `-i` on the full order-four external
projector. -/
theorem secondCohomologyMap_continuousOrderFourCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hfourg : ∀ y : Cohomology ℂ Y 1,
      cohomologyMap ℂ 1 g
        (cohomologyMap ℂ 1 g
          (cohomologyMap ℂ 1 g (cohomologyMap ℂ 1 g y))) = y) :
    cohomologyMap ℂ 2 (𝟙 X ⊗ₘ g)
        (continuousOrderFourCMMinusExternalClass X Y f g alpha beta) =
      -Complex.I •
        continuousOrderFourCMMinusExternalClass X Y f g alpha beta := by
  rw [continuousOrderFourCMMinusExternalClass,
    degreeOneExternalCohomologyBilinear_naturality,
    cohomologyMap_id, LinearMap.id_apply,
    cohomologyMap_continuousOrderFourCMMinusPart Y 1 g beta hfourg]
  rfl

/-- The corrected whole-degree-two detector is nonzero on the full order-four
projected external class.  This packages the exact topological conclusion needed by
a proof that the same detector annihilates the first Hodge filtration. -/
theorem productCMOddDoubleMinusEnd_continuousOrderFourCMMinusExternalClass_ne_zero
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hdeltaAlpha :
      alpha - cohomologyMap ℚ 1 f (cohomologyMap ℚ 1 f alpha) ≠ 0)
    (hdeltaBeta :
      beta - cohomologyMap ℚ 1 g (cohomologyMap ℚ 1 g beta) ≠ 0)
    (hfourf : ∀ x : Cohomology ℂ X 1,
      cohomologyMap ℂ 1 f
        (cohomologyMap ℂ 1 f
          (cohomologyMap ℂ 1 f (cohomologyMap ℂ 1 f x))) = x)
    (hfourg : ∀ y : Cohomology ℂ Y 1,
      cohomologyMap ℂ 1 g
        (cohomologyMap ℂ 1 g
          (cohomologyMap ℂ 1 g (cohomologyMap ℂ 1 g y))) = y) :
    productCMOddDoubleMinusEnd X Y f g
        (continuousOrderFourCMMinusExternalClass X Y f g alpha beta) ≠ 0 := by
  let w := continuousOrderFourCMMinusExternalClass X Y f g alpha beta
  apply productCMOddDoubleMinusEnd_ne_zero_of_joint_eigen X Y f g w
  · exact continuousOrderFourCMMinusExternalClass_ne_zero X Y f g alpha beta
      hdeltaAlpha hdeltaBeta
  · simpa only [firstFactorCohomologyEnd] using
      firstCohomologyMap_continuousOrderFourCMMinusExternalClass
        X Y f g alpha beta hfourf
  · simpa only [secondFactorCohomologyEnd] using
      secondCohomologyMap_continuousOrderFourCMMinusExternalClass
        X Y f g alpha beta hfourg

/-- Equivalently, the sum of the two factor actions has eigenvalue `-2i`. -/
theorem productCMSumEnd_continuousOrderFourCMMinusExternalClass
    (X Y : TopCat) (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology ℚ X 1) (beta : Cohomology ℚ Y 1)
    (hfourf : ∀ x : Cohomology ℂ X 1,
      cohomologyMap ℂ 1 f
        (cohomologyMap ℂ 1 f
          (cohomologyMap ℂ 1 f (cohomologyMap ℂ 1 f x))) = x)
    (hfourg : ∀ y : Cohomology ℂ Y 1,
      cohomologyMap ℂ 1 g
        (cohomologyMap ℂ 1 g
          (cohomologyMap ℂ 1 g (cohomologyMap ℂ 1 g y))) = y) :
    productCMSumEnd X Y f g
        (continuousOrderFourCMMinusExternalClass X Y f g alpha beta) =
      (-2 * Complex.I) •
        continuousOrderFourCMMinusExternalClass X Y f g alpha beta := by
  rw [productCMSumEnd, firstFactorCohomologyEnd,
    secondFactorCohomologyEnd, LinearMap.add_apply,
    firstCohomologyMap_continuousOrderFourCMMinusExternalClass
      X Y f g alpha beta hfourf,
    secondCohomologyMap_continuousOrderFourCMMinusExternalClass
      X Y f g alpha beta hfourg]
  module

end External

end AlgebraicTopology.Singular
