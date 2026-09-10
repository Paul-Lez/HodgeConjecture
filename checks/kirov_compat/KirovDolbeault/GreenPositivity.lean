import KirovDolbeault.GreenBox
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Green positivity bridge

This file proves the pointwise/integral identity underlying the period-lattice positivity
build: for `h` holomorphic on an open `U ⊇ [0,1]²` (the unit box identified with a square in
`ℂ` via `(x,y) ↦ x + y·I`) and `F` a primitive of `h`, the area integral of `‖h‖²` over the
box equals `−(I/2)` times the boundary integral of the `1`-form `F̄ · h dz`.

The mathematical content is Green's theorem applied to `P dx + Q dy` with
`P p = conj(F(w p))·h(w p)`, `Q p = I·P p`, for which the pointwise key cancellation is
`∂Q/∂x − ∂P/∂y = 2I·‖h(w p)‖²`.

The Green's theorem on the unit square (`Jacobians.greenOnUnitBox`) is supplied by
`Jacobians.GreenBox`.
-/

open MeasureTheory Set intervalIntegral Complex

namespace Jacobians

/-- Coordinate map `ℝ² → ℂ`, `(x,y) ↦ x + y·I`, packaged as an ℝ-linear continuous map
(it is `Complex.equivRealProdCLM.symm`). -/
noncomputable def wCLM : (ℝ × ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm

@[simp] lemma wCLM_apply (p : ℝ × ℝ) : wCLM p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I :=
  Complex.equivRealProdCLM_symm_apply p

@[simp] lemma wCLM_one_zero : wCLM (1, 0) = 1 := by simp

@[simp] lemma wCLM_zero_one : wCLM (0, 1) = Complex.I := by simp

/-- `z · conj z = (‖z‖² : ℂ)`. -/
lemma mul_conj_self_eq_normSq (z : ℂ) : z * (starRingEnd ℂ) z = (‖z‖ ^ 2 : ℂ) := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

section GreenPositivity

variable (h F : ℂ → ℂ)

/-- The `dx`-component `P = F̄(w ·) · h(w ·)`. -/
noncomputable def Pfun : ℝ × ℝ → ℂ := fun p => (starRingEnd ℂ) (F (wCLM p)) * h (wCLM p)

/-- The `dy`-component `Q = I · P`. -/
noncomputable def Qfun : ℝ × ℝ → ℂ := fun p => Complex.I * Pfun h F p

/-- The Fréchet derivative of `P` (the product rule output for `F̄(w·) · h(w·)`), where the
`F`-factor's `ℂ`-derivative is `h(w p)` (since `F' = h`) and the `h`-factor's is `deriv h (w p)`. -/
noncomputable def Pder : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℂ := fun p =>
  (starRingEnd ℂ) (F (wCLM p)) • (deriv h (wCLM p) • wCLM)
    + h (wCLM p) • (Complex.conjCLE.toContinuousLinearMap.comp (h (wCLM p) • wCLM))

/-- The Fréchet derivative of `Q = I · P`, namely `I • P'`. -/
noncomputable def Qder : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℂ := fun p => Complex.I • Pder h F p

variable {h F}

/-- `P` is real-differentiable at `p` with derivative `Pder h F p`, provided `h` and `F` have the
expected complex derivatives at `w p` (`F' = h`, `h' = deriv h`). -/
lemma hasFDerivAt_Pfun {p : ℝ × ℝ}
    (hFp : HasDerivAt F (h (wCLM p)) (wCLM p))
    (hhp : HasDerivAt h (deriv h (wCLM p)) (wCLM p)) :
    HasFDerivAt (Pfun h F) (Pder h F p) p := by
  -- derivative of `F ∘ w`
  have hFcomp : HasFDerivAt (fun q => F (wCLM q)) (h (wCLM p) • wCLM) p :=
    hFp.comp_hasFDerivAt p wCLM.hasFDerivAt
  -- derivative of `conj ∘ F ∘ w`
  have hconjF : HasFDerivAt (fun q => (starRingEnd ℂ) (F (wCLM q)))
      (Complex.conjCLE.toContinuousLinearMap.comp (h (wCLM p) • wCLM)) p := by
    have := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hFcomp
    simpa using this
  -- derivative of `h ∘ w`
  have hhcomp : HasFDerivAt (fun q => h (wCLM q)) (deriv h (wCLM p) • wCLM) p :=
    hhp.comp_hasFDerivAt p wCLM.hasFDerivAt
  -- product rule
  have hP := hconjF.mul hhcomp
  exact hP

/-- `Q = I · P` is real-differentiable at `p` with derivative `Qder h F p = I • Pder h F p`. -/
lemma hasFDerivAt_Qfun {p : ℝ × ℝ}
    (hFp : HasDerivAt F (h (wCLM p)) (wCLM p))
    (hhp : HasDerivAt h (deriv h (wCLM p)) (wCLM p)) :
    HasFDerivAt (Qfun h F) (Qder h F p) p :=
  (hasFDerivAt_Pfun hFp hhp).const_mul Complex.I

/-- The first partial of `P`: `∂P/∂x = ‖h‖² + F̄ · h'`. -/
lemma Pder_one_zero (p : ℝ × ℝ) :
    Pder h F p (1, 0)
      = (‖h (wCLM p)‖ ^ 2 : ℂ) + (starRingEnd ℂ) (F (wCLM p)) * deriv h (wCLM p) := by
  simp only [Pder]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, wCLM_one_zero, smul_eq_mul, mul_one,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  rw [mul_conj_self_eq_normSq]
  ring

/-- The second partial of `P`: `∂P/∂y = −I·‖h‖² + I·F̄·h'`. -/
lemma Pder_zero_one (p : ℝ × ℝ) :
    Pder h F p (0, 1)
      = -Complex.I * (‖h (wCLM p)‖ ^ 2 : ℂ)
        + Complex.I * ((starRingEnd ℂ) (F (wCLM p)) * deriv h (wCLM p)) := by
  simp only [Pder]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, wCLM_zero_one, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, Complex.conj_I]
  rw [show h (wCLM p) * ((starRingEnd ℂ) (h (wCLM p)) * -Complex.I)
        = (h (wCLM p) * (starRingEnd ℂ) (h (wCLM p))) * -Complex.I from by ring,
    mul_conj_self_eq_normSq]
  ring

/-- The first partial of `Q`: `∂Q/∂x = I · ∂P/∂x`. -/
lemma Qder_one_zero (p : ℝ × ℝ) :
    Qder h F p (1, 0) = Complex.I * (Pder h F p (1, 0)) := by
  simp [Qder]

/-- **Key cancellation:** `∂Q/∂x − ∂P/∂y = 2I · ‖h(w p)‖²`. -/
lemma integrand_eq (p : ℝ × ℝ) :
    Qder h F p (1, 0) - Pder h F p (0, 1) = 2 * Complex.I * (‖h (wCLM p)‖ ^ 2 : ℂ) := by
  rw [Qder_one_zero, Pder_one_zero, Pder_zero_one]
  ring

variable {U : Set ℂ}

/-- Points of the closed box map into `U` (via `hbox`). -/
lemma wCLM_mem_of_mem_box (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    {p : ℝ × ℝ} (hp : p ∈ Icc (0 : ℝ × ℝ) 1) : wCLM p ∈ U := by
  apply hbox
  refine ⟨p, ?_, rfl⟩
  rw [Set.Icc_prod_eq] at hp
  exact hp

/-- `P` is continuous on the closed box (from continuity of `h`, `F` on `U`). -/
lemma continuousOn_Pfun (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) :
    ContinuousOn (Pfun h F) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hcont : ContinuousOn (Pfun h F) (Icc (0 : ℝ × ℝ) 1) := by
    intro p hp
    have hwU : wCLM p ∈ U := wCLM_mem_of_mem_box hbox hp
    have hch : ContinuousAt h (wCLM p) := (hh _ hwU).continuousAt
    have hcF : ContinuousAt F (wCLM p) := (hF _ hwU).continuousAt
    have hcw : ContinuousAt wCLM p := wCLM.continuous.continuousAt
    have : ContinuousAt (Pfun h F) p := by
      apply ContinuousAt.mul
      · exact (Complex.continuous_conj.continuousAt).comp (hcF.comp hcw)
      · exact hch.comp hcw
    exact this.continuousWithinAt
  rwa [Set.Icc_prod_eq] at hcont

/-- `Q = I · P` is continuous on the closed box. -/
lemma continuousOn_Qfun (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) :
    ContinuousOn (Qfun h F) (Icc 0 1 ×ˢ Icc 0 1) :=
  continuousOn_const.mul (continuousOn_Pfun hbox hh hF)

/-- `‖h(w ·)‖²` (as a ℂ-valued function) is continuous on the closed box. -/
lemma continuousOn_normSq (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z) :
    ContinuousOn (fun p : ℝ × ℝ => (‖h (wCLM p)‖ ^ 2 : ℂ)) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (‖h (wCLM p)‖ ^ 2 : ℂ)) (Icc (0 : ℝ × ℝ) 1) := by
    intro p hp
    have hwU : wCLM p ∈ U := wCLM_mem_of_mem_box hbox hp
    have hch : ContinuousAt h (wCLM p) := (hh _ hwU).continuousAt
    have hcw : ContinuousAt wCLM p := wCLM.continuous.continuousAt
    have : ContinuousAt (fun p : ℝ × ℝ => (‖h (wCLM p)‖ ^ 2 : ℂ)) p :=
      (((Complex.continuous_ofReal.continuousAt).comp (hch.comp hcw).norm).pow 2)
    exact this.continuousWithinAt
  rwa [Set.Icc_prod_eq] at hcont

/-- The Green integrand `∂Q/∂x − ∂P/∂y` is integrable on the closed box. -/
lemma integrableOn_integrand (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z) :
    IntegrableOn (fun p => Qder h F p (1, 0) - Pder h F p (0, 1)) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hcont : ContinuousOn (fun p => Qder h F p (1, 0) - Pder h F p (0, 1))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (continuousOn_const.mul (continuousOn_normSq hbox hh)).congr (fun p _ => integrand_eq p)
  exact hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- **Green positivity bridge.** For `h` holomorphic on an open `U ⊇ [0,1]²` (the box embedded in
`ℂ` via `wCLM (x,y) = x + y·I`) with primitive `F` (`F' = h`), the area integral of `‖h‖²` over
the box equals `−(I/2)` times the boundary integral `∮_{∂box} F̄ · h dz`. -/
theorem integral_normSq_eq_boundary {U : Set ℂ} (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ z ∈ U, HasDerivAt h (deriv h z) z)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ))
      = -(Complex.I / 2) *
        (((∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 0))) * h (wCLM (x, 0)))
            + Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
          - (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 1))) * h (wCLM (x, 1)))
          - Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y))) := by
  have hmem : ∀ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, wCLM p ∈ U := by
    intro p hp
    refine wCLM_mem_of_mem_box hbox ?_
    rw [Set.Icc_prod_eq]
    exact ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
  have hdP : ∀ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt (Pfun h F) (Pder h F p) p :=
    fun p hp => hasFDerivAt_Pfun (hF _ (hmem p hp)) (hh _ (hmem p hp))
  have hdQ : ∀ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt (Qfun h F) (Qder h F p) p :=
    fun p hp => hasFDerivAt_Qfun (hF _ (hmem p hp)) (hh _ (hmem p hp))
  have hgreen := greenOnUnitBox (Pfun h F) (Qfun h F) (Pder h F) (Qder h F)
    (continuousOn_Pfun hbox hh hF) (continuousOn_Qfun hbox hh hF) hdP hdQ
    (integrableOn_integrand hbox hh)
  -- Rewrite the area integral of the Green integrand as `2I · ∬ ‖h‖²`.
  have hinner : (fun x : ℝ => ∫ y in (0:ℝ)..1, (Qder h F (x, y) (1, 0) - Pder h F (x, y) (0, 1)))
      = (fun x : ℝ => 2 * Complex.I * ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ)) := by
    funext x
    rw [intervalIntegral.integral_congr
          (g := fun y => 2 * Complex.I * (‖h (wCLM (x, y))‖ ^ 2 : ℂ)) (fun y _ => integrand_eq (x, y))]
    exact intervalIntegral.integral_const_mul _ _
  have hRHS : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (Qder h F (x, y) (1, 0) - Pder h F (x, y) (0, 1)))
      = 2 * Complex.I * ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (‖h (wCLM (x, y))‖ ^ 2 : ℂ) := by
    rw [hinner]
    exact intervalIntegral.integral_const_mul _ _
  -- Rewrite the boundary integral, pulling `I` out of the vertical edges and unfolding `Pfun/Qfun`.
  have hLHS : ((∫ x in (0:ℝ)..1, Pfun h F (x, 0)) + ∫ y in (0:ℝ)..1, Qfun h F (1, y))
        - (∫ x in (0:ℝ)..1, Pfun h F (x, 1)) - ∫ y in (0:ℝ)..1, Qfun h F (0, y)
      = ((∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 0))) * h (wCLM (x, 0)))
            + Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
          - (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (x, 1))) * h (wCLM (x, 1)))
          - Complex.I * ∫ y in (0:ℝ)..1, (starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y)) := by
    simp only [Pfun, Qfun]
    rw [show (∫ y in (0:ℝ)..1,
            Complex.I * ((starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y))))
          = Complex.I * ∫ y in (0:ℝ)..1, ((starRingEnd ℂ) (F (wCLM (1, y))) * h (wCLM (1, y)))
        from intervalIntegral.integral_const_mul _ _,
       show (∫ y in (0:ℝ)..1,
            Complex.I * ((starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y))))
          = Complex.I * ∫ y in (0:ℝ)..1, ((starRingEnd ℂ) (F (wCLM (0, y))) * h (wCLM (0, y)))
        from intervalIntegral.integral_const_mul _ _]
  rw [hRHS, hLHS] at hgreen
  -- hgreen : boundary = 2I · ∬‖h‖².  Conclude ∬‖h‖² = -(I/2)·boundary.
  rw [hgreen]
  have h2I : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
    rw [show (2 : ℂ) * Complex.I = Complex.I * 2 from by ring]
    field_simp
    rw [Complex.I_sq]; ring
  rw [← mul_assoc, h2I, one_mul]

end GreenPositivity

end Jacobians
