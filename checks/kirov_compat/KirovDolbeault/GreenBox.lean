import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set intervalIntegral

namespace Jacobians

/-- **Green's theorem on the unit square** for a ℂ-valued `C¹` 1-form `P dx + Q dy`:
the counterclockwise boundary integral `∮_{∂[0,1]²}(P dx + Q dy)` equals
`∬_{[0,1]²} (∂Q/∂x − ∂P/∂y)`. (`P' x`, `Q' x` are the Fréchet derivatives; `_ (1,0)` / `_ (0,1)`
extract the `∂/∂x` / `∂/∂y` partials.) -/
theorem greenOnUnitBox (P Q : ℝ × ℝ → ℂ) (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ)
    (HcP : ContinuousOn P (Icc 0 1 ×ˢ Icc 0 1))
    (HcQ : ContinuousOn Q (Icc 0 1 ×ˢ Icc 0 1))
    (HdP : ∀ x ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt P (P' x) x)
    (HdQ : ∀ x ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, HasFDerivAt Q (Q' x) x)
    (Hi : IntegrableOn (fun x => Q' x (1, 0) - P' x (0, 1)) (Icc 0 1 ×ˢ Icc 0 1)) :
    ((∫ x in (0:ℝ)..1, P (x, 0)) + (∫ y in (0:ℝ)..1, Q (1, y)))
        - (∫ x in (0:ℝ)..1, P (x, 1)) - (∫ y in (0:ℝ)..1, Q (0, y))
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (Q' (x, y) (1, 0) - P' (x, y) (0, 1)) := by
  -- Domain-shape bridge: `[[0,1]] = Icc 0 1` and `Ioo (min 0 1) (max 0 1) = Ioo 0 1`.
  have huIcc : Set.uIcc (0:ℝ) 1 = Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)
  have hIoo : Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) = Ioo (0:ℝ) 1 := by
    rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  -- The continuity / differentiability / integrability hypotheses in Mathlib's
  -- `uIcc` / `Ioo (min..) (max..)` shape, for `f := Q` and `g := fun x => -P x`.
  have HcQ' : ContinuousOn Q (Set.uIcc (0:ℝ) 1 ×ˢ Set.uIcc (0:ℝ) 1) := by
    rw [huIcc]; exact HcQ
  have Hcg' : ContinuousOn (fun x => -P x) (Set.uIcc (0:ℝ) 1 ×ˢ Set.uIcc (0:ℝ) 1) := by
    rw [huIcc]; exact HcP.neg
  have HdQ' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasFDerivAt Q (Q' x) x := by
    rw [hIoo]; exact HdQ
  have Hdg' : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasFDerivAt (fun x => -P x) (-(P' x)) x := by
    rw [hIoo]; exact fun x hx => (HdP x hx).neg
  -- The integrand `Q'(1,0) + (-(P'))(0,1)` equals `Q'(1,0) - P'(0,1)` pointwise (as functions).
  have hint : (fun x => Q' x (1, 0) + (-(P' x)) (0, 1))
      = (fun x => Q' x (1, 0) - P' x (0, 1)) := by
    funext x
    simp [ContinuousLinearMap.neg_apply, sub_eq_add_neg]
  have Hi' : IntegrableOn
      (fun x => Q' x (1, 0) + (-(P' x)) (0, 1)) (Set.uIcc (0:ℝ) 1 ×ˢ Set.uIcc (0:ℝ) 1) := by
    rw [huIcc, hint]; exact Hi
  have key := integral2_divergence_prod_of_hasFDerivAt Q (fun x => -P x) Q' (fun x => -(P' x))
    0 0 1 1 HcQ' Hcg' HdQ' Hdg' Hi'
  -- Normalize the `g = -P` boundary integrals (`∫ -P = -∫ P`) and the integrand's `-P'(0,1)`.
  -- After this, `key` is exactly the `.symm` of the goal up to reassociation, closed by
  -- `linear_combination` (works over ℂ; `ring` reconciles `a - b` with `a + -b`).
  simp only [ContinuousLinearMap.neg_apply, intervalIntegral.integral_neg] at key
  linear_combination -key

end Jacobians
