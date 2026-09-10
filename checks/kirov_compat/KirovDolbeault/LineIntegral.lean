import KirovDolbeault.HolomorphicForms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Line integral of a holomorphic 1-form along a smooth path

Defines

  `∫_γ α := ∫ t in 0..1, α(γ t) (γ'(t)) dt`

for `γ : ℝ → X` a path into a compact connected complex 1-manifold and
`α : HolomorphicOneForms X`.

## Base-field workaround

`mfderiv` expects the source and target manifolds to share a base field.
For `γ : ℝ → X` (real source, complex target), we bypass this by
computing `γ'(t)` **via a chart**:

  `γ'(t) ≈ fderiv ℝ ((chartAt ℂ (γ t)).toFun ∘ γ) t 1 : ℂ`

The value of this expression is the "complex speed of `γ` at `t`",
expressed in the local chart around `γ t`. It coincides with the
intrinsic tangent vector modulo the chart identification
`TangentSpace 𝓘(ℂ) (γ t) = ℂ` that Mathlib uses.

Chart-independence of the line integral (the full "intrinsic"
well-definedness) is a TODO(math).

## References

Forster §§10–12; Miranda Ch. 4 §§3–4.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open MeasureTheory Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Complex speed of `γ` at `t`, expressed in the chart around `γ t`. -/
noncomputable def pathSpeed (γ : ℝ → X) (t : ℝ) : ℂ :=
  fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1

/-- Line integral of a holomorphic 1-form `α` along a smooth path `γ`.

`∫_γ α := ∫ t in 0..1, α(γ t)(γ'(t))`, where `γ'(t)` is computed via
`pathSpeed`. -/
noncomputable def lineIntegral (α : HolomorphicOneForms X) (γ : ℝ → X) : ℂ :=
  ∫ t in (0 : ℝ)..1, α.toFun (γ t) (pathSpeed γ t)

/-! ### Phase 1a of the Abel–Jacobi plan: vector line integral -/

/-- Vector line integral of a tuple of holomorphic 1-forms along `γ`.
The building block for the "period map" `Fin (kirovGenus X) → ℂ` whose
image (over closed loops at a basepoint) is the period lattice. -/
noncomputable def lineIntegralVec {n : ℕ} (forms : Fin n → HolomorphicOneForms X)
    (γ : ℝ → X) : Fin n → ℂ :=
  fun i => lineIntegral (forms i) γ

@[simp]
theorem lineIntegralVec_apply {n : ℕ} (forms : Fin n → HolomorphicOneForms X)
    (γ : ℝ → X) (i : Fin n) :
    lineIntegralVec forms γ i = lineIntegral (forms i) γ := rfl

/-! ### Phase 1b: linearity of the line integral in the form

Immediate from pointwise addition/scalar action on `ContMDiffSection`
sections and `intervalIntegral` linearity. The algebraic identities
are stated; integrability hypotheses are passed in for `lineIntegral_add`
(a separate technical lemma, "smooth path ⇒ continuous integrand ⇒
integrable on [0,1]", will add a hypothesis-free variant once the
path-regularity infrastructure is built out). -/

/-- `lineIntegral (0 : HOF X) γ = 0`. -/
theorem lineIntegral_zero (γ : ℝ → X) :
    lineIntegral (0 : HolomorphicOneForms X) γ = 0 := by
  unfold lineIntegral
  have h_zero : ∀ t : ℝ,
      (0 : HolomorphicOneForms X).toFun (γ t) (pathSpeed γ t) = 0 := fun _ => rfl
  simp_rw [h_zero]
  exact intervalIntegral.integral_zero

/-- Additivity of `lineIntegral` in the form, under integrability. -/
theorem lineIntegral_add (α β : HolomorphicOneForms X) (γ : ℝ → X)
    (hα : IntervalIntegrable (fun t : ℝ => α.toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1)
    (hβ : IntervalIntegrable (fun t : ℝ => β.toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1) :
    lineIntegral (α + β) γ = lineIntegral α γ + lineIntegral β γ := by
  unfold lineIntegral
  have h_pw : ∀ t : ℝ,
      (α + β).toFun (γ t) (pathSpeed γ t) =
        α.toFun (γ t) (pathSpeed γ t) + β.toFun (γ t) (pathSpeed γ t) := fun _ => rfl
  simp_rw [h_pw]
  exact intervalIntegral.integral_add hα hβ

/-- Scalar-homogeneity of `lineIntegral` in the form. -/
theorem lineIntegral_smul (c : ℂ) (α : HolomorphicOneForms X) (γ : ℝ → X) :
    lineIntegral (c • α) γ = c * lineIntegral α γ := by
  unfold lineIntegral
  have h_pw : ∀ t : ℝ,
      (c • α).toFun (γ t) (pathSpeed γ t) = c * α.toFun (γ t) (pathSpeed γ t) := by
    intro t
    show (c • α.toFun (γ t)) (pathSpeed γ t) = _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [h_pw]
  exact intervalIntegral.integral_const_mul c _

/-- Negation: `lineIntegral (-α) γ = -lineIntegral α γ`. -/
theorem lineIntegral_neg (α : HolomorphicOneForms X) (γ : ℝ → X) :
    lineIntegral (-α) γ = -lineIntegral α γ := by
  have h : -α = (-1 : ℂ) • α := by rw [neg_smul, one_smul]
  rw [h, lineIntegral_smul]; ring

/-! ### Phase 1b: constant path

Classical fact: the line integral of any holomorphic 1-form along a
constant path is zero. The tangent vector of a constant curve is
zero; a linear form evaluated at zero is zero; the integrand is
identically zero; its integral is zero. -/

/-- `pathSpeed (fun _ => P) t = 0`: the tangent of a constant curve
is zero. Chart pullback of a constant map is constant in ℂ, whose
fderiv is zero. -/
theorem pathSpeed_const (P : X) (t : ℝ) :
    pathSpeed (fun _ : ℝ => P) t = 0 := by
  unfold pathSpeed
  have h_const : (chartAt (H := ℂ) P).toFun ∘ (fun _ : ℝ => P) =
      fun _ : ℝ => (chartAt (H := ℂ) P) P := by
    funext s; rfl
  rw [h_const, fderiv_fun_const]
  rfl

/-- **Line integral of any form along a constant path is zero.** -/
theorem lineIntegral_const (α : HolomorphicOneForms X) (P : X) :
    lineIntegral α (fun _ : ℝ => P) = 0 := by
  unfold lineIntegral
  -- integrand: α.toFun P (pathSpeed (fun _ => P) t) = α.toFun P 0 = 0.
  have h_zero : ∀ t : ℝ,
      α.toFun ((fun _ : ℝ => P) t) (pathSpeed (fun _ : ℝ => P) t) = 0 := by
    intro t
    rw [pathSpeed_const]
    exact (α.toFun P).map_zero
  simp_rw [h_zero]
  exact intervalIntegral.integral_zero

/-! ### Phase 1b: path reversal

`reverse γ t := γ (1 - t)`, and the line integral flips sign under
reversal. The pathSpeed identity `pathSpeed (reverse γ) t =
-pathSpeed γ (1 - t)` holds under differentiability of the chart
pullback at `1 - t`. -/

/-- Time-reversal of a path: `reverse γ t := γ (1 - t)`. -/
def reverse (γ : ℝ → X) : ℝ → X := fun t => γ (1 - t)

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
@[simp] theorem reverse_apply (γ : ℝ → X) (t : ℝ) :
    reverse γ t = γ (1 - t) := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] in
/-- pathSpeed under reversal: sign flip + reparametrization. Requires
chart-pullback `(chartAt ℂ (γ(1-t))).toFun ∘ γ` to be differentiable
at `1 - t` (which holds for smooth γ at points in the chart source). -/
theorem pathSpeed_reverse (γ : ℝ → X) (t : ℝ)
    (hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    pathSpeed (reverse γ) t = -pathSpeed γ (1 - t) := by
  unfold pathSpeed
  -- reverse γ t = γ (1 - t), so chartAt at (reverse γ t) = chartAt at (γ (1 - t)).
  show fderiv ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ (reverse γ)) t (1 : ℝ) =
    -fderiv ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t) (1 : ℝ)
  -- (chartAt).toFun ∘ (reverse γ) = (chartAt).toFun ∘ γ ∘ (1 - ·)
  set ψ : ℝ → ℂ := (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ with hψ
  have h_comp : (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ (reverse γ) =
      ψ ∘ (fun s : ℝ => 1 - s) := by
    funext s; simp [reverse, hψ, Function.comp_def]
  rw [h_comp]
  -- Chain rule: fderiv (ψ ∘ (1-·)) t 1 = fderiv ψ (1-t) (fderiv (1-·) t 1).
  have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t :=
    (differentiableAt_const _).sub differentiableAt_id
  rw [fderiv_comp t hdiff h_sub_diff]
  -- fderiv (1-·) t applied at 1 = -1 (the derivative of `1 - s` is `-1`).
  have h_fderiv_sub : fderiv ℝ (fun s : ℝ => 1 - s) t (1 : ℝ) = (-1 : ℝ) := by
    rw [fderiv_const_sub]; simp
  show (fderiv ℝ ψ (1 - t)) (fderiv ℝ (fun s : ℝ => 1 - s) t 1) = -fderiv ℝ ψ (1 - t) 1
  rw [h_fderiv_sub]
  rw [show ((fderiv ℝ ψ (1 - t)) (-1 : ℝ) : ℂ) = -fderiv ℝ ψ (1 - t) (1 : ℝ) from by
    rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, (fderiv ℝ ψ (1 - t)).map_neg]]

/-- Line integral reverses sign under path reversal, under
differentiability of the chart pullback on [0, 1]. -/
theorem lineIntegral_reverse (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    lineIntegral α (reverse γ) = -lineIntegral α γ := by
  unfold lineIntegral
  -- α.toFun((reverse γ) t)(pathSpeed (reverse γ) t) = -α.toFun(γ(1-t))(pathSpeed γ(1-t)).
  have h_pw : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      α.toFun ((reverse γ) t) (pathSpeed (reverse γ) t) =
        -α.toFun (γ (1 - t)) (pathSpeed γ (1 - t)) := by
    intro t ht
    rw [reverse_apply, pathSpeed_reverse γ t (hdiff t ht)]
    exact (α.toFun (γ (1 - t))).map_neg _
  rw [intervalIntegral.integral_congr h_pw, intervalIntegral.integral_neg]
  -- ∫_0^1 α(γ(1-t))(pathSpeed γ(1-t)) dt = ∫_0^1 α(γ u)(pathSpeed γ u) du
  -- via substitution u = 1 - t.
  congr 1
  have h_sub := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => α.toFun (γ u) (pathSpeed γ u)) 1 (a := 0) (b := 1)
  simp at h_sub
  exact h_sub

/-! ### Phase 1b: path concatenation

`concat γ γ'` traverses `γ` on `[0, 1/2]` and `γ'` on `[1/2, 1]`,
each at double speed. The line integral adds. -/

/-- Concatenation of paths: `concat γ γ' t := γ(2t)` on `[0, 1/2]`,
`γ'(2t - 1)` on `[1/2, 1]`. Typical basepoint-matching requirement
`γ 1 = γ' 0` is not enforced in the definition itself (it's needed
for the concatenation to be continuous at `t = 1/2`, which is
assumed when invoking `lineIntegral_concat`). -/
noncomputable def concat (γ γ' : ℝ → X) : ℝ → X :=
  fun t => if t ≤ 1/2 then γ (2 * t) else γ' (2 * t - 1)

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
theorem concat_apply_left (γ γ' : ℝ → X) {t : ℝ} (ht : t ≤ 1/2) :
    concat γ γ' t = γ (2 * t) := if_pos ht

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
theorem concat_apply_right (γ γ' : ℝ → X) {t : ℝ} (ht : ¬ t ≤ 1/2) :
    concat γ γ' t = γ' (2 * t - 1) := if_neg ht

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] in
/-- pathSpeed of `concat γ γ'` on the strict left half: equals
`2 * pathSpeed γ (2t)` via chain rule on `γ ∘ (2·)`. -/
theorem pathSpeed_concat_left (γ γ' : ℝ → X) (t : ℝ) (ht : t < 1/2)
    (hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (2 * t))).toFun ∘ γ) (2 * t)) :
    pathSpeed (concat γ γ') t = 2 * pathSpeed γ (2 * t) := by
  unfold pathSpeed
  -- concat γ γ' t = γ (2 * t) for t ≤ 1/2.
  have ht_le : t ≤ 1/2 := le_of_lt ht
  have h_pt : concat γ γ' t = γ (2 * t) := concat_apply_left γ γ' ht_le
  show fderiv ℝ ((chartAt (H := ℂ) (concat γ γ' t)).toFun ∘ (concat γ γ')) t (1 : ℝ) =
    2 * fderiv ℝ ((chartAt (H := ℂ) (γ (2 * t))).toFun ∘ γ) (2 * t) (1 : ℝ)
  -- chartAt at concat γ γ' t = chartAt at γ(2t) via h_pt.
  rw [h_pt]
  -- In a neighborhood of t (t < 1/2), concat γ γ' s = γ (2*s). Use fderiv locality.
  set ψ : ℝ → ℂ := (chartAt (H := ℂ) (γ (2 * t))).toFun ∘ γ with hψ
  -- Claim: (chartAt ...).toFun ∘ (concat γ γ') = ψ ∘ (2·) in a nbhd of t.
  have h_eventually : (chartAt (H := ℂ) (γ (2 * t))).toFun ∘ (concat γ γ') =ᶠ[nhds t]
      ψ ∘ (fun s : ℝ => 2 * s) := by
    have h_open : IsOpen (Set.Iio (1/2 : ℝ)) := isOpen_Iio
    have ht_mem : t ∈ Set.Iio (1/2 : ℝ) := ht
    filter_upwards [h_open.mem_nhds ht_mem] with s hs
    simp only [Function.comp_apply, hψ]
    rw [concat_apply_left γ γ' (le_of_lt hs)]
  -- fderiv is local:
  rw [Filter.EventuallyEq.fderiv_eq h_eventually]
  -- Now apply chain rule to ψ ∘ (2·).
  have h_mul_diff : DifferentiableAt ℝ (fun s : ℝ => 2 * s) t :=
    (differentiableAt_const (2 : ℝ)).mul differentiableAt_id
  rw [fderiv_comp t hdiff h_mul_diff]
  -- fderiv (2·) t 1 = 2.
  have h_fderiv_mul : fderiv ℝ (fun s : ℝ => 2 * s) t (1 : ℝ) = (2 : ℝ) := by
    rw [fderiv_const_mul differentiableAt_id]; simp
  show (fderiv ℝ ψ (2 * t)) (fderiv ℝ (fun s : ℝ => 2 * s) t 1) = 2 * fderiv ℝ ψ (2 * t) 1
  rw [h_fderiv_mul]
  -- (fderiv ℝ ψ (2t)) 2 = 2 * (fderiv ℝ ψ (2t)) 1 via ℝ-linearity on CLM.
  have h_smul_eq : (2 : ℝ) = (2 : ℝ) • (1 : ℝ) := by rw [smul_eq_mul, mul_one]
  calc (fderiv ℝ ψ (2 * t)) (2 : ℝ)
      = (fderiv ℝ ψ (2 * t)) ((2 : ℝ) • (1 : ℝ)) := by rw [← h_smul_eq]
    _ = (2 : ℝ) • (fderiv ℝ ψ (2 * t)) 1 :=
        (fderiv ℝ ψ (2 * t)).map_smul (2 : ℝ) (1 : ℝ)
    _ = 2 * (fderiv ℝ ψ (2 * t)) 1 := by rw [Complex.real_smul]; push_cast; ring

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] in
/-- pathSpeed of `concat γ γ'` on the strict right half: equals
`2 * pathSpeed γ' (2t - 1)` via chain rule on `γ' ∘ (2·-1)`. -/
theorem pathSpeed_concat_right (γ γ' : ℝ → X) (t : ℝ) (ht : 1/2 < t)
    (hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ' (2 * t - 1))).toFun ∘ γ') (2 * t - 1)) :
    pathSpeed (concat γ γ') t = 2 * pathSpeed γ' (2 * t - 1) := by
  unfold pathSpeed
  have ht_nle : ¬ t ≤ 1/2 := not_le.mpr ht
  have h_pt : concat γ γ' t = γ' (2 * t - 1) := concat_apply_right γ γ' ht_nle
  show fderiv ℝ ((chartAt (H := ℂ) (concat γ γ' t)).toFun ∘ (concat γ γ')) t (1 : ℝ) =
    2 * fderiv ℝ ((chartAt (H := ℂ) (γ' (2 * t - 1))).toFun ∘ γ') (2 * t - 1) (1 : ℝ)
  rw [h_pt]
  set ψ' : ℝ → ℂ := (chartAt (H := ℂ) (γ' (2 * t - 1))).toFun ∘ γ' with hψ'
  have h_eventually : (chartAt (H := ℂ) (γ' (2 * t - 1))).toFun ∘ (concat γ γ') =ᶠ[nhds t]
      ψ' ∘ (fun s : ℝ => 2 * s - 1) := by
    have h_open : IsOpen (Set.Ioi (1/2 : ℝ)) := isOpen_Ioi
    have ht_mem : t ∈ Set.Ioi (1/2 : ℝ) := ht
    filter_upwards [h_open.mem_nhds ht_mem] with s hs
    simp only [Function.comp_apply, hψ']
    rw [concat_apply_right γ γ' (not_le.mpr hs)]
  rw [Filter.EventuallyEq.fderiv_eq h_eventually]
  have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 2 * s - 1) t :=
    ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id).sub (differentiableAt_const _)
  rw [fderiv_comp t hdiff h_sub_diff]
  have h_fderiv_sub_mul : fderiv ℝ (fun s : ℝ => 2 * s - 1) t (1 : ℝ) = (2 : ℝ) := by
    rw [show (fun s : ℝ => 2 * s - 1) = (fun s : ℝ => 2 * s + (-1)) from by funext s; ring]
    rw [fderiv_add_const, fderiv_const_mul differentiableAt_id]; simp
  show (fderiv ℝ ψ' (2 * t - 1)) (fderiv ℝ (fun s : ℝ => 2 * s - 1) t 1) =
    2 * fderiv ℝ ψ' (2 * t - 1) 1
  rw [h_fderiv_sub_mul]
  have h_smul_eq : (2 : ℝ) = (2 : ℝ) • (1 : ℝ) := by rw [smul_eq_mul, mul_one]
  calc (fderiv ℝ ψ' (2 * t - 1)) (2 : ℝ)
      = (fderiv ℝ ψ' (2 * t - 1)) ((2 : ℝ) • (1 : ℝ)) := by rw [← h_smul_eq]
    _ = (2 : ℝ) • (fderiv ℝ ψ' (2 * t - 1)) 1 :=
        (fderiv ℝ ψ' (2 * t - 1)).map_smul (2 : ℝ) (1 : ℝ)
    _ = 2 * (fderiv ℝ ψ' (2 * t - 1)) 1 := by rw [Complex.real_smul]; push_cast; ring

/-- Left half of the concat integral, reparametrized to `lineIntegral α γ`. -/
private lemma lineIntegral_concat_left (α : HolomorphicOneForms X) (γ γ' : ℝ → X)
    (_hint_γ : IntervalIntegrable
      (fun u : ℝ => α.toFun (γ u) (pathSpeed γ u)) volume 0 1)
    (h_ae : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) (1/2))),
      α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * α.toFun (γ (2 * t)) (pathSpeed γ (2 * t))) :
    ∫ t in (0 : ℝ)..(1/2), α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
      lineIntegral α γ := by
  unfold lineIntegral
  -- Substitution u = 2x: smul_integral_comp_mul_add signature `c • ∫ x in a..b, f (c*x+d) = ...`.
  -- With c = 2, d = 0, a = 0, b = 1/2: `2 • ∫ x in 0..(1/2), f (2*x+0) = ∫ in 0..1, f x`.
  have h_sub_raw := @intervalIntegral.smul_integral_comp_mul_add _ _ _ (0 : ℝ) (1/2 : ℝ)
    (fun u : ℝ => α.toFun (γ u) (pathSpeed γ u)) 2 0
  -- Normalize: 2 * x + 0 → 2 * x, endpoints 0+2*0 → 0, 0+2*(1/2) → 1.
  have h_sub : (2 : ℝ) • ∫ t in (0 : ℝ)..(1/2),
      α.toFun (γ (2 * t)) (pathSpeed γ (2 * t)) =
      ∫ t in (0 : ℝ)..1, α.toFun (γ t) (pathSpeed γ t) := by
    have : (fun x : ℝ => α.toFun (γ (2 * x + 0)) (pathSpeed γ (2 * x + 0))) =
        fun x : ℝ => α.toFun (γ (2 * x)) (pathSpeed γ (2 * x)) := by
      funext x; rw [add_zero]
    rw [this] at h_sub_raw
    have h_endpt1 : (2 : ℝ) * 0 + 0 = 0 := by norm_num
    have h_endpt2 : (2 : ℝ) * ((1 : ℝ)/2) + 0 = 1 := by norm_num
    rw [h_endpt1, h_endpt2] at h_sub_raw
    exact h_sub_raw
  -- Convert ℝ-smul to ℂ-mul.
  have h_sub_mul : (2 : ℂ) * ∫ t in (0 : ℝ)..(1/2),
      α.toFun (γ (2 * t)) (pathSpeed γ (2 * t)) =
      ∫ t in (0 : ℝ)..1, α.toFun (γ t) (pathSpeed γ t) := by
    rw [← h_sub, Complex.real_smul]; push_cast; ring
  calc ∫ t in (0 : ℝ)..(1/2), α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t)
      = ∫ t in (0 : ℝ)..(1/2),
          (2 : ℂ) * α.toFun (γ (2 * t)) (pathSpeed γ (2 * t)) :=
        intervalIntegral.integral_congr_ae_restrict h_ae
    _ = (2 : ℂ) * ∫ t in (0 : ℝ)..(1/2),
          α.toFun (γ (2 * t)) (pathSpeed γ (2 * t)) :=
        intervalIntegral.integral_const_mul _ _
    _ = ∫ t in (0 : ℝ)..1, α.toFun (γ t) (pathSpeed γ t) := h_sub_mul

/-- Right half of the concat integral, reparametrized to `lineIntegral α γ'`. -/
private lemma lineIntegral_concat_right (α : HolomorphicOneForms X) (γ γ' : ℝ → X)
    (_hint_γ' : IntervalIntegrable
      (fun u : ℝ => α.toFun (γ' u) (pathSpeed γ' u)) volume 0 1)
    (h_ae : ∀ᵐ t ∂(volume.restrict (Set.uIoc ((1 : ℝ)/2) 1)),
      α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * α.toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1))) :
    ∫ t in ((1 : ℝ)/2)..1, α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
      lineIntegral α γ' := by
  unfold lineIntegral
  -- Substitution u = 2x - 1.
  have h_sub := @intervalIntegral.smul_integral_comp_mul_sub _ _ _ ((1 : ℝ)/2) 1
    (fun u : ℝ => α.toFun (γ' u) (pathSpeed γ' u)) 2 1
  have h_endpt0 : ((2 : ℝ) * ((1 : ℝ)/2) - 1 : ℝ) = 0 := by norm_num
  have h_endpt1 : ((2 : ℝ) * 1 - 1 : ℝ) = 1 := by norm_num
  rw [h_endpt0, h_endpt1] at h_sub
  calc ∫ t in ((1 : ℝ)/2)..1,
        α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t)
      = ∫ t in ((1 : ℝ)/2)..1,
          (2 : ℂ) * α.toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1)) :=
        intervalIntegral.integral_congr_ae_restrict h_ae
    _ = (2 : ℂ) * ∫ t in ((1 : ℝ)/2)..1,
          α.toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1)) :=
        intervalIntegral.integral_const_mul _ _
    _ = ∫ t in (0 : ℝ)..1, α.toFun (γ' t) (pathSpeed γ' t) := h_sub

/-- **Concatenation identity for the line integral.**
`lineIntegral α (concat γ γ') = lineIntegral α γ + lineIntegral α γ'`
assuming smoothness of each half in the chart pullback, the matching
condition at `t = 1/2`, and integrability / pointwise identities
expressing `pathSpeed (concat)` via the chain rule on each half. -/
theorem lineIntegral_concat (α : HolomorphicOneForms X) (γ γ' : ℝ → X)
    (hint_γ : IntervalIntegrable
      (fun u : ℝ => α.toFun (γ u) (pathSpeed γ u)) volume 0 1)
    (hint_γ' : IntervalIntegrable
      (fun u : ℝ => α.toFun (γ' u) (pathSpeed γ' u)) volume 0 1)
    (hint_concat_left : IntervalIntegrable
      (fun t : ℝ => α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t))
      volume 0 (1/2))
    (hint_concat_right : IntervalIntegrable
      (fun t : ℝ => α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t))
      volume (1/2) 1)
    (h_ae_left : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) (1/2))),
      α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * α.toFun (γ (2 * t)) (pathSpeed γ (2 * t)))
    (h_ae_right : ∀ᵐ t ∂(volume.restrict (Set.uIoc ((1 : ℝ)/2) 1)),
      α.toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * α.toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1))) :
    lineIntegral α (concat γ γ') = lineIntegral α γ + lineIntegral α γ' := by
  have h_left := lineIntegral_concat_left α γ γ' hint_γ h_ae_left
  have h_right := lineIntegral_concat_right α γ γ' hint_γ' h_ae_right
  unfold lineIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_concat_left hint_concat_right]
  unfold lineIntegral at h_left h_right
  rw [h_left, h_right]

/-! ### Phase 1c: chart-local path independence — removed

A previously-stated `lineIntegral_eq_of_chart_local` asserted
path-independence of `lineIntegral α` for two smooth paths whose
images lie within a single chart source. That statement, as given,
is *not provable*: `chartAt x₀` in a `ChartedSpace ℂ X` may have a
non-simply-connected target (e.g., an annulus), in which case
holomorphic integration is not path-independent.

The statement had zero call sites in the project. Removed rather
than repaired (a provable version would need an additional
`Convex` / `SimplyConnected` hypothesis on the chart-image region,
and downstream consumers do not exist yet). If such a consumer
appears later, reinstate with the stronger hypothesis and prove via
`Complex.DifferentiableOn.isExactOn_ball` + endpoint evaluation. -/

/-! ### Phase 4 support: change of variables for the line integral

The pullback-of-forms interacts with the line integral via
`∫_{f ∘ γ} α = ∫_γ (pullbackForm f hf α)`. This is the analytic
identity underlying "the image of a loop has the same period
vector as the loop itself, up to the pullback matrix" — the basic
mechanism that makes `ambientPhi` preserve the period lattice.

**Proof decomposition.** The full lemma follows from a single
pointwise identity:
```
pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t)
```
combined with the definition of `pullbackForm` (which inserts
`mfderiv f` into the integrand), and `intervalIntegral.integral_congr`.

The pointwise identity is the chart-level chain rule transported
through the base-field workaround (`pathSpeed` is defined via
`fderiv ℝ` on chart pullbacks, while `mfderiv` uses `fderiv ℂ` on
`writtenInExtChartAt`). The bridge goes via:
1. Chart-pullback chain rule: `fderiv ℝ (chart_Y ∘ f ∘ γ) t 1
   = (fderiv ℝ f_loc (chart_X (γ t))) (pathSpeed γ t)` where
   `f_loc = chart_Y ∘ f ∘ chart_X.symm`.
2. `fderiv ℝ f_loc = (fderiv ℂ f_loc).restrictScalars ℝ` (since `f`
   is holomorphic).
3. `fderiv ℂ f_loc (chart_X (γ t)) = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t)`
   (via `MDifferentiableAt.mfderiv`). -/

/-- **Core pointwise identity** for the chain rule. Under
differentiability of `γ` in the chart pullback at `t` (i.e., γ is
C¹-smooth in chart coordinates at `t`) and smoothness of `f`, the
tangent of `f ∘ γ` at `t` equals the manifold derivative `mfderiv f`
applied to the tangent of `γ` at `t`.

The proof (complete below) is a three-step chart computation:
1. Chart-pullback chain rule: `fderiv ℝ (chart_Y ∘ f ∘ γ) t 1 =
   (fderiv ℝ f_loc (chart_X (γ t))) (pathSpeed γ t)` via
   `fderiv.comp` on `f_loc ∘ (chart_X ∘ γ)` where `f_loc = chart_Y ∘
   f ∘ chart_X.symm`.
2. `fderiv ℝ f_loc = (fderiv ℂ f_loc).restrictScalars ℝ` via
   `HasFDerivAt.restrictScalars`.
3. `fderiv ℂ f_loc (chart_X (γ t)) = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t)` via
   `MDifferentiableAt.mfderiv` + `writtenInExtChartAt` unfolding. -/
theorem pathSpeed_comp_eq_mfderiv
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X) (t : ℝ)
    (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t) := by
  -- Abbreviations
  set φ_X := chartAt (H := ℂ) (γ t) with hφ_X_def
  set φ_Y := chartAt (H := ℂ) (f (γ t)) with hφ_Y_def
  -- Local representation of f: ℂ → ℂ
  set f_loc : ℂ → ℂ := fun z => φ_Y (f (φ_X.symm z)) with hf_loc_def
  -- Chart pullbacks of γ and (f ∘ γ)
  set g_X : ℝ → ℂ := φ_X.toFun ∘ γ with hg_X_def
  set g_Y : ℝ → ℂ := φ_Y.toFun ∘ (f ∘ γ) with hg_Y_def
  -- Step 1: Key membership facts.
  have hγt_X : γ t ∈ φ_X.source := mem_chart_source ℂ (γ t)
  have hfγt_Y : f (γ t) ∈ φ_Y.source := mem_chart_source ℂ (f (γ t))
  -- Step 2: γ s ∈ φ_X.source for s near t.
  have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
    hγ_cont.eventually (φ_X.open_source.mem_nhds hγt_X)
  -- Step 3: g_Y s = (f_loc ∘ g_X) s for s near t.
  have h_eq : g_Y =ᶠ[𝓝 t] f_loc ∘ g_X := by
    filter_upwards [hγ_source] with s hs
    -- LHS: g_Y s = φ_Y (f (γ s))
    -- RHS: (f_loc ∘ g_X) s = f_loc (g_X s) = φ_Y (f (φ_X.symm (φ_X (γ s))))
    simp only [hg_Y_def, hf_loc_def, hg_X_def, Function.comp_apply]
    congr 2
    exact (φ_X.left_inv hs).symm
  -- Step 4: f_loc is ℂ-differentiable at g_X t (from f smoothness).
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (γ t) :=
    hf.mdifferentiableAt (by decide : ω ≠ 0)
  have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  -- Step 5: ℝ-differentiability of f_loc, bypassing the ℝ/ℂ diamond.
  -- `HasFDerivAt.restrictScalars ℝ` would close this, but Lean can't
  -- synthesize `IsScalarTower ℝ ℂ ℂ` in this context (Complex's module
  -- diamond). We construct the ℝ-`HasFDerivAt` manually from
  -- `IsLittleO` — the underlying asymptotic is the same, only the
  -- CLM's scalar-structure tag differs (via `ContinuousLinearMap.restrictScalars`).
  have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
    hf_loc_diff_ℂ.hasFDerivAt
  have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
      ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hf_loc_hasFD_ℂ
  have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
    hf_loc_hasFD_ℝ.differentiableAt
  have hf_loc_fderiv_ℝ : fderiv ℝ f_loc (g_X t) =
      (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ :=
    hf_loc_hasFD_ℝ.fderiv
  -- Step 6: Chain rule for fderiv ℝ of f_loc ∘ g_X at t.
  have h_chain : fderiv ℝ (f_loc ∘ g_X) t =
      (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) :=
    fderiv_comp t hf_loc_diff_ℝ hγ_diff
  -- Step 7: mfderiv f (γ t) = fderiv ℂ f_loc (g_X t).
  have h_mfderiv : mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) = fderiv ℂ f_loc (g_X t) := by
    rw [hf_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    -- Need: fderiv ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) (γ t) f) ((extChartAt 𝓘(ℂ) (γ t)) (γ t))
    --     = fderiv ℂ f_loc (g_X t)
    -- These are equal up to definitional unfolding (writtenInExtChartAt = f_loc, extChartAt x x = g_X t).
    congr 1
  -- Step 8: Assemble.
  -- pathSpeed (f ∘ γ) t
  --   = fderiv ℝ g_Y t 1                                    (unfold)
  --   = fderiv ℝ (f_loc ∘ g_X) t 1                          (by h_eq.fderiv_eq)
  --   = (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) 1    (chain rule)
  --   = fderiv ℝ f_loc (g_X t) (pathSpeed γ t)
  --   = (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ (pathSpeed γ t)  (hf_loc_fderiv_ℝ)
  --   = fderiv ℂ f_loc (g_X t) (pathSpeed γ t)              (restrictScalars_apply)
  --   = mfderiv f (γ t) (pathSpeed γ t)                     (h_mfderiv.symm)
  show pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t)
  rw [h_mfderiv]
  -- Goal: pathSpeed (f ∘ γ) t = fderiv ℂ f_loc (g_X t) (pathSpeed γ t)
  show fderiv ℝ ((chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ)) t 1 =
    fderiv ℂ f_loc (g_X t) (pathSpeed γ t)
  -- (f ∘ γ) t = f (γ t), so chartAt (f ∘ γ) t = chartAt (f (γ t)) = φ_Y
  have h_gY : (chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ) = g_Y := rfl
  rw [h_gY, h_eq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
      hf_loc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
  rfl

/-- **Change of variables for the line integral** (classical).
Derived from `pathSpeed_comp_eq_mfderiv` + the definition of
`pullbackForm` + `intervalIntegral.integral_congr`.

The `hγ_diff` hypothesis — `γ` is C¹-smooth in chart pullbacks for
`t ∈ [0, 1]` — is the usual path-regularity required for line
integrals to behave sensibly. For smooth closed loops (the use case
in the period lattice), this holds automatically. -/
theorem lineIntegral_pullback
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (α : HolomorphicOneForms Y) (γ : ℝ → X)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    lineIntegral α (f ∘ γ) = lineIntegral (pullbackForm f hf α) γ := by
  unfold lineIntegral
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  show α.toFun (f (γ t)) (pathSpeed (f ∘ γ) t) =
    (α.toFun (f (γ t))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t)) (pathSpeed γ t)
  rw [ContinuousLinearMap.comp_apply,
    pathSpeed_comp_eq_mfderiv f hf γ t hγ_cont.continuousAt (hγ_diff t ht)]

end Jacobians
