import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open MeasureTheory Set

namespace Jacobians

/-- Coordinate map `ℝ² → ℂ`, `(x,y) ↦ x + y·I`. -/
noncomputable def wMap (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- **Surface positivity.** If `h : ℂ → ℂ` is continuous on the closed box image and nonzero at
some point of the OPEN box, then the area integral of `‖h‖²` over the unit box is strictly
positive. -/
theorem integral_normSq_pos (h : ℂ → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => h (wMap p)) (Icc 0 1 ×ˢ Icc 0 1))
    (p₀ : ℝ × ℝ) (hp₀ : p₀ ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) (hp₀ne : h (wMap p₀) ≠ 0) :
    0 < ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wMap (x, y))‖ ^ 2 := by
  set g : ℝ × ℝ → ℝ := fun p => ‖h (wMap p)‖ ^ 2 with hg
  -- `g` is nonnegative everywhere.
  have hgnonneg : ∀ p, 0 ≤ g p := fun p => by positivity
  -- `g` is continuous on the closed box.
  have hgcont : ContinuousOn g (Icc 0 1 ×ˢ Icc 0 1) := hcont.norm.pow 2
  -- `g` is integrable on the (compact) box.
  have hgint : IntegrableOn g (Icc 0 1 ×ˢ Icc 0 1) :=
    hgcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- Convert the iterated interval integral into a set integral over the product box.
  have hconv : (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, g (x, y))
      = ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, g p := by
    have h01 : (0:ℝ) ≤ 1 := zero_le_one
    rw [show (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, g (x, y))
          = ∫ x in Icc (0:ℝ) 1, ∫ y in Icc (0:ℝ) 1, g (x, y) by
        simp only [intervalIntegral.integral_of_le, h01,
          setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]]
    exact (setIntegral_prod _ hgint).symm
  rw [show (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖h (wMap (x, y))‖ ^ 2)
        = ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, g p from hconv]
  -- Strict positivity of a set integral of a nonnegative integrable function reduces to
  -- positivity of the measure of the support inside the box.
  rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall (fun p => hgnonneg p)) hgint]
  -- `g p₀ > 0`, since `h (wMap p₀) ≠ 0`.
  have hg₀ : 0 < g p₀ := by
    have : 0 < ‖h (wMap p₀)‖ := norm_pos_iff.mpr hp₀ne
    simpa [hg] using pow_pos this 2
  -- The open box is open and `g` is continuous there.
  have hboxopen : IsOpen (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := isOpen_Ioo.prod isOpen_Ioo
  have hgcont' : ContinuousOn g (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) :=
    hgcont.mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  -- The set `V` where `g > 0` inside the open box is open, nonempty, and contained in
  -- `support g ∩ box`.
  set V : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 ∩ g ⁻¹' Set.Ioi 0 with hV
  have hVopen : IsOpen V := hgcont'.isOpen_inter_preimage hboxopen isOpen_Ioi
  have hVmem : p₀ ∈ V := ⟨hp₀, hg₀⟩
  have hVsub : V ⊆ Function.support g ∩ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    intro p hp
    refine ⟨ne_of_gt hp.2, ?_⟩
    exact ⟨Ioo_subset_Icc_self hp.1.1, Ioo_subset_Icc_self hp.1.2⟩
  calc 0 < volume V := hVopen.measure_pos volume ⟨p₀, hVmem⟩
    _ ≤ volume (Function.support g ∩ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measure_mono hVsub

end Jacobians
