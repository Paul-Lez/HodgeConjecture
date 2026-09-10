/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetEngine

/-!
# E4 planar atom: the slit-logarithm pairing integral (Forster 20.3/20.5)

The single planar computation behind the E4 pairing identity of `AB_E_ROUTE.md`: for the
one-disk tube datum `σ = H·∂̄ψ` (with `H` equal to the slit logarithm `log((ζ−b)/(ζ−a))`
wherever `∂̄ψ ≠ 0`) and a holomorphic `g`,

  `∫_ℂ H·∂̄ψ·g dA = π·(b−a)·∫₀¹ g(a + s(b−a)) ds`.

Main declarations:

* `slitLogRatio_eq_integral` — the moving-pole representation
  `log((z−b)/(z−a)) = ∫₀¹ (b−a)/(γ_s − z) ds` along `γ_s = a + s(b−a)` (FTC in the segment
  parameter; each branch value stays in the slit plane by
  `ratio_mem_slitPlane_of_notMem_segment` on the sub-segment `[γ_s, b]`).
* `integral_slitLog_dbar_mul` — **the atom**: substituting the representation and applying
  Fubini reduces each parameter slice to the Cauchy–Pompeiu area atom
  `∫ ∂̄χ/(ζ−p) dA = −π·χ(p)` (`DbarDisk.cauchyPompeiu_area`) at the moving pole `p = γ_s`,
  with `χ = ψ·g`; the slice values `π·(b−a)·g(γ_s)` integrate to the segment integral.

**Normalization bookkeeping.**  In the Lebesgue-area chart-coefficient convention of
`resIntegral` (a `(0,1)∧(1,0)` product read against `dA`, with `dz̄∧dz = 2i·dA`), Forster's
`∫∫_X σ∧α = 2πi·∫_c α` reads `∫_ℂ σ̃·g dA = π·∫_c α̃` — the `π` (not `2πi`) produced here is
correct and matches the pinned `resNormalization = −π⁻¹` of the R0 sign test.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.3 and §20.5.
-/

open Complex Filter MeasureTheory Metric Set DbarDisk
open scoped Real Topology ContDiff

noncomputable section

namespace Jacobians.Dolbeault

/-! ## `∂̄` of a locally constant function vanishes -/

/-- `∂̄f` vanishes at a point where `f` is locally constant. -/
theorem dbar_eq_zero_of_eventuallyEq_const {f : ℂ → ℂ} {c ζ : ℂ}
    (h : f =ᶠ[𝓝 ζ] fun _ => c) : DbarDisk.dbar f ζ = 0 := by
  have h0 : fderiv ℝ f ζ = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply c
  simp [DbarDisk.dbar, h0]

/-! ## The moving-pole representation of the slit logarithm -/

/-- Points of the affine parametrization lie on the segment. -/
theorem segParam_mem_segment {a b : ℂ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    a + s • (b - a) ∈ segment ℝ a b := by
  rw [segment_eq_image']
  exact ⟨s, hs, rfl⟩

/-- **The moving-pole representation of the slit logarithm**: off the segment,

  `log((z−b)/(z−a)) = ∫₀¹ (b−a)/(γ_s − z) ds`,  `γ_s = a + s(b−a)`.

FTC in the segment parameter: `s ↦ log((z−b)/(z−γ_s))` runs from the slit logarithm to
`log 1 = 0` with derivative `(b−a)/(z−γ_s)`, each value staying in the slit plane because
`z` misses the sub-segment `[γ_s, b]`. -/
theorem slitLogRatio_eq_integral {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    slitLogRatio a b z = ∫ s in (0 : ℝ)..1, (b - a) / ((a + s • (b - a)) - z) := by
  have hnb : z ≠ b := fun h => hz (h ▸ right_mem_segment ℝ a b)
  -- the running logarithm and its derivative
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.log ((z - b) / (z - (a + s • (b - a)))))
        ((b - a) / (z - (a + s • (b - a)))) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hγs : a + s • (b - a) ∈ segment ℝ a b := segParam_mem_segment hs
    have hne : z - (a + s • (b - a)) ≠ 0 :=
      sub_ne_zero.mpr fun h => hz (h ▸ hγs)
    have hden : HasDerivAt (fun s : ℝ => z - (a + s • (b - a))) (-(b - a)) s := by
      have h1 : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) s := by
        simpa using ((hasDerivAt_id s).smul_const (b - a)).const_add a
      simpa using h1.const_sub z
    have hw : HasDerivAt (fun s : ℝ => (z - b) / (z - (a + s • (b - a))))
        ((z - b) * ((b - a) / (z - (a + s • (b - a))) ^ 2)) s := by
      have hdiv := (hasDerivAt_const s (z - b)).fun_div hden hne
      convert hdiv using 1
      field_simp
      ring
    have hslit : (z - b) / (z - (a + s • (b - a))) ∈ Complex.slitPlane := by
      have hsub : segment ℝ (a + s • (b - a)) b ⊆ segment ℝ a b :=
        (convex_segment a b).segment_subset hγs (right_mem_segment ℝ a b)
      exact ratio_mem_slitPlane_of_notMem_segment fun hc => hz (hsub hc)
    have hlog := hw.clog_real hslit
    convert hlog using 1
    have hzb : z - b ≠ 0 := sub_ne_zero.mpr hnb
    field_simp
  -- integrability of the derivative
  have hint : IntervalIntegrable (fun s : ℝ => (b - a) / (z - (a + s • (b - a))))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine continuousOn_const.div ?_ ?_
    · fun_prop
    · intro s hs
      exact sub_ne_zero.mpr fun h => hz (h ▸ segParam_mem_segment hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- endpoint evaluation
  have he1 : (1 : ℝ) • (b - a) = b - a := one_smul ℝ (b - a)
  have hend1 : Complex.log ((z - b) / (z - (a + (1 : ℝ) • (b - a)))) = 0 := by
    rw [he1, show a + (b - a) = b by ring, div_self (sub_ne_zero.mpr hnb), Complex.log_one]
  have hend0 : Complex.log ((z - b) / (z - (a + (0 : ℝ) • (b - a)))) = slitLogRatio a b z := by
    rw [zero_smul, add_zero, slitLogRatio]
  rw [hend1, hend0, zero_sub] at hFTC
  -- flip the kernel sign
  have hflip : ∀ s : ℝ, (b - a) / ((a + s • (b - a)) - z)
      = -((b - a) / (z - (a + s • (b - a)))) := by
    intro s
    rw [show (a + s • (b - a)) - z = -(z - (a + s • (b - a))) by ring, div_neg]
  calc slitLogRatio a b z
      = -∫ s in (0 : ℝ)..1, (b - a) / (z - (a + s • (b - a))) := by rw [hFTC, neg_neg]
    _ = ∫ s in (0 : ℝ)..1, -((b - a) / (z - (a + s • (b - a)))) := by
        rw [intervalIntegral.integral_neg]
    _ = ∫ s in (0 : ℝ)..1, (b - a) / ((a + s • (b - a)) - z) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [hflip]

/-! ## The atom -/

/-- **The E4 planar atom** (Forster 20.3/20.5): for a smooth compactly supported cutoff `ψ`
that is `≡ 1` on a `ρ`-thickening of the segment `[a, b]` and supported inside an open set
`U` on which `g` is holomorphic, and any weight `H` that agrees with the slit logarithm
`log((ζ−b)/(ζ−a))` wherever `∂̄ψ ≠ 0`,

  `∫_ℂ H·∂̄ψ·g dA = π·(b−a)·∫₀¹ g(a + s(b−a)) ds`.

Proof: substitute the moving-pole representation `slitLogRatio_eq_integral`, swap the
integrals (the joint integrand is continuous on `[0,1] × ℂ` and supported in
`[0,1] × supp ∂̄ψ`), and evaluate each slice by the Cauchy–Pompeiu area atom
`∫ ∂̄(ψg)/(ζ−γ_s) dA = −π·ψg(γ_s) = −π·g(γ_s)`. -/
theorem integral_slitLog_dbar_mul
    {a b : ℂ} {ψC H g : ℂ → ℂ} {U : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hU : IsOpen U)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψC) (hψc : HasCompactSupport ψC)
    (hψU : tsupport ψC ⊆ U)
    (hψ1 : Set.EqOn ψC 1 (thickening ρ (segment ℝ a b)))
    (hH : ∀ ζ, DbarDisk.dbar ψC ζ ≠ 0 → H ζ = slitLogRatio a b ζ)
    (hg : DifferentiableOn ℂ g U) :
    ∫ ζ, H ζ * DbarDisk.dbar ψC ζ * g ζ
      = (π : ℂ) * (b - a) * ∫ s in (0 : ℝ)..1, g (a + s • (b - a)) := by
  classical
  set γ : ℝ → ℂ := fun s => a + s • (b - a) with hγdef
  have hγcont : Continuous γ := by fun_prop
  have hγseg : ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → γ s ∈ segment ℝ a b :=
    fun {s} hs => segParam_mem_segment hs
  have hseg_th : segment ℝ a b ⊆ thickening ρ (segment ℝ a b) :=
    self_subset_thickening hρ _
  -- analyticity of `g` on `U`
  have hgan : ∀ {ζ : ℂ}, ζ ∈ U → AnalyticAt ℂ g ζ :=
    fun {ζ} hζ => hg.analyticAt (hU.mem_nhds hζ)
  -- `∂̄ψ` vanishes on the thickening and off the support
  have hdψ_th : ∀ {ζ : ℂ}, ζ ∈ thickening ρ (segment ℝ a b) → DbarDisk.dbar ψC ζ = 0 := by
    intro ζ hζ
    refine dbar_eq_zero_of_eventuallyEq_const (c := 1) ?_
    filter_upwards [isOpen_thickening.mem_nhds hζ] with w hw
    exact hψ1 hw
  have hdψ_out : ∀ {ζ : ℂ}, ζ ∉ tsupport ψC → DbarDisk.dbar ψC ζ = 0 := by
    intro ζ hζ
    refine dbar_eq_zero_of_eventuallyEq_const (c := 0) ?_
    filter_upwards [(isClosed_tsupport ψC).isOpen_compl.mem_nhds hζ] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  -- the smeared numerator `χ = ψ·g`: smooth, compactly supported, `∂̄χ = ∂̄ψ·g`
  set χ : ℂ → ℂ := fun ζ => ψC ζ * g ζ with hχdef
  have hχzero : ∀ {ζ : ℂ}, ζ ∉ U → χ =ᶠ[𝓝 ζ] fun _ => (0 : ℂ) := by
    intro ζ hζU
    have hζs : ζ ∉ tsupport ψC := fun h => hζU (hψU h)
    filter_upwards [(isClosed_tsupport ψC).isOpen_compl.mem_nhds hζs] with w hw
    show ψC w * g w = 0
    rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
  have hχsm : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [contDiff_iff_contDiffAt]
    intro ζ
    by_cases hζU : ζ ∈ U
    · exact hψ.contDiffAt.mul (((hgan hζU).restrictScalars (𝕜 := ℝ)).contDiffAt)
    · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (hχzero hζU)
  have hχsupp : HasCompactSupport χ := hψc.mul_right
  have hχ_dbar : ∀ ζ, DbarDisk.dbar χ ζ = DbarDisk.dbar ψC ζ * g ζ := by
    intro ζ
    by_cases hζU : ζ ∈ U
    · have hgd : DifferentiableAt ℂ g ζ := (hgan hζU).differentiableAt
      have := FineResidue.dbar_mul (f := ψC) (g := g) (z := ζ)
        (hψ.differentiable (by simp) ζ) (hgd.restrictScalars ℝ)
      rw [hχdef]
      simp only at this ⊢
      rw [this, dbar_eq_zero_of_differentiableAt hgd, mul_zero, add_zero]
    · have hζs : ζ ∉ tsupport ψC := fun h => hζU (hψU h)
      rw [dbar_eq_zero_of_eventuallyEq_const (hχzero hζU), hdψ_out hζs, zero_mul]
  -- the joint kernel
  set K : ℝ → ℂ → ℂ := fun s ζ =>
    DbarDisk.dbar ψC ζ * g ζ * ((b - a) / (γ s - ζ)) with hKdef
  -- continuity of the joint kernel on `[0,1] × ℂ`
  have hKcont : ContinuousOn (Function.uncurry K)
      ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set ℂ)) := by
    intro p hp
    have hp1 : p.1 ∈ Set.Icc (0 : ℝ) 1 := hp.1
    by_cases hth : p.2 ∈ thickening ρ (segment ℝ a b)
    · -- the kernel vanishes on a neighbourhood: `∂̄ψ ≡ 0` on the open thickening
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_ |>.continuousWithinAt
      have hnb : (Set.univ ×ˢ thickening ρ (segment ℝ a b) : Set (ℝ × ℂ)) ∈ 𝓝 p :=
        (isOpen_univ.prod isOpen_thickening).mem_nhds ⟨trivial, hth⟩
      filter_upwards [hnb] with q hq
      show (0 : ℂ) = Function.uncurry K q
      rw [Function.uncurry, hKdef]
      simp only
      rw [hdψ_th hq.2, zero_mul, zero_mul]
    · by_cases hsupp : p.2 ∈ tsupport ψC
      · -- away from the segment: every factor is continuous, denominator nonzero
        have hp2U : p.2 ∈ U := hψU hsupp
        have hne : γ p.1 - p.2 ≠ 0 := by
          refine sub_ne_zero.mpr fun h => hth ?_
          exact h ▸ hseg_th (hγseg hp1)
        refine ContinuousAt.continuousWithinAt ?_
        have hc1 : ContinuousAt (fun q : ℝ × ℂ => DbarDisk.dbar ψC q.2 * g q.2)
            p := by
          exact ((continuous_dbar hψ).comp continuous_snd).continuousAt.mul
            ((hgan hp2U).continuousAt.comp continuousAt_snd)
        have hc2 : ContinuousAt (fun q : ℝ × ℂ => (b - a) / (γ q.1 - q.2)) p := by
          refine ContinuousAt.div continuousAt_const ?_ hne
          exact ((hγcont.comp continuous_fst).sub continuous_snd).continuousAt
        exact hc1.mul hc2
      · -- off the support: the kernel vanishes on a neighbourhood
        refine (continuousAt_const (y := (0 : ℂ))).congr ?_ |>.continuousWithinAt
        have hnb : (Set.univ ×ˢ (tsupport ψC)ᶜ : Set (ℝ × ℂ)) ∈ 𝓝 p :=
          (isOpen_univ.prod (isClosed_tsupport ψC).isOpen_compl).mem_nhds ⟨trivial, hsupp⟩
        filter_upwards [hnb] with q hq
        show (0 : ℂ) = Function.uncurry K q
        rw [Function.uncurry, hKdef]
        simp only
        rw [hdψ_out hq.2, zero_mul, zero_mul]
  -- the kernel vanishes off `tsupport ∂̄ψ` in the second slot
  have hKvanish : ∀ (s : ℝ) {ζ : ℂ}, ζ ∉ tsupport (DbarDisk.dbar ψC) → K s ζ = 0 := by
    intro s ζ hζ
    rw [hKdef]
    simp only
    rw [image_eq_zero_of_notMem_tsupport hζ, zero_mul, zero_mul]
  -- integrability over `[0,1] × ℂ`
  set μIcc : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμdef
  have hmeasset : MeasurableSet ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set ℂ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hprodrestrict : μIcc.prod (volume : Measure ℂ)
      = ((volume : Measure ℝ).prod (volume : Measure ℂ)).restrict
          ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set ℂ)) := by
    rw [hμdef, ← Measure.restrict_univ (μ := (volume : Measure ℂ)), Measure.prod_restrict,
      Measure.restrict_univ]
  have hdψc : HasCompactSupport (DbarDisk.dbar ψC) := hasCompactSupport_dbar hψc
  have hKcpt : IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ tsupport (DbarDisk.dbar ψC)) :=
    isCompact_Icc.prod hdψc
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn
    (hKcont.mono fun p hp => ⟨hp.1, trivial⟩)
  have hKaesm : AEStronglyMeasurable (Function.uncurry K) (μIcc.prod volume) := by
    rw [hprodrestrict]
    exact hKcont.aestronglyMeasurable hmeasset
  have hKint : Integrable (Function.uncurry K) (μIcc.prod volume) := by
    refine Integrable.mono'
      (g := fun p : ℝ × ℂ =>
        ((Set.Icc (0 : ℝ) 1) ×ˢ tsupport (DbarDisk.dbar ψC)).indicator (fun _ => C) p)
      ?_ hKaesm ?_
    · rw [integrable_indicator_iff (measurableSet_Icc.prod
        (isClosed_tsupport (DbarDisk.dbar ψC)).measurableSet)]
      have hμfin : (μIcc.prod volume)
          ((Set.Icc (0 : ℝ) 1) ×ˢ tsupport (DbarDisk.dbar ψC)) ≠ ⊤ := by
        rw [Measure.prod_prod]
        exact (ENNReal.mul_lt_top
          ((measure_mono (Set.subset_univ _)).trans_lt (by
            rw [hμdef, Measure.restrict_apply_univ]
            exact measure_Icc_lt_top))
          (IsCompact.measure_lt_top hdψc)).ne
      exact integrableOn_const hμfin
    · rw [hprodrestrict]
      refine (ae_restrict_iff' hmeasset).mpr (Eventually.of_forall ?_)
      intro p hp
      show ‖Function.uncurry K p‖
        ≤ ((Set.Icc (0 : ℝ) 1) ×ˢ tsupport (DbarDisk.dbar ψC)).indicator (fun _ => C) p
      by_cases hpK : p.2 ∈ tsupport (DbarDisk.dbar ψC)
      · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hp.1, hpK⟩)]
        exact hC p ⟨hp.1, hpK⟩
      · rw [Set.indicator_of_notMem fun hmem => hpK (Set.mem_prod.mp hmem).2]
        have h0 : Function.uncurry K p = 0 := hKvanish p.1 hpK
        rw [h0, norm_zero]
  -- Fubini
  have hswap : (∫ s, (∫ ζ, K s ζ) ∂μIcc) = ∫ ζ, (∫ s, K s ζ ∂μIcc) :=
    integral_integral_swap hKint
  -- each parameter slice is a Cauchy–Pompeiu evaluation
  have hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ ζ, K s ζ) = (π : ℂ) * (b - a) * g (γ s) := by
    intro s hs
    have hpole : γ s ∈ segment ℝ a b := hγseg hs
    have hpoint : ∀ ζ, K s ζ = -(b - a) * (DbarDisk.dbar χ ζ / (ζ - γ s)) := by
      intro ζ
      rw [hKdef]
      simp only
      rw [hχ_dbar ζ, show γ s - ζ = -(ζ - γ s) by ring, div_neg]
      ring
    calc (∫ ζ, K s ζ)
        = ∫ ζ, -(b - a) * (DbarDisk.dbar χ ζ / (ζ - γ s)) := by
          exact integral_congr_ae (Eventually.of_forall hpoint)
      _ = -(b - a) * ∫ ζ, DbarDisk.dbar χ ζ / (ζ - γ s) := integral_const_mul _ _
      _ = -(b - a) * (-(π : ℝ) * χ (γ s)) := by
          rw [cauchyPompeiu_area hχsm hχsupp (γ s)]
      _ = (π : ℂ) * (b - a) * g (γ s) := by
          have hχγ : χ (γ s) = g (γ s) := by
            rw [hχdef]
            simp only
            rw [show ψC (γ s) = 1 from hψ1 (hseg_th hpole), one_mul]
          rw [hχγ]
          ring
  -- each space slice collapses to the slit logarithm
  have hcol : ∀ ζ, (∫ s, K s ζ ∂μIcc) = H ζ * DbarDisk.dbar ψC ζ * g ζ := by
    intro ζ
    by_cases hdζ : DbarDisk.dbar ψC ζ = 0
    · have h0 : ∀ s : ℝ, K s ζ = 0 := by
        intro s
        rw [hKdef]
        simp only
        rw [hdζ, zero_mul, zero_mul]
      simp only [h0, integral_zero, hdζ, mul_zero, zero_mul]
    · have hζseg : ζ ∉ segment ℝ a b := fun hc => hdζ (hdψ_th (hseg_th hc))
      have hpull : ∀ s : ℝ, K s ζ
          = (DbarDisk.dbar ψC ζ * g ζ) * ((b - a) / (γ s - ζ)) := fun s => rfl
      have hIoc : (∫ s, (b - a) / (γ s - ζ) ∂μIcc)
          = ∫ s in (0 : ℝ)..1, (b - a) / ((a + s • (b - a)) - ζ) := by
        rw [hμdef, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      calc (∫ s, K s ζ ∂μIcc)
          = (DbarDisk.dbar ψC ζ * g ζ) * ∫ s, (b - a) / (γ s - ζ) ∂μIcc := by
            simp only [hpull]
            exact integral_const_mul _ _
        _ = (DbarDisk.dbar ψC ζ * g ζ) * slitLogRatio a b ζ := by
            rw [hIoc, ← slitLogRatio_eq_integral hζseg]
        _ = H ζ * DbarDisk.dbar ψC ζ * g ζ := by
            rw [hH ζ hdζ]
            ring
  -- assemble
  have hicc : (∫ s, g (γ s) ∂μIcc) = ∫ s in (0 : ℝ)..1, g (a + s • (b - a)) := by
    rw [hμdef, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  calc ∫ ζ, H ζ * DbarDisk.dbar ψC ζ * g ζ
      = ∫ ζ, (∫ s, K s ζ ∂μIcc) := by
        exact integral_congr_ae (Eventually.of_forall fun ζ => (hcol ζ).symm)
    _ = ∫ s, (∫ ζ, K s ζ) ∂μIcc := hswap.symm
    _ = ∫ s, (π : ℂ) * (b - a) * g (γ s) ∂μIcc := by
        refine setIntegral_congr_fun measurableSet_Icc fun s hs => hslice s hs
    _ = (π : ℂ) * (b - a) * ∫ s, g (γ s) ∂μIcc := integral_const_mul _ _
    _ = (π : ℂ) * (b - a) * ∫ s in (0 : ℝ)..1, g (a + s • (b - a)) := by rw [hicc]

end Jacobians.Dolbeault

end
