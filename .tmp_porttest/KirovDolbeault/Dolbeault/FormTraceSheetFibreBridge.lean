/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceSheetCovector
import KirovDolbeault.Dolbeault.FormTraceFibre

/-!
# The fibre-sum bridge: bundle trace ↔ planar fibre trace (Gate A step 2/3)

Building on the per-sheet covector linchpin (`FormTraceSheetCovector`) and the `localRep`
frame-transition law, this file proves the **single-sheet bridge**: the bundle pushforward summand
`sheetPullback ω₀ s y (1)` (read in the value chart) equals the *planar* `FormTraceFibre.fibreTrace`
summand `coeffAt ω₀ (xs) (sh w)·deriv(sh) w` for the `g ≡ 1` frame, where `sh` is the section read in
the **fixed** source chart at a base fibre point `xs`.

The reconciliation is the `dz`-Jacobian cancellation: the bundle summand is read in the *moving*
fibre point's own chart, the planar summand in the *fixed* `xs`-chart; the `localRep` frame-transition
law (`localRep_eq_transition_mul_self`) supplies the ratio, which the chain rule for `deriv` cancels
against the section-derivative ratio.  This is the source-chart-independence of the value-chart
`dz`-coefficient — the heart of Miranda §VIII.3's "the trace is a well-defined form".

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceSheet

open Jacobians Jacobians.Dolbeault Jacobians.Montel

set_option linter.unusedSectionVars false

variable {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Single-sheet bridge (source-chart independence of the `dz`-coefficient).**  For a bundle
section `s : Y → X` `MDifferentiable` at `y`, with the fibre point `s y` lying in the chart source of
a *fixed* base point `xs`, the bundle per-sheet covector (value chart, affine unit tangent) equals the
planar `coeffAt·deriv` summand read in the fixed `xs`-chart:

> `sheetPullback ω₀ s y 1 = coeffAt ω₀ xs (sh (chart_y y)) · deriv sh (chart_y y)`,

where `sh := chart_xs ∘ s ∘ chart_y.symm` is the section in the fixed source chart.  The proof reads
the LHS via the linchpin (`sheetPullback_one_eq_coeffAt_mul_deriv`, in the *moving* `s y`-chart), then
applies the `localRep` frame-transition law + the chain rule for `deriv` to convert to the fixed
`xs`-chart. -/
theorem sheetPullback_one_eq_fixedChart_coeffAt_mul_deriv (ω₀ : HolomorphicOneForms X) (s : Y → X)
    {y : Y} (xs : X) (hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y)
    (hmem : s y ∈ (chartAt ℂ xs).source)
    (hsh_diff : DifferentiableAt ℂ (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z)))
      ((chartAt ℂ y) y))
    (htrans_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s y)) ((chartAt ℂ xs).symm w)) ((chartAt ℂ xs) (s y))) :
    sheetPullback ω₀ s y (1 : ℂ)
      = coeffAt ω₀ xs ((fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y))
        * deriv (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y) := by
  -- Abbreviations: `P := s y` the moving fibre point; `b' := chart_y y` the base value-coord.
  set P : X := s y with hP
  set b' : ℂ := (chartAt ℂ y) y with hb'
  -- The inner planar section `sh := chart_xs ∘ s ∘ chart_y.symm`, with `sh b' = chart_xs P`.
  set sh : ℂ → ℂ := fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z)) with hsh
  have hshb' : sh b' = (chartAt ℂ xs) P := by
    simp only [hsh, hb', hP]; rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
  -- The outer chart-transition `tr := chart_P ∘ chart_xs.symm`.
  set tr : ℂ → ℂ := fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm w) with htr
  -- LHS via the linchpin (read in the *moving* `P`-chart).
  rw [sheetPullback_one_eq_coeffAt_mul_deriv ω₀ s hs, coeffAt_chartCenter]
  -- RHS coefficient: `coeffAt ω₀ xs (chart_xs P) = localRep ω₀ xs P`, then the frame-transition.
  have hRHScoeff : coeffAt ω₀ xs ((chartAt ℂ xs) P) = Jacobians.Montel.localRep ω₀ xs P := by
    rw [coeffAt]; congr 1; exact (chartAt ℂ xs).left_inv hmem
  rw [hshb', hRHScoeff, localRep_eq_transition_mul_self ω₀ xs P hmem]
  -- The chain-rule identity: `chart_P ∘ s ∘ chart_y.symm =ᶠ[𝓝 b'] tr ∘ sh` near `b'`
  -- (since `chart_xs.symm ∘ chart_xs = id` near `P`, `s` continuous), so its `deriv` factors.
  have hsymm_b' : (chartAt ℂ y).symm b' = y := by
    rw [hb']; exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hcomp_eq : (fun z => (chartAt ℂ (s y)) (s ((chartAt ℂ y).symm z))) =ᶠ[𝓝 b'] tr ∘ sh := by
    -- `s ∘ chart_y.symm` is continuous at `b'` and maps `b' ↦ P ∈ chart_xs.source`.
    have hsymm_cont : ContinuousAt (chartAt ℂ y).symm b' := by
      have hb'_tgt : b' ∈ (chartAt ℂ y).target := by
        rw [hb']; exact (chartAt ℂ y).map_source (mem_chart_source ℂ y)
      exact ((chartAt ℂ y).continuousOn_symm).continuousAt
        ((chartAt ℂ y).open_target.mem_nhds hb'_tgt)
    have hcont : ContinuousAt (fun z => s ((chartAt ℂ y).symm z)) b' := by
      refine ContinuousAt.comp ?_ hsymm_cont
      rw [hsymm_b']; exact hs.continuousAt
    have hval : (fun z => s ((chartAt ℂ y).symm z)) b' = P := by
      simp only [hP]; rw [hsymm_b']
    have hpre : ∀ᶠ z in 𝓝 b', s ((chartAt ℂ y).symm z) ∈ (chartAt ℂ xs).source :=
      hcont.eventually_mem (by simp only [hval]; exact (chartAt ℂ xs).open_source.mem_nhds hmem)
    filter_upwards [hpre] with z hz
    show (chartAt ℂ (s y)) (s ((chartAt ℂ y).symm z))
        = (chartAt ℂ P) ((chartAt ℂ xs).symm ((chartAt ℂ xs) (s ((chartAt ℂ y).symm z))))
    rw [(chartAt ℂ xs).left_inv hz]
  rw [hcomp_eq.deriv_eq]
  -- Chain rule for `tr ∘ sh` at `b'`, with `sh b' = chart_xs P`.
  rw [deriv_comp b' (by rw [hshb']; exact htrans_diff) hsh_diff, hshb']
  ring

/-! ### The `g`-weighted single-sheet bridge (the `fibreTrace` summand)

`α = ω₀·g` is meromorphic, so the `g`-weight rides per-sheet inside the coefficient
`coeff i = chartIntegrand ω₀ g (xs i)`.  The `g`-weighted bundle summand is the holomorphic
per-sheet covector times the per-sheet scalar `g (s y)` (the value of `g` at the fibre point); it
equals the planar `FormTraceFibre.chartIntegrand·deriv` summand. -/

/-- **`g`-weighted single-sheet bridge.**  The holomorphic per-sheet bundle covector
`sheetPullback ω₀ s y 1` weighted by `g (s y)` (the value of `g` at the fibre point) equals the
planar `FormTraceFibre.fibreTrace` summand `chartIntegrand ω₀ g xs (sh w)·deriv(sh) w` for the section
`sh := chart_xs ∘ s ∘ chart_y.symm` read in the fixed `xs`-chart.  This is
`sheetPullback_one_eq_fixedChart_coeffAt_mul_deriv` multiplied by the per-sheet `g`-scalar, with
`chartIntegrand ω₀ g xs (sh b') = coeffAt ω₀ xs (sh b')·g (s y)` (the `g`-pullback at `chart_xs.symm
(sh b') = s y`). -/
theorem g_weighted_sheetPullback_eq_chartIntegrand_mul_deriv (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (s : Y → X) {y : Y} (xs : X) (hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y)
    (hmem : s y ∈ (chartAt ℂ xs).source)
    (hsh_diff : DifferentiableAt ℂ (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z)))
      ((chartAt ℂ y) y))
    (htrans_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s y)) ((chartAt ℂ xs).symm w)) ((chartAt ℂ xs) (s y))) :
    g (s y) * sheetPullback ω₀ s y (1 : ℂ)
      = Jacobians.Dolbeault.FormTraceFibre.chartIntegrand ω₀ g xs
          ((fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y))
        * deriv (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y) := by
  rw [sheetPullback_one_eq_fixedChart_coeffAt_mul_deriv ω₀ s xs hs hmem hsh_diff htrans_diff]
  -- `chartIntegrand ω₀ g xs (sh b') = coeffAt ω₀ xs (sh b') · g (chart_xs.symm (sh b'))`, and
  -- `chart_xs.symm (sh b') = chart_xs.symm (chart_xs (s y)) = s y`.
  have hshb' : (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y)
      = (chartAt ℂ xs) (s y) := by
    show (chartAt ℂ xs) (s ((chartAt ℂ y).symm ((chartAt ℂ y) y))) = _
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
  rw [Jacobians.Dolbeault.FormTraceFibre.chartIntegrand, hshb',
    (chartAt ℂ xs).left_inv hmem]
  ring

/-! ### Uniqueness of the holomorphic local inverse (section identification core, step 2 (A))

The planar section `exists_planar_section` (the `fibreTrace` sheet) and the chart-representation of a
bundle sheet are *both* right-inverses of the same chart map `φ` (analytic, `deriv ≠ 0`) through the
same point.  By uniqueness of the holomorphic local inverse they germ-agree — the section
identification half of step 2.  We prove the clean planar uniqueness here. -/

/-- **Uniqueness of the holomorphic local inverse (germ form).**  If `φ` is analytic at `x₀` with
`deriv φ x₀ ≠ 0` and `φ x₀ = b`, then any two continuous right-inverses `s₁`, `s₂` of `φ` through `x₀`
(`sₖ b = x₀`, `φ (sₖ w) = w` near `b`, `sₖ` continuous at `b`) germ-agree near `b`:
`s₁ =ᶠ[𝓝 b] s₂`.  Both equal the canonical `localInverse` near `b` (via
`HasStrictDerivAt.eventually_left_inverse` composed with the right-inverse property). -/
theorem eventuallyEq_of_rightInverse_of_rightInverse {φ s₁ s₂ : ℂ → ℂ} {x₀ b : ℂ}
    (hφ : AnalyticAt ℂ φ x₀) (hφ' : deriv φ x₀ ≠ 0) (_hb : φ x₀ = b)
    (hs₁b : s₁ b = x₀) (hs₂b : s₂ b = x₀)
    (hs₁c : ContinuousAt s₁ b) (hs₂c : ContinuousAt s₂ b)
    (hrinv₁ : ∀ᶠ w in 𝓝 b, φ (s₁ w) = w) (hrinv₂ : ∀ᶠ w in 𝓝 b, φ (s₂ w) = w) :
    s₁ =ᶠ[𝓝 b] s₂ := by
  -- The canonical local inverse `L` of `φ` at `x₀`; `L (φ x) = x` near `x₀`.
  have hsd : HasStrictDerivAt φ (deriv φ x₀) x₀ := hφ.hasStrictDerivAt
  set L : ℂ → ℂ := hsd.localInverse φ (deriv φ x₀) x₀ hφ' with hL
  have hLleft : ∀ᶠ x in 𝓝 x₀, L (φ x) = x := hsd.eventually_left_inverse hφ'
  -- Each `sₖ w = L (φ (sₖ w)) = L w` near `b`: pull the left-inverse back through `sₖ` (continuous,
  -- `sₖ b = x₀`), then use the right-inverse `φ (sₖ w) = w`.
  have hkey : ∀ {s : ℂ → ℂ}, s b = x₀ → ContinuousAt s b → (∀ᶠ w in 𝓝 b, φ (s w) = w) →
      s =ᶠ[𝓝 b] L := by
    intro s hsb hsc hrinv
    have hsLleft : ∀ᶠ w in 𝓝 b, L (φ (s w)) = s w :=
      hsc.eventually (p := fun x => L (φ x) = x) (by rw [hsb]; exact hLleft)
    filter_upwards [hsLleft, hrinv] with w hw hrw
    rw [← hw, hrw]
  exact (hkey hs₁b hs₁c hrinv₁).trans (hkey hs₂b hs₂c hrinv₂).symm

/-- **The `fibreTrace` planar sheet is *the* local inverse (germ).**  The `FormTraceFibre.fibreTrace`
sheet `i` (the `exists_planar_section` inverse of the chart pullback `φ = f.holoRepr ∘ chart_{xs i}.symm`)
germ-equals any continuous right-inverse `s` of `φ` through `chart_{xs i}(xs i)`:

> `(fibreTrace ω₀ f D).sheet i =ᶠ[𝓝 b] s`,

provided `s (b) = chart_{xs i}(xs i)`, `s` continuous at `b`, and `φ (s w) = w` near `b` (where
`b = f.holoRepr (xs i)`).  Direct from `eventuallyEq_of_rightInverse_of_rightInverse`: the planar sheet
*is* such a right-inverse (its `exists_planar_section` spec), so any other one agrees.  This is the
**section identification** — the bridge from the abstract `Classical.choose` planar sheet to the
chart-representation of a bundle sheet (which, being a section of `F`, is such a right-inverse). -/
theorem fibreTrace_sheet_eventuallyEq (ω₀ : HolomorphicOneForms X) {g : X → ℂ}
    (f : MeromorphicFunction X)
    {b : ℂ} (D : Jacobians.Dolbeault.FormTraceFibre.FibreRegularData g f b) (i : D.ι)
    {s : ℂ → ℂ} (hsb : s b = (chartAt ℂ (D.xs i)) (D.xs i)) (hsc : ContinuousAt s b)
    (hrinv : ∀ᶠ w in 𝓝 b,
      (fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z)) (s w) = w) :
    (Jacobians.Dolbeault.FormTraceFibre.fibreTrace ω₀ f D).sheet i =ᶠ[𝓝 b] s := by
  -- The planar sheet's `exists_planar_section` spec.
  set spec := Classical.choose_spec
    (Jacobians.Dolbeault.FormTraceFibre.exists_planar_section (D.hg_an i) (D.hg_deriv i)
      (D.gval ω₀ f i)) with hspec
  -- Apply uniqueness: both the planar sheet and `s` are right-inverses of `φ` through `x₀`.
  refine eventuallyEq_of_rightInverse_of_rightInverse (φ := fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z))
    (x₀ := (chartAt ℂ (D.xs i)) (D.xs i)) (b := b) (D.hg_an i) (D.hg_deriv i) (D.gval ω₀ f i)
    spec.2.1 hsb spec.1.continuousAt hsc spec.2.2.2 hrinv

end Jacobians.Dolbeault.FormTraceSheet
