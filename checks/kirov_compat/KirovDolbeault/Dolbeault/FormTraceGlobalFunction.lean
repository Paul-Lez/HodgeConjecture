/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceFibre

/-!
# The global trace function `Tr_F α` and its holomorphy off the exceptional set (Gate A, §VIII.3)

This file builds **steps 1–2** of the Miranda §VIII.3 trace-rationality programme (the deep core of
`Jacobians.Dolbeault.FormTraceGlobalConstruct.TraceRationalityWitness`):

1. **The local trace germ at a regular value.** Given a regular non-pole point `x₀` of the cover
   `F = f.toRiemannSphere` (chart-pullback of `f.holoRepr` analytic, nonzero derivative) over which
   `g`'s chart-pullback is analytic, the per-sheet pushforward of `α = ω₀·g` — read entirely in the
   value chart at `b = f.holoRepr x₀` via the planar section germ (`exists_planar_section`,
   `FormTraceFibre`) — is itself **analytic in the base coordinate**.  This is the per-sheet content
   of Miranda's trace `Tr_F α`.

2. **Holomorphy off the exceptional set.** The finite sum of these regular-sheet pushforwards over a
   regular fibre is analytic at the regular base value.  Off the (finite) exceptional set
   `criticalValues f ∪ poleValues ∪ {∞}`, the trace coefficient `Tr_F α` is therefore holomorphic.

This is the genuinely-analytic foundational layer the trace-rationality witness is assembled on; it
reuses the proven per-fibre Lemma 3.2 (`FormTraceFibre`) and the now-unconditional residue
change-of-variables (`MeromorphicTrace.residueChangeOfVariables`).  The remaining content (the global
trace as a single meromorphic function, its rationality on the compact `ℂℙ¹`, and Lemma 3.2 at `∞`)
sits on top of this; see the diagnosis at the bottom of the file and
`Jacobians.Dolbeault.FormTraceGlobalConstruct`.

## The design — read everything in the value chart at `b`

The single per-sheet pushforward of `α = ω₀·g` along a section `s : ℂ → ℂ` (the planar inverse of the
chart-pullback of `f`, `s b = pre`, `deriv s b ≠ 0`) is
`w ↦ (coeffAt ω₀ x₀ (s w) · g (chart_x₀⁻¹ (s w))) · deriv s w`,
the pushforward of the chart integrand `chartIntegrand ω₀ g x₀` (`FormTraceFibre`).  When the chart
integrand is **analytic** at `pre = s b` (i.e. `g`'s chart-pullback is analytic there — `x₀` a
non-pole of `α`), this is a composition of analytics times the analytic section derivative, hence
analytic at `b`.  Summing over the (finite) regular fibre gives the local trace coefficient, analytic
at `b`.  This is step 2: `Tr_F α` is holomorphic at every regular value off the poles of `α`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; rationality
  on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1 — the regular-sheet pushforward is analytic in the base

The atom: pushing the chart integrand of `α = ω₀·g` forward along the planar section germ `s` of a
regular non-pole point is analytic at the base value `b`, provided `g`'s chart-pullback is *analytic*
(not merely meromorphic) at the source point — i.e. `α = ω₀·g` is holomorphic there, the defining
condition of a regular value off the poles. -/

/-- **The chart integrand of `α = ω₀·g` is analytic at the chart image of a non-pole point.**  When
`g`'s chart-pullback is analytic at `chart_a a` (so `α·g` has no pole at `a`), the chart integrand
`chartIntegrand ω₀ g a = coeffAt ω₀ a · (g ∘ chart_a⁻¹)` is analytic there (the product of the
analytic coefficient `coeffAt_analyticAt` with the analytic `g`-pullback). -/
theorem analyticAt_chartIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    AnalyticAt ℂ (chartIntegrand ω₀ g a) ((chartAt ℂ a) a) := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
    (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  exact (coeffAt_analyticAt ω₀ a hmem).mul hg

/-- **Step 1 — the regular-sheet pushforward is analytic at the base.**  For a planar section germ
`s` (analytic at `b`, `s b = c`) and a chart integrand `φ` analytic at `c = s b`, the per-sheet
pushforward `w ↦ φ (s w) · deriv s w` of `α = ω₀·g` is analytic at `b`.  (Composition of the analytic
`φ` with the analytic section `s`, times the analytic section derivative `deriv s`.) -/
theorem analyticAt_sheetPushforward {φ s : ℂ → ℂ} {b c : ℂ}
    (hφ : AnalyticAt ℂ φ c) (hs : AnalyticAt ℂ s b) (hsb : s b = c) :
    AnalyticAt ℂ (fun w => φ (s w) * deriv s w) b := by
  have hcomp : AnalyticAt ℂ (φ ∘ s) b := (hsb ▸ hφ).comp hs
  exact (hcomp.mul hs.deriv : AnalyticAt ℂ (fun w => φ (s w) * deriv s w) b)

/-! ### Step 2 — the local fibre trace coefficient is analytic at a regular value

Assembling step 1 over a regular fibre.  We package the per-fibre regularity data over a regular
value (the `FibreRegularData` of `FormTraceFibre`, *plus* analyticity of `g`'s pullback at each fibre
point — the "regular value off the poles of `α`" condition) and show the trace coefficient
`(fibreTrace ω₀ f D).traceCoeff` is analytic at `b`.

This is the local model of "`Tr_F α` is holomorphic at every regular value off the poles of `α`",
the analytic core of step 2 (holomorphy off the finite exceptional set). -/

variable {g : X → ℂ}

/-- **The per-sheet section germ is analytic at the base, with `s b = pre i`** (read off the
`exists_planar_section` choice baked into `fibreTrace`).  A convenience unpacking of the `fibreTrace`
`sheet` fields. -/
theorem fibreTrace_sheet_analyticAt (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b) (i : D.ι) :
    AnalyticAt ℂ ((fibreTrace ω₀ f D).sheet i) (fibreTrace ω₀ f D).b ∧
      (fibreTrace ω₀ f D).sheet i (fibreTrace ω₀ f D).b = (fibreTrace ω₀ f D).pre i :=
  ⟨(fibreTrace ω₀ f D).sheet_analytic i, (fibreTrace ω₀ f D).sheet_base i⟩

/-- **Step 2, per sheet.**  Over a regular value `b`, each per-sheet summand of the trace coefficient
is analytic at `b`, provided `g`'s chart-pullback is analytic at the fibre point `xs i` (so `α = ω₀·g`
is holomorphic there).  The summand is the pushforward of the chart integrand
`chartIntegrand ω₀ g (xs i)` (analytic at `pre i` by `analyticAt_chartIntegrand`) along the analytic
section `sheet i` (`fibreTrace_sheet_analyticAt`). -/
theorem analyticAt_fibreTrace_summand (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    {b : ℂ} (D : FibreRegularData g f b) (i : D.ι)
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z)) ((chartAt ℂ (D.xs i)) (D.xs i))) :
    AnalyticAt ℂ
      (fun w => (fibreTrace ω₀ f D).coeff i ((fibreTrace ω₀ f D).sheet i w)
        * deriv ((fibreTrace ω₀ f D).sheet i) w)
      (fibreTrace ω₀ f D).b := by
  rw [fibreTrace_coeff]
  exact analyticAt_sheetPushforward (analyticAt_chartIntegrand ω₀ g (D.xs i) hg)
    ((fibreTrace ω₀ f D).sheet_analytic i)
    (by rw [(fibreTrace ω₀ f D).sheet_base i, fibreTrace_pre])

/-- **Step 2 — the local trace coefficient is analytic at a regular value.**  Over a regular value
`b`, with `g`'s chart-pullback analytic at *every* fibre point (so `α = ω₀·g` is holomorphic on the
fibre — `b` is a regular value off the poles of `α`), the trace coefficient `Tr_F α`
(`(fibreTrace ω₀ f D).traceCoeff`) is analytic at `b`:

> `AnalyticAt ℂ (Tr_F α over the fibre) b`.

This is the local model of "the global trace `Tr_F α` is holomorphic off the finite exceptional set
(critical values ∪ poles of `α` ∪ `∞`)", the analytic heart of step 2.  *Proof:* the trace
coefficient is the finite sum of the regular-sheet pushforwards, each analytic at `b`
(`analyticAt_fibreTrace_summand`); a finite sum of analytics is analytic. -/
theorem analyticAt_traceCoeff (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z))
      ((chartAt ℂ (D.xs i)) (D.xs i))) :
    AnalyticAt ℂ (fibreTrace ω₀ f D).traceCoeff (fibreTrace ω₀ f D).b := by
  rw [show (fibreTrace ω₀ f D).traceCoeff
      = fun w => ∑ i, (fibreTrace ω₀ f D).coeff i ((fibreTrace ω₀ f D).sheet i w)
        * deriv ((fibreTrace ω₀ f D).sheet i) w from rfl]
  exact Finset.analyticAt_fun_sum _ (fun i _ => analyticAt_fibreTrace_summand ω₀ f D i (hg i))

end Jacobians.Dolbeault.FormTraceGlobal
