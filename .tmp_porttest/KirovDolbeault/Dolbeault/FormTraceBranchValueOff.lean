/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceBranchPlanarExtend
import KirovDolbeault.Dolbeault.FormTraceGlobalGeometric

/-!
# `hT_off` at a branch value for the geometric trace (Gate A, §VIII.3 — re-pointed)

The re-pointed Gate A path (`globalTrace_of_glue` / `residueSum_eq_zero_of_glue`) needs the global
trace `T` to be `AnalyticAt` at every value off the finite **pole-values** — *including at the
branch values of the cover*, which are NOT pole-values (a generic separating cover puts the branch
locus off the poles of `α = ω₀·g`).  At a branch value `b₀` the per-sheet section derivatives of the
regular fibre blow up, so analyticity there is the genuine §VIII.3 frontier.

This file wires the **planar removable-extension engine** (`FormTraceBranchPlanarExtend`) to the
*geometric* trace: it shows that the **removable extension** `Tᵉˣᵗ` of `valueChartTrace ω₀ f Φ` at a
branch value `b₀` (the geometric trace patched to its punctured limit there) is `AnalyticAt b₀`,
given exactly two honest inputs:

* `hpunct_an` — `valueChartTrace ω₀ f Φ` is **analytic on the punctured neighbourhood** of `b₀`
  (every `b' ≠ b₀` near `b₀` is a regular value off the poles of `α`, where the geometric trace is the
  analytic regular-fibre sum — the off-branch sheet-gluing, already isolated as the per-regular-value
  germ-coherence in `FormTraceGlobalGeometric`);
* `hbnd` — the **boundedness crux** `(z − b₀)·valueChartTrace z → 0` (the §VIII.3 boundedness; for the
  planar geometric trace it reduces *sheet by sheet* to the proven `tendsto_zero_section_deriv`, see
  `FormTraceBranchPlanarExtend.tendsto_zero_fibreSum`).

This is the precise, sound, value-correct replacement for the structurally-impossible
`valueChartTrace`-at-the-branch-value (the `BranchAwareTraceSelection` obstruction): rather than
asking the regular-fibre selection to *host* the branch value (impossible — it has fewer sheets), we
**patch** the trace to its removable limit there, exactly as the bundle trace `traceFunExt` does.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `analyticAt_branchExtension_valueChartTrace` — the removable extension of `valueChartTrace` at a
  branch value is `AnalyticAt`, from `hpunct_an` + `hbnd`.
* `valueChartTrace_branchExtension` — the explicit extension function (patched value).
* `valueChartTrace_branchExtension_eventuallyEq` — the extension germ-equals `valueChartTrace` off the
  branch value (so it shares all the finite/∞ glue with `valueChartTrace`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceBranchPlanar

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-- **The branch-value removable extension of the geometric trace.**  At a branch value `b₀` (where
`valueChartTrace ω₀ f Φ` has a removable singularity), the geometric trace patched to its
punctured-limit value: `Function.update (valueChartTrace ω₀ f Φ) b₀ (limUnder (𝓝[≠] b₀) …)`.  This is
the value-correct trace at the branch value — the planar analogue of the bundle trace `traceFunExt`. -/
noncomputable def valueChartTrace_branchExtension (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (b₀ : ℂ) : ℂ → ℂ :=
  Function.update (valueChartTrace ω₀ f Φ) b₀
    (limUnder (𝓝[≠] b₀) (valueChartTrace ω₀ f Φ))

/-- The branch extension germ-equals `valueChartTrace` off `b₀` (the patch only changes the value at
`b₀`), so it shares all the finite/∞ glue with `valueChartTrace`. -/
theorem valueChartTrace_branchExtension_eventuallyEq (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (b₀ : ℂ) :
    valueChartTrace_branchExtension ω₀ f Φ b₀ =ᶠ[𝓝[≠] b₀] valueChartTrace ω₀ f Φ := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [valueChartTrace_branchExtension, Function.update_of_ne hz]

/-- **`hT_off` at a branch value (the re-pointed §VIII.3 frontier, value-corrected).**  At a branch
value `b₀`, the removable extension `valueChartTrace_branchExtension ω₀ f Φ b₀` is `AnalyticAt b₀`,
given:

* `hpunct_an` — `valueChartTrace ω₀ f Φ` is analytic on the punctured neighbourhood of `b₀` (the
  off-branch regular-fibre analyticity at the nearby regular values off the poles of `α`);
* `hbnd` — the boundedness crux `(z − b₀)·valueChartTrace z → 0` (the §VIII.3 boundedness, reduced
  sheet-by-sheet to the proven `tendsto_zero_section_deriv` via `tendsto_zero_fibreSum`).

This is the precise sound discharge of `hT_off` at a branch value: the geometric trace is patched to
its removable limit and is then analytic — *no* false demand that the regular-fibre selection host the
branch value.  *Proof.*  `analyticAt_update_of_punctured_diff_of_tendsto_zero` (the planar engine),
with punctured-differentiability supplied by `hpunct_an` (`AnalyticAt ⟹ DifferentiableAt`). -/
theorem analyticAt_branchExtension_valueChartTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (hpunct_an : ∀ᶠ z in 𝓝[≠] b₀, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z)
    (hbnd : Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0)) :
    AnalyticAt ℂ (valueChartTrace_branchExtension ω₀ f Φ b₀) b₀ := by
  have hpunct_diff : ∀ᶠ z in 𝓝[≠] b₀, DifferentiableAt ℂ (valueChartTrace ω₀ f Φ) z := by
    filter_upwards [hpunct_an] with z hz using hz.differentiableAt
  exact analyticAt_update_of_punctured_diff_of_tendsto_zero hpunct_diff hbnd

/-! ### Reducing the boundedness crux to the per-sheet atom (assembly-ready)

The boundedness hypothesis `hbnd` of `analyticAt_branchExtension_valueChartTrace` is, near a branch
value `b₀`, the boundedness of the geometric trace `valueChartTrace ω₀ f Φ`.  When `valueChartTrace`
germ-equals (off `b₀`) a *fixed* regular-fibre trace's fibre-sum `(fibreTrace ω₀ f D).traceCoeff =
∑ i, coeff i (sheet i z)·deriv (sheet i) z`, the crux reduces to the finite sum of per-sheet bounds
(`tendsto_zero_fibreSum`), each discharged by `tendsto_zero_section_deriv` from the proven ratio atom.
We package the reduction so the assembly only supplies the per-sheet section/chain-rule data. -/

/-- **Boundedness crux from a regular-fibre germ + per-sheet bounds.**  If `valueChartTrace ω₀ f Φ`
germ-equals (on the punctured neighbourhood of `b₀`) the fibre-sum `(fibreTrace ω₀ f D).traceCoeff` of
a fibre `D`, and each per-sheet term `(z − b₀)·coeff_i(sheet_i z)·deriv(sheet_i) z → 0`, then the
boundedness crux `(z − b₀)·valueChartTrace ω₀ f Φ z → 0` holds.  *Proof.*  `tendsto_zero_fibreSum`
gives the bound for the fibre-sum; transport along the germ-equality. -/
theorem tendsto_zero_valueChartTrace_of_fibreGerm (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (D : FibreRegularData g f b₀)
    (hgerm : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] (fibreTrace ω₀ f D).traceCoeff)
    (hterm : ∀ i, Tendsto (fun z => (z - b₀) *
        ((fibreTrace ω₀ f D).coeff i ((fibreTrace ω₀ f D).sheet i z)
          * deriv ((fibreTrace ω₀ f D).sheet i) z)) (𝓝[≠] b₀) (𝓝 0)) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0) := by
  -- The fibre-sum boundedness from the per-sheet bounds.
  have hsum : Tendsto (fun z => (z - b₀) *
      ∑ i, (fibreTrace ω₀ f D).coeff i ((fibreTrace ω₀ f D).sheet i z)
        * deriv ((fibreTrace ω₀ f D).sheet i) z) (𝓝[≠] b₀) (𝓝 0) :=
    tendsto_zero_fibreSum (ι := (fibreTrace ω₀ f D).ι) hterm
  -- `(fibreTrace ω₀ f D).traceCoeff z = ∑ i, …` (definitional), so transport along `hgerm`.
  refine hsum.congr' ?_
  filter_upwards [hgerm] with z hz
  show (z - b₀) * ∑ i, (fibreTrace ω₀ f D).coeff i ((fibreTrace ω₀ f D).sheet i z)
      * deriv ((fibreTrace ω₀ f D).sheet i) z
    = (z - b₀) * valueChartTrace ω₀ f Φ z
  rw [hz]
  rfl

end Jacobians.Dolbeault.FormTraceGlobal
