/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobalGeometric

/-!
# Holomorphic extension of the trace across branch values (Gate A, §VIII.3 — removable singularity)

The off-exceptional analyticity `hT_off : ∀ z ∉ centres, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z` of the
geometric trace (consumed by `residueSum_eq_zero_of_glue`) must hold at **every** value off the finite
pole-values — *including the branch (critical) values* of the cover `F = f.toRiemannSphere`.  At a
branch value there is **no local sheet system**, so the moving-sheet route (`hreg`/`hsetReg` via
`exists_sphereSheetSystem`) does *not* apply there.

This is Miranda's §VIII.3 point that the trace `Tr_F α` is a *single (mero)morphic function on `ℂℙ¹`* —
the symmetric functions of the sheet values are single-valued and bounded across branch points, so the
trace **extends holomorphically across them** (Riemann's removable-singularity theorem).  In Lean this
is exactly `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`: a function analytic
on a *punctured* neighbourhood of `z` and *continuous at* `z` is analytic at `z`.

This file packages that extension, reducing the branch-value analyticity to its two honest inputs:
* **punctured analyticity** — `valueChartTrace` is analytic at every value in a punctured neighbourhood
  of the branch value (supplied by the regular-value coherence at the nearby *non-branch* values, since
  branch values are isolated); and
* **continuity at the branch value** — the genuine §VIII.3 boundedness/single-valuedness content (the
  symmetric trace extends continuously across the branch point).

It then gives a clean `hT_off` constructor that handles **all** values off the centres: regular values
via the moving-sheet coherence, branch values via the removable-singularity extension — so the only
branch-specific input is the continuity (Riemann extension), never a sheet system.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `analyticAt_valueChartTrace_of_punctured_continuous` — branch-value analyticity from punctured
  analyticity + continuity (Riemann's removable singularity, specialised to `valueChartTrace`).
* `analyticAt_valueChartTrace_off_centres` — the full off-centre analyticity `hT_off`, dispatching each
  value to either the regular-value coherence (`hreg`) or the removable-singularity extension at the
  finitely-many branch values (`hbranch`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr` extends across branch
  points; Lemma 3.2).
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

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### Branch-value analyticity via removable singularity

At a branch value `z` of the cover, the geometric trace is analytic on a *punctured* neighbourhood of
`z` (the nearby values are regular, by isolation of branch points) and, by the §VIII.3
single-valuedness/boundedness, *continuous at* `z`.  Riemann's removable-singularity theorem
(`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) then gives analyticity at
`z`.  This is the holomorphic extension of `Tr_F α` across the branch point — no sheet system required at
`z` itself. -/

/-- **Branch-value analyticity of the geometric trace (Riemann's removable singularity).**  If
`valueChartTrace ω₀ f Φ` is analytic at every value in a *punctured* neighbourhood of `z` (`hpunct`)
and is *continuous at* `z` (`hcont` — the §VIII.3 single-valuedness/boundedness across the branch
point), then it is **analytic at `z`**.  This is Miranda's holomorphic extension of the trace across a
branch value, via `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`; the only
branch-specific input is the continuity (the trace extends), never a sheet system. -/
theorem analyticAt_valueChartTrace_of_punctured_continuous
    (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) {z : ℂ}
    (hpunct : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hcont : ContinuousAt (valueChartTrace ω₀ f Φ) z) :
    AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (hpunct.mono fun _ h => h.differentiableAt) hcont

/-! ### The full off-centre analyticity (regular ⊕ branch)

We assemble `hT_off : ∀ z ∉ centres, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z`.  The finitely-many
**branch values** off the centres are collected in a `Finset br`; at every value off `centres ∪ br`
(a *regular non-pole* value), analyticity comes from the moving-sheet coherence `hreg`.  At a branch
value `z ∈ br` (off the centres), analyticity comes from the removable-singularity extension
(`analyticAt_valueChartTrace_of_punctured_continuous`): a punctured neighbourhood of `z` avoids the
finitely-many points `centres ∪ br` (they are isolated), so `valueChartTrace` is analytic there by
`hreg`, and the continuity at `z` is supplied by `hbranch`. -/

/-- **Off-centre analyticity of the geometric trace, dispatching regular vs branch values.**  Let
`centres br : Finset ℂ` (the finite pole-values and the finite branch values, respectively).  Suppose:

* `hreg` — at every value `w` off `centres ∪ br` (a regular non-pole value), `valueChartTrace ω₀ f Φ` is
  analytic at `w` (the moving-sheet coherence, dischargeable via the sphere sheet system there); and
* `hbranch` — at every branch value `z ∈ br` off the centres, `valueChartTrace ω₀ f Φ` is *continuous at*
  `z` (the §VIII.3 single-valuedness across the branch point — the Riemann-extension input).

Then `valueChartTrace ω₀ f Φ` is analytic at **every** value off the centres `z ∉ centres`.  Regular
values use `hreg`; branch values `z ∈ br` use the removable-singularity extension, whose punctured
analyticity holds because a small punctured ball around `z` avoids the finite set `centres ∪ br`.  This
is the honest `hT_off`: the *only* branch-specific input is the continuity (Riemann extension), never a
sheet system at the branch point. -/
theorem analyticAt_valueChartTrace_off_centres
    (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (centres br : Finset ℂ)
    (hreg : ∀ w ∉ centres ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbranch : ∀ z ∈ br, z ∉ centres → ContinuousAt (valueChartTrace ω₀ f Φ) z)
    {z : ℂ} (hz : z ∉ centres) :
    AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z := by
  by_cases hzbr : z ∈ br
  · -- Branch value: removable-singularity extension.
    refine analyticAt_valueChartTrace_of_punctured_continuous ω₀ f Φ ?_ (hbranch z hzbr hz)
    -- A punctured neighbourhood of `z` avoids the finite set `(centres ∪ br) \ {z}` (isolated points),
    -- on which `valueChartTrace` is analytic by `hreg`.
    have hfin : ((centres ∪ br : Finset ℂ) : Set ℂ).Finite := (centres ∪ br).finite_toSet
    -- The complement of the finite set `(↑(centres ∪ br)) \ {z}` is a punctured neighbourhood of `z`.
    have hcompl : (((centres ∪ br : Finset ℂ) : Set ℂ) \ {z})ᶜ ∈ 𝓝 z :=
      (hfin.diff (t := {z})).isClosed.compl_mem_nhds (by simp)
    -- Restrict to the punctured filter and conclude analyticity from `hreg`.
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with w hw_ne hw_compl
    -- `hw_ne : w ∈ {z}ᶜ`, `hw_compl : w ∉ (↑(centres ∪ br)) \ {z}`.  So `w ∉ centres ∪ br`.
    refine hreg w ?_
    intro hw_mem
    -- `w ∈ centres ∪ br` and `w ≠ z` ⟹ `w ∈ (↑(centres ∪ br)) \ {z}`, contradicting `hw_compl`.
    exact hw_compl ⟨hw_mem, fun hwz => hw_ne (by simpa using hwz)⟩
  · -- Regular value: directly from `hreg` (`z ∉ centres` and `z ∉ br`).
    exact hreg z (by simp [Finset.mem_union, hz, hzbr])

end Jacobians.Dolbeault.FormTraceGlobal
