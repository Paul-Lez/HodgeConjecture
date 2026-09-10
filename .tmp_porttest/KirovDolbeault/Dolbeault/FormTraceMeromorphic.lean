/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobalFunction
import KirovDolbeault.Dolbeault.FormTraceInftyFibre

/-!
# Meromorphy of the local fibre trace at its base (Gate A, §VIII.3 step 1 — foundation)

`Jacobians.Dolbeault.FormTraceGlobalFunction` proved the local fibre trace coefficient is *analytic*
at a **regular** value off the poles of `α` (`analyticAt_traceCoeff`).  This file proves the
companion **meromorphy at any base**: over an arbitrary fibre the local trace coefficient is
`MeromorphicAt` at its base value (and at the reciprocal base `0` for the `∞` fibre).  This is the
local-singularity input the global trace construction needs at the *finite pole-values* (where the
trace has a genuine pole, not just an analytic value) and at `∞`.

The trace coefficient is a finite sum of per-sheet pushforwards `coeff i (sheet i w)·(sheet i)'(w)`,
each meromorphic at the base (`FibreTrace.meromorphicAt_summand`: the meromorphic form coefficient
composed with the analytic section, times the analytic section derivative); a finite sum of
meromorphics is meromorphic (`MeromorphicAt.fun_sum`).

These are clean standalone building blocks (no new geometric input) feeding the
`GlobalTrace.hentire` / `GlobalTrace.hrecip` fields of `FormTraceGlobalAssemble` — the local
meromorphy at each pole that, summed/subtracted into the principal parts, leaves the global
holomorphic remainder.

## What is proved (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `meromorphicAt_traceCoeff_base` — a generic `FibreTrace.traceCoeff` is `MeromorphicAt` at its base.
* `meromorphicAt_traceCoeff_fibreTrace` — the finite-fibre local trace `(fibreTrace ω₀ f D).traceCoeff`
  is `MeromorphicAt` at the base value `b`.
* `meromorphicAt_traceCoeff_inftyFibreTrace` — the `∞`-fibre local trace
  `(inftyFibreTrace ω₀ f D).traceCoeff` is `MeromorphicAt` at the reciprocal base `0`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The local fibre trace coefficient is meromorphic at its base.**  For any `FibreTrace T`, the
trace coefficient `T.traceCoeff` (the finite sum `∑ i, coeff i (sheet i w)·(sheet i)'(w)`) is
`MeromorphicAt` at the base `T.b`: each summand is meromorphic at the base
(`FibreTrace.meromorphicAt_summand`) and a finite sum of meromorphics is meromorphic
(`MeromorphicAt.fun_sum`). -/
theorem meromorphicAt_traceCoeff_base (T : FibreTrace) :
    MeromorphicAt T.traceCoeff T.b := by
  rw [show T.traceCoeff = fun w => ∑ i, T.coeff i (T.sheet i w) * deriv (T.sheet i) w from rfl]
  exact MeromorphicAt.fun_sum (fun i _ => T.meromorphicAt_summand i)

variable {g : X → ℂ}

/-- **The finite-fibre local trace is meromorphic at the base value `b`.**  Specialises
`meromorphicAt_traceCoeff_base` to the unramified-fibre trace `fibreTrace ω₀ f D` over a base value
`b` (the local singularity model of `Tr_F α` at `b`, including the finite pole-values where the trace
has a genuine pole). -/
theorem meromorphicAt_traceCoeff_fibreTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    {b : ℂ} (D : FibreRegularData g f b) :
    MeromorphicAt (fibreTrace ω₀ f D).traceCoeff b := by
  have h := meromorphicAt_traceCoeff_base (fibreTrace ω₀ f D)
  rwa [fibreTrace_b] at h

/-- **The `∞`-fibre local trace is meromorphic at the reciprocal base `0`.**  Specialises
`meromorphicAt_traceCoeff_base` to the `∞`-fibre trace `inftyFibreTrace ω₀ f D` (base `0` in the
reciprocal chart) — the local singularity model of `Tr_F α` at `∞`. -/
theorem meromorphicAt_traceCoeff_inftyFibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (D : InftyFibreData g f) :
    MeromorphicAt (inftyFibreTrace ω₀ f D).traceCoeff 0 := by
  have h := meromorphicAt_traceCoeff_base (inftyFibreTrace ω₀ f D)
  rwa [inftyFibreTrace_b] at h

end Jacobians.Dolbeault.FormTraceGlobal
