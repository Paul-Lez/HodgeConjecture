/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceBundleBranchBound
import KirovDolbeault.Dolbeault.FormTraceSheetFibreBridge
import KirovDolbeault.Dolbeault.FormTraceCoherentSelection

/-!
# The bundle-trace germ bridge `hbridgeBr` (Gate A close, Miranda §VIII.3)

This file discharges the **single core analytic input** of `patchedTraceSelection_ofBundleBranch`
(`Jacobians.Dolbeault.FormTraceBundleBranchBound`): the **bundle-trace germ bridge**

> `hbridgeBr` — at a regular-near-branch value `b₀`, `valueChartTrace ω₀ f Φ` germ-equals, on the
> punctured neighbourhood `𝓝[≠] b₀`, the value-chart local coefficient of the bundle trace SUM
> `traceLocalCoeff (traceFun F (αBr b₀)) (coe b₀) (coe z)`, where `αBr b₀ = ω₀·g` near the fibre.

This is the planar↔bundle identification at *regular* values `z` near `b₀`, term-by-term over the
finite regular fibre — the §VIII.3 "the trace is single-valued by symmetry".  The proof reduces to
the proven per-sheet linchpin `FormTraceSheet.g_weighted_sheetPullback_eq_chartIntegrand_mul_deriv`
and the bundle additivity `TraceForm.traceLocalCoeff_traceFun_eq_finsum`.

## The clean affine-chart reading (the key simplification — no base monodromy)

On `RiemannSphere = OnePoint ℂ` every finite chart is the single global affine chart `chartCoe`
(`RiemannSphere.chartAt_coe`, definitionally).  Hence the tangent trivializations at `coe b₀` and
`coe z` are *the same trivialization* (`trivializationAt … x` depends on `x` only through
`chartAt H x`, which is `chartCoe` for every finite point).  Therefore the fixed-`coe b₀`-frame local
coefficient `traceLocalCoeff (…) (coe b₀) (coe z)` equals the *self-frame* local coefficient
`traceLocalCoeff (…) (coe z) (coe z)` — **no genuine frame transition on the base**.  This is the
sphere-specific dissolution of the base monodromy: the only nontrivial transition is per-sheet on the
*total* space (handled by the proven `localRep_eq_transition_mul_self` inside the per-sheet bridge),
never on the sphere base.

The self-frame coefficient `traceLocalCoeff (traceFun F α) (coe z) (coe z)` is, by
`traceLocalCoeff_traceFun_eq_finsum` + `traceSummand_inCoordinates_apply_one_eq_ref`, exactly the
planar fibre-sum `∑ chartIntegrand·deriv` — the same object `valueChartTrace` is built from.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, pp. 252–253 (the trace is single-valued
  by symmetry; the SUM extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The sphere base-frame swap (the key simplification)

On `RiemannSphere` the tangent trivialization at any finite point `coe b₀` agrees with the one at
`coe z`, because both are built from the single global chart `chartCoe`.  Hence the local coefficient
read in the *fixed* `coe b₀`-frame equals the one read in the *self* `coe z`-frame. -/

/-- **Sphere finite-base trivialization agreement.**  The tangent-bundle trivializations at two finite
points `coe a` and `coe b` of `RiemannSphere` are equal (both are the trivialization built from the
single global affine chart `chartCoe = chartAt ℂ (coe ·)`). -/
theorem trivializationAt_coe_eq (a b : ℂ) :
    trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := RiemannSphere)) ((a : ℂ) : RiemannSphere)
      = trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := RiemannSphere)) ((b : ℂ) : RiemannSphere) :=
  rfl

/-- **Sphere base-frame swap for `localCoeffLin`.**  On `RiemannSphere`, the local-coefficient
functional read in the *fixed* `coe a`-frame equals the one read in the *self* `coe b`-frame, for any
covector `φ` at `coe b`: the two trivializations coincide (`trivializationAt_coe_eq`).  This dissolves
the base "monodromy" — there is no genuine frame transition on the sphere base. -/
theorem localCoeffLin_coe_base_swap (a b : ℂ) (φ : ℂ →L[ℂ] ℂ) :
    localCoeffLin (((a : ℂ) : RiemannSphere)) (((b : ℂ) : RiemannSphere)) φ
      = localCoeffLin (((b : ℂ) : RiemannSphere)) (((b : ℂ) : RiemannSphere)) φ :=
  rfl

/-! ### The `g`-weight rides inside the bundle summand

The meromorphic form `α = ω₀·g` is encoded by a holomorphic form `αBr` whose covector at each fibre
point `x` equals `g x • ω₀.toFun x`.  Hence the bundle per-sheet summand of `αBr` factors as `g (s y)`
times the holomorphic per-sheet summand of `ω₀`. -/

/-- **`g`-weight pull-out for the bundle summand.**  If `αBr.toFun (s y) = g (s y) • ω₀.toFun (s y)`
(the form `αBr` is `ω₀·g` at the fibre point `s y`), then the bundle per-sheet covector of `αBr` at the
affine unit tangent is `g (s y)` times that of `ω₀`:

> `sheetPullback αBr s y 1 = g (s y) * sheetPullback ω₀ s y 1`. -/
theorem sheetPullback_one_eq_g_mul {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ) (s : Y → X) (y : Y)
    (hαBr : αBr.toFun (s y) = g (s y) • ω₀.toFun (s y)) :
    sheetPullback αBr s y (1 : ℂ) = g (s y) * sheetPullback ω₀ s y (1 : ℂ) := by
  show (αBr.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y) (1 : ℂ)
    = g (s y) * (ω₀.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y) (1 : ℂ)
  rw [hαBr, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### The bundle trace SUM as a planar sheet sum (the core decomposition)

At a regular value `coe z` (off the branch locus of `F = f.toRiemannSphere`), with a local sheet
system `S` of `F` at `coe z`, the bundle trace SUM local coefficient — read in the *fixed* `coe b₀`
frame — equals the planar fibre sum `∑ g·sheetPullback ω₀` over the sheets.  This is the bundle side
of the §VIII.3 trace, reduced to the per-sheet holomorphic covectors.  The base-frame swap dissolves
the `coe b₀` ↔ `coe z` transition; the centre identity recovers the raw value; the sheet system
expands the fibre sum; the `g`-weight rides per sheet. -/

/-- **Bundle trace SUM local coefficient = planar sheet sum.**  Let `F = f.toRiemannSphere` be the
nonconstant cover, `coe z` a regular value with a local sheet system `S`, and `αBr` a holomorphic form
with `αBr.toFun (S.sheet i (coe z)) = g (S.sheet i (coe z)) • ω₀.toFun (S.sheet i (coe z))` at each
fibre point.  Then for any base point `coe b₀`,

> `traceLocalCoeff (traceFun F αBr) (coe b₀) (coe z)
>    = ∑ i, g (S.sheet i (coe z)) * sheetPullback ω₀ (S.sheet i) (coe z) 1`. -/
theorem traceLocalCoeff_traceFun_eq_sheetSum (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hαBr : ∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
      = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))) :
    traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((b₀ : ℂ) : RiemannSphere))
        (((z : ℂ) : RiemannSphere))
      = ∑ i, g (S.sheet i (((z : ℂ) : RiemannSphere)))
          * sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) := by
  -- Base-frame swap: `coe b₀` ↦ `coe z` (no monodromy on the sphere base).
  rw [show traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((b₀ : ℂ) : RiemannSphere))
        (((z : ℂ) : RiemannSphere))
      = localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
          (traceFun f.toRiemannSphere αBr (((z : ℂ) : RiemannSphere))) from rfl,
    localCoeffLin_coe_base_swap b₀ z]
  -- Self-frame coefficient = raw value at `1` (centre identity).
  rw [show localCoeffLin (((z : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
        (traceFun f.toRiemannSphere αBr (((z : ℂ) : RiemannSphere)))
      = traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((z : ℂ) : RiemannSphere))
          (((z : ℂ) : RiemannSphere)) from rfl,
    traceLocalCoeff_center]
  -- Expand the fibre sum along the local sheet system.
  rw [S.traceFun_eq_sum_sheetPullback f.contMDiff_toRiemannSphere αBr S.mem_V]
  -- Sum of operators applied at `1`, then pull out the `g`-weight per sheet.
  exact (ContinuousLinearMap.sum_apply Finset.univ
      (fun i => sheetPullback αBr (S.sheet i) (((z : ℂ) : RiemannSphere))) (1 : ℂ)).trans
    (Finset.sum_congr rfl (fun i _ =>
      sheetPullback_one_eq_g_mul ω₀ αBr g (S.sheet i) (((z : ℂ) : RiemannSphere)) (hαBr i)))

/-! ### The per-sheet match: planar moving summand = bundle summand

Both the planar fibre-trace summand (read in the value chart along the sphere sheet) and the bundle
per-sheet summand reduce to the *self-chart intrinsic* summand `g (P)·localRep ω₀ P P·deriv(…)`.  Hence
they are equal, term by term over the sheet index — *no reindexing*, the two sums share the index
`Fin S.n`. -/

/-- **Planar moving summand = bundle summand (per sheet).**  For the sphere sheet `s := S.sheet i`,
read at the value point `coe z`, the planar moving summand (value-chart `chartIntegrand·deriv` along
`s (coe ·)`) equals the `g`-weighted bundle per-sheet covector:

> `chartIntegrand ω₀ g (s (coe z)) (chart_{s(coe z)}(s (coe z)))·deriv (fun w => chart_{s(coe z)}(s (coe w))) z
>    = g (s (coe z))·sheetPullback ω₀ s (coe z) 1`.

Both equal `g (s(coe z))·localRep ω₀ (s(coe z))(s(coe z))·deriv(chart_{s(coe z)} ∘ s(coe ·)) z`: the LHS
by `movingSummand_eq_selfChart` (the `dz`-Jacobian cancellation at the self chart `xs = s(coe z)`), the
RHS by the linchpin `sheetPullback_one_eq_coeffAt_mul_deriv` + `coeffAt_chartCenter`. -/
theorem movingSummand_eq_g_sheetPullback (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (s : RiemannSphere → X) {z : ℂ} (hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s (((z : ℂ) : RiemannSphere))) :
    chartIntegrand ω₀ g (s (((z : ℂ) : RiemannSphere)))
        ((chartAt ℂ (s (((z : ℂ) : RiemannSphere)))) (s (((z : ℂ) : RiemannSphere))))
        * deriv (fun w => (chartAt ℂ (s (((z : ℂ) : RiemannSphere)))) (s (((w : ℂ) : RiemannSphere)))) z
      = g (s (((z : ℂ) : RiemannSphere))) * sheetPullback ω₀ s (((z : ℂ) : RiemannSphere)) (1 : ℂ) := by
  -- RHS via the linchpin (read in the moving `s(coe z)`-chart, source chart `chartCoe` on the sphere).
  rw [FormTraceSheet.sheetPullback_one_eq_coeffAt_mul_deriv ω₀ s hs]
  -- The source sphere chart is `chartCoe`: `(chartAt (coe z)).symm w = coe w`, `chartCoe (coe z) = z`.
  simp only [RiemannSphere.chartAt_coe, RiemannSphere.chartCoe_symm_apply,
    RiemannSphere.chartCoe_apply_coe]
  -- LHS: unfold `chartIntegrand`, the `g`-eval at the chart centre, and `coeffAt = localRep`.
  rw [chartIntegrand, (chartAt ℂ (s (((z : ℂ) : RiemannSphere)))).left_inv
    (mem_chart_source ℂ (s (((z : ℂ) : RiemannSphere))))]
  ring

/-! ### The pointwise planar↔bundle identity at a regular value

Assembling the two sides: at a regular value `z` (sheet system `S`), the planar fibre trace of the
sphere-sheet fibre equals the bundle trace SUM local coefficient.  Both are `∑` over `Fin S.n` of the
*same* per-sheet summand (`movingSummand_eq_g_sheetPullback`); the planar side is read via
`fibreTrace_eventuallyEq_movingSum`, the bundle side via `traceLocalCoeff_traceFun_eq_sheetSum`. -/

/-- **Planar fibre trace = bundle trace SUM coefficient (pointwise, regular value).**  Let `S` be a
local sheet system of `F = f.toRiemannSphere` at the regular value `coe z`, `αBr` a holomorphic form
with `αBr.toFun (S.sheet i (coe z)) = g (S.sheet i (coe z)) • ω₀.toFun (S.sheet i (coe z))`, and `D :=
FibreRegularData.ofSphereSheetSystem S hderiv hmero` the sphere-sheet fibre over `z`.  Then for any base
point `coe b₀`,

> `(fibreTrace ω₀ f D).traceCoeff z = traceLocalCoeff (traceFun F αBr) (coe b₀) (coe z)`. -/
theorem fibreTrace_traceCoeff_eq_traceLocalCoeff (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))))
    (hαBr : ∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
      = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))) :
    (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z
      = traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((b₀ : ℂ) : RiemannSphere))
          (((z : ℂ) : RiemannSphere)) := by
  -- The bundle side: the sheet sum.
  rw [traceLocalCoeff_traceFun_eq_sheetSum ω₀ αBr g f S hαBr]
  -- The planar side: the moving sum along the sphere sheets `sec i := S.holoReprSheet i`, AT `z`
  -- (`D.xs i = S.sheet i (coe z)` definitionally, so `holoReprSheet i z = D.xs i` is `rfl`).
  have hmoving := (fibreTrace_eventuallyEq_movingSum ω₀ f
    (FibreRegularData.ofSphereSheetSystem S hderiv hmero) (fun i => S.holoReprSheet i)
    (fun _ => rfl)
    (fun i => (S.holoReprSheet_contMDiffAt i).continuousAt)
    (fun i => S.holoReprSheet_section i)).self_of_nhds
  rw [hmoving]
  -- Term-by-term: `D.xs i = S.sheet i (coe z)` (defeq), `sec i z = S.sheet i (coe z)`.
  exact Finset.sum_congr rfl (fun i _ =>
    movingSummand_eq_g_sheetPullback ω₀ g (S.sheet i) (S.sheet_mdifferentiableAt i S.mem_V))

/-! ### The bundle-trace germ bridge `hbridgeBr`

Lifting the pointwise identity to the germ equality `hbridgeBr` of `patchedTraceSelection_ofBundleBranch`.
On the punctured neighbourhood `𝓝[≠] b₀`, eventually each `z` is a regular value carrying a sphere sheet
system `S_z`, with (i) the geometric trace agreeing with the sphere-sheet planar fibre trace at `z` (the
`Creg`-coherence, available from the moving-fibre machinery), and (ii) `αBr.toFun = g·ω₀.toFun` at the
fibre points of `S_z` (the form `αBr` is `ω₀·g` near the fibre).  At each such `z` the pointwise identity
`fibreTrace_traceCoeff_eq_traceLocalCoeff` finishes. -/

/-- **The bundle-trace germ bridge `hbridgeBr` from the eventual sphere-sheet coherence.**  Suppose on
`𝓝[≠] b₀`, eventually each `z` carries a sphere sheet system `S_z` of `F = f.toRiemannSphere` at `coe z`
(with regular fibre — `hderiv`, `hmero`) such that the geometric trace agrees with the sphere-sheet fibre
trace at `z` and `αBr` is `ω₀·g` at the fibre points:

> eventually: `valueChartTrace ω₀ f Φ z = (fibreTrace ω₀ f (ofSphereSheetSystem S_z …)).traceCoeff z`
> and `∀ i, αBr.toFun (S_z.sheet i (coe z)) = g (S_z.sheet i (coe z)) • ω₀.toFun (S_z.sheet i (coe z))`.

Then the bundle-trace germ bridge holds:

> `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] z ↦ traceLocalCoeff (traceFun F αBr) (coe b₀) (coe z)`.

This is exactly the `hbridgeBr` input of `patchedTraceSelection_ofBundleBranch`, reduced to the eventual
regular-value sphere-sheet coherence (the standard §VIII.3 residual — *no* monodromy/Puiseux frame). -/
theorem hbridgeBr_of_eventual_sphereCoherence (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (hev : ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f Φ z
            = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
        (∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
          = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere))))) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
      fun z : ℂ => traceLocalCoeff (traceFun f.toRiemannSphere αBr)
        (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere)) := by
  filter_upwards [hev] with z hz
  obtain ⟨S, hderiv, hmero, hvct, hαBr⟩ := hz
  rw [hvct]
  exact fibreTrace_traceCoeff_eq_traceLocalCoeff ω₀ αBr g f S hderiv hmero hαBr

/-! ### Gate A `∑Res = 0` with the branch input as the standard sphere coherence

Wiring `hbridgeBr_of_eventual_sphereCoherence` into `residueSum_eq_zero_ofBundleBranch`: the per-branch
`hbridgeBr` argument is *discharged* from the per-branch eventual sphere-sheet coherence `hevBr`, so the
branch-value input to Gate A is now the **standard regular-value sphere coherence** — the monodromy /
colliding-Puiseux frame is fully gone, replaced by the value-correct symmetric-SUM germ identification
(proven above).  Every other input (the cover scaffolding `cs`/`ρ`/`Dinf`/`Sreg`, the pole sub-fibre
sections, the `∞`/junk/kirovGenus-`0` bookkeeping) is unchanged from `residueSum_eq_zero_ofBundleBranch`. -/

/-- **Gate A `∑Res = 0` from the bundle-branch boundedness with the standard sphere coherence.**
Identical to `residueSum_eq_zero_ofBundleBranch` except the per-branch bundle-trace germ bridge
`hbridgeBr` is replaced by the per-branch **eventual sphere-sheet coherence** `hevBr` (the value-correct
symmetric-SUM identification, discharged via `hbridgeBr_of_eventual_sphereCoherence`).  This is the
close of the §VIII.3 branch-value crux along the monodromy-free path: the only branch-value residual is
the standard regular-value sphere coherence, exactly as at every other (regular/pole) value. -/
theorem residueSum_eq_zero_ofBundleBranchCoherence (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    (br : Finset ℂ)
    (Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderivReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source)
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (αBr : ℂ → HolomorphicOneForms X)
    (hbrBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    -- The per-branch-value eventual sphere-sheet coherence (the value-correct symmetric SUM route).
    (hevBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀,
        ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
          (hderiv : ∀ i, deriv (fun w => f.holoRepr
              ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
              (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
          (_hmero : ∀ i, MeromorphicAt
            (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
              (S.sheet i (((z : ℂ) : RiemannSphere))))),
          valueChartTrace ω₀ f Φ z
              = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
          (∀ i, (αBr b₀).toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
            = g (S.sheet i (((z : ℂ) : RiemannSphere)))
              • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))))
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_ofBundleBranch hac Φ m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj hxs_mem
    hxs_surj secFin hsecFin_base hsecFin_smooth hsecFin_sec hselFin br Sreg hderivReg hmeroReg
    hΦinjReg hΦrangeReg hsheetInjReg hsheetMemReg hCreg_g hncF αBr hbrBr
    (fun b₀ hb₀br hb₀cs =>
      hbridgeBr_of_eventual_sphereCoherence ω₀ (αBr b₀) g f Φ (hevBr b₀ hb₀br hb₀cs))
    hglue_inf hcont_int R₀ hR₀_an hR₀0 hR₀_eq

/-! ### Discharging the geometric-trace half of `hevBr` from the regular-value data

Part (2) of `hevBr` — the geometric trace agrees with the sphere-sheet fibre trace at `z` — is *exactly*
the regular-value coherence already available from the `Sreg`/`Creg` machinery: the
`MovingCoherenceDatum.ofSphereSheetSystemCanon` datum has `.D = ofSphereSheetSystem (Sreg z) …`, so its
`.coherent` (taken at `z` via `self_of_nhds`) gives the identity.  Hence the bundle-branch path needs
*no new* geometric trace input at branch values; the same regular-value sphere data that handles every
regular value discharges it. -/

/-- **The geometric trace agrees with the sphere-sheet fibre trace at a regular value.**  From the
canonical-fibre regular-value data of a sphere sheet system `S` at `z` (`hderiv`/`hmero` + the
canonical-fibre conditions `hΦinj`/`hΦrange`/`hsheetInj`/`hsheetMem`), the geometric trace
`valueChartTrace ω₀ f Φ` evaluated *at* `z` equals the planar fibre trace of the sphere-sheet fibre:

> `valueChartTrace ω₀ f Φ z = (fibreTrace ω₀ f (ofSphereSheetSystem S hderiv hmero)).traceCoeff z`.

This is `MovingCoherenceDatum.ofSphereSheetSystemCanon … |>.coherent` evaluated at `z`
(`Filter.EventuallyEq.self_of_nhds`); the datum's fixed fibre `.D` *is* `ofSphereSheetSystem S …`. -/
theorem valueChartTrace_eq_sphereSheetFibreTrace (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinj : ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrange : ∀ᶠ b' in 𝓝 z,
      Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInj : ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMem : ∀ᶠ b' in 𝓝 z, ∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).source) :
    valueChartTrace ω₀ f Φ z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z :=
  (MovingCoherenceDatum.ofSphereSheetSystemCanon (ω₀ := ω₀) (Φ := Φ) S hderiv hmero
    hΦinj hΦrange hsheetInj hsheetMem).coherent.self_of_nhds

/-! ### Assembling the per-branch `hevBr` from the regular-value data

The per-branch eventual sphere coherence `hevBr` is *entirely* discharged from the regular-value data
already supplied to `patchedTraceSelection_ofBundleBranch` (the `Sreg` family with its canonical-fibre
conditions) PLUS the per-branch `αBr`-agreement-at-fibre-points (the form `αBr b₀ = ω₀·g` near the
fibre — the standard Mittag-Leffler/cutoff residual).  No new geometric input at branch values: the
SAME `Sreg z` data that handles every regular value, applied to regular `z` near `b₀`, gives both the
sphere sheet system and the geometric-trace coherence.  Eventually-`z`-regular near `b₀` is the
finite-bad-set avoidance (`br ∪ image cs` is finite, `b₀` isolated). -/

/-- **The per-branch `hevBr` from the regular-value data + the `αBr`-agreement.**  For a branch value
`b₀ ∈ br` off the pole-values, the eventual sphere-sheet coherence `hevBr b₀` holds, given:

* the regular-value sphere data `Sreg`/`hderivReg`/`hmeroReg` + the canonical-fibre conditions
  `hΦinjReg`/`hΦrangeReg`/`hsheetInjReg`/`hsheetMemReg` (already supplied to the constructor);
* `hαBrAgree` — `αBr b₀ = ω₀·g` at the fibre points `(Sreg z hz).sheet i (coe z)` for `z` near `b₀`
  (the only genuine per-branch residual: the local-holomorphic form agreeing with `ω₀·g` near the fibre).

Eventually-`z`-regular near `b₀` is the finite-bad-set avoidance; at each such `z`, part (2) is
`valueChartTrace_eq_sphereSheetFibreTrace` and (1)/(3) are the supplied data + `hαBrAgree`. -/
theorem hevBr_of_regularData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) {m : ℕ} (cs : Fin m → ℂ) (br : Finset ℂ) {b₀ : ℂ}
    (αBr : HolomorphicOneForms X)
    (Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderivReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source)
    (hαBrAgree : ∀ᶠ z in 𝓝[≠] b₀, ∀ (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      αBr.toFun ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))
        = g ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))
          • ω₀.toFun ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) :
    ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f Φ z
            = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
        (∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
          = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))) := by
  -- Eventually `z ∉ image cs ∪ br` on `𝓝[≠] b₀`: the finite bad set minus `{b₀}` is closed and avoids `b₀`.
  have hfin : (((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}).Finite :=
    ((Finset.univ.image cs ∪ br).finite_toSet).diff
  have hcompl : ((((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}))ᶜ ∈ 𝓝 b₀ :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl, hαBrAgree]
    with z hz_ne hz_compl hz_agree
  have hzb : z ≠ b₀ := by simpa using hz_ne
  have hz : z ∉ Finset.univ.image cs ∪ br := by
    intro hmem
    exact hz_compl ⟨hmem, fun h => hzb (by simpa using h)⟩
  refine ⟨Sreg z hz, hderivReg z hz, hmeroReg z hz, ?_, hz_agree hz⟩
  exact valueChartTrace_eq_sphereSheetFibreTrace ω₀ g f Φ (Sreg z hz) (hderivReg z hz)
    (hmeroReg z hz) (hΦinjReg z hz) (hΦrangeReg z hz) (hsheetInjReg z hz) (hsheetMemReg z hz)

/-! ### Gate A `∑Res = 0` with the branch input reduced to the `αBr`-agreement only

The cleanest close: wiring `hevBr_of_regularData` into `residueSum_eq_zero_ofBundleBranchCoherence`, so
the per-branch input is reduced from the (false/hard) Puiseux frame all the way to the **single standard
residual** `αBr b₀ = ω₀·g near the fibre` (`hαBrAgreeBr`) — every other branch-value obligation is
discharged from the regular-value data the constructor already requires.  This is the §VIII.3 branch
crux closed along the monodromy-free symmetric-SUM path: at branch values, only the local-holomorphic
form `αBr = ω₀·g` remains, exactly the plan's step 1. -/

/-- **Gate A `∑Res = 0`, branch input = the `αBr`-agreement only.**  Identical scaffolding to
`residueSum_eq_zero_ofBundleBranch`, but the entire per-branch bundle data (`hbridgeBr`) is discharged
from the **regular-value data** (already required) + the per-branch local form-agreement `hαBrAgreeBr`
(`αBr b₀ = ω₀·g` at the fibre points near `b₀`).  No monodromy, no Puiseux frame, no new geometric input
at branch values: the same regular-value sphere machinery closes the branch-value crux. -/
theorem residueSum_eq_zero_ofBundleBranchAgree (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    (br : Finset ℂ)
    (Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderivReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source)
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀)
    (αBr : ℂ → HolomorphicOneForms X)
    (hbrBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere)
    -- The single per-branch residual: the local-holomorphic form `αBr b₀ = ω₀·g` at the fibre points.
    (hαBrAgreeBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀, ∀ (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
        (αBr b₀).toFun ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))
          = g ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_ofBundleBranchCoherence hac Φ m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj
    hxs_mem hxs_surj secFin hsecFin_base hsecFin_smooth hsecFin_sec hselFin br Sreg hderivReg
    hmeroReg hΦinjReg hΦrangeReg hsheetInjReg hsheetMemReg hCreg_g hncF αBr hbrBr
    (fun b₀ hb₀br hb₀cs =>
      hevBr_of_regularData ω₀ g f Φ cs br (αBr b₀) Sreg hderivReg hmeroReg hΦinjReg hΦrangeReg
        hsheetInjReg hsheetMemReg (hαBrAgreeBr b₀ hb₀br hb₀cs))
    hglue_inf hcont_int R₀ hR₀_an hR₀0 hR₀_eq

end Jacobians.Dolbeault.FormTraceGlobal
