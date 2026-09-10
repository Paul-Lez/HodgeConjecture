/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobalFunction
import KirovDolbeault.Dolbeault.FormTraceMeromorphic
import KirovDolbeault.Dolbeault.FormTraceGlobalTAssemble

/-!
# The geometric global trace function `T` from a global fibre selection (Gate A, §VIII.3 — geometry)

`Jacobians.Dolbeault.FormTraceGlobalTAssemble` assembles Gate A (`∑ₐ Resₐ(α) = 0`) from a *single*
value-chart trace function `T : ℂ → ℂ` together with the glue hypotheses
`hglue_fin`/`hglue_inf`/`hT_off`/`R₀ 0 = 0` (the constructor `globalTrace_of_glue`).  This file builds
the **geometric `T`** — Miranda's trace `Tr_F α` of `α = ω₀·g` along the branched cover
`F = f.toRiemannSphere`, read in the value chart — directly from a *global fibre selection* `Φ` that
chooses, at each base value `b : ℂ`, a `FibreRegularData g f b` (a finite family of regular non-pole
fibre points with the planar section germs).  Concretely

> `valueChartTrace ω₀ f Φ b := (fibreTrace ω₀ f (Φ b)).traceCoeff b`,

the value-chart `dz`-coefficient of the fibre sum `∑_{sheets} (coeff i)·deriv(sheet i)` over the
chosen fibre `Φ b`.

This is the genuinely-geometric layer: `valueChartTrace` is built from the *same* `fibreTrace.traceCoeff`
machinery the glue hypothesis `hglue_fin` of `globalTrace_of_glue` compares against (which uses the
**pole sub-fibre** selection `fibreReg hac`).  So the substantial §VIII.3 monodromy content — the
global trace being a single holomorphic function off the exceptional set, and germ-agreeing with each
local fibre trace — is isolated as the **germ-coherence hypotheses** `hcoh_fin`/`hcoh_off`: that the
geometric `valueChartTrace` germ-equals a *fixed* local fibre trace near each value.  Producing those
germ equalities is the branched-cover sheet-gluing (the bundle `TraceForm.traceForm` provides it for
the holomorphic frame; the function-weighted/meromorphic case is the remaining geometric frontier);
here we lay the definition and the honest reduction, leaving the coherence as the minimal named input.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `valueChartTrace` (`T Φ`) — the geometric global trace function from a global fibre selection.
* `analyticAt_valueChartTrace_of_eventuallyEq` — `valueChartTrace ω₀ f Φ` is **analytic** at a base
  value `b` *given* it germ-equals a fixed regular fibre trace `D` over `b` (with `g`'s chart-pullback
  analytic at each fibre point of `D`).  Routes through `analyticAt_of_eventuallyEq_regularFibreTrace`;
  this is the off-exceptional analyticity once the germ-coherence is in hand.
* `residueSum_eq_zero_of_geometricSelection` — **Gate A `∑Res = 0` from the geometric selection** plus
  the germ-coherence hypotheses, wired into `residueSum_eq_zero_of_glue`.  This is the honest reduction:
  with `T := valueChartTrace ω₀ f Φ`, every glue field of `globalTrace_of_glue` is supplied from the
  geometric selection and the precisely-named coherence, so Gate A holds unconditionally modulo the
  branched-cover germ-coherence + kirovGenus-`0` `∞`-vanishing.

## The honest soundness note (pole sub-fibre vs full fibre)

`globalTrace_of_glue`'s `hglue_fin` glues `T` to the *pole sub-fibre* trace `fibreReg hac p` (the
sheets through the poles of `α` over `p`), **not** the full fibre `F⁻¹(coe p)`.  The genuine geometric
trace sums over the *full* fibre; the two coincide as germs precisely when the cover separates the
poles of `α` from the regular fibre points over each pole-value (the regular sheets are holomorphic,
so they share the residue but not the germ unless absent from the selection).  We therefore phrase the
finite glue as the coherence hypothesis `hcoh_fin i : valueChartTrace … =ᶠ[𝓝[≠] cs i] (fibreReg …)`
directly — the precise honest content — rather than asserting a false full-fibre germ-equality.  The
separation requirement is folded into the global selection `Φ` (a Gate-D refinement; see
`gate_a_global_trace_T_status_2026-06-08.md`).

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
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The geometric global trace function from a global fibre selection

A **global fibre selection** is a choice, at each base value `b : ℂ`, of a `FibreRegularData g f b`
(the finite family of regular non-pole fibre points over `b` together with their planar section germs
and the meromorphy of `g`'s chart-pullback there).  Miranda's trace `Tr_F α` of `α = ω₀·g`, read in
the value chart, is then the per-value local fibre trace coefficient of the selected fibre. -/

/-- **The geometric global trace function `T`** of `α = ω₀·g` along `F = f.toRiemannSphere`, from a
global fibre selection `Φ : (b : ℂ) → FibreRegularData g f b`: at each base value `b`, the value-chart
`dz`-coefficient `(fibreTrace ω₀ f (Φ b)).traceCoeff b` of the fibre sum over the selected fibre.
This is the geometric trace read in the affine value chart; it is the *same* `fibreTrace.traceCoeff`
object the glue hypothesis of `globalTrace_of_glue` compares against. -/
noncomputable def valueChartTrace (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) : ℂ → ℂ :=
  fun b => (fibreTrace ω₀ f (Φ b)).traceCoeff b

@[simp] theorem valueChartTrace_apply (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (b : ℂ) :
    valueChartTrace ω₀ f Φ b = (fibreTrace ω₀ f (Φ b)).traceCoeff b := rfl

/-! ### Off-exceptional analyticity (`hT_off` ingredient)

`valueChartTrace ω₀ f Φ` evaluated at a *nearby* point `b'` uses a *different* selected fibre `Φ b'`,
so pointwise analyticity at `b` is **not** automatic from single-fibre analyticity — it requires the
selection to be locally coherent (the bundle-coherence / monodromy content).  We therefore route
analyticity through the germ-equality with a *fixed* regular fibre `D` over `b`: once
`valueChartTrace ω₀ f Φ` germ-equals `(fibreTrace ω₀ f D).traceCoeff` near `b` (the coherence) and `D`
is regular off the poles of `α`, analyticity follows from `analyticAt_of_eventuallyEq_regularFibreTrace`
(the proved off-centre analyticity bridge of `FormTraceGlobalFunction`). -/

/-- **Off-exceptional analyticity of the geometric trace, via germ-coherence.**  If
`valueChartTrace ω₀ f Φ` germ-equals (on a full neighbourhood of `b`) the local trace coefficient of a
*fixed* regular fibre `D` over `b` — with `g`'s chart-pullback analytic at every fibre point of `D`
(so `b` is off the poles of `α`) — then `valueChartTrace ω₀ f Φ` is **analytic at `b`**.  This is the
honest `hT_off` ingredient: the geometric trace is holomorphic off the finite exceptional set *given*
the local germ-coherence with a regular fibre (the off-branch sheet-gluing). -/
theorem analyticAt_valueChartTrace_of_eventuallyEq (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b : ℂ}
    (D : FibreRegularData g f b)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z))
      ((chartAt ℂ (D.xs i)) (D.xs i)))
    (hcoh : valueChartTrace ω₀ f Φ =ᶠ[𝓝 b] (fibreTrace ω₀ f D).traceCoeff) :
    AnalyticAt ℂ (valueChartTrace ω₀ f Φ) b :=
  analyticAt_of_eventuallyEq_regularFibreTrace ω₀ f D hg hcoh

/-! ### Gate A from the geometric selection (the honest reduction)

With `T := valueChartTrace ω₀ f Φ`, every glue field of `globalTrace_of_glue` is supplied from the
geometric selection and the germ-coherence:

* `hglue_fin i` — the *coherence at the finite pole-value* `cs i`: `valueChartTrace` germ-equals the
  pole sub-fibre trace `(fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff` off `cs i`;
* `hglue_inf` — the *coherence at `∞`*: `recipCoeff (valueChartTrace …)` germ-equals the `∞`-fibre
  trace coefficient off `0`;
* `hT_off z` — analyticity off the centres, supplied per-centre via the regular-fibre germ-coherence
  (`analyticAt_valueChartTrace_of_eventuallyEq`), here packaged as a direct hypothesis `hT_off`
  (the off-exceptional half is `analyticAt_valueChartTrace_of_eventuallyEq` applied at each regular
  value);
* `hcont_int` / `hR₀_eq` — junk-freeness and the kirovGenus-`0` `∞`-vanishing, as in `globalTrace_of_glue`.

This theorem packages those into `residueSum_eq_zero_of_glue`, so Gate A holds unconditionally modulo
the branched-cover germ-coherence + the kirovGenus-`0` `∞`-vanishing — the precise minimal obligation. -/

/-- **Gate A `∑Res = 0` from the geometric global trace `valueChartTrace`.**  Taking
`T := valueChartTrace ω₀ f Φ` (the geometric trace from a global fibre selection `Φ`), Gate A's
1-form residue theorem holds *unconditionally* for `α = ω₀·g` given the germ-coherence of the
geometric trace with the local fibre traces (`hglue_fin`/`hglue_inf`), its analyticity off the finite
centres (`hT_off`), junk-freeness (`hcont_int`), and the kirovGenus-`0` `∞`-vanishing (`hR₀_*`).  This is
`residueSum_eq_zero_of_glue` specialised to the geometric `T`.

The deep §VIII.3 monodromy content is exactly the two coherence inputs `hglue_fin`/`hglue_inf` (the
geometric trace germ-equals the pole sub-fibre / `∞`-fibre trace) plus `hT_off`; `analyticAt_valueChartTrace_of_eventuallyEq`
reduces `hT_off` further to per-regular-value germ-coherence with a regular fibre. -/
theorem residueSum_eq_zero_of_geometricSelection (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b) {m : ℕ} (cs : Fin m → ℂ) (ρ : ℝ)
    (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ) (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hglue_fin : ∀ i, valueChartTrace ω₀ f Φ
      =ᶠ[𝓝[≠] cs i] (fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff)
    (hglue_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hT_off : ∀ z ∉ Finset.univ.image cs, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTrace ω₀ f Φ - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_glue hac (valueChartTrace ω₀ f Φ) cs ρ hcs_ball hcs_inj hcenters_cs
    Dinf hxs_inj hxs_mem hxs_surj hglue_fin hglue_inf hT_off hcont_int R₀ hR₀_an hR₀0 hR₀_eq

/-! ### Discharging `hT_off` from per-regular-value coherence

The off-exceptional analyticity `hT_off` is itself reducible to the same kind of germ-coherence as the
finite glue: at every value `z` off the finite centres, the geometric trace germ-equals a *fixed*
regular fibre `Dreg z` over `z` (the off-branch sheet-gluing), and that regular fibre has `g`'s
chart-pullback analytic at each fibre point (`z` is a regular value off the poles of `α`).  Packaging
that per-value coherence as `hreg` discharges `hT_off` via `analyticAt_valueChartTrace_of_eventuallyEq`,
so the *only* inputs left are the finite/∞ glue, the per-value off-exceptional coherence, junk-freeness,
and the kirovGenus-`0` `∞`-vanishing — the minimal §VIII.3 obligation. -/

/-- **Gate A from the geometric selection with `hT_off` discharged from coherence.**  Identical to
`residueSum_eq_zero_of_geometricSelection` except the off-centre analyticity `hT_off` is *replaced* by
the per-regular-value coherence `hreg`: for every `z` off the finite centres, a regular fibre `Dreg z`
over `z` with `g`'s chart-pullback analytic at each fibre point and the geometric trace germ-equal to
`(fibreTrace ω₀ f (Dreg z)).traceCoeff` near `z`.  `hT_off` is then
`analyticAt_valueChartTrace_of_eventuallyEq`.  This isolates the irreducible content to exactly the
germ-coherence (finite, `∞`, and off-exceptional) + junk-freeness + the kirovGenus-`0` `∞`-vanishing. -/
theorem residueSum_eq_zero_of_geometricSelection_coh (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b) {m : ℕ} (cs : Fin m → ℂ) (ρ : ℝ)
    (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ) (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hglue_fin : ∀ i, valueChartTrace ω₀ f Φ
      =ᶠ[𝓝[≠] cs i] (fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff)
    (hglue_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hreg : ∀ z ∉ Finset.univ.image cs, ∃ Dreg : FibreRegularData g f z,
      (∀ i, AnalyticAt ℂ (fun w => g ((chartAt ℂ (Dreg.xs i)).symm w))
        ((chartAt ℂ (Dreg.xs i)) (Dreg.xs i))) ∧
      valueChartTrace ω₀ f Φ =ᶠ[𝓝 z] (fibreTrace ω₀ f Dreg).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTrace ω₀ f Φ - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  refine residueSum_eq_zero_of_geometricSelection hac Φ cs ρ hcs_ball hcs_inj hcenters_cs
    Dinf hxs_inj hxs_mem hxs_surj hglue_fin hglue_inf ?_ hcont_int R₀ hR₀_an hR₀0 hR₀_eq
  intro z hz
  obtain ⟨Dreg, hg_an, hcoh⟩ := hreg z hz
  exact analyticAt_valueChartTrace_of_eventuallyEq ω₀ f Φ Dreg hg_an hcoh

/-! ### Non-vacuity of the geometric reduction (end-to-end soundness)

The geometric constructors are *satisfiable*, not a disguised `False`: in the globally-holomorphic
(empty-pole) case the **empty fibre selection** `Φ p := emptyFibreRegularData g f p` gives
`valueChartTrace ω₀ f Φ ≡ 0` (an empty fibre sum), with all the deep inputs (glue, off-exceptional
coherence, junk-freeness) vacuous over the empty centre set, the `∞`-glue `recipCoeff 0 ≡ 0` matching
the empty `∞`-trace, and the kirovGenus-`0` continuation `R₀ ≡ 0` vanishing.  This confirms the geometric
reduction produces a genuine `∑Res = 0`. -/

/-- **The empty fibre selection gives the zero geometric trace.**  With `Φ p := emptyFibreRegularData
g f p` (no fibre points over any value), `valueChartTrace ω₀ f Φ ≡ 0` — the empty fibre sum.  The base
case the non-vacuity witness uses. -/
theorem valueChartTrace_emptySelection (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    valueChartTrace ω₀ f (fun p => emptyFibreRegularData g f p) = fun _ => (0 : ℂ) := by
  funext b
  rw [valueChartTrace_apply]
  show (∑ _i : Empty, _) = (0 : ℂ)
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- **Non-vacuity of the geometric Gate-A reduction.**  For the empty pole set the geometric reduction
`residueSum_eq_zero_of_geometricSelection` is satisfiable via the empty fibre selection: the geometric
trace is `≡ 0` (`valueChartTrace_emptySelection`), all deep inputs are vacuous over the empty centre
set, the `∞`-glue is `recipCoeff 0 ≡ 0`, and `R₀ ≡ 0` vanishes — yielding `∑Res = 0`.  Confirms the
geometric reduction is honest (not a disguised `False`), mirroring `residueSum_eq_zero_of_data_holomorphic`. -/
theorem residueSum_eq_zero_of_geometricSelection_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 := by
  classical
  have hzero := valueChartTrace_emptySelection (g := g) ω₀ f
  refine residueSum_eq_zero_of_geometricSelection (adaptedCover_empty ω₀ g f hdiv)
    (fun p => emptyFibreRegularData g f p) (m := 0) (Fin.elim0) 0
    (fun i => i.elim0) (fun i => i.elim0)
    (by simp) (emptyInftyFibreData g f)
    (fun i => i.elim) (fun i => i.elim) (fun a ha _ => absurd ha (Finset.notMem_empty a))
    (fun i => i.elim0) ?_ (fun z _ => ?_) ?_ (fun _ => 0) analyticAt_const rfl ?_
  · -- hglue_inf: `recipCoeff 0 =ᶠ 0` (empty `∞`-trace).
    rw [hzero, inftyFibreTrace_emptyData_traceCoeff ω₀ f, recipCoeff_zero]
  · -- hT_off: `valueChartTrace ≡ 0` analytic everywhere.
    rw [hzero]; exact analyticAt_const
  · -- hcont_int: vacuous (the centre image is empty, `cs = Fin.elim0`).
    intro L hLa _ p hp
    rw [hLa, Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0))] at hp
    exact absurd hp (Finset.notMem_empty p)
  · -- hR₀_eq: `recipCoeff (0 − L.R) =ᶠ 0`.  The centre image `univ.image L.a = univ.image cs = ∅`
    -- (empty centres, `cs = Fin.elim0`), so `univ : Finset L.ι = ∅` and `L.R ≡ 0`.
    intro L hLa
    rw [hzero]
    have hLR0 : L.R = fun _ => (0 : ℂ) := by
      have hempty : (Finset.univ : Finset L.ι) = ∅ :=
        Finset.image_eq_empty.mp
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      funext z
      show (∑ p : L.ι, L.c p * (z - L.a p) ^ L.n p) = 0
      rw [hempty, Finset.sum_empty]
    rw [hLR0]
    filter_upwards with ζ
    show recipCoeff ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

end Jacobians.Dolbeault.FormTraceGlobal
