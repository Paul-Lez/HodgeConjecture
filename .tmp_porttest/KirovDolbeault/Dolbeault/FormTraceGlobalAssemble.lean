/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceRationalAssemble
import KirovDolbeault.Dolbeault.FormTraceLiouville

/-!
# `TraceAgreementData` from a global trace datum (Gate A, §VIII.3 — steps 1–3 assembled)

`Jacobians.Dolbeault.FormTraceRationalAssemble` reduced Gate A (`∑ₐ Resₐ(α) = 0`) to a single
`TraceAgreementData`: a rational `LaurentForm L` that **germ-agrees with the meromorphic trace
`Tr_F α`** in every chart (finite charts at the finite pole-values, the reciprocal chart at `∞`).
The `hagree_*` fields demand `L.R =ᶠ Tr_F α`, i.e. you must *already know* `L` equals the trace —
which is the whole §VIII.3 argument.

This file splits that into the honest three-step Miranda programme by packaging the **global trace
datum** `GlobalTrace`:

1. **The global trace function** `T : ℂ → ℂ` — the value-chart `dz`-coefficient of `Tr_F α` on the
   finite part of `ℂℙ¹`, agreeing with each *local* fibre trace near each regular value (the glue
   fields `hglue_fin` / `hglue_inf`).  This is the trace as a single function (steps 1–2 — per-sheet
   pushforwards assembled, holomorphic off the finite exceptional set by `analyticAt_traceCoeff`).
2. **The principal parts** `L : LaurentForm` — the partial-fraction expansion at the finite poles
   (`hcenters`), chosen so the **remainder `T − L.R` is a global holomorphic `1`-form**: entire on
   `ℂ` (`hentire`) and holomorphic across `∞` (`hrecip` — `recipCoeff (T − L.R)` continuous at `0`).
3. **The remainder vanishes** — by the kirovGenus-`0` Liouville vanishing
   (`FormTraceLiouville.coeff_eq_zero_of_entire_of_recipCoeff_continuousAt`), `T − L.R = 0`, so
   `L.R = T = Tr_F α` everywhere; the `hagree_*` fields of `TraceAgreementData` then follow from the
   glue fields by rewriting `L.R = T`.

The genuine §VIII.3 content is concentrated in the two analytic fields `hentire` / `hrecip` (the
trace minus its principal parts is a global holomorphic form on the compact `ℂℙ¹`) plus the glue
fields (the global trace agrees with the local fibre traces — essentially the definition of the
trace).  Everything else — the principal-part subtraction's vanishing and the descent to `∑Res = 0`
— is proved here, axiom-clean.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceAgreementData_of_globalTrace` — the full `TraceAgreementData` from a `GlobalTrace` (the
  Liouville vanishing + the glue fields);
* `residueSum_eq_zero_of_globalTrace` — Gate A `∑Res = 0` from a `GlobalTrace`;
* `globalTrace_holomorphic` / `residueSum_eq_zero_holomorphic_via_globalTrace` — **non-vacuity
  end-to-end**: in the empty-pole (globally-holomorphic) case the global trace datum exists (`T ≡ 0`,
  empty `LaurentForm`, empty `∞` fibre), so the assembly is sound (not a disguised `False`).

## The minimal remaining obligation

Gate A is now *unconditional modulo* the construction of a `GlobalTrace` for a suitable adapted
cover — i.e. the trace as a single meromorphic function whose principal-part remainder is a global
holomorphic form.  The irreducible analytic content is `hentire` / `hrecip`.

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
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The global trace datum (the honest steps-1–2 packaging) -/

/-- **The global trace datum** for an adapted cover.  Packages the meromorphic trace `Tr_F α` on
`ℂℙ¹` as a single value-chart coefficient function `T : ℂ → ℂ`, together with the partial-fraction
expansion `L` at the finite poles and the **holomorphic-remainder** data: the principal-part
subtraction `T − L.R` is a global holomorphic `1`-form on the compact `ℂℙ¹`.  Splitting the
`TraceAgreementData.hagree_*` (which demand `L.R =ᶠ Tr_F α`) into the **glue** of `T` with the local
fibre traces (`hglue_fin`/`hglue_inf`, the definition of the trace) and the **remainder vanishing**
(`hentire`/`hrecip`, the kirovGenus-`0` Liouville input) isolates the genuine §VIII.3 content. -/
structure GlobalTrace (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The global value-chart `dz`-coefficient of the trace `Tr_F α` on the finite part of `ℂℙ¹`. -/
  T : ℂ → ℂ
  /-- The partial-fraction expansion of the trace at its finite poles. -/
  L : LaurentForm
  /-- The `L`-centres, mapped to the sphere, are exactly the finite pole-values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre enumeration (the poles of `α` over `∞`). -/
  Dinf : InftyFibreData g f
  /-- `Dinf.xs` is injective. -/
  hxs_inj : Function.Injective Dinf.xs
  /-- `Dinf.xs` lands in `poles`, in the fibre `F⁻¹(∞)`. -/
  hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- `Dinf.xs` enumerates **all** the poles of `α` over `∞`. -/
  hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- **Finite glue.**  Near each finite centre `p`, the global trace `T` agrees with the local fibre
  trace coefficient (the definition of `T` as the trace over the regular fibre). -/
  hglue_fin : ∀ p ∈ (Finset.univ.image L.a),
    T =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff
  /-- **Reciprocal-chart (`∞`) glue.**  Near `0`, the reciprocal-chart global trace `recipCoeff T`
  agrees with the `∞`-fibre trace coefficient. -/
  hglue_inf : recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff
  /-- **The remainder is entire** (holomorphic on all of `ℂ`): `T − L.R`, the trace minus its finite
  principal parts, has no finite poles. -/
  hentire : AnalyticOnNhd ℂ (T - L.R) Set.univ
  /-- **The remainder is holomorphic across `∞`**: the reciprocal coefficient of `T − L.R` is
  continuous at `0` (the kirovGenus-`0` Liouville input). -/
  hrecip : ContinuousAt (recipCoeff (T - L.R)) 0

namespace GlobalTrace

variable {hac : AdaptedCover ω₀ g f poles}

/-- **The trace equals its rational part** (the remainder vanishes by kirovGenus-`0` Liouville).  From the
holomorphic-remainder fields `hentire`/`hrecip`, `T − L.R` is a global holomorphic `1`-form on `ℂℙ¹`,
hence `0` (`FormTraceLiouville.coeff_eq_zero_of_entire_of_recipCoeff_continuousAt`), so `T = L.R`. -/
theorem T_eq_R (G : GlobalTrace ω₀ g f poles hac) : G.T = G.L.R :=
  coeff_eq_of_entire_diff_of_recipCoeff_continuousAt G.hentire G.hrecip

/-- **Finite agreement of `L.R` with the trace.**  Rewriting `L.R = T` (`T_eq_R`) turns the finite
glue field into the `TraceAgreementData.hagree_fin` form `L.R =ᶠ (fibreTrace …).traceCoeff`. -/
theorem hagree_fin (G : GlobalTrace ω₀ g f poles hac) :
    ∀ p ∈ (Finset.univ.image G.L.a),
      G.L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff := by
  intro p hp
  rw [← G.T_eq_R]
  exact G.hglue_fin p hp

/-- **Reciprocal-chart agreement of `recipCoeff L.R` with the `∞`-fibre trace.**  Rewriting
`L.R = T` (`T_eq_R`) turns the reciprocal glue field into the `TraceAgreementData.hagree_inf` form. -/
theorem hagree_inf (G : GlobalTrace ω₀ g f poles hac) :
    recipCoeff G.L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f G.Dinf).traceCoeff := by
  rw [← G.T_eq_R]
  exact G.hglue_inf

/-- **`TraceAgreementData` from a `GlobalTrace`.**  The centre/`∞`-fibre bookkeeping fields are
passed through; the two agreement fields come from the glue fields after the Liouville vanishing
`T = L.R` (`hagree_fin`/`hagree_inf`).  This is the honest assembly of steps 1–3 of the §VIII.3
trace-rationality programme. -/
def toTraceAgreementData (G : GlobalTrace ω₀ g f poles hac) :
    TraceAgreementData ω₀ g f poles hac where
  L := G.L
  hcenters := G.hcenters
  Dinf := G.Dinf
  hxs_inj := G.hxs_inj
  hxs_mem := G.hxs_mem
  hxs_surj := G.hxs_surj
  hagree_fin := G.hagree_fin
  hagree_inf := G.hagree_inf

end GlobalTrace

/-- **`TraceAgreementData` from a `GlobalTrace` (function form).** -/
def traceAgreementData_of_globalTrace (hac : AdaptedCover ω₀ g f poles)
    (G : GlobalTrace ω₀ g f poles hac) :
    TraceAgreementData ω₀ g f poles hac :=
  G.toTraceAgreementData

/-- **Gate A from a `GlobalTrace`.**  If an adapted cover and a `GlobalTrace` (the meromorphic trace
as a single function whose principal-part remainder is a global holomorphic form) exist, then the
1-form residue theorem `∑ₐ Resₐ(α) = 0` holds *unconditionally* for `α = ω₀·g`.  Composes
`traceAgreementData_of_globalTrace` with the proved `residueSum_eq_zero_of_agreementData`. -/
theorem residueSum_eq_zero_of_globalTrace (hac : AdaptedCover ω₀ g f poles)
    (G : GlobalTrace ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_agreementData hac (traceAgreementData_of_globalTrace hac G)

/-! ### Non-vacuity of the global trace datum (end-to-end soundness)

In the globally-holomorphic (empty-pole) case the global trace datum exists: the trace `T ≡ 0`, the
empty `LaurentForm` (no centres, `R ≡ 0`), the empty `∞` fibre.  The glue fields hold (`0 =ᶠ 0` —
the empty trace), the remainder `0 − 0 = 0` is entire with `recipCoeff 0` continuous at `0`.  This
confirms the assembly is honest (satisfiable), not a disguised `False`. -/

/-- `recipCoeff (fun _ => 0) = fun _ => 0`. -/
theorem recipCoeff_zero : recipCoeff (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext ζ; simp [recipCoeff]

/-- **`GlobalTrace` non-vacuity.**  In the globally-holomorphic (empty-pole) case, a `GlobalTrace`
exists with `T ≡ 0`, the empty `LaurentForm`, and the empty `∞` fibre: the glue fields hold (the
empty trace is `0`), and the remainder `0 − 0 = 0` is entire with `recipCoeff` continuous at `0`.
Hence the global-trace assembly is honest. -/
noncomputable def globalTrace_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    GlobalTrace ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  T := fun _ => 0
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  hcenters := by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp
  Dinf := emptyInftyFibreData g f
  hxs_inj := fun i => i.elim
  hxs_mem := fun i => i.elim
  hxs_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)
  hglue_fin := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  hglue_inf := by
    rw [inftyFibreTrace_emptyData_traceCoeff ω₀ f, recipCoeff_zero]
  hentire := by
    have hR : Jacobians.ResidueTheoremX.emptyLaurentForm.R = fun _ => (0 : ℂ) :=
      Jacobians.ResidueTheoremX.emptyLaurentForm_R
    rw [hR]
    have : (fun _ : ℂ => (0 : ℂ)) - (fun _ : ℂ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
      funext z; simp
    rw [this]
    exact analyticOnNhd_const
  hrecip := by
    have hR : Jacobians.ResidueTheoremX.emptyLaurentForm.R = fun _ => (0 : ℂ) :=
      Jacobians.ResidueTheoremX.emptyLaurentForm_R
    rw [hR]
    have hfun : (fun _ : ℂ => (0 : ℂ)) - (fun _ : ℂ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
      funext z; simp
    rw [hfun, recipCoeff_zero]
    exact continuousAt_const

/-- **Gate A, holomorphic case, via the global trace datum (non-vacuity end-to-end).**  In the
empty-pole case, `residueSum_eq_zero_of_globalTrace` applied to `globalTrace_holomorphic` yields
`∑_{a ∈ ∅} Res_a(α) = 0` — confirming the entire global-trace assembly produces a real `∑Res = 0`. -/
theorem residueSum_eq_zero_holomorphic_via_globalTrace (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_globalTrace (adaptedCover_empty ω₀ g f hdiv)
    (globalTrace_holomorphic ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceGlobal
