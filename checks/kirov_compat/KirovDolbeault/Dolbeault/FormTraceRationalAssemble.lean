/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceRationalReduce
import KirovDolbeault.Dolbeault.FormTraceInftyFibre

/-!
# `TraceRationalityWitness` from uniform trace agreement (Gate A, §VIII.3 — the single deep obligation)

`Jacobians.Dolbeault.FormTraceRationalReduce` reduced the `hL32` field of `TraceRationalityWitness` to
the per-finite-centre **trace agreement**, and isolated `infty_eq` as the remaining analytic atom.
`Jacobians.Dolbeault.FormTraceInftyFibre` then reduced `infty_eq` (in its proved reciprocal-chart
form) to the **reciprocal-chart trace agreement** over the pole fibre — *structurally identical* to the
finite case.  This file assembles both: it produces the full `TraceRationalityWitness` (and Gate A
`∑Res=0`) from a **single uniform input** — a rational `LaurentForm L` whose coefficient germ-agrees
with the trace `Tr_F α` at *every* fibre (finite charts at the finite centres, the reciprocal chart at
`∞`).

This pins the entire remaining §VIII.3 wall to one precise, honest statement: the meromorphic trace
`Tr_F α` on the compact `ℂℙ¹` is **rational** — there is a `LaurentForm L` representing it (germ-equal
to it in every chart).  Both residue conditions (`hL32` at the finite centres, `infty_eq` at `∞`) then
hold *by Lemma 3.2 at the respective fibre* (the proved `resAt_traceCoeff_fibreTrace` /
`resAt_traceCoeff_inftyFibreTrace`).  Everything else in the chain to `∑Res=0` is proved, axiom-clean.

## The single obligation, packaged

`TraceAgreementData ω₀ g f poles hac` bundles the honest §VIII.3 output:

* `L` — the rational `1`-form (the trace's partial-fraction expansion);
* `hcenters` — the `L`-centres are exactly the finite pole-values (discrete bookkeeping);
* `Dinf` — the `∞`-fibre enumeration (the poles of `α` over `∞`), an `InftyFibreData` whose `xs`
  enumerates `F⁻¹(∞) ∩ poles`;
* `hagree_fin` — `L.R` germ-agrees with the trace coefficient near each finite centre;
* `hagree_inf` — `recipCoeff L.R` germ-agrees with the `∞`-fibre trace coefficient near `0`.

The two `hagree_*` together are exactly "`L` represents `Tr_F α` on `ℂℙ¹`" (germ-equality in every
chart) — the rationality of the trace.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceRationalityWitness_of_agreementData` — the full `TraceRationalityWitness` from
  `TraceAgreementData`;
* `residueSum_eq_zero_of_agreementData` — Gate A `∑Res=0` from `TraceAgreementData`;
* `traceAgreementData_holomorphic` / `residueSum_eq_zero_holomorphic_via_agreementData` —
  **non-vacuity end-to-end**: in the empty-pole (globally-holomorphic) case the agreement data exists
  (empty `LaurentForm`, empty `∞` fibre), so the whole assembly is sound (not a disguised `False`).

## The minimal remaining obligation

Gate A `∑ₐ Resₐ(α) = 0` is now *unconditional modulo a single construction*:

> for a suitable adapted cover `f`, build a `TraceAgreementData ω₀ g f poles hac` — i.e. exhibit the
> rational `LaurentForm` representing `Tr_F α` and prove it germ-agrees with the trace in every chart.

This is the genuine §VIII.3 trace-rationality wall (the global meromorphic trace on compact `ℂℙ¹` is
rational; partial-fraction extraction + germ-agreement), the same fibre/sheet/branched-cover apparatus
as `exists_properMapDegree`.  See the diagnosis in `FormTraceGlobalConstruct` / `FormResidueTheorem`.

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
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormResidueTheorem

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The uniform trace-agreement datum (the single §VIII.3 obligation) -/

/-- **The trace-agreement datum** for an adapted cover: the honest §VIII.3 output that
`TraceRationalityWitness` reduces to.  A rational `LaurentForm L` representing `Tr_F α` on `ℂℙ¹`,
together with the discrete centre bookkeeping and the **uniform germ-agreement** of `L` with the trace
in every chart (finite charts at the finite centres, the reciprocal chart at `∞`).  Bundling both
residue conditions into agreement makes the remaining obligation a single statement: the trace is
rational. -/
structure TraceAgreementData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The rational `1`-form representing `Tr_F α` on `ℂℙ¹`. -/
  L : LaurentForm
  /-- The `L`-centres, mapped to the sphere, are exactly the finite pole-values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre enumeration: an `InftyFibreData` whose `xs` enumerates the poles of `α` over `∞`. -/
  Dinf : InftyFibreData g f
  /-- `Dinf.xs` is injective (each `∞`-fibre pole enumerated once). -/
  hxs_inj : Function.Injective Dinf.xs
  /-- `Dinf.xs` lands in `poles`, in the fibre `F⁻¹(∞)`. -/
  hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- `Dinf.xs` enumerates **all** the poles of `α` over `∞`. -/
  hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- **Finite agreement.**  Near each finite centre `p`, `L.R` germ-agrees with the trace coefficient
  (the honest "`L.R` is the partial-fraction expansion of `Tr_F α`" condition). -/
  hagree_fin : ∀ p ∈ (Finset.univ.image L.a),
    L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff
  /-- **Reciprocal-chart (`∞`) agreement.**  Near `0`, `recipCoeff L.R` germ-agrees with the
  `∞`-fibre trace coefficient (the honest Lemma-3.2-at-`∞` form). -/
  hagree_inf : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff

/-! ### The full witness and Gate A from the agreement datum -/

/-- **`TraceRationalityWitness` from the uniform trace agreement.**  Given a `TraceAgreementData`
(the rational `L` + the centre bookkeeping + the `∞`-fibre enumeration + finite and reciprocal-chart
agreement), assemble the full `TraceRationalityWitness ω₀ g f poles hac`.

*Proof.*  `hcenters` is passed through; the finite agreement gives `hL32` via the proved
`traceRationalityWitness_of_agree`; the reciprocal-chart agreement gives the reciprocal-chart
`infty_eq` (`resAt (recipCoeff L.R) 0 = ∑_{∞-fibre} Res`) via
`resAt_recipCoeff_eq_inftyResidueSum_of_agree`, which `traceRationalityWitness_of_agree_recip` lifts to
the `infty_eq` field through the proved bridge `resAtInfty_eq_resAt_recipCoeff`. -/
def traceRationalityWitness_of_agreementData (hac : AdaptedCover ω₀ g f poles)
    (A : TraceAgreementData ω₀ g f poles hac) :
    TraceRationalityWitness ω₀ g f poles hac :=
  traceRationalityWitness_of_agree_recip hac A.L A.hcenters A.hagree_fin
    (resAt_recipCoeff_eq_inftyResidueSum_of_agree ω₀ f A.Dinf A.L poles
      A.hxs_inj A.hxs_mem A.hxs_surj A.hagree_inf)

/-- **Gate A from the uniform trace agreement.**  If an adapted cover and a `TraceAgreementData`
(the rational trace `L` germ-agreeing with `Tr_F α` in every chart) exist, then the 1-form residue
theorem `∑ₐ Resₐ(α) = 0` holds *unconditionally* for `α = ω₀·g`.  This composes
`traceRationalityWitness_of_agreementData` with the proved `residueSum_eq_zero_of_adapted`. -/
theorem residueSum_eq_zero_of_agreementData (hac : AdaptedCover ω₀ g f poles)
    (A : TraceAgreementData ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_adapted hac (traceRationalityWitness_of_agreementData hac A)

/-! ### Non-vacuity of the agreement datum (end-to-end soundness)

In the globally-holomorphic (empty-pole) case the agreement datum exists — the empty `LaurentForm`
(no centres, `R ≡ 0`, `recipCoeff R ≡ 0`), the empty `∞` fibre, vacuous finite agreement, and the
reciprocal agreement `0 =ᶠ 0`.  This confirms the assembly is honest (satisfiable), not a disguised
`False`, and matches `traceRationalityWitness_holomorphic`. -/

/-- The empty `∞`-fibre datum (no `∞`-fibre poles): index `Empty`, vacuous regularity. -/
noncomputable def emptyInftyFibreData (g : X → ℂ) (f : MeromorphicFunction X) :
    InftyFibreData g f where
  ι := Empty
  fintype_ι := inferInstance
  xs := fun e => e.elim
  hrecip_an := fun e => e.elim
  hrecip_deriv := fun e => e.elim
  hrecip_val := fun e => e.elim
  hg_mero := fun e => e.elim

/-- The `∞`-fibre trace over the empty fibre has trace coefficient `≡ 0` (empty sum). -/
theorem inftyFibreTrace_emptyData_traceCoeff (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) :
    (inftyFibreTrace ω₀ f (emptyInftyFibreData g f)).traceCoeff = fun _ => (0 : ℂ) := by
  funext w
  show (∑ i : Empty, _) = (0 : ℂ)
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- **`TraceAgreementData` non-vacuity.**  In the globally-holomorphic (empty-pole) case, a
`TraceAgreementData` exists for the empty `LaurentForm` and empty `∞` fibre: `hcenters` holds (both
sides empty), the finite agreement is vacuous, and the reciprocal agreement is `recipCoeff 0 ≡ 0 =ᶠ 0`
(the empty `∞`-trace coefficient).  Hence the agreement-based assembly is honest (satisfiable). -/
noncomputable def traceAgreementData_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    TraceAgreementData ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  hcenters := by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp
  Dinf := emptyInftyFibreData g f
  hxs_inj := fun i => i.elim
  hxs_mem := fun i => i.elim
  hxs_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)
  hagree_fin := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  hagree_inf := by
    rw [inftyFibreTrace_emptyData_traceCoeff ω₀ f]
    -- `recipCoeff (emptyLaurentForm.R) = recipCoeff (fun _ => 0) = fun _ => 0`.
    have hR : Jacobians.ResidueTheoremX.emptyLaurentForm.R = fun _ => (0 : ℂ) :=
      Jacobians.ResidueTheoremX.emptyLaurentForm_R
    rw [hR]
    filter_upwards with ζ
    show recipCoeff (fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

/-- **Gate A, holomorphic case, via the agreement datum (non-vacuity end-to-end).**  In the empty-pole
case, `residueSum_eq_zero_of_agreementData` applied to `traceAgreementData_holomorphic` yields
`∑_{a ∈ ∅} Res_a(α) = 0` — confirming the entire uniform-agreement assembly produces a real `∑Res=0`
(here trivially `0 = 0`). -/
theorem residueSum_eq_zero_holomorphic_via_agreementData (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_agreementData (adaptedCover_empty ω₀ g f hdiv)
    (traceAgreementData_holomorphic ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceGlobal
