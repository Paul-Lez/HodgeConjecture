/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirect
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Genus-`0` discharge of Gate A's residual #5 (the `∞`-vanishing of the trace remainder)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_of_directGeometry`
(`SerreResidueDirect.lean`) closes Gate A `∑Res = 0` from the residue-level §VIII.3 geometry, but takes
as caller hypotheses the **kirovGenus-`0` `∞`-vanishing** field-group `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` (the
analytic continuation of `recipCoeff (T − L.R)` off `0`, **vanishing at `0`**) — the "residual #5"
that, before this file, was discharged *only* for the empty-pole case.

## The soundness finding (`R₀ 0 = 0` was the residue theorem in disguise)

With the principal-part `LaurentForm L` capturing the **finite** principal parts of the trace
`T := valueChartTracePatched ω₀ f Φ br`, the field `hR₀0 : R₀ 0 = 0` is — via
`continuousAt_recipCoeff_of_vanishing` — equivalent to `ContinuousAt (recipCoeff (T − L.R)) 0`, i.e. the
remainder `T − L.R` being holomorphic at `∞` *with no `dζ`-term* (`T − L.R = o(z⁻²)` at `∞`).  Since
`recipCoeff L.R` has a **simple pole** at `0` whose residue is `resAtInfty L.R`
(`resAtInfty_eq_resAt_recipCoeff`) and `recipCoeff T` has a simple pole at `0` whose residue is
`∑_{F a = ∞} formFnResidue` (the `∞`-fibre Lemma 3.2, via `hcoh_full`), continuity of `recipCoeff
(T − L.R)` at `0` **forces those two simple-pole residues to cancel** — which is exactly the `∞`-residue
identity `infty_eq`, and `infty_eq` together with the finite Lemma 3.2 and the `ℂℙ¹` residue theorem
**is** Gate A `∑Res = 0`.  So discharging `R₀ 0 = 0` for a *nonempty* trace through the `T = L.R` route
is **circular** with the theorem; the repo records the same fact at `FormTraceGlobalConstruct.lean`
(the "`infty_eq` circularity").

## The honest, non-circular discharge (the `∞`-residue, not the full vanishing)

The §VIII.3 close does **not** need the full vanishing `R₀ 0 = 0`; it only needs the *residue* of
`recipCoeff (T − L.R)` at `0` to vanish:

> `resAt (recipCoeff (T − L.R)) 0 = 0`.

This is **strictly weaker** than `R₀ 0 = 0` (the latter is the value at `0`, the former is the
`ζ⁻¹`-coefficient) and is **non-circular**: it is *Cauchy's theorem at infinity* — the residue at
infinity of an **entire** `1`-form coefficient vanishes, because `recipCoeff h = d/dζ [H(ζ⁻¹)]` for a
global primitive `H` of `h` (`Differentiable.isExactOn_univ`), so its small-circle integral vanishes
(`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`).  The entire-ness of `T − L.R` is the **finite**
junk-freeness `hcont_int` (genuinely about the finite centres, *not* `∞`), already an input.

So this file **fully discharges** the residual-#5 field-group `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq`,
re-deriving the `∞`-residue identity `infty_eq` from the *proven* `resAt (recipCoeff (T − L.R)) 0 = 0`
(Cauchy) plus the genuine `∞`-coherence `hcoh_full` (#6).  It also re-proves the **finite** Lemma-3.2
residue identity directly from the principal-part extraction (the residue of `T − L.R` at each finite
centre is `0` because it germ-equals an analytic function there — `exists_laurentForm_principalPart`),
*without* the global `T = L.R`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `resAt_recipCoeff_eq_zero_of_entire` — **Cauchy at infinity**: `resAt (recipCoeff h) 0 = 0` for `h`
  entire (`AnalyticOnNhd ℂ h Set.univ`).  The non-circular replacement of `R₀ 0 = 0`.
* `holoPunctured_recipCoeff_entire` / `meromorphicAt_recipCoeff_laurent` — the `HoloPunctured`/meromorphy
  inputs of `resAt` additivity at `0`.
* `resAt_eq_laurentR_of_principalPart` — the **finite residue match** `resAt T (cs i) = resAt L.R (cs i)`
  (free from the principal-part extraction; no `R₀`, no global `T = L.R`).
* `infty_eq_of_remainderResZero` — the **`∞`-residue identity** from `resAt (recipCoeff (T − L.R)) 0 = 0`
  + `hcoh_full`.
* `globalTraceData_of_genus0` / `residueTheorem_of_directGeometry_genus0` — the residue-level close of
  Gate A **without** the residual-#5 field-group, keeping only the finite junk-freeness `hcont_int` and
  the `∞`-coherence `hcoh_full`.
* `directTraceGeometry_ofCanonicalSimpleInfty_genus0` — the capstone constructor: a `DirectTraceGeometry`
  whose `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` fields are discharged internally.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* `FormTraceGlobalConstruct.lean` (the `infty_eq`
  circularity note).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## Cauchy at infinity: the `∞`-residue of an entire `1`-form coefficient vanishes

For an **entire** coefficient `h : ℂ → ℂ` of `dz`, the residue at infinity of `h dz` (read in the
reciprocal chart as `resAt (recipCoeff h) 0`) is `0`.  This is *Cauchy's theorem at `∞`*: `recipCoeff
h (ζ) = −h(ζ⁻¹)·ζ⁻² = d/dζ [H(ζ⁻¹)]` for a global primitive `H` of `h`, so on any small circle `C(0, r)`
the integral of `recipCoeff h` is the integral of a derivative around a closed loop avoiding `0`, hence
`0` (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`).  This is the **non-circular** replacement
of the kirovGenus-`0` `∞`-vanishing `R₀ 0 = 0`: it uses *only* entire-ness, never `∑Res = 0`. -/

/-- **Cauchy at infinity (the `∞`-residue of an entire `1`-form coefficient is `0`).**  For an entire
`h : ℂ → ℂ` (`AnalyticOnNhd ℂ h Set.univ`), `resAt (recipCoeff h) 0 = 0`.

*Proof.*  `h` is differentiable, so it has a global primitive `H` (`Differentiable.isExactOn_univ`:
`∀ z, HasDerivAt H (h z) z`).  On the circle `C(0, r)` (`0 < r < 1`), `recipCoeff h (ζ) = h(ζ⁻¹)·(−(ζ²)⁻¹)`
is the derivative of `ζ ↦ H(ζ⁻¹)` (chain rule, `ζ ≠ 0` on the circle), so the contour integral vanishes
(`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`); hence the residue is `0`. -/
theorem resAt_recipCoeff_eq_zero_of_entire {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h Set.univ) :
    resAt (recipCoeff h) 0 = 0 := by
  have hdiff : Differentiable ℂ h := fun z => (hh z (Set.mem_univ z)).differentiableAt
  obtain ⟨H, hH⟩ := hdiff.isExactOn_univ
  have hcint : ∀ r ∈ Set.Ioo (0 : ℝ) 1, (∮ ζ in C((0 : ℂ), r), recipCoeff h ζ) = 0 := by
    intro r hr
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := fun ζ : ℂ => H ζ⁻¹)
      hr.1.le (fun ζ hζ => ?_)
    have hζne : ζ ≠ 0 := by
      intro he
      rw [he, mem_sphere_iff_norm, sub_zero, norm_zero] at hζ
      exact (ne_of_lt hr.1) hζ
    have hcomp : HasDerivAt (fun ζ : ℂ => H (ζ⁻¹)) (h (ζ⁻¹) * (-(ζ ^ 2)⁻¹)) ζ :=
      (hH (ζ⁻¹) (Set.mem_univ _)).comp ζ (hasDerivAt_inv hζne)
    have hval : recipCoeff h ζ = h (ζ⁻¹) * (-(ζ ^ 2)⁻¹) := by
      show -(h (ζ⁻¹)) * ζ ^ (-2 : ℤ) = h (ζ⁻¹) * (-(ζ ^ 2)⁻¹)
      rw [zpow_neg, zpow_two]; ring
    rw [hval]
    exact hcomp.hasDerivWithinAt
  rw [resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall (by norm_num) hcint), smul_zero]

/-! ## `HoloPunctured`/meromorphy inputs for `resAt` additivity at `0` -/

/-- **`recipCoeff` of an entire coefficient has an isolated singularity at `0`.**  For `h` entire,
`recipCoeff h (ζ) = −h(ζ⁻¹)·ζ⁻²` is holomorphic on `ball 0 1 \ {0}` (the only singularity is the `ζ⁻²`
Jacobian at `0`); the `HoloPunctured` input of `resAt_add` at `0`. -/
theorem holoPunctured_recipCoeff_entire {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h Set.univ) :
    HoloPunctured (recipCoeff h) 0 := by
  refine ⟨1, one_pos, fun z hz => ?_⟩
  have hzne : z ≠ 0 := fun he => hz.2 (by rw [he]; exact Set.mem_singleton 0)
  show DifferentiableAt ℂ (fun ζ => -(h (ζ⁻¹)) * ζ ^ (-2 : ℤ)) z
  exact (((hh z⁻¹ (Set.mem_univ _)).differentiableAt.comp z (differentiableAt_inv hzne)).neg).mul
    (differentiableAt_zpow.mpr (Or.inl hzne))

/-- **The reciprocal coefficient of a `LaurentForm` is meromorphic at `0`.**  `recipCoeff L.R` splits
over the per-monomial reciprocals (`recipCoeff_R`), each meromorphic at `0` (an integer power of the
meromorphic `ζ ↦ ζ⁻¹ − a` times the `ζ⁻²` Jacobian).  Gives the `HoloPunctured` input at `0`. -/
theorem meromorphicAt_recipCoeff_laurent (L : LaurentForm) : MeromorphicAt (recipCoeff L.R) 0 := by
  rw [recipCoeff_R]
  have hsum : (fun ζ => ∑ i, (fun ζ => -(L.c i * (ζ⁻¹ - L.a i) ^ L.n i) * ζ ^ (-2 : ℤ)) ζ)
      = ∑ i, (fun ζ => -(L.c i * (ζ⁻¹ - L.a i) ^ L.n i) * ζ ^ (-2 : ℤ)) := by
    funext ζ; rw [Finset.sum_apply]
  rw [hsum]
  refine MeromorphicAt.sum (fun i _ => ?_)
  have hbase : MeromorphicAt (fun ζ : ℂ => (ζ⁻¹ - L.a i) ^ L.n i) 0 :=
    ((analyticAt_id.meromorphicAt).inv.sub (MeromorphicAt.const _ _)).zpow _
  exact ((((MeromorphicAt.const (L.c i) 0).mul hbase)).neg).mul ((analyticAt_id.meromorphicAt).zpow _)

/-! ## The finite residue match (free from the principal-part extraction)

The finite Lemma-3.2 residue reading `resAt T (cs i) = resAt L.R (cs i)` needs **only** that
`T − L.R` is analytic at `cs i` — the pole is removed.  This is the punctured-germ-analytic output of
`exists_laurentForm_principalPart` (`hLrem`), so it is *free*: no junk-freeness, no `R₀`, no global
`T = L.R`. -/

/-- **The finite residue match.**  At a finite centre `c`, if `T` is meromorphic at `c` and `T − L.R`
germ-equals an analytic function `R` off `c` (`hR_eq` — the pole removed, as `exists_laurentForm_principalPart`
supplies), then `resAt T c = resAt L.R c`.  *Proof.*  `resAt (T − L.R) c = resAt R c = 0` (analytic), and
`resAt` is additive, so `resAt T c = resAt L.R c`. -/
theorem resAt_eq_laurentR_of_principalPart {T : ℂ → ℂ} {L : LaurentForm} {c : ℂ}
    (hT : MeromorphicAt T c) {R : ℂ → ℂ} (hR_an : AnalyticAt ℂ R c)
    (hR_eq : (T - L.R) =ᶠ[𝓝[≠] c] R) :
    resAt T c = resAt L.R c := by
  have hLR : MeromorphicAt L.R c := by
    have hsum : L.R = ∑ i, (fun z => L.c i * (z - L.a i) ^ L.n i) := by
      funext z; rw [show L.R = fun z => ∑ i, L.c i * (z - L.a i) ^ L.n i from rfl, Finset.sum_apply]
    rw [hsum]
    exact MeromorphicAt.sum (fun i _ => LaurentForm.meromorphicAt_monomial _ _ _ _)
  have hrem0 : resAt (T - L.R) c = 0 := by
    rw [resAt_congr hR_eq]; exact resAt_eq_zero_of_analyticAt hR_an
  have hadd : resAt ((T - L.R) + L.R) c = resAt (T - L.R) c + resAt L.R c :=
    resAt_add (hT.sub hLR).holoPunctured hLR.holoPunctured
  have hsimp : (T - L.R) + L.R = T := by funext z; simp
  rw [hsimp, hrem0, zero_add] at hadd
  exact hadd

/-! ## The `∞`-residue identity from the entire-remainder `∞`-residue + the `∞`-coherence

`infty_eq` (`resAtInfty L.R L.ρ = ∑_{F a = ∞} formFnResidue ω₀ g a`) follows from:

* the `LaurentForm` bridge `resAtInfty L.R = resAt (recipCoeff L.R) 0`;
* the additivity `resAt (recipCoeff L.R) 0 = resAt (recipCoeff T) 0` (the remainder's `∞`-residue
  `resAt (recipCoeff (T − L.R)) 0 = 0` — Cauchy at `∞` for the entire `T − L.R`);
* the `∞`-fibre Lemma 3.2 `resAt (recipCoeff T) 0 = ∑_{F a = ∞} formFnResidue` (via `hcoh_full`).

No step assumes `∑Res = 0`: the kirovGenus-`0` content is `hcoh_full` (the geometric `∞`-coherence) and the
entire-ness of the remainder; the residue-zero step is Cauchy. -/

/-- **The `∞`-residue identity from the entire remainder + the `∞`-coherence (non-circular).**  Given:
`hentire` (the remainder `T − L.R` is entire — the finite junk-freeness), `hcoh_full` (the `∞`-coherence
against the full `∞`-fibre `Dinf_full`), the full `∞`-fibre enumeration data, and the pole-only
`∞`-enumeration with the non-`α`-pole points contributing residue `0`, then

> `resAtInfty L.R L.ρ = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`.

The remainder's `∞`-residue `resAt (recipCoeff (T − L.R)) 0 = 0` is **proven** (Cauchy at `∞`,
`resAt_recipCoeff_eq_zero_of_entire`), replacing the circular `R₀ 0 = 0`. -/
theorem infty_eq_of_remainderResZero
    {Φ : (b : ℂ) → FibreRegularData g f b} {br : Finset ℂ} {L : LaurentForm}
    (hentire : AnalyticOnNhd ℂ (valueChartTracePatched ω₀ f Φ br - L.R) Set.univ)
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfull_inj : Function.Injective Dinf_full.xs)
    {ιP : Type} [Fintype ιP] (xsInf_po : ιP → X)
    (hpo_inj : Function.Injective xsInf_po)
    (hpo_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpo_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole : ∀ k, Dinf_full.xs k ∉ poles → formFnResidue ω₀ g (Dinf_full.xs k) = 0) :
    resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  set T := valueChartTracePatched ω₀ f Φ br with hT
  -- `resAtInfty L.R = resAt (recipCoeff L.R) 0`, then `= resAt (recipCoeff T) 0` via the entire remainder.
  rw [resAtInfty_eq_resAt_recipCoeff]
  have hsplit : recipCoeff T = recipCoeff L.R + recipCoeff (T - L.R) := by
    rw [recipCoeff_sub]; funext ζ; simp
  have hhp_rem : HoloPunctured (recipCoeff (T - L.R)) 0 := holoPunctured_recipCoeff_entire hentire
  have hLRhp : HoloPunctured (recipCoeff L.R) 0 := (meromorphicAt_recipCoeff_laurent L).holoPunctured
  have hadd := resAt_add hLRhp hhp_rem
  rw [← hsplit] at hadd
  have hrem_res0 : resAt (recipCoeff (T - L.R)) 0 = 0 := resAt_recipCoeff_eq_zero_of_entire hentire
  have hLR_eq_T : resAt (recipCoeff L.R) 0 = resAt (recipCoeff T) 0 := by
    rw [hadd, hrem_res0, add_zero]
  rw [hLR_eq_T]
  -- `∞`-fibre Lemma 3.2: `resAt (recipCoeff T) 0 = ∑_{F a = ∞} formFnResidue` via `hcoh_full`.
  have hcoh : recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf_full).traceCoeff :=
    hcoh_inf_of_inftyMovingCoherenceNF ω₀ g f Φ br Dinf_full hcoh_full
  rw [resAt_congr hcoh, resAt_traceCoeff_inftyFibreTraceNF ω₀ f Dinf_full,
    residueSum_full_eq_poleOnly Dinf_full.xs xsInf_po hfull_inj hpo_inj hpole_image hnonpole]
  exact residueSum_xs_eq_inftyFilter xsInf_po hpo_inj hpo_mem hpo_surj

/-! ## The residue-level close of Gate A, residual-#5 group discharged

`globalTraceData_of_genus0` assembles a `GlobalTraceData` — and hence `∑Res = 0` — from the
residue-level §VIII.3 geometry **without** the residual-#5 field-group `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq`.
The `∞`-residue identity is re-derived (`infty_eq_of_remainderResZero`) from the *proven* entire-remainder
`∞`-residue (`resAt_recipCoeff_eq_zero_of_entire`, Cauchy at `∞`) plus the `∞`-coherence `hcoh_full`
(#6); the finite Lemma-3.2 residue identity is `resAt_eq_laurentR_of_principalPart` (free).  The
**finite** junk-freeness `hcont_int` (needed for the remainder's entire-ness) and the `∞`-coherence
`hcoh_full` remain — both genuine and non-circular. -/

/-- **`GlobalTraceData` from the residue-level geometry, residual-#5 group discharged.**  Mirrors the
inputs of `residueTheorem_of_directGeometry` but with `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` **removed**: the
`∞`-residue identity comes from the entire remainder (`hcont_int` gives entire-ness via
`analyticOnNhd_remainder_of_junkFree'`, then `resAt_recipCoeff_eq_zero_of_entire` is Cauchy at `∞`) and
the `∞`-coherence `hcoh_full`.  Producing one ⇒ Gate A `∑Res = 0`. -/
noncomputable def globalTraceData_of_genus0
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (D : (p : ℂ) → FibreRegularData g f p)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hpole_image : ∀ i, (Finset.univ.image (Cfull i).D.xs).filter (· ∈ poles)
      = Finset.univ.image (D (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    GlobalTraceData ω₀ g f poles := by
  classical
  set T := valueChartTracePatched ω₀ f Φ br with hT
  -- Meromorphy of `T` at the centres from the full-fibre coherence.
  have hT_mero : ∀ i, MeromorphicAt T (cs i) := by
    intro i
    have hgerm : T =ᶠ[𝓝[≠] (cs i)] (fibreTrace ω₀ f (Cfull i).D).traceCoeff :=
      (valueChartTracePatched_eventuallyEq ω₀ f Φ br (cs i)).trans (Cfull i).coherent_punctured
    exact (meromorphicAt_traceCoeff_fibreTrace ω₀ f (Cfull i).D).congr hgerm.symm
  -- Principal-part `LaurentForm`.
  set hPP := exists_laurentForm_principalPart cs ρ hcs_ball hcs_inj hT_mero with hPP_def
  set L := hPP.choose with hL_def
  have hLcenters : Finset.univ.image L.a = Finset.univ.image cs := hPP.choose_spec.1
  have hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R :=
    hPP.choose_spec.2
  -- The remainder `T − L.R` is entire (the **finite** junk-freeness `hcont_int`).
  have hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z := by
    intro z hz; rw [hLcenters] at hz; exact hT_off_patched hreg hbnd hz
  have hrem : ∀ p ∈ Finset.univ.image L.a,
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R := by
    intro p hp; rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp; exact hLrem i
  have hcont : ∀ p ∈ Finset.univ.image L.a, ContinuousAt (T - L.R) p :=
    hcont_int L hLcenters hLrem
  have hentire : AnalyticOnNhd ℂ (T - L.R) Set.univ :=
    analyticOnNhd_remainder_of_junkFree' hT_off hrem hcont
  refine
    { L := L
      D := D
      hxs_inj := hxs_inj
      hxs_mem := hxs_mem
      hxs_surj := hxs_surj
      hcenters := by rw [hLcenters]; exact hcenters_cs
      hL32 := ?_
      infty_eq := ?_ }
  · -- Finite Lemma 3.2: `∑ resAt(fibreTrace coeff) = ∑ formFnResidue = resAt T (cs i) = resAt L.R (cs i)`.
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hLHS :
        (∑ j, resAt ((fibreTrace ω₀ f (D (cs i))).coeff j) ((fibreTrace ω₀ f (D (cs i))).pre j))
          = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j) :=
      Finset.sum_congr rfl (fun j _ => resAt_fibreTrace_coeff ω₀ f (D (cs i)) j)
    have hres_fin : resAt T (cs i) = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j) :=
      hres_fin_of_fullFibreCoherence D i (Cfull i) (hfull_inj i) (hxs_inj (cs i)) (hpole_image i)
        (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_an i k hk))
    obtain ⟨R, hR_an, hR_eq⟩ := hLrem i
    rw [hLHS, ← hres_fin, resAt_eq_laurentR_of_principalPart (hT_mero i) hR_an hR_eq]
  · -- The `∞`-residue identity, via the entire-remainder `∞`-residue (Cauchy) + `hcoh_full`.
    exact infty_eq_of_remainderResZero hentire Dinf_full hcoh_full hfullInf_inj xsInf_po
      hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf
      (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_inf_an k hk))

/-- **Gate A `∑Res = 0` from the residue-level geometry, residual-#5 group discharged.**  The total
residue of `α = ω₀·g` over its poles vanishes, from the residue-level §VIII.3 geometry with the
`R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` field-group **dropped** — the kirovGenus-`0` `∞`-vanishing is re-derived
internally (Cauchy at `∞` for the entire remainder + the `∞`-coherence `hcoh_full`).  Only the finite
junk-freeness `hcont_int` and the `∞`-coherence `hcoh_full` remain. -/
theorem residueTheorem_of_directGeometry_genus0
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (D : (p : ℂ) → FibreRegularData g f p)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hpole_image : ∀ i, (Finset.univ.image (Cfull i).D.xs).filter (· ∈ poles)
      = Finset.univ.image (D (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_traceExists ω₀ g poles
    (serreTraceExists_of_globalTraceData
      (globalTraceData_of_genus0 Φ m cs ρ hcs_ball hcs_inj br hreg hbnd Cfull D hxs_inj hxs_mem
        hxs_surj hcenters_cs hfull_inj hpole_image hnonpole_an hcont_int Dinf_full hcoh_full
        hfullInf_inj xsInf_po hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf hnonpole_inf_an))

/-! ## Non-vacuity (end-to-end soundness)

`residueTheorem_of_directGeometry_genus0` is satisfiable, not a disguised `False`: for the empty pole
set the empty fibre selection (`Φ` empty, `m = 0`, `br = ∅`, the zero trace `T ≡ 0`) satisfies every
input — including the **finite** junk-freeness `hcont_int` (the zero remainder is continuous) and the
`∞`-coherence `hcoh_full` (both sides `0`).  Confirms the residual-#5-discharged inputs are honest. -/

/-- **Non-vacuity of the residual-#5-discharged residue-level close.**  For the empty pole set,
`residueTheorem_of_directGeometry_genus0` is satisfiable via the empty selection and `br = ∅`, yielding
`∑_{a ∈ ∅} formFnResidue ω₀ g a = 0`.  Confirms the inputs are not a disguised `False`. -/
theorem residueTheorem_of_directGeometry_genus0_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 := by
  have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
      = fun _ => (0 : ℂ) := by
    funext z
    rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
      valueChartTrace_emptySelection ω₀ f]
  refine residueTheorem_of_directGeometry_genus0 (g := g) (poles := (∅ : Finset X))
    (fun p => emptyFibreRegularData g f p)
    0 Fin.elim0 0 (fun i => i.elim0) (fun i => i.elim0) (∅ : Finset ℂ)
    (fun w _ => by rw [valueChartTrace_emptySelection ω₀ f]; exact analyticAt_const)
    (fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀))
    (fun i => i.elim0)
    (fun p => emptyFibreRegularData g f p)
    (fun _ i => i.elim) (fun _ i => i.elim)
    (fun _ a ha => absurd ha (Finset.notMem_empty a))
    (by simp)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    ?_ (emptyInftyFibreDataNF g f) ?_ (by intro i; exact i.elim)
    (ιInfP := Empty) Empty.elim (by intro i; exact i.elim)
    (fun i => i.elim) (fun a ha => absurd ha (Finset.notMem_empty a))
    (by simp) (fun i => i.elim)
  · -- finite junk-freeness: `T − L.R = 0 − 0 = 0` is continuous (empty centres ⟹ `L.R = 0`).
    intro L hLa _ p hp
    have hLR0 : L.R = fun _ => (0 : ℂ) :=
      laurentForm_R_eq_zero_of_emptyImage
        (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
    rw [hpatch0, hLR0]
    have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; simp
    rw [h0]; exact continuousAt_const
  · -- the `∞`-coherence: `recipCoeff 0 =ᶠ recipCoeff (inftyMovingSumNF empty) = recipCoeff 0`.
    have hmoving0 : inftyMovingSumNF ω₀ f (emptyInftyFibreDataNF g f) = fun _ => (0 : ℂ) := by
      funext b'; rw [inftyMovingSumNF]
      exact @Finset.sum_of_isEmpty _ _ _ _ (inferInstanceAs (IsEmpty Empty)) _
    rw [hpatch0, hmoving0]

end Jacobians.Dolbeault.SerreResidueTheorem
