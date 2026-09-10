/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobalConstruct
import KirovDolbeault.Dolbeault.FormTraceGlobalFunction
import KirovDolbeault.Dolbeault.FormTraceInftyRecip

/-!
# Reducing `TraceRationalityWitness` to the trace-representation agreement (Gate A, §VIII.3 step 4)

`Jacobians.Dolbeault.FormTraceGlobalConstruct` isolated the deep §VIII.3 core of Gate A into the
`TraceRationalityWitness` — a rational `LaurentForm L` representing `Tr_F α` on `ℂℙ¹`, with the three
fields `hcenters`/`hL32`/`infty_eq`.  This file reduces the field `hL32` — one of the two *analytic*
fields — to a single honest geometric input: **`L.R` agrees with the local trace coefficient near
each finite value**.  It then packages the full witness and pins down the precise minimal remaining
obligation, isolating `infty_eq` as the sole irreducible analytic atom.

## The `hL32` reduction (Miranda Lemma 3.2 read through the agreement)

The fibre trace `fibreTrace ω₀ f (fibreReg hac p)` over a finite center `p` has base `b = p`, and
Miranda's Lemma 3.2 (`resAt_traceCoeff_fibreTrace`, *proved*, unconditional via the residue
change-of-variables `MeromorphicTrace.residueChangeOfVariables`) gives

> `resAt (Tr_F α over the fibre) p = ∑ᵢ Res_{xᵢ}(α)`   (the fibre residue sum).

So if the rational `L.R` **agrees with the local trace coefficient on a punctured neighbourhood of
`p`** (`L.R =ᶠ[𝓝[≠] p] (fibreTrace …).traceCoeff` — the honest "`L` represents `Tr_F α`" condition),
then `resAt L.R p = resAt (Tr_F α) p = ∑ᵢ Res_{xᵢ}(α)`, which is exactly the `hL32` field
(`FibreTrace.resAt_traceCoeff'` turns its `∑ᵢ resAt (coeff i) (pre i)` LHS into `resAt traceCoeff p`).

## `infty_eq` is the genuinely-irreducible analytic atom (the circularity)

One cannot derive `infty_eq` from `hcenters` + `hL32` + rationality: by the `ℂℙ¹` residue theorem
baked into `LaurentForm` (`resAtInfty_eq`), `resAtInfty L.R L.ρ = −∑_{finite centres} resAt L.R p`,
which under `hL32` is `−∑_{finite fibres} Res`.  Asking `infty_eq` — that this equal the `∞`-fibre
residue sum `∑_{∞-fibre} Res` — is therefore equivalent to `∑_{all fibres} Res = 0`, i.e. **the
residue theorem itself**.  So `infty_eq` carries genuinely new content: it is the *independent*
analytic computation of `resAtInfty L.R` as the `∞`-fibre residue sum (Lemma 3.2 at `∞`, the
reciprocal-chart contour content), which the finite data cannot supply.  This is the precise minimal
remaining obligation; its close-path is the reciprocal-chart change-of-variables
`resAtInfty R ρ = resAt (ζ ↦ −R(ζ⁻¹)·ζ⁻²) 0` (the `z = 1/ζ` contour substitution, Mathlib-lacking)
composed with the same `resAt_traceCoeff_fibreTrace` machinery applied to the reciprocal-chart pole
fibre.

## What this file proves (axiom-clean)

* `hL32_of_agree` / `resAt_eq_fibreResidueSum_of_agree` — the `hL32` field, and the fibre-residue
  identity, from the per-center agreement;
* `traceRationalityWitness_of_agree` — the full `TraceRationalityWitness` from `L` + `hcenters` (the
  discrete centre bookkeeping) + the per-center agreement (`hL32`) + the `∞`-fibre residue identity
  (`infty_eq`, carried as the isolated atom);
* `residueSum_eq_zero_of_agree` — Gate A `∑Res=0` from these honest inputs;
* `agree_holomorphic` / `traceRationalityWitness_holomorphic` — **non-vacuity end-to-end**: in the
  empty-pole (globally-holomorphic) case the agreement, `hcenters`, and `infty_eq` all hold for the
  empty `LaurentForm`, so the whole reduction chain is sound (not a disguised `False`).

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
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### Lemma 3.2 at a finite centre, read through the agreement -/

/-- **Lemma 3.2 at a finite centre, from the trace agreement.**  If the rational coefficient `L.R`
agrees with the local trace coefficient `(fibreTrace ω₀ f (fibreReg hac p)).traceCoeff` on a
punctured neighbourhood of `p`, then the `hL32` field holds at `p`:

> `∑ᵢ resAt ((fibreTrace ω₀ f (fibreReg hac p)).coeff i) ((fibreTrace ω₀ f (fibreReg hac p)).pre i)
>     = resAt L.R p`.

*Proof.*  By `FibreTrace.resAt_traceCoeff'` the LHS is `resAt (Tr_F α) (fibreTrace …).b = resAt (Tr_F
α) p`; by `resAt_congr` and the agreement that is `resAt L.R p`. -/
theorem hL32_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm) (p : ℂ)
    (hagree : L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff) :
    (∑ i, resAt ((fibreTrace ω₀ f (fibreReg hac p)).coeff i)
        ((fibreTrace ω₀ f (fibreReg hac p)).pre i)) = resAt L.R p := by
  rw [← (fibreTrace ω₀ f (fibreReg hac p)).resAt_traceCoeff']
  -- `(fibreTrace …).b = p`, and `L.R =ᶠ traceCoeff` off `p`, so the residues agree.
  rw [fibreTrace_b]
  exact (resAt_congr hagree).symm

/-- **The fibre residue sum at a finite centre, from the trace agreement.**  Combining
`hL32_of_agree` with `resAt_traceCoeff_fibreTrace`: when `L.R` agrees with the local trace coefficient
off `p`, its residue there is the fibre residue sum of `α = ω₀·g`:

> `resAt L.R p = ∑ᵢ formFnResidue ω₀ g ((fibreReg hac p).xs i)`. -/
theorem resAt_eq_fibreResidueSum_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (p : ℂ) (hagree : L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff) :
    resAt L.R p = ∑ i, formFnResidue ω₀ g ((fibreReg hac p).xs i) := by
  -- `resAt L.R p = resAt (Tr_F α) p` (agreement), then Lemma 3.2 over the fibre (base `p`, `rfl`).
  rw [resAt_congr hagree]
  exact resAt_traceCoeff_fibreTrace ω₀ f (fibreReg hac p)

/-! ### The full `TraceRationalityWitness` from the agreement + the `∞`-residue identity

With `hL32` reduced to the per-center agreement (`hL32_of_agree`), the only remaining genuinely-deep
content is `hcenters` (a discrete choice of which centres `L` carries — the finite pole-values) and
`infty_eq` (Lemma 3.2 at `∞`, the honest large-circle contour content; see the file header). -/

/-- **`TraceRationalityWitness` from the trace agreement.**  Given:

* a `LaurentForm L`,
* `hcenters` — the `L`-centres, mapped to the sphere, are exactly the finite pole-values (the discrete
  choice of representation),
* `hagree` — for each centre `p` of `L`, `L.R` agrees with the local trace coefficient off `p` (the
  honest "`L.R` is the partial-fraction expansion of the meromorphic `Tr_F α`" condition), and
* `hinfty` — Lemma 3.2 at `∞` (the `∞`-residue of `L.R` is the `∞`-fibre residue sum; the isolated
  analytic atom),

a `TraceRationalityWitness ω₀ g f poles hac` exists.  *Proof:* `hcenters`/`hinfty` are passed
through; `hL32` is `hL32_of_agree` applied at each centre. -/
def traceRationalityWitness_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hagree : ∀ p ∈ (Finset.univ.image L.a),
      L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hinfty : resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a) :
    TraceRationalityWitness ω₀ g f poles hac where
  L := L
  hcenters := hcenters
  hL32 := fun p hp => hL32_of_agree hac L p (hagree p hp)
  infty_eq := hinfty

/-- **Gate A from the trace agreement.**  If an adapted cover and a `LaurentForm` representing
`Tr_F α` (with the centre bookkeeping, the per-centre agreement, and the `∞`-residue identity) exist,
then the 1-form residue theorem `∑ₐ Resₐ(α) = 0` holds *unconditionally* for `α = ω₀·g`.  This
composes `traceRationalityWitness_of_agree` with the proved
`Jacobians.Dolbeault.FormTraceGlobal.residueSum_eq_zero_of_adapted`. -/
theorem residueSum_eq_zero_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hagree : ∀ p ∈ (Finset.univ.image L.a),
      L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hinfty : resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_adapted hac (traceRationalityWitness_of_agree hac L hcenters hagree hinfty)

/-! ### `infty_eq` via the reciprocal chart at `0`

Using the proved one-variable bridge `resAtInfty_eq_resAt_recipCoeff`
(`Jacobians.Dolbeault.FormTraceInftyRecip`), the `infty_eq` field can be stated as a residue at `0`
of the reciprocal-chart coefficient — the honest Lemma-3.2-at-`∞` content, structurally identical to
the finite case.  This variant of the witness assembly takes that reciprocal form directly. -/

open Jacobians.Dolbeault.FormTraceInftyRecip in
/-- **`TraceRationalityWitness` with `infty_eq` in reciprocal-chart form.**  Identical to
`traceRationalityWitness_of_agree`, but the `∞`-residue identity is supplied as a residue at `0` of
the reciprocal-chart coefficient `recipCoeff L.R` (the honest Lemma-3.2-at-`∞` form, via the proved
`resAtInfty_eq_resAt_recipCoeff` bridge):

> `resAt (recipCoeff L.R) 0 = ∑_{a : F a = ∞} Res_a(α)`.

This is the precise minimal remaining `∞`-obligation: the residue at `0` of the reciprocal-chart trace
coefficient is the `∞`-fibre residue sum (Lemma 3.2 over the pole fibre, in the reciprocal chart). -/
def traceRationalityWitness_of_agree_recip (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hagree : ∀ p ∈ (Finset.univ.image L.a),
      L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hinftyRecip : resAt (recipCoeff L.R) 0
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a) :
    TraceRationalityWitness ω₀ g f poles hac :=
  traceRationalityWitness_of_agree hac L hcenters hagree
    (by rw [resAtInfty_eq_resAt_recipCoeff]; exact hinftyRecip)

/-! ### Non-vacuity of the reduction (end-to-end soundness)

The reduction's hypotheses are *genuine* (true, satisfiable), not a disguised `False`: in the
globally-holomorphic (empty-pole) case, the empty `LaurentForm` satisfies `hcenters`, the (vacuous)
agreement, and `hinfty`, so `traceRationalityWitness_of_agree` produces a witness and Gate A holds.
This confirms the entire reduction chain — `hL32_of_agree` and the agreement framing — is sound. -/

/-- **The agreement is vacuously satisfiable** for the empty `LaurentForm` (no centres). -/
theorem agree_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) :
    ∀ p ∈ (Finset.univ.image (Jacobians.ResidueTheoremX.emptyLaurentForm.a)),
      Jacobians.ResidueTheoremX.emptyLaurentForm.R
        =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f
          (fibreReg (adaptedCover_empty ω₀ g f hdiv) p)).traceCoeff := by
  intro p hp
  rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **Non-vacuity witness for the reduction (end-to-end).**  In the globally-holomorphic (empty-pole)
case, `traceRationalityWitness_of_agree` applied to the empty `LaurentForm` yields a
`TraceRationalityWitness` — the agreement is vacuous, `hcenters` holds (both sides empty), and the
`∞`-fibre residue sum over `∅` matches `Res_∞ ≡ 0`.  Hence the agreement-based reduction is honest
(satisfiable), not a disguised `False`. -/
def traceRationalityWitness_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    TraceRationalityWitness ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) :=
  traceRationalityWitness_of_agree (adaptedCover_empty ω₀ g f hdiv)
    Jacobians.ResidueTheoremX.emptyLaurentForm
    (by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp)
    (agree_holomorphic ω₀ g f hdiv)
    (by
      rw [resAtInfty, Jacobians.ResidueTheoremX.emptyLaurentForm_R]
      show -(2 * π * I : ℂ)⁻¹ • (∮ _z in C((0 : ℂ),
        Jacobians.ResidueTheoremX.emptyLaurentForm.ρ), (0 : ℂ)) = _
      rw [show Jacobians.ResidueTheoremX.emptyLaurentForm.ρ = 0 from rfl,
        circleIntegral.integral_radius_zero, smul_zero]
      simp)

end Jacobians.Dolbeault.FormTraceGlobal
