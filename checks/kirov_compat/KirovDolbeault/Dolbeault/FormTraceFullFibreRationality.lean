/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobal
import KirovDolbeault.Dolbeault.FormTraceInftyFibre
import KirovDolbeault.Dolbeault.FormTraceInftyRecip

/-!
# Gate A `∑ₐ Resₐ(α) = 0` from the full-fibre trace rationality (Miranda §VIII.3, clean assembly)

This file closes the residue theorem `∑_{a ∈ poles} formFnResidue ω₀ g a = 0` for a meromorphic
`1`-form `α = ω₀·g` by the **clean three-step Miranda §VIII.3 assembly** on the **full fibre** of a
nonconstant cover `F = f.toRiemannSphere`, reusing only already-proven atoms and **bypassing** the
debt-laden `globalCoverData`/`PatchedTraceSelection`/`hglue_fin` scaffold (which hardcodes the
*pole-sub-fibre* of the moving unramified model and so manufactures spurious obligations such as the
sheet-separation `hsep`).  Because we work with the **full** fibre `F⁻¹(y)` — whose non-pole points
contribute residue `0` (`α` holomorphic there) — the full-fibre and pole-sub-fibre residue sums agree
*on residues*, so no separation/`hsep` ever arises.

## The clean argument (Miranda §VIII.3, full-fibre)

```
∑_X Res(α)  =  ∑_{y ∈ ℂℙ¹} ∑_{x ∈ F⁻¹(y)} Res_x(α)     (organize by fibres — Finset combinatorics)
            =  ∑_{y} Res_y(Tr_F α)                       (Lemma 3.2, FibreTrace.resAt_traceCoeff')
            =  0                                          (ℂℙ¹ residue theorem on the rational Tr_F α).
```

Steps 2–3 are **proven atoms** packaged in `Jacobians.Dolbeault.FormTraceGlobal.GlobalTraceData`
(the bare-`FibreRegularData`, full-fibre reduction — *not* `AdaptedCover`/`Φ`).  The genuine remaining
content (Step 1) is that the trace `Tr_F α` **is** a rational `1`-form `LaurentForm L`: i.e. its
principal-part coefficient `L.R` agrees with the local trace coefficient near each finite pole-value
and (in the reciprocal chart) near `∞`.  That is **exactly Miranda's normal-form / partial-fraction
content (3.1)**, isolated here as the single field `agree`/`agree_infty` of `TraceRationalityData`.

## What this file proves (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

* `inftyFibreResidueSum_eq_filter` — the `∞`-fibre residue re-indexing (pure `Finset` combinatorics,
  the `∞` analogue of `FormTraceFibre.fibreResidueSum_eq_filter`);
* `hL32_of_agree_fibreRegularData` — Lemma 3.2 at a finite center read through the full-fibre agreement
  (the bare `FibreRegularData` version of `FormTraceGlobal.…`/`FormTraceRationalReduce.hL32_of_agree`,
  with **no** `AdaptedCover`);
* `infty_eq_of_agree` — `infty_eq` read through the reciprocal-chart agreement at `∞`
  (`resAtInfty L.R = resAt (recipCoeff L.R) 0` ↦ the `∞`-fibre Lemma 3.2 ↦ the `∞`-fibre residue sum);
* `TraceRationalityData` — the clean Step-1 bundle: the cover `f`, the full-fibre enumerations of the
  finite and `∞` pole-fibres, the `LaurentForm L`, and the **single genuine obligation** that `L`
  represents `Tr_F α` (the agreements `agree`/`agree_infty`);
* `TraceRationalityData.toGlobalTraceData` / `residueSum_eq_zero` — the residue theorem
  `∑ₐ Resₐ(α) = 0` from a `TraceRationalityData`, by assembling a `GlobalTraceData` and invoking the
  proven descent;
* `traceRationalityData_holomorphic` — **non-vacuity end-to-end** (the empty-pole / globally-holomorphic
  case): the obligations are *true and satisfiable*, not a disguised `False`.

## The single minimal remaining obligation (precise diagnosis)

Below `TraceRationalityData` everything is **complete and axiom-clean**.  Gate A is reduced to the
single construction `∃ T, TraceRationalityData ω₀ g f poles` for a nonconstant `f` — concretely the
two agreements `agree`/`agree_infty`, i.e. **the meromorphic trace `Tr_F α` on the compact `ℂℙ¹` is
rational** (Miranda §VIII.3: a meromorphic function on `ℂℙ¹` is a rational function; the principal
parts are read off the fibres by the normal form (3.1)).  This is Miranda's Step-1 analytic content
and nothing more: there is **no** unramified-over-poles demand (`AdaptedCover.hnp`/`hderiv`), **no**
moving-fibre selection `Φ`, and **no** `hglue_fin`/`hsep`.  The cover only needs to be nonconstant.

The reason `agree_infty` is carried **separately** from `agree` (rather than derived from it) is the
genuine §VIII.3 circularity: by the `ℂℙ¹` residue theorem baked into `LaurentForm`
(`resAtInfty_eq`), `resAtInfty L.R = −∑_{finite centers} resAt L.R`, so deriving the `∞`-fibre
identity from the finite agreements alone is *equivalent to the residue theorem itself*.  The
`∞`-agreement is therefore the one independent analytic input (Lemma 3.2 at `∞`, the reciprocal-chart
normal form), exactly as recorded in `FormTraceRationalReduce` (file header, the `infty_eq`
irreducibility note).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3: the trace `Tr` and Lemma 3.2
  (pp. 252–253); normal-form (3.1), p. 253; partial fractions / residue theorem on `ℂℙ¹`, p. 254.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17 (the residue functional `Res`; 17.1–17.3).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFullFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### Step 2/3 bookkeeping — the `∞`-fibre residue re-indexing

The `∞`-analogue of `FormTraceFibre.fibreResidueSum_eq_filter`: when the `∞`-fibre data `Dinf`
injectively enumerates exactly the poles in `F⁻¹(∞)`, the per-fibre residue sum over `Dinf` equals the
fibre-restricted residue sum over the pole set (the `∞`-fibre group in `FormResidueTrace.infty_eq`).
Pure `Finset` combinatorics — no analysis. -/

/-- **`∞`-fibre residue sum = `∞`-fibre-restricted pole-set sum.**  If the `∞`-fibre data `Dinf` has
`xs` injectively enumerating exactly the poles in the fibre `F⁻¹(∞)` (`hxs_inj`, `hxs_mem`,
`hxs_surj`), then

> `∑ i, formFnResidue ω₀ g (Dinf.xs i) = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`. -/
theorem inftyFibreResidueSum_eq_filter (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreData g f) (poles : Finset X)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a) :
    ∑ i, formFnResidue ω₀ g (Dinf.xs i)
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  classical
  -- The `∞`-fibre filter set is the image of the (injective) enumeration `xs`.
  have hImg : (Finset.univ : Finset Dinf.ι).image Dinf.xs
      = poles.filter (fun a => f.toRiemannSphere a = OnePoint.infty) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(hxs_mem i).1, (hxs_mem i).2⟩
    · rintro ⟨ha_pole, ha_fib⟩; exact hxs_surj a ha_pole ha_fib
  -- `∑ i = ∑_{a ∈ univ.image xs}` (injective re-indexing), and that image is the filter set.
  rw [← hImg, Finset.sum_image (fun i _ j _ h => hxs_inj h)]

/-! ### Step 1 — Lemma 3.2 read through the full-fibre trace agreement

The full-fibre `FibreTrace` `fibreTrace ω₀ f (D p)` over a finite center `p` has base `b = p`, and
Miranda's Lemma 3.2 (`FibreTrace.resAt_traceCoeff'`, *proved* via the unconditional residue
change-of-variables `MeromorphicTrace.residueChangeOfVariables`) gives `resAt (Tr_F α over the fibre)
p = ∑ᵢ resAt (coeff i) (pre i)`.  So if the rational `L.R` agrees with the local trace coefficient on
a punctured neighbourhood of `p`, then `∑ᵢ resAt (coeff i) (pre i) = resAt L.R p` — exactly the
`hL32` field.  Identical to `FormTraceRationalReduce.hL32_of_agree`, but on the **bare**
`FibreRegularData D p` (the full-fibre datum), with **no** `AdaptedCover`. -/

/-- **Lemma 3.2 at a finite center, from the full-fibre trace agreement.**  If the rational coefficient
`L.R` agrees with the full-fibre trace coefficient `(fibreTrace ω₀ f (D p)).traceCoeff` on a punctured
neighbourhood of the center `p`, then the `hL32` field holds at `p`:

> `∑ᵢ resAt ((fibreTrace ω₀ f (D p)).coeff i) ((fibreTrace ω₀ f (D p)).pre i) = resAt L.R p`.

*Proof.*  By `FibreTrace.resAt_traceCoeff'` the LHS is `resAt (Tr_F α over the fibre) (fibreTrace …).b
= resAt (Tr_F α) p`; by `resAt_congr` and the agreement that is `resAt L.R p`. -/
theorem hL32_of_agree_fibreRegularData (L : LaurentForm) {p : ℂ} (D : FibreRegularData g f p)
    (hagree : L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f D).traceCoeff) :
    (∑ i, resAt ((fibreTrace ω₀ f D).coeff i) ((fibreTrace ω₀ f D).pre i)) = resAt L.R p := by
  rw [← (fibreTrace ω₀ f D).resAt_traceCoeff']
  -- `(fibreTrace ω₀ f D).b = p`, and `L.R =ᶠ traceCoeff` off `p`, so the residues agree.
  rw [fibreTrace_b]
  exact (resAt_congr hagree).symm

/-! ### Step 1 at `∞` — `infty_eq` read through the reciprocal-chart agreement

The reciprocal-chart bridge `resAtInfty_eq_resAt_recipCoeff` (*proved*,
`Jacobians.Dolbeault.FormTraceInftyRecip`) turns `resAtInfty L.R` into the residue at `0` of the
reciprocal coefficient `recipCoeff L.R`.  If that agrees with the `∞`-fibre trace coefficient near `0`,
its residue is the `∞`-fibre Lemma 3.2 residue (`resAt_traceCoeff_inftyFibreTrace`), which the
re-indexing turns into the `∞`-fibre residue sum.  Identical structure to the finite case. -/

/-- **`infty_eq` from the reciprocal-chart agreement at `∞`.**  Given the `∞`-fibre data `Dinf`
enumerating the poles over `∞`, and the agreement `recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f
Dinf).traceCoeff`, the residue at infinity of `L.R` is the `∞`-fibre residue sum:

> `resAtInfty L.R L.ρ = ∑_{a ∈ poles, F a = ∞} formFnResidue ω₀ g a`.

*Proof.*  `resAtInfty L.R = resAt (recipCoeff L.R) 0` (bridge) `= resAt (inftyFibreTrace …).traceCoeff
0` (agreement, `resAt_congr`) `= ∑ᵢ formFnResidue ω₀ g (Dinf.xs i)` (Lemma 3.2 at `∞`) `= ∑_{∞-fibre}`
(re-indexing). -/
theorem infty_eq_of_agree (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) (L : LaurentForm)
    (Dinf : InftyFibreData g f) (poles : Finset X)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hagree_infty : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff) :
    resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a := by
  rw [resAtInfty_eq_resAt_recipCoeff, resAt_congr hagree_infty,
    resAt_traceCoeff_inftyFibreTrace ω₀ f Dinf,
    inftyFibreResidueSum_eq_filter ω₀ f Dinf poles hxs_inj hxs_mem hxs_surj]

/-! ### The clean Step-1 bundle `TraceRationalityData` and the residue theorem

`TraceRationalityData ω₀ g f poles` is the `GlobalTraceData` with its two analytic fields `hL32`/
`infty_eq` *replaced* by the single genuine §VIII.3 content — the **agreements** that `L` represents
`Tr_F α` (finite centers + `∞`).  Everything else (the full-fibre enumerations + `hcenters`) is the
discrete fibre bookkeeping, all of whose downstream consequences are proven atoms. -/

/-- **The full-fibre trace-rationality bundle** for `α = ω₀·g` through `F = f.toRiemannSphere`, over the
pole set `poles`.  Identical data to `GlobalTraceData`, except the two analytic fields are the
**agreements** (the single honest "`L` is the rational form `Tr_F α`" content, Miranda (3.1)) rather
than the already-derivable `hL32`/`infty_eq`:

* `L` — the candidate rational trace as a `LaurentForm` on `ℂℙ¹`;
* `D` / `hxs_*` — per-center **full-fibre** regularity data, `(D p).xs` enumerating *all* poles in
  `F⁻¹(coe p)` (non-pole points contribute residue `0`, so they need not be enumerated);
* `Dinf` / `hxs∞_*` — the **`∞`-fibre** data enumerating all poles in `F⁻¹(∞)`;
* `hcenters` — the `L`-centers map (by `coe`) onto the finite pole values;
* `agree` — for each center `p`, `L.R` agrees with the full-fibre trace coefficient off `p`;
* `agree_infty` — in the reciprocal chart, `recipCoeff L.R` agrees with the `∞`-fibre trace coefficient
  off `0`.

`agree`/`agree_infty` are the *entire* remaining §VIII.3 content (trace rationality); no
`AdaptedCover`, no `Φ`, no `hglue_fin`/`hsep`. -/
structure TraceRationalityData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) where
  /-- The candidate rational `1`-form representing `Tr_F α` on `ℂℙ¹`. -/
  L : LaurentForm
  /-- Per-center full-fibre regularity data. -/
  D : (p : ℂ) → FibreRegularData g f p
  /-- `(D p).xs` is injective (each fibre point enumerated once). -/
  hxs_inj : ∀ p, Function.Injective (D p).xs
  /-- `(D p).xs` lands in the poles, in the fibre `F⁻¹(coe p)`. -/
  hxs_mem : ∀ p, ∀ i, (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere)
  /-- `(D p).xs` enumerates *all* the poles in the fibre `F⁻¹(coe p)`. -/
  hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, (D p).xs i = a
  /-- The `∞`-fibre data enumerating the poles over `∞`. -/
  Dinf : InftyFibreData g f
  /-- `Dinf.xs` is injective. -/
  hxsInf_inj : Function.Injective Dinf.xs
  /-- `Dinf.xs` lands in the poles, in the fibre `F⁻¹(∞)`. -/
  hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- `Dinf.xs` enumerates *all* the poles in the fibre `F⁻¹(∞)`. -/
  hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- The `L`-centers, mapped to the sphere, are exactly the finite pole values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- **Step 1 (finite):** `L.R` represents `Tr_F α` near each finite center. -/
  agree : ∀ p ∈ (Finset.univ.image L.a),
    L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (D p)).traceCoeff
  /-- **Step 1 (`∞`):** `recipCoeff L.R` represents `Tr_F α` near `0` in the reciprocal chart. -/
  agree_infty : recipCoeff L.R =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff

namespace TraceRationalityData

variable (T : TraceRationalityData ω₀ g f poles)

/-- **The `GlobalTraceData` assembled from a `TraceRationalityData`.**  The shared discrete data is
carried through; the two analytic fields are discharged: `hL32` from the finite agreements
(`hL32_of_agree_fibreRegularData`) and `infty_eq` from the reciprocal-chart agreement
(`infty_eq_of_agree`).  This is the clean reduction of `GlobalTraceData` to the single Miranda-(3.1)
content. -/
noncomputable def toGlobalTraceData : GlobalTraceData ω₀ g f poles where
  L := T.L
  D := T.D
  hxs_inj := T.hxs_inj
  hxs_mem := T.hxs_mem
  hxs_surj := T.hxs_surj
  hcenters := T.hcenters
  hL32 := fun p hp => hL32_of_agree_fibreRegularData T.L (T.D p) (T.agree p hp)
  infty_eq := infty_eq_of_agree ω₀ f T.L T.Dinf poles T.hxsInf_inj T.hxsInf_mem T.hxsInf_surj
    T.agree_infty

/-- **Gate A for the represented form, from a `TraceRationalityData`.**  The total residue of
`α = ω₀·g` over its poles vanishes:

> `∑_{a ∈ poles} formFnResidue ω₀ g a = 0`.

*Proof (complete).*  `toGlobalTraceData` + the proven descent `GlobalTraceData.residueSum_eq_zero`
(which routes through the proven `FormResidueTrace`/`finiteResidueSum_trace_eq_zero_of_fibres'`). -/
theorem residueSum_eq_zero (T : TraceRationalityData ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  GlobalTraceData.residueSum_eq_zero T.toGlobalTraceData

/-- **Gate A (`residueSum` form), from a `TraceRationalityData`.**  The Mittag–Leffler residue-sum
`residueSum ω₀ g poles` of `α = ω₀·g` vanishes — the precise input the residue functional
`Res : H¹(X, Ω) → ℂ` descent consumes. -/
theorem residueSum_eq_zero' (T : TraceRationalityData ω₀ g f poles) :
    residueSum ω₀ g poles = 0 :=
  T.residueSum_eq_zero

end TraceRationalityData

/-- **The Gate-A reduction, existential form (full-fibre route).**  If a `TraceRationalityData ω₀ g f
poles` exists — i.e. the meromorphic trace `Tr_F α` on `ℂℙ¹` is **rational** (the agreements) and the
pole-fibres are enumerated — then the represented `α = ω₀·g` satisfies the 1-form residue theorem
`∑ₐ Resₐ(α) = 0` *unconditionally* (the entire downstream is proven).  This packages "Gate A is reduced
to the trace rationality, on the full-fibre route" as a single statement, with **no** `AdaptedCover`,
**no** moving selection `Φ`, **no** `hglue_fin`/`hsep`. -/
theorem residueSum_eq_zero_of_traceRationalityData (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X)
    (T : TraceRationalityData ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  T.residueSum_eq_zero

/-! ### Non-vacuity (end-to-end soundness)

The `TraceRationalityData` obligations are *genuine* (true, satisfiable), not a disguised `False`: in
the **globally-holomorphic** (empty-pole) case we exhibit a `TraceRationalityData` with the empty pole
set — the empty `LaurentForm` (no centers, `R ≡ 0`, `recipCoeff R ≡ 0`), empty per-center fibre data,
the empty `∞`-fibre data, and vacuous/trivially-true agreements.  This confirms the whole reduction
chain is sound (the residue theorem does hold in this case, with the trivial trace), mirroring
`FormResidueTheorem.formResidueTrace_of_holomorphic` and `FormTraceGlobal.globalTraceData_empty`. -/

/-- The **empty `∞`-fibre data** (no poles over `∞`): `ι = Empty`, all fields vacuous. -/
def emptyInftyFibreData (g : X → ℂ) (f : MeromorphicFunction X) : InftyFibreData g f where
  ι := Empty
  fintype_ι := inferInstance
  xs := Empty.elim
  hrecip_an := fun i => i.elim
  hrecip_deriv := fun i => i.elim
  hrecip_val := fun i => i.elim
  hg_mero := fun i => i.elim

/-- The reciprocal coefficient of the empty `LaurentForm` is identically `0` (its `R` is the empty sum
`≡ 0`, and `recipCoeff 0 ζ = −0·ζ⁻² = 0`). -/
theorem recipCoeff_emptyLaurentForm :
    recipCoeff Jacobians.ResidueTheoremX.emptyLaurentForm.R = fun _ => (0 : ℂ) := by
  funext ζ
  rw [Jacobians.ResidueTheoremX.emptyLaurentForm_R, recipCoeff]
  simp

/-- The trace coefficient of the empty `∞`-fibre trace is identically `0` (empty sum of sheets). -/
theorem traceCoeff_inftyFibreTrace_empty (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    (inftyFibreTrace ω₀ f (emptyInftyFibreData g f)).traceCoeff = fun _ => (0 : ℂ) := by
  funext ζ
  rw [FibreTrace.traceCoeff]
  exact Finset.sum_empty

/-- **Non-vacuity witness (end-to-end).**  A `TraceRationalityData ω₀ g f ∅` always exists (empty pole
set): the empty `LaurentForm`, empty per-center and `∞`-fibre data, vacuous `hcenters`, the vacuous
finite agreement, and the `∞`-agreement `0 =ᶠ 0`.  Hence the `TraceRationalityData` obligations are
*satisfiable* — the reduction is honest, not a disguised `False`; the residue theorem holds with the
trivial trace. -/
noncomputable def traceRationalityData_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) : TraceRationalityData ω₀ g f ∅ where
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  D := fun p => emptyFibreRegularData g f p
  hxs_inj := by intro _ i; exact i.elim
  hxs_mem := fun _ i => i.elim
  hxs_surj := fun _ a ha => absurd ha (Finset.notMem_empty a)
  Dinf := emptyInftyFibreData g f
  hxsInf_inj := by intro i; exact i.elim
  hxsInf_mem := fun i => i.elim
  hxsInf_surj := fun a ha => absurd ha (Finset.notMem_empty a)
  hcenters := by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp
  agree := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  agree_infty := by
    rw [recipCoeff_emptyLaurentForm, traceCoeff_inftyFibreTrace_empty ω₀ f]

/-- **The residue theorem, globally-holomorphic case (via the full-fibre reduction).**  The non-vacuity
witness yields `∑_{a ∈ ∅} formFnResidue ω₀ g a = 0` through the full-fibre `TraceRationalityData`
pipeline (consistent with the direct `residueSum_eq_zero_of_holomorphic`). -/
theorem residueSum_eq_zero_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  (traceRationalityData_holomorphic ω₀ g f).residueSum_eq_zero

end Jacobians.Dolbeault.FormTraceFullFibre
