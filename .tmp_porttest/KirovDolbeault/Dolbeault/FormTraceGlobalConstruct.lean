/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobal
import KirovDolbeault.Discharge.Manifold.CriticalValuesFiniteGeneral

/-!
# Constructing `GlobalTraceData` — discharging the routine fields (Gate A, node A-ii bridge (e))

`Jacobians.Dolbeault.FormTraceGlobal` reduced Gate A (the 1-form residue theorem `∑ₐ Resₐ(α) = 0`
for `α = ω₀·g`) to the single construction of a `GlobalTraceData ω₀ g f poles`.  Its five fields are

* `L`, `hL32`, `infty_eq` — the **rational trace** `Tr_F α` on `ℂℙ¹` (the deep §VIII.3 content), and
* `D`, `hxs_inj`/`hxs_mem`/`hxs_surj`, `hcenters` — the **per-center fibre data** (regular fibres over
  the finite pole-values, enumerating the poles in each fibre).

This file discharges the *routine* fields — the fibre enumeration `D` + `hxs_*` and the center
matching `hcenters` — from a clean **adapted-cover** hypothesis, isolating the single genuinely-deep
obligation `TraceRationalityWitness` (the rational `L` + Lemma 3.2 bookkeeping `hL32`/`infty_eq`).

## The adapted cover

The cover `F = f.toRiemannSphere` must be **unramified over the finite pole-values** of `α`: each
pole `a` of `α` (mapping to a finite value `coe p`) must be a *regular non-pole point of `f`* — so its
fibre `F⁻¹(coe p)` is a finite set of such points and `FibreRegularData.ofRegular` applies.  We bundle
this geometric prerequisite (plus `g`'s chart-pullback meromorphy at the fibre points) as
`AdaptedCover ω₀ g f poles`.  A generic nonconstant meromorphic `f` (gate D) is adapted, because the
critical values are finite (`criticalValues_finite_general`) and the pole-values are finite, so the
two finite sets can be made disjoint — but that genericity perturbation is itself §VIII.3-level and is
deferred (it is *not* the deep core; the deep core is trace rationality).

## What is discharged here (axiom-clean)

* `fibreReg` / `FibreEnumeration` — the per-center `FibreRegularData` from the adapted cover, with
  `(fibreReg p).xs` the subtype enumeration of `poles ∩ F⁻¹(coe p)`;
* `fibreReg_hxs_inj` / `_hxs_mem` / `_hxs_surj` — the three enumeration fields, *proved*;
* `globalTraceData_of_adapted` — assembles `GlobalTraceData` from an `AdaptedCover` **plus** a
  `TraceRationalityWitness` (the deep `L`/`hL32`/`infty_eq`), discharging `D`/`hxs_*`/`hcenters`.

## The minimal remaining obligation

After this file, Gate A is reduced to:

> `∃ (f) (adapted : AdaptedCover ω₀ g f poles), TraceRationalityWitness ω₀ g f poles adapted`

i.e. **(i)** an adapted cover, and **(ii)** the trace `Tr_F α` is a rational `LaurentForm` matching
the per-fibre residues at the finite centers (`hL32`) and at `∞` (`infty_eq`).

**Why the deep core is irreducible (the `infty_eq` circularity).**  One might hope to *fabricate* `L`
as a sum of simple poles `r_p·(z − p)⁻¹` at the finite centers `p`, with `r_p` the (already-computed)
fibre residue sums — then `hcenters` and `hL32` hold *by construction* (`resAt_center_eq`,
`resAt_fibreTrace_coeff`).  But the `ℂℙ¹` residue theorem baked into `LaurentForm`
(`resAtInfty_eq`) forces `resAtInfty L.R = −∑_p r_p`, so `infty_eq` would then *demand*
`−∑_p r_p = ∑_{a : F a = ∞} Res_a(α)`, i.e. `∑_{a ∈ poles} Res_a(α) = 0` — **the residue theorem
itself**.  So `infty_eq` for the *genuine* trace (whose `resAtInfty` is an honest large-circle contour
integral of the actual pushforward, *not* fabricated) is the real content: it is Lemma 3.2 at `∞` for
`Tr_F α`, and combined with the proved finite-center Lemma 3.2 and the `ℂℙ¹` residue theorem it
*is* Gate A.  Hence `L` must be the actual rational trace; there is no shortcut.

This makes (ii) the genuine §VIII.3 wall: build `Tr_F α` as a global meromorphic function on the
compact `ℂℙ¹` (holomorphic off the finite exceptional set — critical values + pole-images + `∞` — by
the per-sheet pushforwards, meromorphic at the exceptional points), extract its principal parts into a
`LaurentForm`, and read off the `∞`-residue.  (i) is a finite genericity choice (the bad source set
`criticalSet f ∪ poles f` is finite; perturb `f` off the finitely many poles of `α`).  Everything
else — the per-fibre Lemma 3.2 (`FormTraceFibre`), the fibre enumeration (here), and the descent to
`∑Res = 0` (`FormTraceGlobal`) — is *proved*, axiom-clean.

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

/-! ### The adapted-cover hypothesis

The geometric prerequisite for the fibre data: the cover `F = f.toRiemannSphere` is unramified over
the finite pole-values, i.e. every pole `a` of `α = ω₀·g` mapping to a *finite* value is a regular
non-pole point of `f` (chart-pullback of `f.holoRepr` analytic with nonzero derivative at `chart a`),
and `g`'s chart-pullback is meromorphic there. -/

/-- **An adapted cover** for `α = ω₀·g` over the pole set `poles`.  The cover `F = f.toRiemannSphere`
is unramified over the finite pole-values: every pole `a ∈ poles` whose image `F a` is a finite value
(`≠ ∞`) is a **regular non-pole point of `f`** — `f.holoRepr`'s chart-pullback is analytic at
`chart a` with nonzero derivative — and `g`'s chart-pullback is meromorphic at `chart a` (so `α·g`
has an isolated singularity).  This is the honest geometric input the unramified-fibre `FibreTrace`
machinery (`FormTraceFibre`) consumes; a generic nonconstant `f` (gate D) satisfies it. -/
structure AdaptedCover (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) : Prop where
  /-- `f` is genuinely nonconstant (nontrivial divisor), so all fibres are finite. -/
  hdiv : (f.div : Divisor X) ≠ 0
  /-- Every pole mapping to a finite value is a **non-pole of `f`** (`f.holoRepr` analytic there). -/
  hnp : ∀ a ∈ poles, f.toRiemannSphere a ≠ OnePoint.infty → 0 ≤ f.orderAtPoint a
  /-- Every pole mapping to a finite value is a **regular point of `f`** (chart-pullback deriv ≠ 0). -/
  hderiv : ∀ a ∈ poles, f.toRiemannSphere a ≠ OnePoint.infty →
    deriv (fun z => f.holoRepr ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) ≠ 0
  /-- `g`'s chart-pullback is meromorphic at every pole (so `α·g` has an isolated singularity). -/
  hg_mero : ∀ a ∈ poles,
    MeromorphicAt (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

/-! ### The per-center fibre enumeration

For each finite center `p : ℂ`, the poles in the fibre `F⁻¹(coe p)` form a finite set
`poleFibre f poles p := poles.filter (· ↦ F · = coe p)`.  We index the sheets by
`Fin #(poleFibre f poles p)` (a `Type 0`, as `FibreRegularData.ι` requires), with the enumeration
`xs := Subtype.val ∘ (poleFibre …).equivFin.symm`.  At a finite value, a non-pole `a` with
`F a = coe p` has `f.holoRepr a = p` (`toRiemannSphere_of_nonneg` + `OnePoint.coe` injective), which
is the `hval` field.  Combined with the adapted-cover regularity (`hnp`/`hderiv`/`hg_mero`) this feeds
`FibreRegularData.ofRegular`. -/

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-- The poles in the fibre `F⁻¹(coe p)` of `α = ω₀·g`, as a `Finset X`. -/
def poleFibre (f : MeromorphicFunction X) (poles : Finset X) (p : ℂ) : Finset X :=
  poles.filter (fun a => f.toRiemannSphere a = ((p : ℂ) : RiemannSphere))

@[simp] theorem mem_poleFibre {f : MeromorphicFunction X} {poles : Finset X} {p : ℂ} {a : X} :
    a ∈ poleFibre f poles p ↔ a ∈ poles ∧ f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) := by
  rw [poleFibre, Finset.mem_filter]

/-- The enumeration of the fibre poles `poleFibre f poles p` by `Fin #(poleFibre f poles p)`:
`Subtype.val ∘ (poleFibre …).equivFin.symm`.  A `Type 0`-indexed injective enumeration of the fibre,
as `FibreRegularData.ι` requires. -/
noncomputable def fibreEnum (f : MeromorphicFunction X) (poles : Finset X) (p : ℂ) :
    Fin (poleFibre f poles p).card → X :=
  fun i => ((poleFibre f poles p).equivFin.symm i : X)

/-- Each enumerated point lies in the fibre `poleFibre f poles p`. -/
theorem fibreEnum_mem (f : MeromorphicFunction X) (poles : Finset X) (p : ℂ)
    (i : Fin (poleFibre f poles p).card) : fibreEnum f poles p i ∈ poleFibre f poles p :=
  ((poleFibre f poles p).equivFin.symm i).2

/-- The fibre enumeration is **injective**. -/
theorem fibreEnum_injective (f : MeromorphicFunction X) (poles : Finset X) (p : ℂ) :
    Function.Injective (fibreEnum f poles p) := by
  intro i j h
  exact (poleFibre f poles p).equivFin.symm.injective (Subtype.ext h)

/-- The fibre enumeration is **surjective** onto the fibre: for `a ∈ poleFibre f poles p` there is an
index hitting it. -/
theorem fibreEnum_surjective (f : MeromorphicFunction X) (poles : Finset X) (p : ℂ)
    {a : X} (ha : a ∈ poleFibre f poles p) : ∃ i, fibreEnum f poles p i = a := by
  refine ⟨(poleFibre f poles p).equivFin ⟨a, ha⟩, ?_⟩
  show ((poleFibre f poles p).equivFin.symm ((poleFibre f poles p).equivFin ⟨a, ha⟩) : X) = a
  rw [Equiv.symm_apply_apply]

/-- A pole `a` in a *finite-value* fibre `F⁻¹(coe p)` of an adapted cover has `f.holoRepr a = p`:
it is a non-pole (`hnp`), so `F a = coe (holoRepr a)`, and `coe` is injective. -/
theorem holoRepr_eq_of_mem_poleFibre (hac : AdaptedCover ω₀ g f poles) {p : ℂ} {a : X}
    (ha : a ∈ poleFibre f poles p) : f.holoRepr a = p := by
  rw [mem_poleFibre] at ha
  obtain ⟨ha_pole, ha_fib⟩ := ha
  have hne : f.toRiemannSphere a ≠ OnePoint.infty := by
    rw [ha_fib]; exact OnePoint.coe_ne_infty p
  have hnp : 0 ≤ f.orderAtPoint a := hac.hnp a ha_pole hne
  rw [f.toRiemannSphere_of_nonneg hnp] at ha_fib
  exact OnePoint.coe_injective ha_fib

/-- **The per-center fibre regularity data** for an adapted cover.  At center `p`, the sheets are
indexed by `Fin #(poleFibre f poles p)` via `fibreEnum`.  The regularity fields are read off the
adapted-cover hypothesis (`hnp`/`hderiv`/`hg_mero`) at each fibre pole; `hval` (`f.holoRepr (xs i) =
p`) is `holoRepr_eq_of_mem_poleFibre`. -/
noncomputable def fibreReg (hac : AdaptedCover ω₀ g f poles) (p : ℂ) :
    FibreRegularData g f p :=
  FibreRegularData.ofRegular g f p
    (ι := Fin (poleFibre f poles p).card)
    (xs := fibreEnum f poles p)
    (hnp := fun i => by
      have ha := fibreEnum_mem f poles p i
      rw [mem_poleFibre] at ha
      exact hac.hnp _ ha.1 (by rw [ha.2]; exact OnePoint.coe_ne_infty p))
    (hderiv := fun i => by
      have ha := fibreEnum_mem f poles p i
      rw [mem_poleFibre] at ha
      exact hac.hderiv _ ha.1 (by rw [ha.2]; exact OnePoint.coe_ne_infty p))
    (hval := fun i => holoRepr_eq_of_mem_poleFibre hac (fibreEnum_mem f poles p i))
    (hmero := fun i => by
      have ha := fibreEnum_mem f poles p i
      rw [mem_poleFibre] at ha
      exact hac.hg_mero _ ha.1)

@[simp] theorem fibreReg_xs (hac : AdaptedCover ω₀ g f poles) (p : ℂ)
    (i : Fin (poleFibre f poles p).card) :
    (fibreReg hac p).xs i = fibreEnum f poles p i := rfl

@[simp] theorem fibreReg_ι (hac : AdaptedCover ω₀ g f poles) (p : ℂ) :
    (fibreReg hac p).ι = Fin (poleFibre f poles p).card := rfl

/-- `(fibreReg hac p).xs` is **injective** (each fibre pole enumerated once). -/
theorem fibreReg_hxs_inj (hac : AdaptedCover ω₀ g f poles) (p : ℂ) :
    Function.Injective (fibreReg hac p).xs := fibreEnum_injective f poles p

/-- `(fibreReg hac p).xs` lands in `poles`, in the fibre `F⁻¹(coe p)`. -/
theorem fibreReg_hxs_mem (hac : AdaptedCover ω₀ g f poles) (p : ℂ)
    (i : Fin (poleFibre f poles p).card) :
    (fibreReg hac p).xs i ∈ poles ∧
      f.toRiemannSphere ((fibreReg hac p).xs i) = ((p : ℂ) : RiemannSphere) := by
  have ha := fibreEnum_mem f poles p i
  rw [mem_poleFibre] at ha
  exact ha

/-- `(fibreReg hac p).xs` enumerates **all** the poles in the fibre `F⁻¹(coe p)`. -/
theorem fibreReg_hxs_surj (hac : AdaptedCover ω₀ g f poles) (p : ℂ) (a : X) (ha : a ∈ poles)
    (hfib : f.toRiemannSphere a = ((p : ℂ) : RiemannSphere)) :
    ∃ i, (fibreReg hac p).xs i = a :=
  fibreEnum_surjective f poles p (mem_poleFibre.mpr ⟨ha, hfib⟩)

/-! ### The trace-rationality witness — the deep §VIII.3 obligation

With the fibre data discharged, the only remaining content is the **rationality of the trace**
`Tr_F α` on `ℂℙ¹`: a `LaurentForm L` whose centers are exactly the finite pole-values (`hcenters`),
matching the per-fibre residue sums at the finite centers (`hL32`) and at `∞` (`infty_eq`).  This is
the genuinely-deep §VIII.3 content ("every meromorphic function on the compact `ℂℙ¹` is rational");
there is no Mathlib API for it.  We isolate it as `TraceRationalityWitness`, relative to the
adapted-cover fibre data `fibreReg hac`. -/

/-- **The trace-rationality witness** for an adapted cover.  The honest §VIII.3 content that remains
after the fibre enumeration is discharged: a rational `LaurentForm L` representing `Tr_F α` on
`ℂℙ¹`, with

* `hcenters` — the `L`-centers (mapped to the sphere) are exactly the finite pole-values;
* `hL32` — Lemma 3.2 at the finite centers (`L.R`'s residue = the per-fibre residue sum, computed
  from `fibreReg hac`);
* `infty_eq` — Lemma 3.2 at `∞` (the residue at infinity = the `∞`-fibre residue sum).

These are the three `GlobalTraceData` fields that genuinely encode the trace's rationality. -/
structure TraceRationalityWitness (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The rational `1`-form representing `Tr_F α` on `ℂℙ¹`. -/
  L : LaurentForm
  /-- The `L`-centers, mapped to the sphere, are exactly the finite pole-values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- Lemma 3.2 at the finite centers (residue of `L.R` = the per-fibre residue sum). -/
  hL32 : ∀ p ∈ (Finset.univ.image L.a),
    (∑ i, resAt ((fibreTrace ω₀ f (fibreReg hac p)).coeff i)
      ((fibreTrace ω₀ f (fibreReg hac p)).pre i)) = resAt L.R p
  /-- Lemma 3.2 at `∞`: the residue at infinity is the `∞`-fibre residue sum. -/
  infty_eq : resAtInfty L.R L.ρ
    = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a

/-- **`GlobalTraceData` from an adapted cover + trace rationality.**  Given an `AdaptedCover` (the
unramified-over-finite-pole-values geometric input) and a `TraceRationalityWitness` (the rational
trace `L` + Lemma 3.2 bookkeeping), assemble a `GlobalTraceData ω₀ g f poles`.  The fibre data
`D`/`hxs_*` are the *proved* `fibreReg`/`fibreReg_hxs_*`; the deep fields `L`/`hcenters`/`hL32`/
`infty_eq` come from the witness.  This discharges every routine field of `GlobalTraceData`, reducing
its construction to the witness. -/
noncomputable def globalTraceData_of_adapted (hac : AdaptedCover ω₀ g f poles)
    (W : TraceRationalityWitness ω₀ g f poles hac) :
    GlobalTraceData ω₀ g f poles where
  L := W.L
  D := fibreReg hac
  hxs_inj := fibreReg_hxs_inj hac
  hxs_mem := fibreReg_hxs_mem hac
  hxs_surj := fibreReg_hxs_surj hac
  hcenters := W.hcenters
  hL32 := W.hL32
  infty_eq := W.infty_eq

/-- **Gate A from an adapted cover + trace rationality (existential).**  If an adapted cover and a
trace-rationality witness exist, then `α = ω₀·g` has a `GlobalTraceData`, hence (by
`exists_formResidueTrace_of_globalTraceData` + the proved descent) a `FormResidueTrace`, hence the
1-form residue theorem `∑ₐ Resₐ(α) = 0` holds *unconditionally* for `α`.  This is the reduction of
Gate A to the two §VIII.3 ingredients (the adapted cover and the trace's rationality). -/
theorem residueSum_eq_zero_of_adapted (hac : AdaptedCover ω₀ g f poles)
    (W : TraceRationalityWitness ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  (globalTraceData_of_adapted hac W).residueSum_eq_zero

/-! ### Non-vacuity of the new structures

The `AdaptedCover` and `TraceRationalityWitness` obligations are genuine (true, satisfiable), not a
disguised `False`: for the **empty pole set** (`α = ω₀·g` globally holomorphic) any nonconstant `f`
(`f.div ≠ 0`) gives an `AdaptedCover` (the `hnp`/`hderiv`/`hg_mero` fields are vacuous), and the empty
`LaurentForm` gives a `TraceRationalityWitness` (no centers, trace `≡ 0`, vacuous `hL32`, `∞`-fibre
sum `0`).  This confirms the structures are honest, mirroring `globalTraceData_empty`. -/

/-- **`AdaptedCover` non-vacuity.**  For the empty pole set, any nonconstant `f` (`f.div ≠ 0`) is an
adapted cover (the regularity fields are vacuous). -/
theorem adaptedCover_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) : AdaptedCover ω₀ g f ∅ where
  hdiv := hdiv
  hnp := fun a ha => absurd ha (Finset.notMem_empty a)
  hderiv := fun a ha => absurd ha (Finset.notMem_empty a)
  hg_mero := fun a ha => absurd ha (Finset.notMem_empty a)

/-- **`TraceRationalityWitness` non-vacuity.**  For the empty pole set, the empty `LaurentForm` is a
trace-rationality witness: no centers (`hcenters`/`hL32` vacuous), and the `∞`-fibre sum over `∅`
vanishes (matching `Res_∞ ≡ 0`). -/
noncomputable def traceRationalityWitness_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    TraceRationalityWitness ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  hcenters := by
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp
  hL32 := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  infty_eq := by
    rw [resAtInfty, Jacobians.ResidueTheoremX.emptyLaurentForm_R]
    show -(2 * π * I : ℂ)⁻¹ • (∮ _z in C((0 : ℂ),
      Jacobians.ResidueTheoremX.emptyLaurentForm.ρ), (0 : ℂ)) = _
    rw [show Jacobians.ResidueTheoremX.emptyLaurentForm.ρ = 0 from rfl,
      circleIntegral.integral_radius_zero, smul_zero]
    simp

end Jacobians.Dolbeault.FormTraceGlobal
