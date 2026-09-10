/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueDirect
import KirovDolbeault.Dolbeault.FormTraceGlobalFibreSelection

/-!
# Assembling `DirectTraceGeometry` for an adapted cover (Gate A, Miranda §VIII.3 genericity)

`Jacobians.Dolbeault.SerreResidueTheorem.DirectTraceGeometry ω₀ g f poles` (`SerreResidueDirect.lean`)
is the **honest** residue-level §VIII.3 trace geometry whose existence makes Gate A `∑ Res = 0`
unconditional (`residueTheorem_of_exists_directTraceGeometry`).  It bundles 38 fields; its non-vacuity
witness `directTraceGeometry_holomorphic` constructs every field for `poles = ∅`.

This file drives Miranda's genericity ("simply choose any nonconstant `f`", p. 254) toward a *general*
adapted cover, **proving the wireable field-groups** — the pole-only finite/`∞` fibre data, the
pole↔full-fibre matching (`hpole_image`/`hpole_image_inf`), the non-pole residue-`0` analyticity
(`hnonpole_an`/`hnonpole_inf_an`), and the centre bookkeeping — from concrete pole-enumeration inputs,
and packaging the **deep analytic residuals** (the per-centre full-fibre moving coherence `Cfull`, the
off-centre regular-value analyticity `hreg`, the branch boundedness `hbnd`, the junk-freeness
`hcont_int`, and the kirovGenus-`0` `∞`-vanishing `R₀`) as explicit hypotheses.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

The genuinely-new content is the **pole sub-fibre** combinatorics: from a full-fibre regularity datum
`Dfull : FibreRegularData g f b` whose `xs` enumerates the *entire* fibre `F⁻¹(coe b)`, the pole-only
sub-fibre `poleSubfibre` enumerates exactly the `α`-poles in that fibre (a `FibreRegularData g f b` over
the subtype `{i // Dfull.xs i ∈ poles}`), and `poleSubfibre`'s enumeration is injective, lands in the
poles over `coe b`, is surjective onto them, and its image is exactly the pole-filter of the full
enumeration (`hpole_image`).  This is the pole↔full matching the honest residue-level route needs — the
`D` (pole-only) vs `Cfull` (full-fibre) separation that *eliminates* the false germ `agree`.

* `poleSubfibre` / `poleSubfibre_xs_*` — the pole-only sub-`FibreRegularData` (reuses `Dfull`'s fields on
  the subtype, a genuine `f`-regular `FibreRegularData`) + injectivity / pole-membership / surjectivity /
  `hpole_image` (the finite-fibre group `D`/`hxs_*`/`hpole_image`).
* `poleSubEnum_*` — the `∞`-analogue (the `∞`-fibre group `xsInf_po`/`hpoInf_*`/`hpole_image_inf`).
* `inftyFibreEnum_*` / `inftyFibreDataNF_full` — the **full `∞`-fibre** datum from simple poles
  (enumerating *all* `f`-poles); closes `Dinf_full`/`hfullInf_inj`/`hinf_mem`/`hinf_surj`.
* `poleValueEnum_*` / `hcenters_cs_poleValueEnum` / `exists_poleValueEnum_ball` — the **finite centre**
  (pole-value) enumeration; closes `m`/`cs`/`ρ`/`hcs_ball`/`hcs_inj`/`hcenters_cs`.
* `canonicalFibreSelection_hΦ_*` — the canonical-selection `Φ`-enumeration discharge (from a single
  pole-value-goodness genericity `hgood`).
* `directTraceGeometry_ofAdapted` / `…ofAdaptedSimpleInfty` / `…ofCanonicalSimpleInfty` — the
  maximal-proven-prefix constructors (general `Φ` → canonical `Φ` + simple `∞`), each building the proven
  field-groups and taking the deep analytic content as named hypotheses.
* `residueTheorem_of_canonicalAdapted` — the capstone: Gate A `∑Res = 0` directly from the residuals.

## Honest scope (this is a 38-field assembly)

A *full* closure of `DirectTraceGeometry` for general `poles` is **not** delivered here: the fields
`hcont_int` (junk-freeness) and `R₀`/`hR₀0`/`hR₀_eq` (kirovGenus-`0` `∞`-vanishing) are residual *everywhere
in the repo* — only the empty-pole case discharges them (the kirovGenus-`0` `H⁰(ℂℙ¹,Ω)=0` content applied to
a *nonempty* trace is genuinely-open analytic content, never built), and the per-centre full-fibre moving
coherence `Cfull` requires a per-centre `LocalSheetSystem` + the regular-value `g`-meromorphy wiring.
`directTraceGeometry_ofAdapted` takes these as hypotheses, so the residual is *precisely* those
field-groups, not a false field.  Each field the constructor *proves* is genuinely satisfiable.

## Soundness

No `axiom`, no gaps, **no false field**.  Every proven field is a true, satisfiable statement; the
deep residuals are exposed as hypotheses (not papered over).  The germ `agree`/`agree_infty` is **never**
introduced.  All public declarations are authoritatively `[propext, Classical.choice, Quot.sound]`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256 (the genericity:
  "choose any nonconstant `f`").
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256.
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

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## The pole sub-fibre of a full-fibre regularity datum

The honest residue-level route separates the **full-fibre** moving coherence `Cfull` (whose germ
equality is *sound*) from the **pole-only** fibre data `D`.  Given a full-fibre datum `Dfull` (its `xs`
enumerating the entire fibre `F⁻¹(coe b)`), the pole-only sub-fibre enumerates exactly the `α`-poles in
that fibre.  Since the fibre points over a finite value `coe b` are all `f`-regular non-poles (they map
to a finite sphere value), the sub-fibre is again a genuine `FibreRegularData` — we simply restrict
`Dfull`'s fields to the subtype `{i // Dfull.xs i ∈ poles}`.  ("Pole" here is an `α = ω₀·g` pole
(`∈ poles : Finset X`), *not* a pole of `f`.) -/

/-- **The pole-only sub-fibre** of a full-fibre regularity datum.  Over the subtype `{i // Dfull.xs i ∈
poles}` of fibre indices whose point is an `α`-pole, the `FibreRegularData g f b` whose `xs` is the
restriction `Dfull.xs ∘ Subtype.val`.  Every field is inherited from `Dfull` (the fibre points are
`f`-regular non-poles, intrinsic to the finite value `coe b`). -/
noncomputable def poleSubfibre (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b) :
    FibreRegularData g f b where
  ι := {i : Dfull.ι // Dfull.xs i ∈ poles}
  fintype_ι := Subtype.fintype _
  xs := fun i => Dfull.xs i.1
  hg_an := fun i => Dfull.hg_an i.1
  hg_deriv := fun i => Dfull.hg_deriv i.1
  hval := fun i => Dfull.hval i.1
  hg_mero := fun i => Dfull.hg_mero i.1

@[simp] theorem poleSubfibre_xs (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b)
    (i : {i : Dfull.ι // Dfull.xs i ∈ poles}) :
    (poleSubfibre poles Dfull).xs i = Dfull.xs i.1 := rfl

/-- The pole sub-fibre enumeration is **injective** when the full enumeration is. -/
theorem poleSubfibre_xs_injective (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b)
    (hfull_inj : Function.Injective Dfull.xs) :
    Function.Injective (poleSubfibre poles Dfull).xs := by
  intro i j h
  exact Subtype.ext (hfull_inj h)

/-- The pole sub-fibre points **are `α`-poles in the fibre `F⁻¹(coe b)`** — provided the full
enumeration's points lie in the fibre (`hfull_mem`).  This is the `hxs_mem` content. -/
theorem poleSubfibre_xs_mem (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b)
    (hfull_mem : ∀ i, f.toRiemannSphere (Dfull.xs i) = (((b : ℂ) : RiemannSphere)))
    (i : {i : Dfull.ι // Dfull.xs i ∈ poles}) :
    (poleSubfibre poles Dfull).xs i ∈ poles ∧
      f.toRiemannSphere ((poleSubfibre poles Dfull).xs i) = (((b : ℂ) : RiemannSphere)) :=
  ⟨i.2, hfull_mem i.1⟩

/-- The pole sub-fibre enumerates **all** `α`-poles over `coe b` — provided the full enumeration's range
is the whole fibre (`hfull_range`).  This is the `hxs_surj` content. -/
theorem poleSubfibre_xs_surj (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b)
    (hfull_range : Set.range Dfull.xs = f.toRiemannSphere ⁻¹' {(((b : ℂ) : RiemannSphere))})
    (a : X) (ha : a ∈ poles) (hfa : f.toRiemannSphere a = (((b : ℂ) : RiemannSphere))) :
    ∃ i, (poleSubfibre poles Dfull).xs i = a := by
  -- `a` is in the fibre, so in the range of `Dfull.xs`; the preimage index is in the pole subtype.
  have hmem : a ∈ Set.range Dfull.xs := by
    rw [hfull_range, Set.mem_preimage, Set.mem_singleton_iff]; exact hfa
  obtain ⟨i, rfl⟩ := hmem
  exact ⟨⟨i, ha⟩, rfl⟩

/-- **The pole↔full matching `hpole_image`.**  The pole points of the full enumeration `Dfull.xs` are
exactly the image of the pole sub-fibre enumeration:

> `(univ.image Dfull.xs).filter (· ∈ poles) = univ.image (poleSubfibre poles Dfull).xs`.

Pure `Finset` combinatorics (the sub-fibre `xs` is `Dfull.xs` restricted to the pole-subtype, so its
image is the pole-filter of `Dfull.xs`'s image).  This is the field connecting the pole-only `D` to the
full-fibre `Cfull` at the residue level. -/
theorem poleSubfibre_hpole_image (poles : Finset X) {b : ℂ} (Dfull : FibreRegularData g f b) :
    (Finset.univ.image Dfull.xs).filter (· ∈ poles)
      = Finset.univ.image (poleSubfibre poles Dfull).xs := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, poleSubfibre_xs]
  constructor
  · rintro ⟨⟨i, rfl⟩, hpole⟩
    exact ⟨⟨i, hpole⟩, rfl⟩
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩

/-! ## The pole sub-enumeration of a raw `∞`-fibre enumeration

The `∞`-analogue of `poleSubfibre`: for a raw enumeration `xs : ι → X` of the full `∞`-fibre, the
pole-only sub-enumeration over the subtype `{k // xs k ∈ poles}`.  Used for the `xsInf_po` field
(the `α`-poles among the full `∞`-fibre) and its `hpole_image_inf` matching. -/

/-- The pole sub-enumeration `xs ∘ Subtype.val` over `{k // xs k ∈ poles}` is **injective** when `xs`
is. -/
theorem poleSubEnum_injective {ι : Type} (poles : Finset X) (xs : ι → X)
    (hxs_inj : Function.Injective xs) :
    Function.Injective (fun k : {k // xs k ∈ poles} => xs k.1) := by
  intro i j h; exact Subtype.ext (hxs_inj h)

/-- The pole sub-enumeration points **are `α`-poles over `∞`** when the full enumeration's points are
over `∞` (`hxs_mem`). -/
theorem poleSubEnum_mem {ι : Type} (poles : Finset X) (xs : ι → X)
    (hxs_mem : ∀ k, f.toRiemannSphere (xs k) = OnePoint.infty)
    (k : {k // xs k ∈ poles}) :
    (fun k : {k // xs k ∈ poles} => xs k.1) k ∈ poles ∧
      f.toRiemannSphere ((fun k : {k // xs k ∈ poles} => xs k.1) k) = OnePoint.infty :=
  ⟨k.2, hxs_mem k.1⟩

/-- The pole sub-enumeration covers **all** `α`-poles over `∞` when the full enumeration is
surjective onto the `∞`-fibre poles (`hxs_surj`). -/
theorem poleSubEnum_surj {ι : Type} (poles : Finset X) (xs : ι → X)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ k, xs k = a)
    (a : X) (ha : a ∈ poles) (hfa : f.toRiemannSphere a = OnePoint.infty) :
    ∃ k, (fun k : {k // xs k ∈ poles} => xs k.1) k = a := by
  obtain ⟨k, rfl⟩ := hxs_surj a ha hfa
  exact ⟨⟨k, ha⟩, rfl⟩

/-- **The `∞`-pole↔full matching `hpole_image_inf`.**  The pole points of the full `∞`-enumeration are
exactly the image of the pole sub-enumeration.  Pure `Finset` combinatorics. -/
theorem poleSubEnum_hpole_image {ι : Type} [Fintype ι] (poles : Finset X) (xs : ι → X) :
    (Finset.univ.image xs).filter (· ∈ poles)
      = (Finset.univ : Finset {k // xs k ∈ poles}).image (fun k => xs k.1) := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hpole⟩
    exact ⟨⟨i, hpole⟩, rfl⟩
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩

/-! ## The full `∞`-fibre datum from simple poles (`Dinf_full`)

The full `∞`-fibre is `F⁻¹(∞) = {x | f.orderAtPoint x < 0}` (the poles of `f`), finite on the compact
`X` (`f.finite_poles`).  When every pole of `f` is **simple** (`orderAtPoint = −1`, the cover unramified
over `∞`) and `g`'s chart pullback is meromorphic at each, `InftyFibreDataNF.ofRegular` packages the
whole `∞`-fibre into a sound `InftyFibreDataNF`.  This **fully discharges** the `∞`-fibre-data group
`Dinf_full`/`hfullInf_inj`/`hinf_mem`/`hinf_surj` of `directTraceGeometry_ofAdapted` from the adapted
inputs (simple `∞`-poles + `g`-meromorphy) — no residual. -/

/-- The full `∞`-fibre as a `Fin`-enumeration: `Subtype.val ∘ (poles-of-`f`).toFinset.equivFin.symm`. -/
noncomputable def inftyFibreEnum (f : MeromorphicFunction X) :
    Fin (f.finite_poles.toFinset.card) → X :=
  fun i => (f.finite_poles.toFinset.equivFin.symm i : X)

theorem inftyFibreEnum_lt (f : MeromorphicFunction X) (i : Fin (f.finite_poles.toFinset.card)) :
    f.orderAtPoint (inftyFibreEnum f i) < 0 := by
  have hmem := (f.finite_poles.toFinset.equivFin.symm i).2
  rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hmem

theorem inftyFibreEnum_mem (f : MeromorphicFunction X) (i : Fin (f.finite_poles.toFinset.card)) :
    f.toRiemannSphere (inftyFibreEnum f i) = OnePoint.infty :=
  f.toRiemannSphere_of_pole (inftyFibreEnum_lt f i)

theorem inftyFibreEnum_injective (f : MeromorphicFunction X) :
    Function.Injective (inftyFibreEnum f) := by
  intro i j h
  exact f.finite_poles.toFinset.equivFin.symm.injective (Subtype.ext h)

/-- `inftyFibreEnum` enumerates **all** poles of `f` (every `a` with `F a = ∞` is hit). -/
theorem inftyFibreEnum_surj (f : MeromorphicFunction X) {a : X}
    (hfa : f.toRiemannSphere a = OnePoint.infty) : ∃ i, inftyFibreEnum f i = a := by
  classical
  -- `F a = ∞ ⟹ a` is a pole, so `a ∈ (poles-of-f).toFinset`.
  have ha_pole : f.orderAtPoint a < 0 := by
    by_contra h
    rw [f.toRiemannSphere_of_nonneg (not_lt.mp h)] at hfa
    exact (OnePoint.coe_ne_infty _) hfa
  have haF : a ∈ f.finite_poles.toFinset := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact ha_pole
  refine ⟨f.finite_poles.toFinset.equivFin ⟨a, haF⟩, ?_⟩
  show (f.finite_poles.toFinset.equivFin.symm (f.finite_poles.toFinset.equivFin ⟨a, haF⟩) : X) = a
  rw [Equiv.symm_apply_apply]

/-- **The full `∞`-fibre datum from simple poles.**  When every pole of `f` is simple
(`hsimple : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = −1`) with `g`-meromorphy `hmero`, the
`InftyFibreDataNF g f` enumerating the *entire* `∞`-fibre `F⁻¹(∞)`. -/
noncomputable def inftyFibreDataNF_full (g : X → ℂ) (f : MeromorphicFunction X)
    (hsimple : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i))) :
    InftyFibreDataNF g f :=
  InftyFibreDataNF.ofRegular g f (inftyFibreEnum f) hsimple hmero

@[simp] theorem inftyFibreDataNF_full_xs (g : X → ℂ) (f : MeromorphicFunction X)
    (hsimple : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i))) :
    (inftyFibreDataNF_full g f hsimple hmero).xs = inftyFibreEnum f := rfl

/-! ## The finite centre (pole-value) enumeration

The centres `cs` are the finite pole-VALUES of `α`: the distinct finite sphere-values `coe (cs i)` of
the poles (the `∞`-value handled separately by the `∞`-fibre).  These form a finite subset of `ℂ` — the
`holoRepr`-image of the non-`∞` poles — enumerated injectively by `Finset.equivFin`.  The bookkeeping
field `hcenters_cs` (`(univ.image cs).image coe = (poles.image F).erase ∞`) is **proven** from the
relation `coe (holoRepr a) = F a` for non-`∞` poles. -/

/-- The finite **pole-value** set in `ℂ`: the `holoRepr`-image of the non-`∞` poles of `α`. -/
noncomputable def poleValues (f : MeromorphicFunction X) (poles : Finset X) : Finset ℂ :=
  (poles.filter (fun a => f.toRiemannSphere a ≠ OnePoint.infty)).image f.holoRepr

/-- The injective `Fin`-enumeration of the pole-values. -/
noncomputable def poleValueEnum (f : MeromorphicFunction X) (poles : Finset X) :
    Fin (poleValues f poles).card → ℂ :=
  fun i => (poleValues f poles).equivFin.symm i

theorem poleValueEnum_injective (f : MeromorphicFunction X) (poles : Finset X) :
    Function.Injective (poleValueEnum f poles) :=
  fun _i _j h => (poleValues f poles).equivFin.symm.injective (Subtype.ext h)

/-- `univ.image (poleValueEnum) = poleValues` (the enumeration is a bijection onto the pole-value set). -/
theorem image_poleValueEnum (f : MeromorphicFunction X) (poles : Finset X) :
    Finset.univ.image (poleValueEnum f poles) = poleValues f poles := by
  classical
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, poleValueEnum]
  constructor
  · rintro ⟨i, rfl⟩; exact ((poleValues f poles).equivFin.symm i).2
  · intro hc; exact ⟨(poleValues f poles).equivFin ⟨c, hc⟩, by rw [Equiv.symm_apply_apply]⟩

/-- **The centre bookkeeping `hcenters_cs`.**  Mapping the pole-value enumeration to the sphere recovers
exactly the finite pole-values: `(univ.image (poleValueEnum)).image coe = (poles.image F).erase ∞`.
Proven from `coe (holoRepr a) = F a` for non-`∞` poles. -/
theorem hcenters_cs_poleValueEnum (f : MeromorphicFunction X) (poles : Finset X) :
    (Finset.univ.image (poleValueEnum f poles)).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty := by
  classical
  rw [image_poleValueEnum, poleValues, Finset.image_image]
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Function.comp_apply]
  constructor
  · rintro ⟨a, ⟨ha_pole, ha_ne⟩, rfl⟩
    -- `coe (holoRepr a) = F a` (a is an `f`-non-pole, finite value), and `F a ≠ ∞`.
    have hnp : 0 ≤ f.orderAtPoint a := by
      by_contra h; exact ha_ne (f.toRiemannSphere_of_pole (not_le.mp h))
    rw [← f.toRiemannSphere_of_nonneg hnp]
    exact ⟨ha_ne, a, ha_pole, rfl⟩
  · rintro ⟨hy_ne, a, ha_pole, rfl⟩
    -- `F a ≠ ∞ ⟹ a` is an `f`-non-pole, so `F a = coe (holoRepr a)`.
    have hnp : 0 ≤ f.orderAtPoint a := by
      by_contra h; exact hy_ne (f.toRiemannSphere_of_pole (not_le.mp h))
    exact ⟨a, ⟨ha_pole, hy_ne⟩, (f.toRiemannSphere_of_nonneg hnp).symm⟩

/-- **A radius bounding all centres** (`hcs_ball` data).  Any finite set of complex numbers lies in some
ball about `0`; specialized to the pole-value enumeration. -/
theorem exists_poleValueEnum_ball (f : MeromorphicFunction X) (poles : Finset X) :
    ∃ ρ : ℝ, ∀ i, poleValueEnum f poles i ∈ ball (0 : ℂ) ρ := by
  obtain ⟨M, hM⟩ := ((poleValues f poles).image (fun c => ‖c‖)).exists_le
  refine ⟨M + 1, fun i => ?_⟩
  rw [mem_ball, dist_zero_right]
  have hmem : poleValueEnum f poles i ∈ poleValues f poles := by
    rw [← image_poleValueEnum]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have := hM (‖poleValueEnum f poles i‖) (Finset.mem_image_of_mem _ hmem)
  linarith

/-! ## The maximal proven-prefix constructor `directTraceGeometry_ofAdapted`

The honest reduction of Miranda's genericity for a *general* adapted cover `f`.  Given:

* the global full-fibre selection `Φ` with the three pole-value enumeration properties `hΦ_inj` /
  `hΦ_mem` / `hΦ_surj` (`Φ p` enumerates exactly the fibre `F⁻¹(coe p)`, injectively, catching all
  poles — the genuine selection content);
* the finite centre data `m`/`cs`/`ρ`/`hcs_ball`/`hcs_inj`/`br` and `hcenters_cs`;
* the per-centre **full-fibre** moving coherence `Cfull` with `hCfull_inj` (its fibre enumeration is
  injective) and `hCfull_image : univ.image (Cfull i).D.xs = univ.image (Φ (cs i)).xs` (the moving
  datum's fixed fibre and the selection fibre have the *same image* — both the full fibre over `cs i`;
  the weaker image-equality, not data-equality, which is all the residue-level matching needs);
* the **non-pole residue-`0` analyticity** `hnonpole_an` (the full fibre's non-pole points have analytic
  `g`-pullback);
* the **full `∞`-fibre** sound datum `Dinf_full` with `hfullInf_inj` / `hinf_mem` / `hinf_surj` (it
  enumerates exactly the `∞`-fibre, catching all `∞`-poles) and `hnonpole_inf_an`;

and the **deep analytic residuals** — `hreg` (regular-value analyticity), `hbnd` (branch boundedness),
`hcont_int` (junk-freeness), `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` (kirovGenus-`0` `∞`-vanishing), `hcoh_full`
(`∞`-single-valuedness) — as explicit hypotheses,

this constructs a `DirectTraceGeometry ω₀ g f poles`.  The pole-only fibre `D := poleSubfibre ∘ Φ` and
the `∞`-pole sub-enumeration are **proven** (via the `poleSubfibre`/`poleSubEnum` combinatorics); the
matching fields `hpole_image`/`hpole_image_inf` follow.  This reduces Gate A to *precisely* the deep
analytic residuals (the kirovGenus-`0` content + the per-centre/`∞` coherence), with **no false field**. -/

/-- **`DirectTraceGeometry` from an adapted cover (maximal proven prefix).**  Builds the pole-only
finite/`∞` fibre groups, the pole↔full matching, and the centre bookkeeping from `Φ` + the concrete
enumeration data; the deep analytic content (regular-value analyticity, branch boundedness,
junk-freeness, kirovGenus-`0` `∞`-vanishing, the full-fibre/`∞` coherence) is taken as named hypotheses.
Reduces Gate A's genericity to the smallest honest residual. -/
noncomputable def directTraceGeometry_ofAdapted
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (hΦ_inj : ∀ p, Function.Injective (Φ p).xs)
    (hΦ_mem : ∀ p, ∀ i, f.toRiemannSphere ((Φ p).xs i) = (((p : ℂ) : RiemannSphere)))
    (hΦ_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere)) →
      ∃ i, (Φ p).xs i = a)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i, Finset.univ.image (Cfull i).D.xs = Finset.univ.image (Φ (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (Dinf_full : InftyFibreDataNF g f) (hfullInf_inj : Function.Injective Dinf_full.xs)
    (hinf_mem : ∀ k, f.toRiemannSphere (Dinf_full.xs k) = OnePoint.infty)
    (hinf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ k, Dinf_full.xs k = a)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k)))
    -- The deep analytic residuals (kirovGenus-`0` content + coherence), exposed as hypotheses.
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full)) :
    DirectTraceGeometry ω₀ g f poles where
  Φ := Φ
  m := m
  cs := cs
  ρ := ρ
  hcs_ball := hcs_ball
  hcs_inj := hcs_inj
  br := br
  hreg := hreg
  hbnd := hbnd
  Cfull := Cfull
  -- The pole-only fibre is the pole sub-fibre of the canonical selection.
  D := fun p => poleSubfibre poles (Φ p)
  hxs_inj := fun p => poleSubfibre_xs_injective poles (Φ p) (hΦ_inj p)
  hxs_mem := fun p i => poleSubfibre_xs_mem poles (Φ p) (hΦ_mem p) i
  hxs_surj := fun p a ha hfa => by
    -- `a` (a pole over `coe p`) is in the range of `Φ p` (`hΦ_surj`); its index lies in the pole
    -- subtype since `a ∈ poles`.
    obtain ⟨i, rfl⟩ := hΦ_surj p a ha hfa
    exact ⟨⟨i, ha⟩, rfl⟩
  hcenters_cs := hcenters_cs
  hfull_inj := hCfull_inj
  hpole_image := fun i => by
    -- `D (cs i) = poleSubfibre poles (Φ (cs i))`; rewrite the full-fibre filter through the
    -- image-equality `hCfull_image i`, then `poleSubfibre_hpole_image`.
    rw [hCfull_image i]
    exact poleSubfibre_hpole_image poles (Φ (cs i))
  hnonpole_an := hnonpole_an
  hcont_int := hcont_int
  R₀ := R₀
  hR₀_an := hR₀_an
  hR₀0 := hR₀0
  hR₀_eq := hR₀_eq
  Dinf_full := Dinf_full
  hcoh_full := hcoh_full
  hfullInf_inj := hfullInf_inj
  ιInfP := {k // Dinf_full.xs k ∈ poles}
  fintypeInfP := Subtype.fintype _
  xsInf_po := fun k => Dinf_full.xs k.1
  hpoInf_inj := poleSubEnum_injective poles Dinf_full.xs hfullInf_inj
  hpoInf_mem := fun k => poleSubEnum_mem poles Dinf_full.xs hinf_mem k
  hpoInf_surj := fun a ha hfa => poleSubEnum_surj poles Dinf_full.xs hinf_surj a ha hfa
  hpole_image_inf := poleSubEnum_hpole_image poles Dinf_full.xs
  hnonpole_inf_an := hnonpole_inf_an

/-- **`DirectTraceGeometry` from an adapted cover with simple `∞`-poles.**  A specialization of
`directTraceGeometry_ofAdapted` that **closes the entire `∞`-fibre-data group**: the full `∞`-fibre
datum `Dinf_full` is *constructed* as `inftyFibreDataNF_full` (enumerating all poles of `f`, each
simple), so the four `∞`-fibre inputs `Dinf_full`/`hfullInf_inj`/`hinf_mem`/`hinf_surj` are discharged
from the adapted inputs `hsimpleInf` (every `f`-pole simple) + `hmeroInf` (`g`-meromorphy over `∞`).
The remaining inputs are the finite-fibre selection `Φ`, the per-centre full-fibre coherence `Cfull`,
and the deep analytic residuals — exactly the smallest honest residual of Gate A. -/
noncomputable def directTraceGeometry_ofAdaptedSimpleInfty
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (hΦ_inj : ∀ p, Function.Injective (Φ p).xs)
    (hΦ_mem : ∀ p, ∀ i, f.toRiemannSphere ((Φ p).xs i) = (((p : ℂ) : RiemannSphere)))
    (hΦ_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere)) →
      ∃ i, (Φ p).xs i = a)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i, Finset.univ.image (Cfull i).D.xs = Finset.univ.image (Φ (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    -- The `∞`-fibre genericity: every `f`-pole simple + `g`-meromorphy over `∞`.
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    -- The deep analytic residuals (kirovGenus-`0` content + coherence), exposed as hypotheses.
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    DirectTraceGeometry ω₀ g f poles :=
  directTraceGeometry_ofAdapted Φ hΦ_inj hΦ_mem hΦ_surj m cs ρ hcs_ball hcs_inj br hcenters_cs
    Cfull hCfull_inj hCfull_image hnonpole_an
    (inftyFibreDataNF_full g f hsimpleInf hmeroInf)
    (inftyFibreEnum_injective f)
    (fun k => inftyFibreEnum_mem f k)
    (fun _a _ha hfa => inftyFibreEnum_surj f hfa)
    hnonpole_inf_an hreg hbnd hcont_int R₀ hR₀_an hR₀0 hR₀_eq hcoh_full

/-! ## The canonical-selection enumeration discharge (`hΦ_inj`/`hΦ_mem`/`hΦ_surj`)

The canonical full-fibre selection `canonicalFibreSelection g f hdiv` discharges the three
`Φ`-enumeration inputs of `directTraceGeometry_ofAdapted` from a *single* genericity hypothesis: every
**pole-value** `coe p` (a value with some `α`-pole over it) is a **good value** (off the branch locus,
`g`-meromorphic at the fibre — `GoodValue`).  At a good value the canonical selection injectively
enumerates the full fibre (range = fibre); at a non-good value it is the empty datum, whose `xs` is
vacuous, and the genericity forces *no* `α`-pole over such a value (so `hΦ_surj` holds vacuously). -/

/-- **`hΦ_inj` for the canonical selection.**  Always holds: at good values by
`canonicalFibreSelection_xs_injective`; at non-good values the datum is empty (`xs` over `Empty`). -/
theorem canonicalFibreSelection_hΦ_inj (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (p : ℂ) : Function.Injective (canonicalFibreSelection g f hdiv p).xs := by
  by_cases h : GoodValue g f hdiv p
  · exact canonicalFibreSelection_xs_injective g f hdiv h
  · rw [canonicalFibreSelection, dif_neg h]; intro i; exact i.elim

/-- **`hΦ_mem` for the canonical selection.**  Each enumerated point lies in the fibre `F⁻¹(coe p)`:
at good values from `canonicalFibreSelection_xs_range`; at non-good values vacuously (no points). -/
theorem canonicalFibreSelection_hΦ_mem (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (p : ℂ) (i : (canonicalFibreSelection g f hdiv p).ι) :
    f.toRiemannSphere ((canonicalFibreSelection g f hdiv p).xs i) = (((p : ℂ) : RiemannSphere)) := by
  by_cases h : GoodValue g f hdiv p
  · have hmem : (canonicalFibreSelection g f hdiv p).xs i ∈ Set.range (canonicalFibreSelection g f hdiv p).xs :=
      ⟨i, rfl⟩
    rw [canonicalFibreSelection_xs_range g f hdiv h, Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact hmem
  · rw [canonicalFibreSelection, dif_neg h] at i; exact i.elim

/-- **`hΦ_surj` for the canonical selection, from pole-value goodness.**  If every value with an
`α`-pole over it is good (`hgood`), the canonical selection catches all poles: at a good pole-value the
fibre range covers it; a non-good value has no `α`-pole (contrapositive of `hgood`). -/
theorem canonicalFibreSelection_hΦ_surj (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {poles : Finset X}
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (p : ℂ) (a : X) (ha : a ∈ poles) (hfa : f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) :
    ∃ i, (canonicalFibreSelection g f hdiv p).xs i = a := by
  have h : GoodValue g f hdiv p := hgood p ⟨a, ha, hfa⟩
  have hmem : a ∈ Set.range (canonicalFibreSelection g f hdiv p).xs := by
    rw [canonicalFibreSelection_xs_range g f hdiv h, Set.mem_preimage, Set.mem_singleton_iff]
    exact hfa
  exact hmem

/-- **`DirectTraceGeometry` from the canonical selection with simple `∞`-poles.**  The most-wired
constructor: `Φ := canonicalFibreSelection g f hdiv` (so the three `Φ`-enumeration inputs are
discharged from the single pole-value-goodness genericity `hgood`), and the full `∞`-fibre is
constructed from simple poles.  The *remaining* inputs are the finite centre data + the deep analytic
residuals (per-centre full-fibre coherence `Cfull`, regular-value analyticity `hreg`, branch
boundedness `hbnd`, junk-freeness `hcont_int`, kirovGenus-`0` `∞`-vanishing `R₀`, `∞`-single-valuedness
`hcoh_full`) — the smallest honest residual of Gate A's genericity. -/
noncomputable def directTraceGeometry_ofCanonicalSimpleInfty (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i,
      Finset.univ.image (Cfull i).D.xs = Finset.univ.image (canonicalFibreSelection g f hdiv (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R)
          =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R)
        =ᶠ[𝓝[≠] 0] R₀)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    DirectTraceGeometry ω₀ g f poles :=
  directTraceGeometry_ofAdaptedSimpleInfty (canonicalFibreSelection g f hdiv)
    (canonicalFibreSelection_hΦ_inj f hdiv)
    (canonicalFibreSelection_hΦ_mem f hdiv)
    (canonicalFibreSelection_hΦ_surj f hdiv hgood)
    m cs ρ hcs_ball hcs_inj br hcenters_cs Cfull hCfull_inj hCfull_image hnonpole_an
    hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd hcont_int R₀ hR₀_an hR₀0 hR₀_eq hcoh_full

/-! ## The capstone reduction of Gate A to the residual hypotheses

Chaining `directTraceGeometry_ofCanonicalSimpleInfty` into the proven `residueTheorem_of_directTraceGeometry`
gives Gate A `∑Res = 0` directly from the residual hypotheses — making the standing of Gate A crisp:
all the combinatorial / pole-only / `∞`-fibre / centre-bookkeeping content is *proven*, and the residue
theorem holds for `α = ω₀·g` modulo *exactly* the per-centre full-fibre coherence + the deep analytic
kirovGenus-`0` content. -/

/-- **Gate A `∑Res = 0` from the canonical-selection residuals.**  With the canonical full-fibre
selection, simple `∞`-poles, and pole-value goodness, the residue theorem `∑_{a ∈ poles} formFnResidue
ω₀ g a = 0` holds modulo *only* the per-centre full-fibre coherence `Cfull` and the deep analytic
residuals (`hreg`/`hbnd`/`hcont_int`/`R₀`/`hcoh_full`).  The pole-only fibre data, the pole↔full
matching, the full `∞`-fibre, and the centre bookkeeping are all discharged. -/
theorem residueTheorem_of_canonicalAdapted (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) (cs i))
    (hCfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hCfull_image : ∀ i,
      Finset.univ.image (Cfull i).D.xs = Finset.univ.image (canonicalFibreSelection g f hdiv (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k)))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R)
          =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br - L.R)
        =ᶠ[𝓝[≠] 0] R₀)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_directTraceGeometry
    (directTraceGeometry_ofCanonicalSimpleInfty hdiv hgood m cs ρ hcs_ball hcs_inj br hcenters_cs
      Cfull hCfull_inj hCfull_image hnonpole_an hsimpleInf hmeroInf hnonpole_inf_an hreg hbnd
      hcont_int R₀ hR₀_an hR₀0 hR₀_eq hcoh_full)

end Jacobians.Dolbeault.SerreResidueTheorem
