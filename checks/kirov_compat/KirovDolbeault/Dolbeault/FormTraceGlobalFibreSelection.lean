/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGateAAssemble

/-!
# The canonical full-fibre selection `Φ` (Gate A wall 2, Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceGateAAssemble.residueSum_eq_zero_of_globalCoverData` reduced Gate A's
`∑ₐ Resₐ(α) = 0` to (wall 1) the adapted-cover genericity, (wall 2) the **global coherent selection**
`Φ` with its regular-value canonical-fibre conditions + the per-pole moving sections, and (wall 3) the
`∞`-rationality.

This file discharges the **regular-value part of wall 2** by constructing the *canonical full-fibre
selection* — at each base value `b`, `Φ b` enumerates the **entire** fibre `F⁻¹(coe b)` of the compact
sphere map `F = f.toRiemannSphere` (whose cardinality is the proper-map degree at regular values), via
the proved finiteness of the fibres (`fibre_finite_of_div_ne_zero`).  The construction is
**monodromy-free** (the symmetric-lever, Miranda §VIII.3): there is no continuous sheet labeling, only
the canonical fibre *as a set*.

The genuine analytic inputs are all *intrinsic to being off the branch locus*:

* every point of a finite-value fibre is a **non-pole** (`nonpole_of_toRiemannSphere_eq_coe`), so the
  `hg_an`/`hval` fields of `FibreRegularData` hold;
* off the branch locus every fibre point is a **regular point of `f`**
  (`sheet_holoRepr_deriv_ne_zero`), so `hg_deriv ≠ 0`.

The only datum-dependent field is `hg_mero` — `g`'s chart pullback meromorphic at the fibre points —
which is supplied as the standard regular-value hypothesis on the numerator `g` of `α = ω₀·g`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `FibreRegularData.ofFullFibre` — the full-fibre regularity datum at a value `coe b` off the branch
  locus (every fibre point a regular non-pole), with `g`-meromorphy supplied.
* `canonicalFibreSelection` — the global selection `Φ`: the full-fibre datum at "good" values
  (off-branch, `g`-meromorphic at the fibre), the empty datum elsewhere.
* `canonicalFibreSelection_xs_range` / `_injective` — at a good value the canonical selection
  *injectively enumerates the full fibre* `F⁻¹(coe b)`.
* `canonicalFibreSelection_hΦrangeReg` / `_hΦinjReg` — the **canonical-fibre conditions**
  `hΦrangeReg`/`hΦinjReg` of `residueSum_eq_zero_of_globalCoverData`, eventually near every regular
  value, from the regular-value `g`-data.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; single-valued
  **by symmetry**, the full-fibre symmetric sum).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere Jacobians.ProperMapDegreeSheets
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The finite enumeration of the full fibre

For a nonconstant `f` (`f.div ≠ 0`) every sphere fibre is finite (`fibre_finite_of_div_ne_zero`).
We enumerate the fibre `F⁻¹(coe b)` over a finite value `coe b` by `Fin N` via the finset
`(hfib).toFinset` and its `equivFin`. -/

/-- The cardinality of the (finite) fibre `F⁻¹(coe b)` over a finite value `coe b`. -/
def fullFibreCard (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) : ℕ :=
  (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.card

/-- The `Fin (fullFibreCard …)`-enumeration of the fibre `F⁻¹(coe b)`:
`Subtype.val ∘ (toFinset).equivFin.symm`. -/
noncomputable def fullFibreEnum (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (b : ℂ) : Fin (fullFibreCard f hdiv b) → X :=
  fun i => ((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
    (Fin.cast (by rw [fullFibreCard]) i) : X)

/-- Each enumerated point lies in the fibre: `F (fullFibreEnum f hdiv b i) = coe b`. -/
theorem fullFibreEnum_mem (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (i : Fin (fullFibreCard f hdiv b)) :
    f.toRiemannSphere (fullFibreEnum f hdiv b i) = (((b : ℂ) : RiemannSphere)) := by
  have hmem := ((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
    (Fin.cast (by rw [fullFibreCard]) i)).2
  rwa [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hmem

/-- The full-fibre enumeration is **injective**. -/
theorem fullFibreEnum_injective (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (b : ℂ) : Function.Injective (fullFibreEnum f hdiv b) := by
  intro i j h
  have := (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm.injective
    (Subtype.ext h)
  exact Fin.cast_injective _ this

/-- The full-fibre enumeration has **range exactly the fibre** `F⁻¹(coe b)`. -/
theorem fullFibreEnum_range (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) :
    Set.range (fullFibreEnum f hdiv b) = f.toRiemannSphere ⁻¹' {(((b : ℂ) : RiemannSphere))} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact fullFibreEnum_mem f hdiv b i
  · intro hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    have hxF : x ∈ (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]; exact hx
    refine ⟨Fin.cast (by rw [fullFibreCard]) (((fibre_finite_of_div_ne_zero f hdiv
      (((b : ℂ) : RiemannSphere))).toFinset.equivFin) ⟨x, hxF⟩), ?_⟩
    show (((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
      (Fin.cast _ (Fin.cast _ (((fibre_finite_of_div_ne_zero f hdiv
        (((b : ℂ) : RiemannSphere))).toFinset.equivFin) ⟨x, hxF⟩)))) : X) = x
    rw [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]

/-! ### The full-fibre regularity datum at a regular value

At a finite value `coe b` **off the branch locus**, every point of the fibre `F⁻¹(coe b)` is a
*regular non-pole point* of `f`:

* it is a non-pole (its sphere value `coe b` is finite, `nonpole_of_toRiemannSphere_eq_coe`), so
  `f.holoRepr`'s chart pullback is analytic and `f.holoRepr (xs i) = b` (the `hval` field);
* it is regular (off the branch locus the sphere cover is locally injective, hence the chart-pullback
  derivative is nonzero, `sheet_holoRepr_deriv_ne_zero`).

The only datum-dependent field `hg_mero` (`g`'s chart pullback meromorphic at each fibre point) is
supplied.  This packages the *full* fibre into a `FibreRegularData` — the canonical fibre, with no
labeling. -/

/-- **The full-fibre regularity datum.**  At a finite value `coe b` off the branch locus of `F =
f.toRiemannSphere`, the `FibreRegularData g f b` whose `xs` enumerates the **entire** fibre
`F⁻¹(coe b)` (`fullFibreEnum`).  Every fibre point is a regular non-pole (intrinsic to being
off-branch); `hg_mero` is supplied. -/
noncomputable def FibreRegularData.ofFullFibre (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (hoff : (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
      ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))) :
    FibreRegularData g f b :=
  FibreRegularData.ofRegular g f b
    (ι := Fin (fullFibreCard f hdiv b))
    (xs := fullFibreEnum f hdiv b)
    (hnp := fun i => (f.nonpole_of_toRiemannSphere_eq_coe (fullFibreEnum_mem f hdiv b i)).1)
    (hderiv := fun i =>
      sheet_holoRepr_deriv_ne_zero f hdiv hoff (fullFibreEnum_mem f hdiv b i))
    (hval := fun i => (f.nonpole_of_toRiemannSphere_eq_coe (fullFibreEnum_mem f hdiv b i)).2)
    (hmero := hmero)

@[simp] theorem FibreRegularData.ofFullFibre_xs (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (hoff : (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
      ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))) (i) :
    (FibreRegularData.ofFullFibre (g := g) f hdiv b hoff hmero).xs i = fullFibreEnum f hdiv b i :=
  rfl

/-! ### The canonical global full-fibre selection `Φ`

`Φ b` is the full-fibre datum at every value where it can be built — the **good values** `b`, where
`coe b` is off the branch locus and `g`'s chart pullback is meromorphic at each fibre point.  At every
other value (branch values, or values with bad `g`-data) `Φ b` is the empty datum.  This is the
*canonical* selection: at regular values it enumerates the **full** fibre with no labeling, exactly the
symmetric-lever input of `MovingCoherenceDatum.ofSphereSheetSystemCanon`.

The empty fallback at branch values is harmless: the branch-value crux of
`residueSum_eq_zero_of_globalCoverData` is handled by the **bundle trace SUM** (`αBr`, the
monodromy-free symmetric extension), not by `Φ` at the branch value; the canonical-fibre conditions
`hΦrangeReg`/`hΦinjReg` are required only *near regular values* (off `cs ∪ branchValues f`), where `Φ`
*is* the full fibre. -/

/-- **The good-value predicate.**  `b` is *good* when `coe b` is off the branch locus of `F =
f.toRiemannSphere` and `g`'s chart pullback is meromorphic at every full-fibre point over `coe b`.  At
good values the canonical selection enumerates the full fibre as a regular non-pole family. -/
def GoodValue (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) :
    Prop :=
  (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere ∧
  ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
    ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))

/-- **The canonical full-fibre selection.**  `Φ b` is the full-fibre datum at good values and the empty
datum elsewhere. -/
noncomputable def canonicalFibreSelection (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) : (b : ℂ) → FibreRegularData g f b :=
  fun b => if h : GoodValue g f hdiv b then FibreRegularData.ofFullFibre f hdiv b h.1 h.2
    else emptyFibreRegularData g f b

/-- At a **good value**, the canonical selection *is* the full-fibre datum. -/
theorem canonicalFibreSelection_eq_ofFullFibre (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    canonicalFibreSelection g f hdiv b = FibreRegularData.ofFullFibre f hdiv b h.1 h.2 := by
  rw [canonicalFibreSelection, dif_pos h]

/-- At a **good value**, the canonical selection's fibre points are `fullFibreEnum` — so the underlying
fibre-point map has **range exactly the full fibre** `F⁻¹(coe b)`. -/
theorem canonicalFibreSelection_xs_range (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    Set.range (canonicalFibreSelection g f hdiv b).xs
      = f.toRiemannSphere ⁻¹' {(((b : ℂ) : RiemannSphere))} := by
  rw [canonicalFibreSelection_eq_ofFullFibre g f hdiv h]
  -- `(ofFullFibre …).xs = fullFibreEnum …` definitionally; `fullFibreEnum`'s range is the fibre.
  exact fullFibreEnum_range f hdiv b

/-- At a **good value**, the canonical selection's fibre points are **injective**. -/
theorem canonicalFibreSelection_xs_injective (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    Function.Injective (canonicalFibreSelection g f hdiv b).xs := by
  rw [canonicalFibreSelection_eq_ofFullFibre g f hdiv h]
  exact fullFibreEnum_injective f hdiv b

/-! ### Off-branch good-value neighbourhoods

A value `z` with `coe z ∉ branchLocus` has a whole neighbourhood of values `b'` with `coe b' ∉
branchLocus`: the branch locus is closed (finite, for a nonconstant `f`), so its complement is open,
and `coe` is continuous.  This is the first half of the good-value condition near a regular value. -/

/-- **Off-branch is an open condition (finite-value side).**  If `coe z ∉ branchLocus
f.toRiemannSphere`, then `coe b' ∉ branchLocus f.toRiemannSphere` for all `b'` near `z`. -/
theorem eventually_notMem_branchLocus (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) :
    ∀ᶠ b' in 𝓝 z, (((b' : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := by
  -- The branch locus is closed (finite), so its complement is open and `coe ⁻¹' (branchLocusᶜ)` is a
  -- neighbourhood of `z` (continuity of `coe`, `z` in it).
  have hfin : (branchLocus f.toRiemannSphere).Finite :=
    finite_branchLocus_of_nonconstant f.toRiemannSphere f.contMDiff_toRiemannSphere
      (hncF_of_div_ne_zero f hdiv)
  have hopen : IsOpen ((branchLocus f.toRiemannSphere)ᶜ) := hfin.isClosed.isOpen_compl
  have hmem : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' (branchLocus f.toRiemannSphere)ᶜ)
      ∈ 𝓝 z :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (hopen.mem_nhds hz)
  filter_upwards [hmem] with b' hb' using hb'

/-! ### The canonical-fibre conditions `hΦrangeReg` / `hΦinjReg`

At a regular value `z` (off the finite branch values), the canonical selection enumerates the full
fibre `F⁻¹(coe b')` for every `b'` near `z` — *provided* `g`'s chart pullback is meromorphic at the
fibre points there (the standard regular-value `g`-data, the only datum-dependent input).  This gives
both `hΦrangeReg` (the range is the fibre) and `hΦinjReg` (the enumeration is injective) — the two
canonical-fibre conditions of `residueSum_eq_zero_of_globalCoverData`. -/

/-- **`hΦrangeReg` for the canonical selection.**  At a value `z` off the branch values (`coe z ∉
branchLocus`), the canonical full-fibre selection enumerates the **full fibre** `F⁻¹(coe b')` for `b'`
near `z`, given the regular-value `g`-meromorphy `hgmero` (`g`'s chart pullback meromorphic at the
full-fibre points, eventually near `z`).  Off-branch is an open condition (`eventually_notMem_branchLocus`)
so each such `b'` is a *good value*, where the canonical selection is the full-fibre datum. -/
theorem canonicalFibreSelection_hΦrangeReg (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hgmero : ∀ᶠ b' in 𝓝 z, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    ∀ᶠ b' in 𝓝 z, Set.range (canonicalFibreSelection g f hdiv b').xs
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} := by
  filter_upwards [eventually_notMem_branchLocus f hdiv hz, hgmero] with b' hb'off hb'mero
  exact canonicalFibreSelection_xs_range g f hdiv ⟨hb'off, hb'mero⟩

/-- **`hΦinjReg` for the canonical selection.**  At a value `z` off the branch values, the canonical
full-fibre selection's fibre points are **injective** for `b'` near `z`, given the regular-value
`g`-meromorphy `hgmero`.  (Same good-value neighbourhood as `hΦrangeReg`.) -/
theorem canonicalFibreSelection_hΦinjReg (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hgmero : ∀ᶠ b' in 𝓝 z, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    ∀ᶠ b' in 𝓝 z, Function.Injective (canonicalFibreSelection g f hdiv b').xs := by
  filter_upwards [eventually_notMem_branchLocus f hdiv hz, hgmero] with b' hb'off hb'mero
  exact canonicalFibreSelection_xs_injective g f hdiv ⟨hb'off, hb'mero⟩

/-! ### The per-pole moving sections from the sphere sheet system

At a finite pole-value `cs i` (a regular value of `f` by the adapted cover), the sphere sheet system
`S_i` at `coe(cs i)` (`exists_sphereSheetSystem`) supplies the moving sections that enumerate the full
fibre.  For the per-pole field `secFin`/`hselFin` of `residueSum_eq_zero_of_globalCoverData` the moving
sections are indexed by the **pole sub-fibre** `(fibreReg hac (cs i)).ι`: `secFin i j` is the sphere
sheet passing through the `j`-th pole `(fibreReg hac (cs i)).xs j` at the base.

Since each pole over `cs i` is a fibre point and the sheets sweep the full fibre, there is a (unique)
sheet through each pole — we extract its index by `sheetIndexOf`.  The re-selection bijection `hselFin`
then follows from the **symmetric lever** once the moving fibre `Φ b' = full fibre` and the section
range agree as sets — which is the *separation condition* (full fibre over `cs i` = pole sub-fibre). -/

/-- **The sheet index through a fibre point.**  For a `LocalSheetSystem S` of `F = f.toRiemannSphere`
at `coe b₀`, and a point `x` in the fibre `F⁻¹(coe b₀)`, the sheet index `i` with `S.sheet i (coe b₀) =
x` (the sheets sweep the fibre, `fibre_eq`). -/
noncomputable def sheetIndexOf {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) : Fin S.n := by
  have hmem : x ∈ f.toRiemannSphere ⁻¹' {(((b₀ : ℂ) : RiemannSphere))} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hx
  rw [S.fibre_eq _ S.mem_V] at hmem
  exact hmem.choose

/-- The sheet at `sheetIndexOf S hx` passes through `x` at the base. -/
theorem sheet_sheetIndexOf {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) :
    S.sheet (sheetIndexOf S hx) (((b₀ : ℂ) : RiemannSphere)) = x := by
  have hmem : x ∈ f.toRiemannSphere ⁻¹' {(((b₀ : ℂ) : RiemannSphere))} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hx
  rw [S.fibre_eq _ S.mem_V] at hmem
  exact hmem.choose_spec

/-- **`sheetIndexOf` inverts the sheet map at the base.**  For `x = S.sheet k (coe b₀)`, the recovered
index `sheetIndexOf S hx` is `k` — the sheets are injective in the index at the base (`sheet_inj`), so
the index hitting `S.sheet k (coe b₀)` is `k` itself.  (`σ` is a section of `k ↦ S.sheet k (coe b₀)`.) -/
theorem sheetIndexOf_sheet {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) (k : Fin S.n)
    (hk : f.toRiemannSphere (S.sheet k (((b₀ : ℂ) : RiemannSphere)))
      = (((b₀ : ℂ) : RiemannSphere))) :
    sheetIndexOf S hk = k := by
  -- Both `sheetIndexOf S hk` and `k` are sheet indices hitting `S.sheet k (coe b₀)`; sheets are
  -- injective in the index at the base, so the indices coincide.
  apply S.sheet_inj (((b₀ : ℂ) : RiemannSphere)) S.mem_V
  show S.sheet (sheetIndexOf S hk) (((b₀ : ℂ) : RiemannSphere))
    = S.sheet k (((b₀ : ℂ) : RiemannSphere))
  exact sheet_sheetIndexOf S hk

/-- **The per-pole moving section through the `j`-th pole.**  Given a sphere sheet system `S` at `coe
b₀` and a pole `x` in the fibre `F⁻¹(coe b₀)`, the moving section `b' ↦ S.sheet (sheetIndexOf S hx)
(coe b')` of `f.holoRepr` through `x` at the base.  This is `holoReprSheet S (sheetIndexOf S hx)`,
smooth and a section of `f.holoRepr` near `b₀` (the translation lemmas of `FormTraceSphereSheetTranslate`). -/
noncomputable def poleMovingSection {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) : ℂ → X :=
  S.holoReprSheet (sheetIndexOf S hx)

/-- `poleMovingSection` passes through the pole `x` at the base. -/
theorem poleMovingSection_base {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) :
    poleMovingSection S hx b₀ = x := by
  rw [poleMovingSection, S.holoReprSheet_base]; exact sheet_sheetIndexOf S hx

/-- `poleMovingSection` is `C^ω` at the base. -/
theorem poleMovingSection_contMDiffAt {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (poleMovingSection S hx) b₀ :=
  S.holoReprSheet_contMDiffAt (sheetIndexOf S hx)

/-- `poleMovingSection` is a section of `f.holoRepr` near the base. -/
theorem poleMovingSection_section {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) :
    ∀ᶠ b' in 𝓝 b₀, f.holoRepr (poleMovingSection S hx b') = b' :=
  S.holoReprSheet_section (sheetIndexOf S hx)

/-- `poleMovingSection S hx b'` has sphere value `coe b'` near `b₀` (its `holoRepr` is `b'`, a
non-pole), i.e. it lies in the fibre `F⁻¹(coe b')`. -/
theorem poleMovingSection_mem_fibre {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {x : X}
    (hx : f.toRiemannSphere x = (((b₀ : ℂ) : RiemannSphere))) :
    poleMovingSection S hx = (fun b' => S.sheet (sheetIndexOf S hx) (((b' : ℂ) : RiemannSphere))) :=
  rfl

/-! ### The separation at a pole-value: pole sub-fibre = full fibre

The per-pole field `secFin`/`hselFin` of `residueSum_eq_zero_of_globalCoverData` glues the moving
sections (indexed by the **pole sub-fibre** `fibreReg hac (cs i)`) to the moving fibre `Φ b'` (the
**full** fibre), via a bijection `(Φ b').ι ≃ (fibreReg hac (cs i)).ι`.  This requires the pole
sub-fibre over `cs i` to be the *whole* fibre — the **separation condition**: every point of
`F⁻¹(coe cs_i)` is a pole of `α`.

This is the repo's honest pole/regular separation (the Gate-D refinement of the global selection;
cf. the soundness note in `FormTraceGlobalGeometric`): with a full-fibre `Φ`, the finite glue
germ-equals the pole sub-fibre trace *iff* the cover separates the poles from the regular fibre points
over each pole-value — and a full-fibre selection forces the strong form (full fibre = poles). -/

/-- **The pole-value separation condition.**  At the finite pole-value `c`, every point of the fibre
`F⁻¹(coe c)` is a pole of `α` (`x ∈ poles`).  Equivalently, the pole sub-fibre over `c` is the whole
fibre.  This is the Gate-D separation that makes the per-pole moving sections enumerate the full fibre. -/
def PoleValueSeparated (f : MeromorphicFunction X) (poles : Finset X) (c : ℂ) : Prop :=
  ∀ x, f.toRiemannSphere x = (((c : ℂ) : RiemannSphere)) → x ∈ poles

/-- **`sheetIndexOf` of the poles is surjective under separation.**  At a separated pole-value `coe b₀`
(every fibre point a pole), the indices `sheetIndexOf S (h : pole in fibre)` ranging over the poles
`poleFibre f poles b₀` hit **every** sheet index: each `S.sheet k (coe b₀)` is a fibre point, hence a
pole, hence equal to some `poleFibre`-point whose recovered index is `k` (`sheetIndexOf_sheet`). -/
theorem sheetIndexOf_pole_surjective {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere)))
    (poles : Finset X) (hsep : PoleValueSeparated f poles b₀) (k : Fin S.n) :
    ∃ x : poleFibre f poles b₀,
      sheetIndexOf S (x := (x : X)) (mem_poleFibre.mp x.2).2 = k := by
  -- `S.sheet k (coe b₀)` is a fibre point over `coe b₀`, hence a pole (separation), hence a member of
  -- `poleFibre f poles b₀`; its recovered index is `k` by `sheetIndexOf_sheet`.
  have hfib : f.toRiemannSphere (S.sheet k (((b₀ : ℂ) : RiemannSphere)))
      = (((b₀ : ℂ) : RiemannSphere)) := S.sheet_section k _ S.mem_V
  have hpole : S.sheet k (((b₀ : ℂ) : RiemannSphere)) ∈ poles := hsep _ hfib
  refine ⟨⟨S.sheet k (((b₀ : ℂ) : RiemannSphere)), mem_poleFibre.mpr ⟨hpole, hfib⟩⟩, ?_⟩
  exact sheetIndexOf_sheet S k hfib

/-! ### The per-pole moving sections and the set-form re-selection

We now assemble the per-pole field for the canonical full-fibre selection at a separated off-branch
pole-value `cs i`.  The moving sections are `secFin j := poleMovingSection S (j-th pole in fibre)`; the
re-selection `hselFin` follows from the **symmetric lever** (`equivOfInjective_image_eq`) once the
moving fibre `Φ b' = full fibre` and the section values enumerate the *same* set near `cs i`. -/

variable {poles : Finset X}

/-- The sheet-index of the `j`-th pole in the fibre over a pole-value `p`, for a sphere sheet system
`S` at `coe p`. -/
noncomputable def poleSheetIndex (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) : Fin S.n :=
  sheetIndexOf S (x := (fibreReg hac p).xs j) (fibreReg_hxs_mem hac p j).2

/-- **The pole sheet-index map is surjective under separation.**  Over a separated pole-value `p`,
every sheet index `k` is `poleSheetIndex` of some pole `j`: `S.sheet k (coe p)` is a fibre point,
hence a pole (separation), hence equal to `(fibreReg hac p).xs j` for some `j` (`fibreReg_hxs_surj`);
the recovered index of that pole is `k` (`sheetIndexOf_sheet`, via proof-irrelevance of the fibre
witness). -/
theorem poleSheetIndex_surjective (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (hsep : PoleValueSeparated f poles p) :
    Function.Surjective (poleSheetIndex hac S) := by
  intro k
  -- `S.sheet k (coe p)` is a fibre point over `coe p`, hence a pole, hence a `fibreReg`-point.
  have hfib : f.toRiemannSphere (S.sheet k (((p : ℂ) : RiemannSphere)))
      = (((p : ℂ) : RiemannSphere)) := S.sheet_section k _ S.mem_V
  have hpole : S.sheet k (((p : ℂ) : RiemannSphere)) ∈ poles := hsep _ hfib
  obtain ⟨j, hj⟩ := fibreReg_hxs_surj hac p _ hpole hfib
  refine ⟨j, ?_⟩
  -- `poleSheetIndex hac S j = sheetIndexOf S (…)`; the index depends only on the point `(fibreReg).xs
  -- j = S.sheet k (coe p)` (proof-irrelevant witness), so it is `k` by `sheetIndexOf_sheet`.
  show sheetIndexOf S (x := (fibreReg hac p).xs j) (fibreReg_hxs_mem hac p j).2 = k
  rw [show sheetIndexOf S (x := (fibreReg hac p).xs j) (fibreReg_hxs_mem hac p j).2
      = sheetIndexOf S (x := S.sheet k (((p : ℂ) : RiemannSphere))) hfib from by
    congr 1 <;> rw [hj]]
  rw [sheetIndexOf_sheet S k hfib]

/-- **The per-pole moving sections.**  For a pole-value `p` with sphere sheet system `S`, the moving
section through the `j`-th pole: `secFin j := poleMovingSection S (…)`. -/
noncomputable def poleSecFin (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) : ℂ → X :=
  poleMovingSection S (x := (fibreReg hac p).xs j) (fibreReg_hxs_mem hac p j).2

@[simp] theorem poleSecFin_eq (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) (b' : ℂ) :
    poleSecFin hac S j b' = S.sheet (poleSheetIndex hac S j) (((b' : ℂ) : RiemannSphere)) := rfl

/-- `poleSecFin` passes through the `j`-th pole at the base. -/
theorem poleSecFin_base (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) :
    poleSecFin hac S j p = (fibreReg hac p).xs j :=
  poleMovingSection_base S (fibreReg_hxs_mem hac p j).2

/-- `poleSecFin` is `C^ω` at the base. -/
theorem poleSecFin_contMDiffAt (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (poleSecFin hac S j) p :=
  poleMovingSection_contMDiffAt S (fibreReg_hxs_mem hac p j).2

/-- `poleSecFin` is a section of `f.holoRepr` near the base. -/
theorem poleSecFin_section (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (j : (fibreReg hac p).ι) :
    ∀ᶠ b' in 𝓝 p, f.holoRepr (poleSecFin hac S j b') = b' :=
  poleMovingSection_section S (fibreReg_hxs_mem hac p j).2

/-- **The per-pole section values enumerate the full fibre (under separation).**  At a separated
pole-value `p`, the section values `j ↦ poleSecFin hac S j b'` enumerate the **full** fibre `F⁻¹(coe
b')` for `b'` with `coe b' ∈ S.V`: their range is the image of the *surjective* index map
`poleSheetIndex hac S` under `k ↦ S.sheet k (coe b')`, i.e. the full sheet-value range
(`sheetValues_range_eq_fibre`). -/
theorem poleSecFin_range_eq_fibre (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere)))
    (hsep : PoleValueSeparated f poles p) {b' : ℂ}
    (hb' : (((b' : ℂ) : RiemannSphere)) ∈ S.V) :
    Set.range (fun j => poleSecFin hac S j b')
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} := by
  -- `poleSecFin hac S j b' = S.sheet (poleSheetIndex hac S j) (coe b')`, so the range is the image of
  -- `range (poleSheetIndex hac S) = univ` (surjective) under `k ↦ S.sheet k (coe b')`.
  have hcomp : (fun j => poleSecFin hac S j b')
      = (fun k => S.sheet k (((b' : ℂ) : RiemannSphere))) ∘ (poleSheetIndex hac S) := by
    funext j; rw [poleSecFin_eq]; rfl
  rw [hcomp, Set.range_comp, (poleSheetIndex_surjective hac S hsep).range_eq, Set.image_univ]
  exact sheetValues_range_eq_fibre S hb'

/-- **The pole sheet-index map is injective.**  `poleSheetIndex hac S j` recovers the sheet index
through the `j`-th pole, so distinct poles give distinct indices (`fibreReg`-points injective +
`sheet_sheetIndexOf`). -/
theorem poleSheetIndex_injective (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere))) :
    Function.Injective (poleSheetIndex hac S) := by
  intro j₁ j₂ h
  -- `(fibreReg).xs j = S.sheet (poleSheetIndex hac S j) (coe p)` (`sheet_sheetIndexOf`); equal indices
  -- give equal poles, hence equal `j` (`fibreReg`-points injective).
  apply fibreReg_hxs_inj hac p
  have e₁ : S.sheet (poleSheetIndex hac S j₁) (((p : ℂ) : RiemannSphere)) = (fibreReg hac p).xs j₁ :=
    sheet_sheetIndexOf S (fibreReg_hxs_mem hac p j₁).2
  have e₂ : S.sheet (poleSheetIndex hac S j₂) (((p : ℂ) : RiemannSphere)) = (fibreReg hac p).xs j₂ :=
    sheet_sheetIndexOf S (fibreReg_hxs_mem hac p j₂).2
  rw [← e₁, ← e₂, h]

/-- **The per-pole section values are injective (under separation, near the base).**  For `b'` with
`coe b' ∈ S.V`, `j ↦ poleSecFin hac S j b'` is injective: it is `poleSheetIndex hac S` (injective)
followed by `k ↦ S.sheet k (coe b')` (injective on `S.V`, `sheet_inj`). -/
theorem poleSecFin_injective (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere))) {b' : ℂ}
    (hb' : (((b' : ℂ) : RiemannSphere)) ∈ S.V) :
    Function.Injective (fun j => poleSecFin hac S j b') := by
  intro j₁ j₂ h
  simp only [poleSecFin_eq] at h
  exact poleSheetIndex_injective hac S (S.sheet_inj _ hb' h)

/-- **Each per-pole section stays in the matching chart source near the base.**  `poleSecFin hac S j`
is continuous at `p` (`poleSecFin_contMDiffAt`) with value `(fibreReg hac p).xs j` (the base, by
`poleSecFin_base`), so it eventually lies in the open chart source of that fibre point. -/
theorem poleSecFin_eventually_mem_source (hac : AdaptedCover ω₀ g f poles) {p : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((p : ℂ) : RiemannSphere))) :
    ∀ᶠ b' in 𝓝 p, ∀ j, poleSecFin hac S j b' ∈ (chartAt ℂ ((fibreReg hac p).xs j)).source := by
  rw [eventually_all]
  intro j
  have hcont : ContinuousAt (poleSecFin hac S j) p := (poleSecFin_contMDiffAt hac S j).continuousAt
  have hbase : poleSecFin hac S j p = (fibreReg hac p).xs j := poleSecFin_base hac S j
  have hsrc : (chartAt ℂ ((fibreReg hac p).xs j)).source ∈ 𝓝 ((fibreReg hac p).xs j) :=
    (chartAt ℂ ((fibreReg hac p).xs j)).open_source.mem_nhds (mem_chart_source ℂ _)
  have := hcont.preimage_mem_nhds (by rw [hbase]; exact hsrc)
  filter_upwards [this] with b' hb' using hb'

/-! ### The per-pole set-form re-selection `hselFin`

The capstone of the per-pole field: at a separated off-branch pole-value `cs i`, the canonical
full-fibre selection `Φ` satisfies the §VIII.3 re-selection `hselFin` of
`residueSum_eq_zero_of_globalCoverData`.  The per-`b'` bijection `e : (Φ b').ι ≃ (fibreReg hac (cs
i)).ι` is reconstructed *pointwise* by the **symmetric lever** (`equivOfInjective_image_eq`) from the
set-equality `range (Φ b').xs = range (poleSecFin · b')` — both equal the full fibre `F⁻¹(coe b')`
(`canonicalFibreSelection_xs_range` and `poleSecFin_range_eq_fibre`, the latter using separation).  No
labeling. -/

/-- **`hselFin` for the canonical selection at a pole-value.**  At a finite pole-value `cs_i` that is
off the branch locus and **separated** (every fibre point a pole), with a sphere sheet system `S` at
`coe cs_i` and the regular-value `g`-meromorphy `hgmero` near `cs_i`, the canonical full-fibre
selection satisfies the per-pole re-selection: near `cs_i`, there is a value-matching bijection between
the full fibre `Φ b'` and the pole sub-fibre's moving sections `poleSecFin hac S · b'`, each section in
the matching chart source.  The bijection is the symmetric lever's pointwise reconstruction from
range-equality (both ranges are the full fibre). -/
theorem canonicalFibreSelection_hselFin (hac : AdaptedCover ω₀ g f poles)
    (hdiv : (f.div : Divisor X) ≠ 0) {cs_i : ℂ}
    (hoff : (((cs_i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hsep : PoleValueSeparated f poles cs_i)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((cs_i : ℂ) : RiemannSphere)))
    (hgmero : ∀ᶠ b' in 𝓝 cs_i, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    ∀ᶠ b' in 𝓝 cs_i, ∃ e : (canonicalFibreSelection g f hdiv b').ι ≃ (fibreReg hac cs_i).ι,
      (∀ i', (canonicalFibreSelection g f hdiv b').xs i' = poleSecFin hac S (e i') b') ∧
      (∀ j, poleSecFin hac S j b' ∈ (chartAt ℂ ((fibreReg hac cs_i).xs j)).source) := by
  -- The finite-value preimage of `S.V` is a neighbourhood of `cs_i` (continuity of `coe`).
  have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 cs_i :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)
  filter_upwards [eventually_notMem_branchLocus f hdiv hoff, hgmero, hVnhds,
    poleSecFin_eventually_mem_source hac S] with b' hb'off hb'mero hb'V hb'mem
  -- `b'` is a good value, so `Φ b'` injectively enumerates the full fibre.
  have hgood : GoodValue g f hdiv b' := ⟨hb'off, hb'mero⟩
  have hΦinj : Function.Injective (canonicalFibreSelection g f hdiv b').xs :=
    canonicalFibreSelection_xs_injective g f hdiv hgood
  have hΦrange : Set.range (canonicalFibreSelection g f hdiv b').xs
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} :=
    canonicalFibreSelection_xs_range g f hdiv hgood
  -- The section values are injective and enumerate the same fibre.
  have hsecinj : Function.Injective (fun j => poleSecFin hac S j b') :=
    poleSecFin_injective hac S hb'V
  have hsecrange : Set.range (fun j => poleSecFin hac S j b')
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} :=
    poleSecFin_range_eq_fibre hac S hsep hb'V
  -- The symmetric lever: a value-matching bijection from equal ranges.
  obtain ⟨e, he⟩ := equivOfInjective_image_eq hΦinj hsecinj (by rw [hΦrange, hsecrange])
  exact ⟨e, fun i' => he i', hb'mem⟩

/-! ### Wall 2 eliminated: Gate A `∑Res = 0` with the canonical full-fibre selection

The capstone.  Wiring the canonical full-fibre selection `Φ := canonicalFibreSelection` and its
discharged fields (`hΦrangeReg`/`hΦinjReg` from `canonicalFibreSelection_hΦrangeReg`/`_hΦinjReg`; the
per-pole `secFin := poleSecFin hac (S i)` with `hselFin` from `canonicalFibreSelection_hselFin`) into
`residueSum_eq_zero_of_globalCoverData`, **wall 2 is eliminated**: the global coherent selection and its
moving coherence are *constructed*, monodromy-free (the symmetric lever).

What remains are exactly:

* **Wall 1** — the adapted-cover genericity packaged here as: the finite pole-value data, each
  pole-value off the branch locus (`hcsoff`) and **separated** (`hsep`: its whole fibre is poles), plus
  the regular-value `g`-data (`hgmero` at the full-fibre points, `hmeroReg`/`hCreg_g` at the sphere
  sheets);
* **Wall 3** — the `∞`-rationality bookkeeping (`Dinf`/`hxs_*`/`αBr`/`hαBrAgreeBr`/`hglue_inf`/
  `hcont_int`/`R₀`/`hR₀_*`), handled separately.

The separation `hsep` is the Gate-D pole/regular separation the repo's own soundness note isolates: a
full-fibre selection germ-coheres to the pole sub-fibre trace at a pole-value iff that value's fibre is
entirely poles. -/

/-- **Gate A `∑Res = 0`, wall 2 eliminated by the canonical full-fibre selection.**  With `Φ` the
canonical full-fibre selection, all of `residueSum_eq_zero_of_globalCoverData`'s Φ-fields — the
selection, the regular-value canonical-fibre conditions `hΦrangeReg`/`hΦinjReg`, and the per-pole
moving sections `secFin`/`hselFin` — are discharged from the construction (the symmetric lever, no
labeling).  The hypotheses are the wall-1 genericity (finite pole-value data, off-branch + separated
pole-values, regular-value `g`-data) and the wall-3 `∞`-bookkeeping. -/
theorem residueSum_eq_zero_of_canonicalSelection (hdiv : (f.div : Divisor X) ≠ 0)
    (hac : AdaptedCover ω₀ g f poles)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    -- Wall-1 genericity for the canonical selection: pole-values off-branch + separated.
    (hcsoff : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hsep : ∀ i, PoleValueSeparated f poles (cs i))
    -- The regular-value `g`-meromorphy at the full-fibre points (the only datum-dependent Φ-input).
    (hgmero : ∀ z, (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere →
      ∀ᶠ b' in 𝓝 z, ∀ i, MeromorphicAt
        (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i)))
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      AnalyticAt ℂ
        (fun w => g ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (αBr : ℂ → HolomorphicOneForms X)
    (hαBrAgreeBr : ∀ b₀ ∈ branchValues f hdiv, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀, ∀ (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
        (αBr b₀).toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
          = g ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
    (hglue_inf : recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv)
        (branchValues f hdiv))
      =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) (branchValues f hdiv) - L.R)
          =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv)
          (branchValues f hdiv) - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv)
        (branchValues f hdiv) - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  classical
  -- A sphere sheet system at each (off-branch) pole-value `cs i` (`exists_sphereSheetSystem` gives
  -- `Nonempty`; pick one with `.some`).
  have hnc : ∃ x, f.orderAtPoint x ≠ 0 := exists_orderAtPoint_ne_zero f hdiv
  set S : ∀ i, Jacobians.LocalSheetSystem f.toRiemannSphere (((cs i : ℂ) : RiemannSphere)) :=
    fun i => (exists_sphereSheetSystem f hnc (hcsoff i)).some with hS
  refine residueSum_eq_zero_of_globalCoverData hdiv hac (canonicalFibreSelection g f hdiv)
    m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj hxs_mem hxs_surj
    (fun i => poleSecFin hac (S i)) (fun i j => poleSecFin_base hac (S i) j)
    (fun i j => poleSecFin_contMDiffAt hac (S i) j)
    (fun i j => poleSecFin_section hac (S i) j) ?_ hmeroReg ?_ ?_ hCreg_g αBr hαBrAgreeBr
    hglue_inf hcont_int R₀ hR₀_an hR₀0 hR₀_eq
  · -- `hselFin`: the per-pole re-selection, from `canonicalFibreSelection_hselFin`.
    intro i
    exact canonicalFibreSelection_hselFin hac hdiv (hcsoff i) (hsep i) (S i)
      (hgmero (cs i) (hcsoff i))
  · -- `hΦinjReg`: at a regular value `z` off `cs ∪ branchValues`, `coe z ∉ branchLocus`.
    intro z hz
    exact canonicalFibreSelection_hΦinjReg g f hdiv
      (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => hz (Finset.mem_union_right _ h)))
      (hgmero z (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => hz (Finset.mem_union_right _ h))))
  · -- `hΦrangeReg`: same off-branch witness.
    intro z hz
    exact canonicalFibreSelection_hΦrangeReg g f hdiv
      (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => hz (Finset.mem_union_right _ h)))
      (hgmero z (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => hz (Finset.mem_union_right _ h))))

/-! ### Non-vacuity of the canonical-selection Φ-fields (soundness)

The Φ-field obligations are genuine — *not* a disguised `False`.  The datum-dependent `g`-meromorphy
input `hgmero` is satisfied for the zero numerator `g = 0` (the constantly-`0` chart pullback is
analytic, hence meromorphic) at every value off the branch locus.  This confirms the regular-value
canonical-fibre conditions are honestly satisfiable. -/

/-- **The `g`-meromorphy input holds for `g = 0`.**  With the zero numerator, the chart pullback of
`g` at every full-fibre point is the constant `0`, which is analytic, hence meromorphic — so `hgmero`
holds (eventually, indeed everywhere) near every value.  Honest non-vacuity of the regular-value
`g`-data. -/
theorem hgmero_zero (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (z : ℂ) :
    ∀ᶠ b' in 𝓝 z, ∀ i, MeromorphicAt
      (fun w => (0 : X → ℂ) ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
      ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i)) := by
  filter_upwards with b' i
  exact (analyticAt_const (v := (0 : ℂ))).meromorphicAt

/-- **The regular-value canonical-fibre conditions are non-vacuous.**  At any value `z` off the branch
locus, the canonical full-fibre selection for the zero numerator `g = 0` enumerates the full fibre near
`z` (`hΦrangeReg` with injectivity) — a concrete satisfiable instance, confirming the Φ-fields are not
disguised `False`. -/
theorem canonicalFibreSelection_hΦrangeReg_nonvacuous (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) :
    ∀ᶠ b' in 𝓝 z, Set.range (canonicalFibreSelection (0 : X → ℂ) f hdiv b').xs
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} :=
  canonicalFibreSelection_hΦrangeReg (0 : X → ℂ) f hdiv hz (hgmero_zero f hdiv z)

end Jacobians.Dolbeault.FormTraceGlobal
