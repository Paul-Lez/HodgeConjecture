/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSetSelection
import KirovDolbeault.Dolbeault.FormTraceSphereSheetTranslate

/-!
# The set-form re-selection from a sphere sheet system + canonical fibre (Gate A, §VIII.3)

`Jacobians.Dolbeault.FormTraceMovingFibreSetSelection` reduced Gate A's `∑Res = 0` to a
`MovingSheetSelectionSet`, whose per-value re-selection is the **labeling-independent set form**
`hsetFin`/`hsetReg`: near each base value `b₀`, the moving fibre `Φ b'` and the section values
`fun i => sec i b'` are both injective with the *same image* (no sheet ordering).

This file discharges that set-form re-selection at a **regular (non-branch) value** from the proved
sphere sheet machinery, using the **symmetric-invariance lever** in its purest form: the sheet values
`b' ↦ S.sheet i (coe b')` sweep out the *entire fibre* `F⁻¹(coe b')` (`LocalSheetSystem.fibre_eq`), so
the only `Φ`-hypothesis is that the re-selected fibre `Φ b'` **also enumerates that same fibre as a
set** (the *canonical-fibre* condition) — never a labeling.  The two then have equal range automatically,
and `MovingCoherenceDatum.ofSheetSectionsSet` (the lever) reconstructs the per-`b'` bijection pointwise.

Concretely, at a finite regular value `coe b₀` off the branch locus:
* the moving sections are the translated sheets `holoReprSheet S i = (b' ↦ S.sheet i (coe b'))` of
  `Jacobians.exists_sphereSheetSystem` (smooth + sections of `f.holoRepr`, proved in
  `FormTraceSphereSheetTranslate`);
* their values over `b'` enumerate `F⁻¹(coe b')` *as a set* (`fibreValues_eq_sheetRange`, from
  `S.fibre_eq` translated to `f.holoRepr` via `coe`);
* the caller supplies only the **canonical-fibre re-selection** `hcanon`: near `b₀`, `(Φ b').xs` is an
  injective enumeration of `F⁻¹(coe b')` whose values are non-poles — i.e. `Φ b'` *is the fibre*, with
  no sheet labeling.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `sheetValues_range_eq_fibre` — the sheet values over `b'` enumerate the full sphere fibre
  `F⁻¹(coe b')` (`LocalSheetSystem.fibre_eq` for `f.toRiemannSphere`, read at `coe b'`).
* `MovingCoherenceDatum.ofSphereSheetSystemSet` — a `MovingCoherenceDatum` at `b₀` from a sphere sheet
  system at `coe b₀`, with the *canonical-fibre* re-selection (the moving fibre enumerates the sphere
  fibre as a set) — the symmetric lever, no labeling.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; single-valued
  **by symmetry**).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The sheet values enumerate the full fibre (the symmetric lever's geometric input)

`LocalSheetSystem.fibre_eq` says the sheet map sweeps the entire fibre `F⁻¹(coe b')` of the compact
sphere map `F = f.toRiemannSphere`.  Translated to the moving `holoReprSheet` sections, this says the
section values `fun i => S.sheet i (coe b') = holoReprSheet S i b'` enumerate `F⁻¹(coe b')` as a set, for
`b'` in the finite-value preimage of `S.V`.  This is the geometric fact that makes the canonical-fibre
re-selection automatic. -/

/-- **The sheet values enumerate the sphere fibre.**  For a `LocalSheetSystem S` of the sphere map
`F = f.toRiemannSphere` at `coe b₀`, and `b'` with `coe b' ∈ S.V`, the sheet values `fun i => S.sheet i
(coe b')` have range exactly the fibre `F⁻¹({coe b'})`:

> `Set.range (fun i => S.sheet i (coe b')) = f.toRiemannSphere ⁻¹' {coe b'}`. -/
theorem sheetValues_range_eq_fibre {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere))) {b' : ℂ}
    (hb' : (((b' : ℂ) : RiemannSphere)) ∈ S.V) :
    Set.range (fun i => S.sheet i (((b' : ℂ) : RiemannSphere)))
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} :=
  (S.fibre_eq (((b' : ℂ) : RiemannSphere)) hb').symm

/-! ### The set-form coherence datum from a sphere sheet system + canonical fibre

We feed the translated sheets into `MovingCoherenceDatum.ofSheetSectionsSet`.  The reference fibre is the
sheet fibre `FibreRegularData.ofSphereSheetSystem S …` (so `D.xs i = S.sheet i (coe b₀)`); the moving
sections are `holoReprSheet S i`.  The set-form hypothesis is the **canonical-fibre re-selection**: near
`b₀`, the re-selected fibre points `(Φ b').xs` are injective and enumerate exactly the sphere fibre
`F⁻¹(coe b')` (= the sheet-value range), with each `(Φ b').xs` value a non-pole.  No labeling. -/

/-- **A set-form moving-fibre coherence datum from a sphere sheet system + canonical fibre.**  Given a
`LocalSheetSystem S` for the compact sphere map `F = f.toRiemannSphere` at the finite base value
`coe b₀` (with the two regular-value residuals `hderiv`/`hmero` for the reference sheet fibre), the
moving sections are the translated sheets `holoReprSheet S i`.  The caller supplies the
**canonical-fibre re-selection** `hcanon`: near `b₀`,

> `(Φ b').xs` is injective, the sheet values `fun i => S.sheet i (coe b')` are injective, and the
> *range* of `(Φ b').xs` equals the range of the sheet values — i.e. the moving fibre `Φ b'` enumerates
> the *same fibre set* as the sheets — together with each sheet value lying in the matching chart source.

Then `Φ` has a `MovingCoherenceDatum` at `b₀`.  The per-`b'` index bijection is reconstructed *pointwise*
from set-equality by the symmetric lever (`MovingCoherenceDatum.ofSheetSectionsSet`); **no global
continuous sheet-labeling**. -/
noncomputable def MovingCoherenceDatum.ofSphereSheetSystemSet
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun z => f.holoRepr ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) (S.sheet i (((b₀ : ℂ) : RiemannSphere)))))
    (hcanon : ∀ᶠ b' in 𝓝 b₀,
      Function.Injective (Φ b').xs ∧
      Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))) ∧
      Set.range (Φ b').xs = Set.range (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))) ∧
      (∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).source)) :
    MovingCoherenceDatum ω₀ g f Φ b₀ :=
  MovingCoherenceDatum.ofSheetSectionsSet
    (FibreRegularData.ofSphereSheetSystem (g := g) S hderiv hmero)
    (fun i => S.holoReprSheet i)
    (fun _i => rfl)
    (fun i => S.holoReprSheet_contMDiffAt i)
    (fun i => S.holoReprSheet_section i)
    hcanon

/-! ### The canonical-fibre re-selection from "`Φ b'` is the full fibre"

The cleanest form of the canonical-fibre re-selection: if, near `b₀`, the re-selected fibre `Φ b'`
**injectively enumerates the entire sphere fibre** `F⁻¹(coe b')` (with values non-poles), then the
set-form hypothesis `hcanon` holds — because the sheet values *also* enumerate that fibre
(`sheetValues_range_eq_fibre`).  The two ranges are then equal *by transitivity through the fibre*, with
no labeling.  We package this as the constructor whose `Φ`-hypothesis is purely "the moving fibre is the
fibre", the genuine labeling-independent geometric content. -/

/-- **The canonical-fibre re-selection holds when `Φ b'` enumerates the full fibre.**  Suppose, near
`b₀`, the sphere sheet values are injective and stay in the matching chart sources, and `(Φ b').xs` is an
injective enumeration whose range is exactly the sphere fibre `F⁻¹(coe b')`.  Then the set-form
hypothesis `hcanon` of `MovingCoherenceDatum.ofSphereSheetSystemSet` holds: the two ranges agree because
both equal the fibre (`sheetValues_range_eq_fibre`).  This isolates the `Φ`-content to the
labeling-independent fact "`Φ b'` *is* the fibre as a set". -/
theorem canon_of_fibre_enumeration {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere)))
    (hΦinj : ∀ᶠ b' in 𝓝 b₀, Function.Injective (Φ b').xs)
    (hΦrange : ∀ᶠ b' in 𝓝 b₀,
      Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInj : ∀ᶠ b' in 𝓝 b₀,
      Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMem : ∀ᶠ b' in 𝓝 b₀, ∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).source) :
    ∀ᶠ b' in 𝓝 b₀,
      Function.Injective (Φ b').xs ∧
      Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))) ∧
      Set.range (Φ b').xs = Set.range (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))) ∧
      (∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).source) := by
  -- The finite-value preimage of `S.V` is a neighbourhood of `b₀` (continuity of `coe`).
  have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 b₀ :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)
  filter_upwards [hΦinj, hΦrange, hsheetInj, hsheetMem, hVnhds]
    with b' hinj hrange hsinj hmem hbV
  refine ⟨hinj, hsinj, ?_, hmem⟩
  -- Both ranges equal the fibre: `Φ`'s by hypothesis, the sheets' by `sheetValues_range_eq_fibre`.
  rw [hrange, ← sheetValues_range_eq_fibre S hbV]

end Jacobians.Dolbeault.FormTraceMovingFibre
