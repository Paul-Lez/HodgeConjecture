/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSphereSet

/-!
# The regular-value coherence engine for the canonical-fibre selection (Gate A, §VIII.3)

`Jacobians.Dolbeault.FormTraceMovingFibreSphereSet` built the two ingredients of the per-regular-value
moving-sheet coherence from a sphere sheet system, *with no labeling*:

* `MovingCoherenceDatum.ofSphereSheetSystemSet` — the moving datum at a finite base value `coe b₀`,
  given the **canonical-fibre re-selection** `hcanon` (near `b₀`, the moving fibre `Φ b'` enumerates the
  same fibre *set* as the sphere sheets) plus the two regular-value residuals `hderiv`/`hmero`;
* `canon_of_fibre_enumeration` — the canonical-fibre re-selection `hcanon` reduces to the
  labeling-independent fact "`Φ b'` *is* the fibre `F⁻¹(coe b')` as a set" (its range equals the fibre,
  both injective, sheets in their chart sources).

This file **chains those two** into the single regular-value engine `MovingCoherenceDatum.ofSphereSheetSystemCanon`:
a `MovingCoherenceDatum` at a regular value `b₀` whose *only* `Φ`-content is the canonical-fibre condition
"`(Φ b').xs` injectively enumerates the full fibre `F⁻¹(coe b')` near `b₀`", with the regularity reduced
to `hderiv`/`hmero` at the sphere-sheet fibre points and the sheet injectivity/chart-source data read off
the sheet system.  This is exactly the per-regular-value coherence datum
`BranchAwareTraceSelection.Creg` consumes — packaged so the eventual global-`Φ` builder supplies only the
canonical-fibre condition (piece (i)) and the off-branch regularity (piece (ii)).

The set-equality of the moving fibre and the sheet values is **automatic** once `Φ b'` is the canonical
fibre, because the sheet values *also* enumerate that fibre (`sheetValues_range_eq_fibre`): both ranges
equal `F⁻¹(coe b')`, with no labeling — the symmetric-invariance lever in its purest form.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MovingCoherenceDatum.ofSphereSheetSystemCanon` — the regular-value coherence datum from a sphere sheet
  system whose only `Φ`-input is the canonical-fibre condition (`Φ b'` is the fibre as a set near `b₀`),
  with the regularity residuals `hderiv`/`hmero` and the sheet-injectivity/chart-source data.

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

/-! ### The regular-value coherence datum from the canonical fibre

We feed `canon_of_fibre_enumeration` (the canonical-fibre re-selection, whose `Φ`-content is purely
"`Φ b'` *is* the fibre as a set") into `MovingCoherenceDatum.ofSphereSheetSystemSet` (the moving datum
from a sphere sheet system).  The caller supplies:

* `hderiv`/`hmero` — the off-branch regularity of the reference sheet fibre (piece (ii));
* `hΦinj`/`hΦrange` — the canonical-fibre condition (piece (i)): near `b₀`, `(Φ b').xs` is injective with
  range exactly `F⁻¹(coe b')`;
* `hsheetInj`/`hsheetMem` — the sphere sheets are injective and stay in the matching chart sources near
  `b₀` (read off the sheet system; both hold automatically near `b₀` by `S.sheet_inj` + continuity of the
  sheets into the chart sources, but are recorded explicitly so the engine is self-contained).

The set-equality of the moving fibre and the sheet values is *not* an input — it is reconstructed inside
from "both equal the fibre". -/

/-- **The regular-value coherence engine.**  A `MovingCoherenceDatum ω₀ g f Φ b₀` at a regular (finite)
value `coe b₀`, from a `LocalSheetSystem S` of the compact sphere map `F = f.toRiemannSphere`, whose only
`Φ`-content is the **canonical-fibre condition** (`hΦinj`/`hΦrange`: near `b₀`, the moving fibre `(Φ b').xs`
is an injective enumeration of the full fibre `F⁻¹(coe b')`).  The two regular-value residuals
`hderiv`/`hmero` (piece (ii)) and the sphere-sheet injectivity/chart-source data (`hsheetInj`/`hsheetMem`)
are supplied; the set-equality of the moving fibre and the sheet values is reconstructed *inside* from
`sheetValues_range_eq_fibre` (both ranges equal the fibre), with **no labeling**.  This is the
per-regular-value datum `BranchAwareTraceSelection.Creg` consumes, isolating its inputs to pieces (i)+(ii). -/
noncomputable def MovingCoherenceDatum.ofSphereSheetSystemCanon
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun z => f.holoRepr ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))) (S.sheet i (((b₀ : ℂ) : RiemannSphere)))))
    (hΦinj : ∀ᶠ b' in 𝓝 b₀, Function.Injective (Φ b').xs)
    (hΦrange : ∀ᶠ b' in 𝓝 b₀,
      Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hsheetInj : ∀ᶠ b' in 𝓝 b₀,
      Function.Injective (fun i => S.sheet i (((b' : ℂ) : RiemannSphere))))
    (hsheetMem : ∀ᶠ b' in 𝓝 b₀, ∀ i, S.sheet i (((b' : ℂ) : RiemannSphere)) ∈
      (chartAt ℂ (S.sheet i (((b₀ : ℂ) : RiemannSphere)))).source) :
    MovingCoherenceDatum ω₀ g f Φ b₀ :=
  MovingCoherenceDatum.ofSphereSheetSystemSet S hderiv hmero
    (canon_of_fibre_enumeration S hΦinj hΦrange hsheetInj hsheetMem)

end Jacobians.Dolbeault.FormTraceMovingFibre
