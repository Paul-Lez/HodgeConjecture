/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.LocalSheetDataFromContMDiff
import KirovDolbeault.Discharge.Manifold.Degree

/-! # `LocalSheetData` from a `RegularValueWitnessReg` (zzLSD)

This file packages the existing point-builder
`LocalSheetData.ofContMDiffMfderivNeZero`
(`Manifold/LocalSheetDataFromContMDiff.lean`, ZZ169) with the regular-value
witness bundle `Jacobians.Discharge.ContMDiff.RegularValueWitnessReg`
(`Manifold/Degree.lean`).

The regular-value-witness structure already carries, as a field
(`is_regular`), exactly the chart-pullback-derivative-nonzero certificate
consumed by `ofContMDiffMfderivNeZero`. So the supplier here is a
one-step composition: pull `h_deriv` out of `w.is_regular` at the given
preimage point and feed it into the ZZ169 builder.

This is the supplier feeding the `h_sheets` hypothesis of
`Jacobians.Discharge.h_lc_holds_for_subset_of_localSheets_supplier`
(`Manifold/HLcUnconditional.lean`) on the regular-value side of any
`Cᶜ` decomposition where `C` contains the critical values.

## Anti-cheat

* No `axiom`, no gaps.
* No signature changes to any pre-existing definition.
* No new mathlib imports (transitively available via the two local imports).
-/

@[expose] public section

open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge

universe u v

namespace LocalSheetData

/-- **`LocalSheetData` supplier at a regular value.**

Given an analytic map `f : X → Y` between complex manifolds, a regular-value
witness `w : RegularValueWitnessReg f`, and a preimage point
`x ∈ f ⁻¹' {w.value}`, produce a `LocalSheetData f w.value x`.

The construction extracts the chart-pullback-derivative-nonzero certificate
`w.is_regular x hx` and feeds it together with
`hf.contMDiffAt` into `LocalSheetData.ofContMDiffMfderivNeZero` (ZZ169). -/
noncomputable def ofRegularValueWitnessReg
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (w : Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f)
    {x : X} (hx : x ∈ f ⁻¹' {w.toWitness.value}) :
    LocalSheetData f w.toWitness.value x :=
  -- `hx : x ∈ f ⁻¹' {w.toWitness.value}` unfolds to `f x = w.toWitness.value`.
  LocalSheetData.ofContMDiffMfderivNeZero
    (hf := hf.contMDiffAt)
    (hxy := hx)
    (h_deriv := w.is_regular x hx)

end LocalSheetData

end Jacobians.Discharge

end
