/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.HurwitzPatchingDataConstruction

set_option autoImplicit true

/-! # Discharge of `h_lc` via ZZ153 ∘ ZZ157 (ZZ158)

ZZ155 (`fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo` in
`FibreCardWellDefinedAtRegular.lean`) consumes a hypothesis `h_lc` of the
shape

```
∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ IsConstantMap f →
  ∀ (C : Set Y),
    IsLocallyConstant (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard)
```

This file delivers the **structural composition glue** that turns a
per-fibre-point local-sheet supplier on a subset `R ⊆ Y` into the
locally-constant fibre cardinality on `R`. Concretely:

* `fibreCard_isLocallyConstant_on_subset_of_localSheets` — for every
  `y₀ ∈ R`, given `LocalSheetData f y₀ x` for every preimage `x` of `y₀`
  and finiteness of the fibre, ZZ157 (`HurwitzPatchingData.ofLocalSheets`)
  packages the patching data and ZZ153
  (`fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz`) reads off
  local constancy of `(f ⁻¹' {·}).ncard` on the subtype `R`.

* `h_lc_holds_for_subset_of_localSheets_supplier` — the parameterised
  ZZ155-shape `h_lc` for a *fixed* candidate critical-value set
  `C : Set Y`, conditional on a `LocalSheetData` supplier on `Cᶜ`.

The outer hypothesis (existence of per-fibre-point `LocalSheetData` on
the regular subset) is the analytic content that ZZ152
(`AnalyticAt.exists_local_biholomorphism`) supplies in chart-flat
coordinates: a separate supplier chip transports that witness from `ℂ → ℂ`
charts back to `f : X → Y` via the analytic atlases of `X` and `Y`. This
chip leaves that supplier as a hypothesis and discharges the
*ZZ153 ∘ ZZ157* structural skeleton above it.

## Anti-cheat

* No `axiom`, no gaps.
* No signature change to any pre-existing definition or theorem.
* Adds one new file, imported into the manifest.
-/

@[expose] public section

open Set Filter Topology

namespace Jacobians.Discharge

universe u v

/-- **Local-constancy of fibre cardinality on a subset, from a per-fibre
local-sheet supplier.**

Given `f : X → Y` continuous with `X` compact T2 and `Y` T2, a subset
`R : Set Y`, finiteness of the fibre over every `y ∈ R`, and a
`LocalSheetData f y x` for every `y ∈ R` and every `x ∈ f ⁻¹' {y}`, the
fibre-cardinality function `fun y : R => (f ⁻¹' {y.val}).ncard` is locally
constant.

This is `HurwitzPatchingData.ofLocalSheets` (ZZ157) chained into
`fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz` (ZZ153). -/
theorem fibreCard_isLocallyConstant_on_subset_of_localSheets
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (R : Set Y)
    (h_fib : ∀ y ∈ R, (f ⁻¹' {y}).Finite)
    (h_sheets : ∀ y ∈ R, ∀ x ∈ f ⁻¹' {y}, LocalSheetData f y x) :
    IsLocallyConstant
      (fun y : (R : Set Y) => (f ⁻¹' {y.val}).ncard) := by
  -- Step 1: For every y₀ ∈ R, build the HurwitzPatchingData from the
  -- per-fibre LocalSheetData via ZZ157.
  have h_pkg : ∀ y₀ ∈ R, HurwitzPatchingData f y₀ := by
    intro y₀ hy₀
    refine HurwitzPatchingData.ofLocalSheets (f := f) hf
      (h_fib y₀ hy₀) ?_
    intro x hx
    exact h_sheets y₀ hy₀ x hx
  -- Step 2: ZZ153 reads off local-constancy on the subtype R.
  exact fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz f R h_pkg

/-- **`h_lc`-shape for a *fixed* candidate set `C`, from a `LocalSheetData`
supplier on `Cᶜ`.**

This is the canonical instance of the ZZ155 hypothesis `h_lc` at a
specific `C : Set Y`: when `C` is large enough that the local-biholomorphism
witnesses (`LocalSheetData`) are available on every point of `Cᶜ`, the
fibre cardinality is locally constant on the regular subtype.

The supplier hypothesis `h_sheets` is satisfied when `C ⊇ critical_values f`
(where critical values are the f-images of points where the local
multiplicity exceeds 1): on the complement, the analytic local normal form
is `z ↦ z` (multiplicity 1), and `AnalyticAt.exists_local_biholomorphism`
(ZZ152) yields the open partial homeomorphism that is exactly a
`LocalSheetData`. The transport from chart-flat `ℂ → ℂ` to `f : X → Y` is
the analytic content packaged by a separate supplier chip.

This wrapper exposes the ZZ155-compatible per-`C` shape; the outer
universal-`C` quantifier of ZZ155's hypothesis is satisfied at every
specific `C` for which the `LocalSheetData` supplier is available. -/
theorem h_lc_holds_for_subset_of_localSheets_supplier
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (C : Set Y)
    (h_fib : ∀ y ∈ (Cᶜ : Set Y), (f ⁻¹' {y}).Finite)
    (h_sheets : ∀ y ∈ (Cᶜ : Set Y), ∀ x ∈ f ⁻¹' {y},
      LocalSheetData f y x) :
    IsLocallyConstant
      (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard) :=
  fibreCard_isLocallyConstant_on_subset_of_localSheets
    hf (Cᶜ : Set Y) h_fib h_sheets

end Jacobians.Discharge

end
