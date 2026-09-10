/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.FibreCardOnRegularSubset

/-! # Composition: Hurwitz local-constancy + preconnected regular subset
⇒ `fibre_card_well_defined_at_regular_statement` (ZZ155, ZZ172-corrected)

Compose ZZ134 (`fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`)
with a per-`f` packaging of the regular subset `R` and its analytic
locality + topological connectedness, into the named owed statement
`fibre_card_well_defined_at_regular_statement X Y`.

This file is the structural glue. The unconditional discharges of the two
analytic hypotheses (locally-constant ncard on the regular subset, the
chart-pullback-deriv content) plug in via the packaged shape this file
consumes.

Compared with the pre-ZZ172 version, the universally-false `h_C_fin`
hypothesis (which asserted that *every* set in `Y` is finite) is removed.
The corrected witness type `RegularValueWitnessReg f` no longer carries a
`C : Set Y` parameter — its regularity certificate is intrinsic to `f`.

No gaps, no `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

namespace Degree

universe u v

/-- **The ZZ155 composition (ZZ172-corrected).** Conditional on a packaged
existence (for every non-constant analytic `f`) of a regular-value subset
`R ⊆ Y` carrying:

* support: every regular witness's value lies in `R`,
* locally-constant ncard on `R` (analytic / covering-space content),
* preconnected `R` (topological content).

Conclude the unfolded form of `fibre_card_well_defined_at_regular_statement X Y`.

Stated in the unfolded `∀ f hf hnc w₁ w₂, w₁.card = w₂.card` shape rather
than against the def, to avoid `intro`-time elaboration "typeclass instance
problem is stuck" issues observed when applying the def directly. The
underlying statement is identical (the def's body). -/
theorem fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_pkg : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (R : Set Y),
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ R) ∧
        IsLocallyConstant (fun y : R => (f ⁻¹' {y.val}).ncard) ∧
        IsPreconnected (Set.univ : Set R)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  apply fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
  intro f hf hnc
  obtain ⟨R, h_supp, h_lc, h_conn⟩ := h_pkg f hf hnc
  refine ⟨R, fun y => (f ⁻¹' {y}).ncard, ?_, h_supp, h_lc, h_conn⟩
  -- card_of w.value = w.card via ncard ↔ toFinset.card.
  intro w
  classical
  exact Set.ncard_eq_toFinset_card (f ⁻¹' {w.value}) w.fiber_finite

end Degree

end ContMDiff

end Jacobians.Discharge
