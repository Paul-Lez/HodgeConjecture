/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.Degree

set_option autoImplicit true

/-! # Fibre-cardinality well-definedness on the regular subset (ZZ134, ZZ172-corrected)

## Goal

Discharge `fibre_card_well_defined_at_regular_statement`-shape conclusions
from a packaged `(R, card_of, h_witness, h_supp, h_lc, h_conn)` bundle.

Compared with the pre-ZZ172 version of this file, the bundle no longer
takes a critical-value set `C : Set Y` parameter: the regular-witness
type `RegularValueWitnessReg f` (post-ZZ172) carries an intrinsic
chart-pullback-derivative-nonzero certificate, so callers wire support
membership `∀ w, w.value ∈ R` directly to whatever regular-value subset `R`
they choose.

## What is delivered

* `fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant` —
  uniform top-level reduction. Conclusion is the unfolded form of
  `fibre_card_well_defined_at_regular_statement X Y`.

## Status

Purely structural. The two analytic obligations
(`IsLocallyConstant` of `card_of` on `R`, `IsPreconnected` of `R`) are
inputs — they would be discharged by the analytic implicit-function
theorem on Riemann surfaces (local triviality of regular-value covering)
and the connectedness lemma "connected real-2-manifold minus finite
critical values is connected", neither of which is formalised at this
mathlib pin.

No gaps. No `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

universe u v

namespace Degree

/-! ## Top-level reduction (uniform over `f`) -/

/-- **Top-level reduction (regular-form).** The
`fibre_card_well_defined_at_regular_statement` conclusion follows from the
existence, for every non-constant analytic `f`, of a regular-value subset
`R ⊆ Y` together with a fibre-cardinality function locally constant on `R`,
preconnected `R`, and the support witness `∀ w : RegularValueWitnessReg f,
w.value ∈ R`. -/
lemma fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (R : Set Y) (card_of : Y → ℕ),
        (∀ w : RegularValueWitness f, card_of w.value = w.card) ∧
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ R) ∧
        IsLocallyConstant (fun y : R => card_of y.val) ∧
        IsPreconnected (Set.univ : Set R)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  intro f hf hnc w₁ w₂
  obtain ⟨R, card_of, h_witness, h_supp, h_lc_sub, h_conn_sub⟩ := h_lc f hf hnc
  exact fibre_card_eq_of_locallyConstant_subtype_reg
    (R := R) card_of h_witness h_supp h_lc_sub h_conn_sub w₁ w₂

end Degree

end ContMDiff

end Jacobians.Discharge
