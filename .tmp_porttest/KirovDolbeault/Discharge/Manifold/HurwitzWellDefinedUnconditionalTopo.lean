/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.HurwitzWellDefinedFromHPath
import KirovDolbeault.Discharge.Manifold.PathConnectedComplFinite

/-! # Hurwitz constant-card with unconditional topology (ZZ176)

Compose ZZ160's `fibre_card_well_defined_at_regular_holds_of_h_path`
(post-ZZ172, corrected) with ZZ165's
`isPathConnected_compl_finite_of_connected_chartedSpace_complex`
(unconditional path-connectedness of finite-complement subsets of a
connected complex 1-manifold) to discharge the topological residual
without any assumption.

The remaining residual is the **per-`f` analytic packaging** `h_pkg`:

```
∀ f : X → Y, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ IsConstantMap f →
  ∃ C : Set Y, C.Finite ∧
    (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y)) ∧
    IsLocallyConstant (fun y : (Cᶜ : Set Y) ↦ (f ⁻¹' {y.val}).ncard)
```

This packaging encapsulates the analytic content that is genuinely owed at
this mathlib pin: a finite critical-value set `C` (analytic identity
theorem), and locally-constant fibre cardinality on its complement
(local-triviality of the regular-value covering — Hurwitz local normal
form, ZZ151/152, lifted by ZZ169).

No gaps, no `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

namespace Degree

universe u v

/-- **Hurwitz constant-card, unconditional topology (ZZ176).**

Discharge of the corrected `fibre_card_well_defined_at_regular_statement`
that takes only the analytic per-`f` packaging — the topological
path-connectedness residual is supplied unconditionally from ZZ165.

When `h_pkg` lands (analytic identity theorem for the `C.Finite` leg, plus
ZZ151/152/169 chain for `IsLocallyConstant`), this theorem is one rewrite
away from strict closure of `Degree` item 3.reg. -/
theorem fibre_card_well_defined_at_regular_holds_of_h_pkg
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_pkg : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (C : Set Y), C.Finite ∧
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y)) ∧
        IsLocallyConstant
          (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  -- Unconditional path-connectedness of finite-complement subsets: the
  -- complement of any finite set in a connected complex 1-manifold is
  -- path-connected. The @-form pins `Y` and its instances so the ambient
  -- `IsManifold 𝓘(ℂ) ω Y` instance is used.
  have h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y) := fun C hC hne =>
    @Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      Y _ _ _ _ _ C hC hne
  -- Apply the corrected ZZ160 with the supplied analytic packaging.
  intro f hf hnc w₁ w₂
  exact fibre_card_well_defined_at_regular_holds_of_h_path h_path h_pkg f hf hnc w₁ w₂

end Degree

end ContMDiff

end Jacobians.Discharge
