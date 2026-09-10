/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.HPkgUnconditional
import KirovDolbeault.Discharge.Manifold.HurwitzWellDefinedUnconditionalTopo
import KirovDolbeault.Discharge.Manifold.Degree

/-! # `degreeFiber` is well-defined across regular witnesses

Combines `h_pkg_holds_unconditional` (`Manifold/HPkgUnconditional.lean`)
with `fibre_card_well_defined_at_regular_holds_of_h_pkg`
(`Manifold/HurwitzWellDefinedUnconditionalTopo.lean`) to discharge the
"witness independence" of `degreeFiber`: the `Classical.choice`-selected
witness's `card` equals the `card` of any other `RegularValueWitnessReg`.

This is the analytic content owed for item 9 (`ContMDiff.degree`) in
`Basic.lean`. -/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace Jacobians.Discharge

universe u v

/-- **Witness independence of `degreeFiber`.** For any
`RegularValueWitnessReg f`, the chosen witness's `card` equals
`degreeFiber f hf`. -/
theorem degreeFiber_eq_card_of_regular_witness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f)
    (w : Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f) :
    Jacobians.Discharge.ContMDiff.degreeFiber f hf = w.card := by
  classical
  -- Witness independence from h_pkg + ZZ176.
  have h_well :
      ∀ (g : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g →
        ¬ Jacobians.Discharge.IsConstantMap g →
        ∀ (w₁ w₂ : Jacobians.Discharge.ContMDiff.RegularValueWitnessReg g),
          w₁.card = w₂.card :=
    Jacobians.Discharge.ContMDiff.Degree.fibre_card_well_defined_at_regular_holds_of_h_pkg
      (h_pkg :=
        Jacobians.Discharge.ContMDiff.Degree.h_pkg_holds_unconditional)
  -- Nonempty regular-witness type.
  have hne : Nonempty (Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f) :=
    ⟨w⟩
  -- Unfold degreeFiber via degreeFiber_eq_witness_card.
  have h_unfold :
      Jacobians.Discharge.ContMDiff.degreeFiber f hf = (Classical.choice hne).card :=
    Jacobians.Discharge.ContMDiff.degreeFiber_eq_witness_card f hf hnc hne
  rw [h_unfold]
  -- And well-definedness equates the chosen card with w.card.
  exact h_well f hf hnc (Classical.choice hne) w

end Jacobians.Discharge

end

end
