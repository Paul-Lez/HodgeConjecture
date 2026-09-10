/-
Thin forwarder from `Jacobians.*` to the ported discharge under
`Jacobians.Discharge.*`. The discharge ships
`Nonempty (RegularValueWitnessReg f)` unconditionally for non-constant
analytic `f : X → Y` between compact connected complex 1-manifolds
(`regular_value_exists_reg_unconditional`), so the `else 0`
fallback in `degreeFiber` no longer fires for non-constant maps.

Original code MIT-licensed by Bryan Sanchez (2026); audit verifies
`#print axioms` returns only `[propext, Classical.choice, Quot.sound]`.
Axiom-verified clean (`#print axioms` returns only `[propext, Classical.choice, Quot.sound]`).
-/
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional
import KirovDolbeault.Discharge.Manifold.DegreeWellDefined

open scoped Manifold ContDiff

namespace Jacobians

/-- `Jacobians.IsConstantMap` is the discharge's `IsConstantMap`. -/
abbrev IsConstantMap {X : Type _} {Y : Type _} (f : X → Y) : Prop :=
  Jacobians.Discharge.IsConstantMap f

/-- `Jacobians.RegularValueWitness` is the discharge's structure. -/
abbrev RegularValueWitness {X : Type _} {Y : Type _} (f : X → Y) : Type _ :=
  Jacobians.Discharge.ContMDiff.RegularValueWitness f

/-- `Jacobians.RegularValueWitnessReg` is the discharge's regularity-
certified witness. -/
abbrev RegularValueWitnessReg
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type _} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) : Type _ :=
  Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f

/-- `Jacobians.degreeFiber` is the discharge's fibre-cardinality degree. -/
noncomputable abbrev degreeFiber := @Jacobians.Discharge.ContMDiff.degreeFiber

/-- **Unconditional existence of a regular witness** for non-constant
analytic maps between compact connected complex 1-manifolds. Forwards
to `Jacobians.Discharge.ContMDiff.Degree.regular_value_exists_reg_unconditional`. -/
theorem regularValueWitnessReg_nonempty_of_nonConstantMap
    {X : Type _} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type _} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) :
    Nonempty (RegularValueWitnessReg f) :=
  Jacobians.Discharge.ContMDiff.Degree.regular_value_exists_reg_unconditional
    f hf hnc

/-- **Degree well-definedness.** For non-constant analytic `f`, the
fibre-cardinality degree `degreeFiber f hf` equals the `card` of *any*
regularity-certified regular-value witness. Forwards to the ported,
axiom-clean `Jacobians.Discharge.degreeFiber_eq_card_of_regular_witness`. -/
theorem degreeFiber_eq_card_of_regularWitness
    {X : Type _} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type _} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (w : RegularValueWitnessReg f) :
    degreeFiber f hf = w.card :=
  Jacobians.Discharge.degreeFiber_eq_card_of_regular_witness f hf hnc w

end Jacobians
