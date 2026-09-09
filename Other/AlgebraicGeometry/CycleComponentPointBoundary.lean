/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection
public import Other.AlgebraicGeometry.SmoothClosedPointCoclassSectionNormalization

/-! # The singular boundary of a maximal-codimension component is empty

The already proved strict algebraic dimension drop gives a negative Krull
dimension for its singular boundary. We deduce actual emptiness, both
algebraically and analytically; the auxiliary ambient open is therefore the
whole scheme. No smoothness or emptiness of the component is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Topology Opposite

namespace AlgebraicGeometry

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = d)

include d hx in
/-- Every singular-filtration remainder of a maximal-codimension component is empty. -/
theorem cycleComponentSingularClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    cycleComponentSingularClosedFiltration s x k = ⊥ := by
  have hdim := cycleComponentSingularClosedFiltration_dimension_lt s x (d := d) hx k
  simp only [Nat.sub_self, Nat.cast_zero] at hdim
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  let y' : cycleComponentSingularClosedFiltration s x k := ⟨y, hy⟩
  let Z : IrreducibleCloseds (cycleComponentSingularClosedFiltration s x k) :=
    ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hnonneg : 0 ≤ topologicalKrullDim (cycleComponentSingularClosedFiltration s x k) :=
    Order.krullDim_nonneg_iff.mpr ⟨Z⟩
  exact (not_lt_of_ge hnonneg) hdim

include d hx in
/-- The actual algebraic ambient singular supports vanish, not just their cohomology. -/
theorem cycleComponentSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    cycleComponentSingularAmbientClosedFiltration s x k = ⊥ := by
  apply SetLike.coe_injective
  change cycleComponentι X x '' (cycleComponentSingularClosedFiltration s x k : Set _) = ∅
  rw [cycleComponentSingularClosedFiltration_eq_bot_of_coheight_eq_dimension s x hx k]
  exact Set.image_empty _

include d hx in
/-- In maximal codimension, the auxiliary algebraic ambient open is the whole scheme. -/
theorem cycleComponentSmoothLocusAmbientOpen_eq_top_of_coheight_eq_dimension :
    cycleComponentSmoothLocusAmbientOpen s x = ⊤ := by
  rw [cycleComponentSmoothLocusAmbientOpen,
    cycleComponentSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension s x hx 0]
  apply Opens.ext
  exact Set.compl_empty

namespace ComplexPoint

include d hx in
/-- All analytic singular supports of a maximal-codimension component are empty. -/
theorem cycleComponentSingularAnalyticClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    cycleComponentSingularAnalyticClosedFiltration s x k = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹' (cycleComponentSingularAmbientClosedFiltration s x k : Set X) = ∅
  rw [cycleComponentSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension s x hx k]
  exact Set.preimage_empty

include d hx in
/-- The exact original-ambient open used by the general component class is all of X. -/
theorem cycleComponentSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension :
    cycleComponentSmoothSupportAmbientOpen s x = ⊤ := by
  rw [cycleComponentSmoothSupportAmbientOpen,
    cycleComponentSingularAnalyticClosedFiltration_eq_bot_of_coheight_eq_dimension s x hx 0]
  apply Opens.ext
  exact Set.compl_empty

include d hx in
/-- The actual auxiliary ambient scheme-open inclusion is an isomorphism in the point case. -/
theorem cycleComponentSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension :
    IsIso (cycleComponentSmoothLocusAmbientOpen s x).ι := by
  rw [cycleComponentSmoothLocusAmbientOpen_eq_top_of_coheight_eq_dimension s x hx]
  exact X.topIso.isIso_hom

include d hx in
/-- Consequently the auxiliary ambient scheme retains actual projectivity in this
point case; projectivity of arbitrary auxiliary opens is not asserted. -/
theorem cycleComponentSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension :
    IsProjective ((cycleComponentSmoothLocusAmbientOpen s x).ι ≫ s) := by
  let := cycleComponentSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension s x hx
  obtain ⟨P⟩ := (inferInstance : IsProjective s).nonempty_presentation
  refine ⟨⟨{
    ambientDimension := P.ambientDimension
    immersion := (cycleComponentSmoothLocusAmbientOpen s x).ι ≫ P.immersion
    isClosedImmersion := ?_
    immersion_toBase := ?_ }⟩⟩
  · let := P.isClosedImmersion
    infer_instance
  · rw [Category.assoc, P.immersion_toBase]

end ComplexPoint
end AlgebraicGeometry
