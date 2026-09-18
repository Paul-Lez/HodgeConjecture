/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import Other.AlgebraicGeometry.Cycle.SmoothPair.PointCoclassSection
public import Other.LinearAlgebra.HodgeStructure

/-! # The singular boundary of a maximal-codimension component is empty

The already proved strict algebraic dimension drop gives a negative Krull
dimension for its singular boundary. We deduce actual emptiness, both
algebraically and analytically; the auxiliary ambient open is therefore the
whole scheme. No smoothness or emptiness of the component is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Opposite

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  (hi : Order.coheight (closedEmbeddingGenericPoint i) = dim X.left)

include hi in
/-- Every singular-filtration remainder of a maximal-codimension component is empty. -/
theorem closedEmbeddingSingularClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    closedEmbeddingSingularClosedFiltration i k = ⊥ := by
  have hdim := closedEmbeddingSingularClosedFiltration_dimension_lt i hi k
  simp only [Nat.sub_self, Nat.cast_zero] at hdim
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  let y' : closedEmbeddingSingularClosedFiltration i k := ⟨y, hy⟩
  let Z : IrreducibleCloseds (closedEmbeddingSingularClosedFiltration i k) :=
    ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hnonneg : 0 ≤ topologicalKrullDim (closedEmbeddingSingularClosedFiltration i k) :=
    Order.krullDim_nonneg_iff.mpr ⟨Z⟩
  exact (not_lt_of_ge hnonneg) hdim

include hi in
/-- The actual algebraic ambient singular supports vanish, not just their cohomology. -/
theorem closedEmbeddingSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    closedEmbeddingSingularAmbientClosedFiltration i k = ⊥ := by
  apply SetLike.coe_injective
  change i.left '' (closedEmbeddingSingularClosedFiltration i k : Set _) = ∅
  rw [closedEmbeddingSingularClosedFiltration_eq_bot_of_coheight_eq_dimension i hi k]
  exact Set.image_empty _

include hi in
/-- In maximal codimension, the auxiliary algebraic ambient open is the whole scheme. -/
theorem closedEmbeddingSmoothLocusAmbientOpen_eq_top_of_coheight_eq_dimension :
    closedEmbeddingSmoothLocusAmbientOpen i = ⊤ := by
  rw [closedEmbeddingSmoothLocusAmbientOpen,
    closedEmbeddingSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension i hi 0]
  exact Opens.ext Set.compl_empty

namespace ComplexPoint

include hi in
/-- All analytic singular supports of a maximal-codimension component are empty. -/
theorem closedEmbeddingSingularAnalyticClosedFiltration_eq_bot_of_coheight_eq_dimension (k : ℕ) :
    closedEmbeddingSingularAnalyticClosedFiltration i k = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹' (closedEmbeddingSingularAmbientClosedFiltration i k : Set X.left) = ∅
  rw [closedEmbeddingSingularAmbientClosedFiltration_eq_bot_of_coheight_eq_dimension i hi k]
  exact Set.preimage_empty

include hi in
/-- The exact original-ambient open used by the general component class is all of X. -/
theorem closedEmbeddingSmoothSupportAmbientOpen_eq_top_of_coheight_eq_dimension :
    closedEmbeddingSmoothSupportAmbientOpen i = ⊤ := by
  rw [closedEmbeddingSmoothSupportAmbientOpen,
    closedEmbeddingSingularAnalyticClosedFiltration_eq_bot_of_coheight_eq_dimension i hi 0]
  exact Opens.ext Set.compl_empty

include hi in
/-- The actual auxiliary ambient scheme-open inclusion is an isomorphism in the point case. -/
theorem closedEmbeddingSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension :
    IsIso (closedEmbeddingSmoothLocusAmbientOpen i).ι := by
  rw [closedEmbeddingSmoothLocusAmbientOpen_eq_top_of_coheight_eq_dimension i hi]
  exact X.left.topIso.isIso_hom

include hi in
/-- Consequently the auxiliary ambient scheme retains actual projectivity in this
point case; projectivity of arbitrary auxiliary opens is not asserted. -/
theorem closedEmbeddingSmoothLocusAmbientOpen_isProjective_of_coheight_eq_dimension :
    IsProjective ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom) := by
  let := closedEmbeddingSmoothLocusAmbientOpen_ι_isIso_of_coheight_eq_dimension i hi
  obtain ⟨P⟩ := (inferInstance : IsProjective X.hom).nonempty_presentation
  refine ⟨⟨{
    ambientDimension := P.ambientDimension
    immersion := (closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ P.immersion
    isClosedImmersion := ?_
    immersion_toBase := ?_ }⟩⟩
  · let := P.isClosedImmersion
    infer_instance
  · rw [Category.assoc, P.immersion_toBase]

end ComplexPoint
end AlgebraicGeometry
