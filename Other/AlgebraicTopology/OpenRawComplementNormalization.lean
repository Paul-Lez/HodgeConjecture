/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.GlobalRawOpenComplement

/-!
# Raw cochain restriction and the intrinsic complement presentation

The intrinsic-to-top-open complement transport is an actual isomorphism of
complexes. Raw restriction is an epimorphism of complexes, and composes literally.
These statements permit cancellation of complex maps; they assert no surjectivity
of restriction on cycles or cohomology.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

namespace AlgebraicTopology.Singular
variable (R : Type) [Field R] (X : TopCat.{0})
/-- The prescribed intrinsic-to-top-open raw transport is an actual isomorphism. -/
lemma globalRawComplementToTopOpenCochains_isIso (U : Opens X) :
    IsIso (globalRawComplementToTopOpenCochains R X U) := by
  let e := (chainPairFunctor R).mapIso (topOpenIntersectionPairIso X U)
  let e₃ := (Arrow.leftFunc.mapIso e)
  let ed := HomologicalComplex.linearDualIso e₃
  let eext := (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R)).mapIso ed
  have hm : (relativeDualCochainShortComplexIntMap R (topOpenIntersectionPairIso X U).hom).τ₃ =
      eext.hom := rfl
  dsimp only [globalRawComplementToTopOpenCochains]
  rw [hm]
  infer_instance

/-- Raw restriction is an epimorphism before taking cycles or cohomology. -/
lemma openRawSingularRestrictionInt_epi {V W : Opens X} (i : W ⟶ V) :
    Epi (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
      ComplexShape.embeddingUpNat) := by
  let : Epi (relativeCochainRestrictionInt R (openInclusionPair X i)) :=
    (relativeDualCochainShortComplexInt_shortExact R (openInclusionPair X i)).epi_g
  let : Epi (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
      ComplexShape.embeddingUpNat ≫ (openRawSingularCochainComplexIntIsoDual R X W).hom) := by
    rw [openRawSingularRestrictionInt_transport]
    infer_instance
  exact (epi_comp_iff_of_isIso (HomologicalComplex.extendMap
    (openRawSingularRestriction R X i) ComplexShape.embeddingUpNat)
    (openRawSingularCochainComplexIntIsoDual R X W).hom).mp inferInstance

/-- Literal raw restriction composes contravariantly. -/
lemma openRawSingularRestriction_comp {V W Z : Opens X} (i : W ⟶ V) (j : Z ⟶ W) :
    openRawSingularRestriction R X (j ≫ i) =
      openRawSingularRestriction R X i ≫ openRawSingularRestriction R X j := by
  ext n : 1
  exact (singularCochainPresheaf R X n).map_comp i.op j.op
end AlgebraicTopology.Singular
