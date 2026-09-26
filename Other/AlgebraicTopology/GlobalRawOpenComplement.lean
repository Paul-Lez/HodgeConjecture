/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization

/-!
# Raw complement cochains on the actual top-open intersection

The intrinsic complement complex is transported to cochains on `⊤ ∩ U`, preserving
the literal restriction map. Raw restriction is an epimorphism of complexes; this
allows cancellation of equalities of maps, without asserting surjectivity on
cycles or cohomology.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace AlgebraicTopology.Singular
variable (R : Type) [Field R] (X : TopCat.{0})

/-- Restriction of raw cochains to a subspace is an epimorphism of complexes. -/
lemma globalRawSingularRestrictionInt_epi (A : Set X) :
    Epi (globalRawSingularRestrictionInt R X A) := by
  let : Epi (relativeCochainRestrictionInt R (TopPair.ofSubset A)) :=
    (relativeDualCochainShortComplexInt_shortExact R (TopPair.ofSubset A)).epi_g
  let : Epi (globalRawSingularRestrictionInt R X A ≫
      (globalRawPushforwardSingularCochainComplexIntIsoRelative R X A).hom) := by
    rw [globalRawSingularRestrictionInt_transport_relative]
    infer_instance
  exact (epi_comp_iff_of_isIso (globalRawSingularRestrictionInt R X A)
    (globalRawPushforwardSingularCochainComplexIntIsoRelative R X A).hom).mp inferInstance

/-- Intrinsic raw complement cochains transported to the actual top-open intersection. -/
def globalRawComplementToTopOpenCochains (U : Opens X) :
    globalRawPushforwardSingularCochainComplexInt R X U ⟶
      (openRawSingularCochainComplex R X (⊤ ⊓ U)).extend ComplexShape.embeddingUpNat :=
  (globalRawPushforwardSingularCochainComplexIntIsoRelative R X U).hom ≫
    ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).map
      (relativeDualCochainShortComplexIntMap R (topOpenIntersectionPairIso X U).hom).τ₃ ≫
    (openRawSingularCochainComplexIntIsoDual R X (⊤ ⊓ U)).inv

/-- This transport preserves the literal cochain restriction from the ambient space. -/
lemma globalRawSingularRestrictionInt_comp_topOpen (U : Opens X) :
    globalRawSingularRestrictionInt R X U ≫ globalRawComplementToTopOpenCochains R X U =
      HomologicalComplex.extendMap (openRawSingularRestriction R X (Opens.infLELeft ⊤ U))
        ComplexShape.embeddingUpNat := by
  let F := (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)
  let f := relativeDualCochainShortComplexIntMap R (topOpenIntersectionPairIso X U).hom
  apply (cancel_mono (openRawSingularCochainComplexIntIsoDual R X (⊤ ⊓ U)).hom).mp
  dsimp only [globalRawComplementToTopOpenCochains]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, globalRawSingularRestrictionInt_transport_relative,
    openRawSingularRestrictionInt_transport,
    ← globalRawCochainIntIso_comp_topOpenDual R X U]
  change ((globalRawSingularCochainComplexIntIsoRelative R X).hom ≫
      F.map (relativeCochainRestrictionInt R (TopPair.ofSubset (U : Set X)))) ≫ F.map f.τ₃ =
    ((globalRawSingularCochainComplexIntIsoRelative R X).hom ≫ F.map f.τ₂) ≫
      F.map (relativeCochainRestrictionInt R (openInclusionPair X (Opens.infLELeft ⊤ U)))
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k => (globalRawSingularCochainComplexIntIsoRelative R X).hom ≫ F.map k)
    f.comm₂₃.symm
end AlgebraicTopology.Singular
