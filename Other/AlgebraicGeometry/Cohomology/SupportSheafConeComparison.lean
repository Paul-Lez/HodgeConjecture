/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.DerivedCategory.MappingCoconeFunctor
public import Other.AlgebraicGeometry.Cohomology.SupportConeInjectiveModelLemmas

/-! # The sheaf map underlying the supported-injective cone comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

set_option backward.isDefEq.respectTransparency false in
/-- The shifted supported complex maps to the ambient injective cone through the
canonical short-complex lift and the fixed open-resolution comparison. -/
def supportSheafToAmbientInjectiveCone :
    (TopCat.Sheaf.supportRestrictionComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩
      (ambientRationalInjectiveComplex X)).X₁⟦(1 : ℤ)⟧ ⟶
    CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ) :=
  CochainComplex.mappingCocone.shiftedLiftShortComplex _ ≫
    CochainComplex.mappingCone.map _ _ (𝟙 _)
      (ambientRationalOpenResolutionComparison X Z hZ)
      (by rw [Category.id_comp]; exact supportRestriction_comp_openResolutionComparison X Z hZ)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections gives the exact chain maps used in the existing support
normalization, including the additive functor's shift comparison. -/
lemma supportSheafToAmbientInjectiveCone_globalSections :
    let Y := TopCat.of (ComplexPoint X)
    let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    (Γ.mapHomologicalComplex (.up ℤ)).map (supportSheafToAmbientInjectiveCone X Z hZ) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (ambientRationalInjectiveRestriction X Z hZ) Γ).hom =
    ((Γ.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫
      CochainComplex.mappingCocone.shiftedLiftShortComplex
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y
          ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ (ambientRationalInjectiveComplex X)) ≫
      supportConeToAmbientInjectiveGlobalCone X Z hZ := by
  dsimp only
  rw [supportSheafToAmbientInjectiveCone, Functor.map_comp, Category.assoc,
    CochainComplex.mappingCone.mapHomologicalComplexIso_naturality,
    ← Category.assoc, CochainComplex.mappingCocone.map_shiftedLiftShortComplex]
  rfl

end AlgebraicGeometry.ComplexPoint
