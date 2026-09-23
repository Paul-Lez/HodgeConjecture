/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RationalSupportConeBoundaryComparison
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-!
# The boundary sign of the actual supported injective comparison

The repository's fixed rational support comparison sends a positive complement
boundary to the negative canonical kernel boundary. The theorem traces the
actual cone maps and the existing final negation; no normalization is changed.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

/-- The positive canonical cone comparison for the actual supported injective sections. -/
def actualInjectiveSupportHomologyIsoCone (n : ℤ) :
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (ambientRationalInjectiveComplex X)).X₁.homology n ≅
    (CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g).homology (n - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone _
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ _) (n - 1) n (by omega)

/-- Unfolding the existing support comparison exposes its final negation. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_eq_neg (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    rationalSupportAddEquivSupportedInjectiveHomology X Z hZ n a =
      -((actualInjectiveSupportHomologyIsoCone X Z hZ n).inv
        ((asIso (HomologicalComplex.homologyMap
          (supportConeToAmbientInjectiveGlobalCone X Z hZ) (n - 1))).inv
          (HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.mapHomologicalComplexIso
              (ambientRationalInjectiveRestriction X Z hZ)
              (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
                (TopCat.of (ComplexPoint X)))).hom (n - 1)
            (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n a)))) := rfl

/-- The actual global-cone comparison preserves positive complement inclusion. -/
lemma actualSupportConeToAmbientInjectiveGlobalCone_inr :
    CochainComplex.mappingCone.inr
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g ≫
      supportConeToAmbientInjectiveGlobalCone X Z hZ =
    globalAmbientRationalOpenResolutionComparison X Z hZ ≫
      CochainComplex.mappingCone.inr
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (ambientRationalInjectiveRestriction X Z hZ)) := by
  simp [supportConeToAmbientInjectiveGlobalCone, CochainComplex.mappingCone.map]

/-- The existing rational support comparison sends a positive complement boundary
to the negative of the canonical supported-injective kernel boundary. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_boundary (n : ℤ)
    (z : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (ambientRationalInjectiveComplex X)).X₃.homology (n - 1)) :
    rationalSupportAddEquivSupportedInjectiveHomology X Z hZ n
      (hypercohomologyMap X
        (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1)
        ((complementRationalHypercohomologyAddEquivGlobalSections X Z (n - 1)).symm
          (HomologicalComplex.homologyMap
            (globalAmbientRationalOpenResolutionComparison X Z hZ) (n - 1) z))) =
    -((actualInjectiveSupportHomologyIsoCone X Z hZ n).inv
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
            (ambientRationalInjectiveComplex X)).g) (n - 1) z)) := by
  rw [rationalSupportAddEquivSupportedInjectiveHomology_eq_neg,
    rationalSupportAddEquivAmbientInjectiveConeGlobalSections_boundary,
    AddEquiv.apply_symm_apply]
  congr 2
  let e := asIso (HomologicalComplex.homologyMap
    (supportConeToAmbientInjectiveGlobalCone X Z hZ) (n - 1))
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  have hi : globalAmbientRationalOpenResolutionComparison X Z hZ ≫
      ((Γ.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (ambientRationalInjectiveRestriction X Z hZ)) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (ambientRationalInjectiveRestriction X Z hZ) Γ).hom) =
      CochainComplex.mappingCone.inr
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
          (ambientRationalInjectiveComplex X)).g ≫
        supportConeToAmbientInjectiveGlobalCone X Z hZ := by
    rw [CochainComplex.mappingCone.map_inr,
      actualSupportConeToAmbientInjectiveGlobalCone_inr]
  have hiH := congrArg (fun f => HomologicalComplex.homologyMap f (n - 1)) hi
  simp only [HomologicalComplex.homologyMap_comp] at hiH
  exact e.addCommGroupIsoToAddEquiv.symm_apply_eq.mpr (ConcreteCategory.congr_hom hiH z)

end AlgebraicGeometry.ComplexPoint
