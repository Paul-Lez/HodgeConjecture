/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RawComplementResolutionComparison
public import Other.AlgebraicGeometry.SupportedInjectiveBoundaryNormalization
public import Other.Algebra.Homology.DerivedCategory.MappingCoconeBoundaryNaturality

/-!
# Literal raw complement boundaries in actual supported singular sections

The fixed rational support comparison sends a raw complement boundary to minus
its canonical supported-singular kernel boundary under the actual injective
comparison. This proves the support-model transport without assuming a winding
or divisor formula. Restriction to local relative charts is a separate step.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)

local instance actualSingularSupportOpenParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- The positive cone comparison for actual supported singular sections on the top open. -/
def actualSingularSupportHomologyIsoCone (n : ℤ) :
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.homology n ≅
    (CochainComplex.mappingCone
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g).homology (n - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone _
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ _ (fun _ => inferInstance))
    (n - 1) n (by omega)

/-- Actual outside sections of the prescribed singular-to-ambient-injective map. -/
def actualSingularToInjectiveOutside :
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃ ⟶
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (ambientRationalInjectiveComplex X)).X₃ :=
  (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).map
    (((TopCat.Sheaf.openRestrictionPushforward (TopCat.of (ComplexPoint X))
      ⟨Zᶜ, hZ.isOpen_compl⟩).mapHomologicalComplex (.up ℤ)).map
        (complexSingularToAmbientInjective X)))

omit [IsProjective X.hom] in
lemma actualSingularToInjectiveOutside_comp_resolution :
    actualSingularToInjectiveOutside X Z hZ ≫
      globalAmbientRationalOpenResolutionComparison X Z hZ =
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).map (ambientSingularOutsideResolutionComparison X Z hZ)) := by
  change _ = (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤
    |>.mapHomologicalComplex (.up ℤ)).map (_ ≫ _)
  rw [Functor.map_comp]
  rfl

/-- The actual singular-to-injective supported comparison preserves canonical kernel boundaries. -/
lemma actualSingularSupportBoundary_comp_injective (n : ℤ)
    (z : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₃.homology (n - 1)) :
    (actualInjectiveSupportHomologyIsoCone X Z hZ n).inv
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
            (ambientRationalInjectiveComplex X)).g) (n - 1)
        (HomologicalComplex.homologyMap (actualSingularToInjectiveOutside X Z hZ) (n - 1) z)) =
    (complexSupportedSingularInjectiveHomologyIso X ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ n).hom
      ((actualSingularSupportHomologyIsoCone X Z hZ n).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
              (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
              (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g) (n - 1) z)) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := (TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)
  let f := Γ.mapShortComplex.map
    (TopCat.Sheaf.supportRestrictionComplexShortComplexMap Y U (complexSingularToAmbientInjective X))
  have hn := CochainComplex.mappingCocone.shortExactHomologyIsoCone_inv_inr_naturality f
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
      Y U ⊤ _ (fun _ => inferInstance))
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
    (n - 1) n (by omega)
  exact (ConcreteCategory.congr_hom hn z).symm

/-- A literal raw complement boundary in the fixed rational support model maps to
minus its canonical supported-singular boundary under the actual injective comparison. -/
lemma coneSupportAddEquivSupportedInjectiveHomology_raw_boundary (n : ℤ)
    (z : (globalRawPushforwardSingularCochainComplexInt ℚ
      (TopCat.of (ComplexPoint X)) Zᶜ).homology (n - 1)) :
    coneSupportAddEquivSupportedInjectiveHomology X Z hZ n
      (hypercohomologyMap X
        (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X Z)) (n - 1)
        ((complementRationalHypercohomologyAddEquivGlobalSections X Z (n - 1)).symm
          (HomologicalComplex.homologyMap
            (globalRawComplementToDerivedPushforwardInt X Z hZ) (n - 1) z))) =
    -((complexSupportedSingularInjectiveHomologyIso X ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤ n).hom
      ((actualSingularSupportHomologyIsoCone X Z hZ n).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
              (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
              (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g) (n - 1)
          (HomologicalComplex.homologyMap
            (globalRawComplementToActualSingularOutside X Z hZ) (n - 1) z)))) := by
  have hm := globalRawComplementToActualSingularOutside_comp_ambient_homologyMap X Z hZ (n - 1)
  rw [← actualSingularToInjectiveOutside_comp_resolution,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hm
  have hz := ConcreteCategory.congr_hom hm z
  simp only [ConcreteCategory.comp_apply] at hz
  erw [← hz, coneSupportAddEquivSupportedInjectiveHomology_boundary,
    actualSingularSupportBoundary_comp_injective]

end AlgebraicGeometry.ComplexPoint
