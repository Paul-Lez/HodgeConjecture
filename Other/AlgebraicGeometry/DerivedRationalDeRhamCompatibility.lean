/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedGlobalHodgeFiltrationComparison
public import Other.AlgebraicGeometry.FilteredSupportInjectiveComparison
public import Other.AlgebraicGeometry.FilteredCycleComponentSupport

/-!
# Rational coefficient comparison for actual and public de Rham cohomology

The standard ambient rational injective resolution maps strictly to the fixed
injective model of the holomorphic de Rham complex.  This file proves that the
resulting map on actual derived global sections agrees with the public
`fieldToDeRhamCohomology` map under the canonical comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance derivedRationalDeRhamCompatibilityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance derivedRationalDeRhamCompatibilityHasDerivedCategoryAddCommGrp :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

local instance : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamComplexInt
  infer_instance

/-- The normalized strict rational-to-de Rham lift, bundled between the two
bounded-below injective models. -/
def rationalInjectiveToDeRhamPlusMap :
    ambientRationalInjectivePlus X ⟶
      globalHypercohomologyInjectivePlus X (holomorphicDeRhamComplexInt X) := by
  let g := rationalInjectiveToDeRham X
  refine ObjectProperty.homMk ?_
  dsimp only [ambientRationalInjectivePlus,
    globalHypercohomologyInjectivePlus,
    HomologicalComplex.liftObjectProperty]
  exact
    { f := fun n ↦ ObjectProperty.homMk (g.f n)
      comm' := fun i j _ ↦ by
        apply ObjectProperty.hom_ext
        exact g.comm i j }

/-- Forgetting the bounded-below injective-object wrapper recovers the strict
rational-to-de Rham map. -/
@[simp]
theorem rationalInjectiveToDeRhamPlusMap_underlying :
    ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomologicalComplex
      (.up ℤ)).map (rationalInjectiveToDeRhamPlusMap X).hom =
        rationalInjectiveToDeRham X := by
  dsimp only [rationalInjectiveToDeRhamPlusMap,
    ambientRationalInjectivePlus,
    globalHypercohomologyInjectivePlus,
    HomologicalComplex.liftObjectProperty]
  ext n
  rfl

/-- The rational coefficient map commutes with the two chosen augmentations
and the localization comparison. -/
theorem rationalToDeRhamCoefficientInjectiveIso_naturality :
    rationalToHolomorphicDeRhamPlus X ≫
        (globalHypercohomologyCoefficientInjectiveIso X
          (holomorphicDeRhamComplexInt X)).hom =
      (constantRationalToInjectiveDerivedPlusIso X).hom ≫
        DerivedCategory.Plus.Qh.map
          (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
            (((HomotopyCategory.Plus.quotient
              (InjectiveObject (AnalyticAdditiveSheaf X))).map
                (rationalInjectiveToDeRhamPlusMap X)))) := by
  have hg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
              (((HomotopyCategory.Plus.quotient
                (InjectiveObject (AnalyticAdditiveSheaf X))).map
                  (rationalInjectiveToDeRhamPlusMap X))))) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
            (rationalInjectiveToDeRham X)) := by
    rfl
  apply (DerivedCategory.Plus.ι.map_injective)
  dsimp only [rationalToHolomorphicDeRhamPlus,
    globalHypercohomologyCoefficientInjectiveIso,
    constantRationalToInjectiveDerivedPlusIso]
  simp only [Functor.map_comp, Functor.map_preimage, Functor.preimageIso_hom,
    Iso.trans_hom, Category.assoc]
  rw [hg]
  change
    (DerivedCategory.singleFunctorIsoCompQ
        (AnalyticAdditiveSheaf X) 0).hom.app (constantFieldSheaf ℚ X) ≫
      DerivedCategory.Q.map (constantRationalSheafComplexIntIsoSingleZero X).inv ≫
      DerivedCategory.Q.map (fieldToHolomorphicDeRhamComplexInt ℚ X) ≫
      DerivedCategory.Q.map (globalHypercohomologyInjectiveMap X
        (holomorphicDeRhamComplexInt X)) ≫
      (DerivedCategory.quotientCompQhIso
        (AnalyticAdditiveSheaf X)).inv.app
          (globalHypercohomologyInjectiveComplex X
            (holomorphicDeRhamComplexInt X)) =
    (DerivedCategory.singleFunctorIsoCompQ
        (AnalyticAdditiveSheaf X) 0).hom.app (constantFieldSheaf ℚ X) ≫
      DerivedCategory.Q.map (constantRationalSheafComplexIntIsoSingleZero X).inv ≫
      DerivedCategory.Q.map (ambientRationalInjectiveAugmentation X) ≫
      (DerivedCategory.quotientCompQhIso
        (AnalyticAdditiveSheaf X)).inv.app
          (ambientRationalInjectiveComplex X) ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
          (rationalInjectiveToDeRham X))
  have hq := (DerivedCategory.quotientCompQhIso
    (AnalyticAdditiveSheaf X)).inv.naturality
      (rationalInjectiveToDeRham X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hq
  rw [← hq]
  simp only [← Category.assoc, ← Functor.map_comp,
    ambientRationalInjectiveAugmentation_comp_toDeRham]

/-- The actual derived-global injective-model comparisons intertwine the
rational-to-de Rham map with its strict lift. -/
@[reassoc]
theorem derivedRationalToDeRhamInjectiveModelIso_naturality :
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (rationalToHolomorphicDeRhamPlus X)) ≫
      (derivedGlobalSectionsInjectiveModelIso X
        (holomorphicDeRhamComplexInt X)).hom =
    (derivedRationalGlobalInjectiveModelIso X).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (rationalInjectiveToDeRham X)) := by
  let F := TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤
  let g := rationalInjectiveToDeRhamPlusMap X
  have hi := F.rightDerivedFunctorPlusInjectiveModelIso_map_naturality g
  change
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (DerivedCategory.Plus.Qh.map
              ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.map
                ((HomotopyCategory.Plus.quotient
                  (InjectiveObject (AnalyticAdditiveSheaf X))).map
                    (rationalInjectiveToDeRhamPlusMap X))))) ≫
      ((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
          (globalHypercohomologyInjectivePlus X
            (holomorphicDeRhamComplexInt X))).hom =
    ((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
        (ambientRationalInjectivePlus X)).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (rationalInjectiveToDeRham X)) at hi
  have hc := congrArg
    (fun q => (TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).map q)
    (rationalToDeRhamCoefficientInjectiveIso_naturality X)
  simp only [Functor.map_comp] at hc
  dsimp only [derivedGlobalSectionsInjectiveModelIso,
    derivedRationalGlobalInjectiveModelIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun q => DerivedCategory.Plus.ι.map
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).map
          (constantRationalToInjectiveDerivedPlusIso X).hom) ≫ q) hi

/-- On public hypercohomology, the rational-to-de Rham map is computed by the
strict map between the ambient rational and de Rham injective models. -/
theorem rationalToDeRhamInjectiveHomology_naturality
    (n : ℤ) (a : FieldCohomology ℚ X n) :
    hypercohomologyAddEquivInjectiveHomology X
        (holomorphicDeRhamComplexInt X) n
          (fieldToDeRhamCohomology ℚ X n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (rationalInjectiveToDeRham X)) n
        (rationalCohomologyAddEquivAmbientInjectiveHomology X n a) := by
  change hypercohomologyAddEquivGlobalSectionsKInjective X
      (globalHypercohomologyInjectiveComplex X
        (holomorphicDeRhamComplexInt X)) n
      (hypercohomologyMap X
        (globalHypercohomologyInjectiveMap X
          (holomorphicDeRhamComplexInt X)) n
        (hypercohomologyMap X
          (fieldToHolomorphicDeRhamComplexInt ℚ X) n a)) =
    (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
          (rationalInjectiveToDeRham X)) n).hom
      (hypercohomologyAddEquivGlobalSectionsKInjective X
        (ambientRationalInjectiveComplex X) n
          (hypercohomologyMap X
            (ambientRationalInjectiveAugmentation X) n a))
  rw [← hypercohomologyMap_comp_apply,
    ← ambientRationalInjectiveAugmentation_comp_toDeRham,
    hypercohomologyMap_comp_apply]
  exact hypercohomologyAddEquivGlobalSectionsKInjective_naturality X
    (ambientRationalInjectiveComplex X)
    (globalHypercohomologyInjectiveComplex X
      (holomorphicDeRhamComplexInt X))
    (rationalInjectiveToDeRham X) n
    (hypercohomologyMap X (ambientRationalInjectiveAugmentation X) n a)

/-- Actual derived rational cohomology computed on the standard ambient
rational injective resolution. -/
def derivedRationalGlobalAddEquivAmbientInjectiveHomology (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          ((DerivedCategory.Plus.singleFunctor
            (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X)))) ≃+
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
          (ambientRationalInjectiveComplex X)).homology n :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (derivedRationalGlobalInjectiveModelIso X) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _)
      |>.addCommGroupIsoToAddEquiv

/-- On actual derived global sections, rational-to-de Rham comparison is
computed by the same strict map of injective models. -/
theorem derivedRationalToDeRhamInjectiveHomology_naturality
    (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          ((DerivedCategory.Plus.singleFunctor
            (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X)))) :
    derivedGlobalSectionsAddEquivInjectiveHomology X
        (holomorphicDeRhamComplexInt X) n
          (derivedRationalToGlobalDeRhamCohomology X n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (rationalInjectiveToDeRham X)) n
        (derivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat n
  let Γg := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
      (rationalInjectiveToDeRham X)
  have hm := congrArg
    (fun q => H.map q ≫
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (globalHypercohomologyInjectiveComplex X
              (holomorphicDeRhamComplexInt X)))).hom)
    (derivedRationalToDeRhamInjectiveModelIso_naturality X)
  simp only [Functor.map_comp, Category.assoc] at hm
  have hf := (DerivedCategory.homologyFunctorFactors
    AddCommGrpCat n).hom.naturality Γg
  have hm' := hm.trans (congrArg
    (fun q => H.map (derivedRationalGlobalInjectiveModelIso X).hom ≫ q) hf)
  change
    ConcreteCategory.hom
      (H.map (DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (rationalToHolomorphicDeRhamPlus X))) ≫
       H.map (derivedGlobalSectionsInjectiveModelIso X
        (holomorphicDeRhamComplexInt X)).hom ≫
       ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (globalHypercohomologyInjectiveComplex X
              (holomorphicDeRhamComplexInt X)))).hom) a =
    ConcreteCategory.hom
      (H.map (derivedRationalGlobalInjectiveModelIso X).hom ≫
       ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (ambientRationalInjectiveComplex X))).hom ≫
       (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map Γg) a
  exact ConcreteCategory.congr_hom hm' a

/-- The actual derived rational-to-de Rham map agrees exactly with the public
`fieldToDeRhamCohomology` map under the canonical additive equivalences. -/
theorem derivedRationalToPublicDeRham_naturality
    (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          ((DerivedCategory.Plus.singleFunctor
            (AnalyticAdditiveSheaf X) 0).obj
              (constantFieldSheaf ℚ X)))) :
    derivedGlobalDeRhamAddEquivHypercohomology X n
        (derivedRationalToGlobalDeRhamCohomology X n a) =
      fieldToDeRhamCohomology ℚ X n
        (derivedRationalCohomologyAddEquiv X n a) := by
  apply (hypercohomologyAddEquivInjectiveHomology X
    (holomorphicDeRhamComplexInt X) n).injective
  dsimp only [derivedGlobalDeRhamAddEquivHypercohomology,
    derivedGlobalSectionsAddEquivHypercohomology, AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply]
  calc
    _ = HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
              (rationalInjectiveToDeRham X)) n
          (derivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) :=
      derivedRationalToDeRhamInjectiveHomology_naturality X n a
    _ = HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
              (rationalInjectiveToDeRham X)) n
          (rationalCohomologyAddEquivAmbientInjectiveHomology X n
            (derivedRationalCohomologyAddEquiv X n a)) := by
      congr 1
      exact (rationalCohomologyAddEquivAmbientInjectiveHomology X n).apply_symm_apply
        (derivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) |>.symm
    _ = _ := (rationalToDeRhamInjectiveHomology_naturality X n
      (derivedRationalCohomologyAddEquiv X n a)).symm

/-- For a rational class with closed support, coefficient comparison followed
by forgetting support becomes the public rational-to-de Rham map applied to
the public support-forgetting class. -/
theorem rationalSupportedToPublicDeRham_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    derivedGlobalDeRhamAddEquivHypercohomology X n
        (supportedDeRhamForgetSupport X Z n
          (rationalSupportedToDeRhamCohomology X Z n a)) =
      fieldToDeRhamCohomology ℚ X n (forgetSupport X Z n a) := by
  rw [rationalSupportedToDeRhamCohomology_forgetSupport]
  rw [derivedRationalToPublicDeRham_naturality,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.ComplexPoint
