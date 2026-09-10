import Other.AlgebraicGeometry.DerivedGlobalHodgeFiltrationComparison
import Other.AlgebraicGeometry.FilteredSupportInjectiveComparison
import Other.AlgebraicGeometry.FilteredCycleComponentSupport

@[expose] noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

local instance : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamComplexInt
  infer_instance

def testRationalInjectiveToDeRhamPlusMap :
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

@[simp]
theorem testRationalInjectiveToDeRhamPlusMap_underlying :
    ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomologicalComplex
      (.up ℤ)).map (testRationalInjectiveToDeRhamPlusMap X).hom =
        rationalInjectiveToDeRham X := by
  dsimp only [testRationalInjectiveToDeRhamPlusMap,
    ambientRationalInjectivePlus,
    globalHypercohomologyInjectivePlus,
    HomologicalComplex.liftObjectProperty]
  ext n
  rfl

theorem testRationalToDeRhamCoefficientInjectiveIso_naturality :
    rationalToHolomorphicDeRhamPlus X ≫
        (globalHypercohomologyCoefficientInjectiveIso X
          (holomorphicDeRhamComplexInt X)).hom =
      (constantRationalToInjectiveDerivedPlusIso X).hom ≫
        DerivedCategory.Plus.Qh.map
          (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
            (((HomotopyCategory.Plus.quotient
              (InjectiveObject (AnalyticAdditiveSheaf X))).map
                (testRationalInjectiveToDeRhamPlusMap X)))) := by
  have hg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
              (((HomotopyCategory.Plus.quotient
                (InjectiveObject (AnalyticAdditiveSheaf X))).map
                  (testRationalInjectiveToDeRhamPlusMap X))))) =
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

@[reassoc]
theorem testDerivedRationalToDeRhamInjectiveModelIso_naturality :
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
  let g := testRationalInjectiveToDeRhamPlusMap X
  have hi := F.rightDerivedFunctorPlusInjectiveModelIso_map_naturality g
  change
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (DerivedCategory.Plus.Qh.map
              ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.map
                ((HomotopyCategory.Plus.quotient
                  (InjectiveObject (AnalyticAdditiveSheaf X))).map
                    (testRationalInjectiveToDeRhamPlusMap X))))) ≫
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
    (testRationalToDeRhamCoefficientInjectiveIso_naturality X)
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

theorem testRationalToDeRhamInjectiveHomology_naturality
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

def testDerivedRationalGlobalAddEquivAmbientInjectiveHomology (n : ℤ) :
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

theorem testDerivedRationalToDeRhamInjectiveHomology_naturality
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
        (testDerivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) := by
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
    (testDerivedRationalToDeRhamInjectiveModelIso_naturality X)
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

theorem testDerivedRationalToPublicDeRham_naturality
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
          (testDerivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) :=
      testDerivedRationalToDeRhamInjectiveHomology_naturality X n a
    _ = HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
              (rationalInjectiveToDeRham X)) n
          (rationalCohomologyAddEquivAmbientInjectiveHomology X n
            (derivedRationalCohomologyAddEquiv X n a)) := by
      congr 1
      exact (rationalCohomologyAddEquivAmbientInjectiveHomology X n).apply_symm_apply
        (testDerivedRationalGlobalAddEquivAmbientInjectiveHomology X n a) |>.symm
    _ = _ := (testRationalToDeRhamInjectiveHomology_naturality X n
      (derivedRationalCohomologyAddEquiv X n a)).symm

theorem testRationalSupportedToPublicDeRham_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ)
    (a : RationalCohomologyWithSupport X Z n) :
    derivedGlobalDeRhamAddEquivHypercohomology X n
        (supportedDeRhamForgetSupport X Z n
          (rationalSupportedToDeRhamCohomology X Z n a)) =
      fieldToDeRhamCohomology ℚ X n (forgetSupport X Z n a) := by
  rw [rationalSupportedToDeRhamCohomology_forgetSupport]
  rw [testDerivedRationalToPublicDeRham_naturality,
    AddEquiv.apply_symm_apply]

variable [IsProjective X.hom]
  (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

theorem testCycleComponentSupportedDeRhamClass_forget_toPublic :
    derivedGlobalDeRhamAddEquivHypercohomology X (2 * (p : ℤ))
        (supportedDeRhamForgetSupport X
          (cycleComponentAnalyticClosedSupport X x) (2 * (p : ℤ))
            (cycleComponentSupportedDeRhamClass X x (d := d) hx)) =
      fieldToDeRhamCohomology ℚ X (2 * (p : ℤ))
        (cycleComponentSheafClass X x (d := d) hx) := by
  rw [cycleComponentSupportedDeRhamClass]
  rw [testRationalSupportedToPublicDeRham_forgetSupport]
  rw [cycleComponentSheafClass_eq_forgetSupport]
  rfl

theorem testCycleComponentSheafClass_isHodge_of_supported
    (h : cycleComponentSupportedDeRhamClass X x (d := d) hx ∈
      supportedHodgeFiltration X (cycleComponentAnalyticClosedSupport X x)
        (p : ℤ) (2 * (p : ℤ))) :
    IsHodgeClass ℚ X p (cycleComponentSheafClass X x (d := d) hx) := by
  change fieldToDeRhamCohomology ℚ X (2 * (p : ℤ))
      (cycleComponentSheafClass X x (d := d) hx) ∈
        hodgeFiltration X (p : ℤ) (2 * (p : ℤ))
  rw [← testCycleComponentSupportedDeRhamClass_forget_toPublic
    X x (d := d) hx]
  exact derivedGlobalFilteredRange_mem_hodgeFiltration X p (2 * (p : ℤ))
    (cycleComponentSupportedDeRhamClass_forget_mem_globalFilteredRange
      X x (d := d) hx h)

end AlgebraicGeometry.ComplexPoint
