import Other.AlgebraicGeometry.DerivedGlobalHypercohomologyComparison

@[expose] noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem test_rightDerivedFunctorPlusInjectiveModelIso_map_naturality
    (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex.Plus (InjectiveObject C)} (g : I ⟶ J) :
    DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map
            ((InjectiveObject.ι C).mapHomotopyCategoryPlus.map
              ((HomotopyCategory.Plus.quotient _).map g)))) ≫
      (F.rightDerivedFunctorPlusInjectiveModelIso J).hom =
    (F.rightDerivedFunctorPlusInjectiveModelIso I).hom ≫
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map
          (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom)) := by
  let K : HomotopyCategory.Plus C :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
    ((HomotopyCategory.Plus.quotient _).obj I)
  let L : HomotopyCategory.Plus C :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
    ((HomotopyCategory.Plus.quotient _).obj J)
  let qg : K ⟶ L :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient _).map g)
  have hu : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map qg) ≫
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app L) =
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app K) ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map qg) := by
    apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).1
    have hn := F.rightDerivedFunctorPlusUnit.naturality qg
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have hFg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (F.mapHomotopyCategoryPlus.map qg)) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient D (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map
              (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom))) := by
    rfl
  dsimp only [Functor.rightDerivedFunctorPlusInjectiveModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc]
  rw [hFg]
  congr 1
  exact (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).map g.hom))

end CategoryTheory.Functor

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (.of ℂ)))

local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
  [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]

def testCoefficientPlusMap (f : K ⟶ L) :
    TopCat.Sheaf.supportCoefficientPlus (TopCat.of (ComplexPoint X)) K 0 ⟶
      TopCat.Sheaf.supportCoefficientPlus (TopCat.of (ComplexPoint X)) L 0 :=
  DerivedCategory.Plus.ι.preimage (DerivedCategory.Q.map f)

@[simp]
theorem testCoefficientPlusMap_underlying (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (testCoefficientPlusMap X f) =
      DerivedCategory.Q.map f := by
  exact Functor.map_preimage _ _

theorem testCoefficientInjectiveIso_naturality (f : K ⟶ L) :
    testCoefficientPlusMap X f ≫
        (globalHypercohomologyCoefficientInjectiveIso X L).hom =
      (globalHypercohomologyCoefficientInjectiveIso X K).hom ≫
        DerivedCategory.Plus.Qh.map
          (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
            (((HomotopyCategory.Plus.quotient
              (InjectiveObject (AnalyticAdditiveSheaf X))).map
                (globalHypercohomologyInjectivePlusMap X f)))) := by
  have hg :
      DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map
            (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus).map
              (((HomotopyCategory.Plus.quotient
                (InjectiveObject (AnalyticAdditiveSheaf X))).map
                  (globalHypercohomologyInjectivePlusMap X f))))) =
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) := by
    change DerivedCategory.Plus.ι.map _ = _
    rfl
  apply (DerivedCategory.Plus.ι.map_injective)
  dsimp only [testCoefficientPlusMap,
    globalHypercohomologyCoefficientInjectiveIso]
  simp only [Functor.map_comp, Functor.map_preimage, Functor.preimageIso_hom,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  -- normalize the Qh/quotient comparison
  rw [hg]
  change
    DerivedCategory.Q.map f ≫
        DerivedCategory.Q.map (globalHypercohomologyInjectiveMap X L) ≫
          (DerivedCategory.quotientCompQhIso
            (AnalyticAdditiveSheaf X)).inv.app
              (globalHypercohomologyInjectiveComplex X L) =
      DerivedCategory.Q.map (globalHypercohomologyInjectiveMap X K) ≫
        (DerivedCategory.quotientCompQhIso
          (AnalyticAdditiveSheaf X)).inv.app
            (globalHypercohomologyInjectiveComplex X K) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (.up ℤ)).map
              (globalHypercohomologyInjectiveMapMap X f))
  have hq := (DerivedCategory.quotientCompQhIso
    (AnalyticAdditiveSheaf X)).inv.naturality
      (globalHypercohomologyInjectiveMapMap X f)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hq
  rw [← hq]
  simp only [← Category.assoc, ← Functor.map_comp,
    globalHypercohomologyInjectiveMap_comp_map]

theorem testDerivedGlobalSectionsInjectiveModelIso_naturality (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map (testCoefficientPlusMap X f)) ≫
      (derivedGlobalSectionsInjectiveModelIso X L).hom =
    (derivedGlobalSectionsInjectiveModelIso X K).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) := by
  let F := TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤
  let g := globalHypercohomologyInjectivePlusMap X f
  have hi := F.test_rightDerivedFunctorPlusInjectiveModelIso_map_naturality g
  change
    DerivedCategory.Plus.ι.map
        ((TopCat.Sheaf.derivedGlobalSections
          (TopCat.of (ComplexPoint X))).map
            (DerivedCategory.Plus.Qh.map
              ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.map
                ((HomotopyCategory.Plus.quotient
                  (InjectiveObject (AnalyticAdditiveSheaf X))).map
                    (globalHypercohomologyInjectivePlusMap X f))))) ≫
      ((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
          (globalHypercohomologyInjectivePlus X L)).hom =
    ((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) ⊤).rightDerivedFunctorPlusInjectiveModelIso
        (globalHypercohomologyInjectivePlus X K)).hom ≫
      DerivedCategory.Q.map
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) at hi
  have hc := congrArg
    (fun q => (TopCat.Sheaf.derivedGlobalSections
      (TopCat.of (ComplexPoint X))).map q)
    (testCoefficientInjectiveIso_naturality X f)
  simp only [Functor.map_comp] at hc
  dsimp only [derivedGlobalSectionsInjectiveModelIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun q => DerivedCategory.Plus.ι.map
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).map
          (globalHypercohomologyCoefficientInjectiveIso X K).hom) ≫ q) hi

set_option maxHeartbeats 800000 in
theorem testDerivedGlobalSectionsAddEquivInjectiveHomology_naturality
    (f : K ⟶ L) (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) :
    derivedGlobalSectionsAddEquivInjectiveHomology X L n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (testCoefficientPlusMap X f)) a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (globalHypercohomologyInjectiveMapMap X f)) n
        (derivedGlobalSectionsAddEquivInjectiveHomology X K n a) := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat n
  let Γg := ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
      (globalHypercohomologyInjectiveMapMap X f)
  have hm := congrArg
    (fun q => H.map q ≫
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app
        (TopCat.Sheaf.globalSectionsComplexInt
          (TopCat.of (ComplexPoint X))
            (globalHypercohomologyInjectiveComplex X L))).hom)
    (testDerivedGlobalSectionsInjectiveModelIso_naturality X f)
  simp only [Functor.map_comp, Category.assoc] at hm
  have hf := (DerivedCategory.homologyFunctorFactors
    AddCommGrpCat n).hom.naturality Γg
  have hm' := hm.trans (congrArg
    (fun q => H.map (derivedGlobalSectionsInjectiveModelIso X K).hom ≫ q) hf)
  exact ConcreteCategory.congr_hom hm' a

set_option maxHeartbeats 800000 in
theorem testDerivedGlobalSectionsAddEquivHypercohomology_naturality
    (f : K ⟶ L) (n : ℤ)
    (a : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections
        (TopCat.of (ComplexPoint X))).obj
          (TopCat.Sheaf.supportCoefficientPlus
            (TopCat.of (ComplexPoint X)) K 0))) :
    derivedGlobalSectionsAddEquivHypercohomology X L n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
          ((TopCat.Sheaf.derivedGlobalSections
            (TopCat.of (ComplexPoint X))).map
              (testCoefficientPlusMap X f)) a) =
      hypercohomologyMap X f n
        (derivedGlobalSectionsAddEquivHypercohomology X K n a) := by
  apply (hypercohomologyAddEquivInjectiveHomology X L n).injective
  dsimp only [derivedGlobalSectionsAddEquivHypercohomology,
    AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply]
  rw [testDerivedGlobalSectionsAddEquivInjectiveHomology_naturality,
    hypercohomologyAddEquivInjectiveHomology_naturality,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.ComplexPoint
