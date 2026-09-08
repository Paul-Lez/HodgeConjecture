/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusInjectiveModel
public import HodgeConjecture.Other.AlgebraicTopology.DerivedSheafSupportForget
public import HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalComparison
public import HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalConeForget

/-! # The actual derived support-forgetting square for rational coefficients -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

local instance derivedRationalForgetSheafCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

local instance derivedRationalForgetGroupCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual derived global sections of rational constants, computed using
the standard ambient rational resolution and the actual derived unit. -/
def derivedRationalGlobalInjectiveModelIso :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X structureMap))).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap))) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X structureMap))
        (ambientRationalInjectiveComplex structureMap)) :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X structureMap))).mapIso
      (constantRationalToInjectiveDerivedPlusIso structureMap)) ≪≫
    Functor.rightDerivedFunctorPlusInjectiveModelIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X structureMap)) ⊤)
      (ambientRationalInjectivePlus structureMap)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical ordinary-cohomology counterpart of the supported
comparison, with the actual rational augmentation normalization. -/
def derivedRationalCohomologyAddEquiv (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X structureMap))).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap)))) ≃+
      FieldCohomology ℚ structureMap n :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
    (derivedRationalGlobalInjectiveModelIso structureMap) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _).addCommGroupIsoToAddEquiv).trans
    (rationalCohomologyAddEquivAmbientInjectiveHomology structureMap n).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma derivedRationalSupportInjectiveModelIso_forget
    (Z : Closeds (TopCat.of (ComplexPoint X structureMap))) :
    DerivedCategory.Plus.ι.map
      ((TopCat.Sheaf.derivedForgetClosedSupport (TopCat.of (ComplexPoint X structureMap)) Z).app
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap))) ≫
      (derivedRationalGlobalInjectiveModelIso structureMap).hom =
    (derivedRationalSupportInjectiveModelIso structureMap Z).hom ≫
      DerivedCategory.Q.map
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X structureMap)) Z.compl ⊤
          (ambientRationalInjectiveComplex structureMap)).f := by
  let Y := TopCat.of (ComplexPoint X structureMap)
  let I := ambientRationalInjectivePlus structureMap
  have hi := NatTrans.rightDerivedFunctorPlusInjectiveModel_naturality
    (TopCat.Sheaf.closedSupportSectionsInclusion Y Z) I
  have hm : ((TopCat.Sheaf.closedSupportSectionsInclusion Y Z).mapHomologicalComplex
      (.up ℤ)).app
        (((InjectiveObject.ι (AnalyticAdditiveSheaf structureMap)).mapHomologicalComplex
          (.up ℤ)).obj I.obj) =
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
        (ambientRationalInjectiveComplex structureMap)).f := by
    ext n
    simp [TopCat.Sheaf.closedSupportSectionsInclusion,
      TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex,
      TopCat.Sheaf.supportRestrictionComplexShortComplex]
    rfl
  rw [hm] at hi
  have hn := (TopCat.Sheaf.derivedForgetClosedSupport Y Z).naturality
    (constantRationalToInjectiveDerivedPlusIso structureMap).hom
  dsimp only [derivedRationalGlobalInjectiveModelIso,
    derivedRationalSupportInjectiveModelIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]
  exact congrArg (fun f => DerivedCategory.Plus.ι.map
    ((TopCat.Sheaf.derivedClosedSupportSections Y Z).map
      (constantRationalToInjectiveDerivedPlusIso structureMap).hom) ≫ f) hi

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- The actual `D⁺` support-forgetting inclusion agrees with the repository's
existing `forgetSupport`, under the constructed supported and ordinary
rational comparisons. Both the derived-unit square and the cone signs are
proved, with no supplied compatibility input. -/
lemma derivedRationalSupportAddEquiv_forgetSupport
    (Z : Closeds (TopCat.of (ComplexPoint X structureMap))) (n : ℤ)
    (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X structureMap)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
          (constantFieldSheaf ℚ structureMap)))) :
    derivedRationalCohomologyAddEquiv structureMap n
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedForgetClosedSupport (TopCat.of (ComplexPoint X structureMap)) Z).app
          ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
            (constantFieldSheaf ℚ structureMap))) x) =
    forgetSupport structureMap Z n (derivedRationalSupportAddEquiv structureMap Z n x) := by
  let Y := TopCat.of (ComplexPoint X structureMap)
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
    (ambientRationalInjectiveComplex structureMap)
  let H := DerivedCategory.homologyFunctor AddCommGrpCat n
  have hm := congrArg (fun f => H.map f ≫
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₂).hom)
    (derivedRationalSupportInjectiveModelIso_forget structureMap Z)
  simp only [Functor.map_comp, Category.assoc] at hm
  have hf := (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).hom.naturality S.f
  have hm' := hm.trans (congrArg
    (fun f => H.map (derivedRationalSupportInjectiveModelIso structureMap Z).hom ≫ f) hf)
  let eS := (H.mapIso (derivedRationalSupportInjectiveModelIso structureMap Z) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₁).addCommGroupIsoToAddEquiv
  let eG := (H.mapIso (derivedRationalGlobalInjectiveModelIso structureMap) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₂).addCommGroupIsoToAddEquiv
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology structureMap n).injective
  calc
    _ = eG ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedForgetClosedSupport Y Z).app
          ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf structureMap) 0).obj
            (constantFieldSheaf ℚ structureMap))) x) :=
      (rationalCohomologyAddEquivAmbientInjectiveHomology structureMap n).apply_symm_apply _
    _ = HomologicalComplex.homologyMap S.f n (eS x) :=
      ConcreteCategory.congr_hom hm' x
    _ = _ := by
      rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
        structureMap Z Z.isClosed n]
      exact congrArg (fun y => HomologicalComplex.homologyMap S.f n y)
        (AddEquiv.apply_symm_apply
          (rationalSupportAddEquivSupportedInjectiveHomology structureMap Z Z.isClosed n)
          (eS x)).symm

end AlgebraicGeometry.ComplexPoint
