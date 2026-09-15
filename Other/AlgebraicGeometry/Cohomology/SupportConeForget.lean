/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeForget
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import Other.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyShift
public import Other.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel

/-!
# Support-forgetting in the rational injective model

The comparisons below express support-forgetting through the concrete ambient injective
resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

attribute [local instance] rationalConeForgetSheafDerivedCategory

local instance supportConeForgetHasDerivedCategoryAddCommGrpCat :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- Ordinary rational cohomology computed by the ambient rational injective resolution. -/
def rationalCohomologyAddEquivAmbientInjectiveHomology (n : ℤ) :
    H^n(X; ℚ) ≃+
      (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology n :=
  (TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective AddCommGrpCat
    (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveAugmentationPlus X)
    n).addCommGroupIsoToAddEquiv

/-- The ambient injective-resolution comparison carries the derived unit to the map on the
cohomology of complexes of global sections. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_toHypercohomology
    (n : ℤ)
    (x : (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
      (TopCat.of (ComplexPoint X))
      (constantFieldSheafComplexIntPlus ℚ X).obj).homology n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
        (((TopCat.Sheaf.toHypercohomology AddCommGrpCat
          (TopCat.of (ComplexPoint X)) n).app
          (constantFieldSheafComplexIntPlus ℚ X)).hom x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (ambientRationalInjectiveAugmentation X)) n x :=
  ConcreteCategory.congr_hom
    (TopCat.Sheaf.toHypercohomology_hypercohomologyIsoOfQuasiIsoToInjective_hom
      AddCommGrpCat (TopCat.of (ComplexPoint X))
      (ambientRationalInjectiveAugmentationPlus X) n) x

/-- The map from the shifted ambient support cone to the ambient injective resolution. -/
def ambientRationalInjectiveForgetSupportComplex
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (ambientRationalInjectiveConePlus X Z hZ).obj ⟶ ambientRationalInjectiveComplex X :=
  ((CochainComplex.mappingCone.triangle
      (ambientRationalInjectiveRestriction X Z hZ)).mor₃)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Replacing constants and the support cone by their ambient injective models commutes with
forgetting support. -/
lemma rationalSupportConeToAmbientInjectiveConePlus_forgetSupport
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    (rationalSupportConeToAmbientInjectiveConePlus X Z hZ).hom ≫
        ambientRationalInjectiveForgetSupportComplex X Z hZ =
      forgetSupportComplex X Z ≫ ambientRationalInjectiveAugmentation X := by
  dsimp only [rationalSupportConeToAmbientInjectiveConePlus,
    ambientRationalInjectiveForgetSupportComplex, forgetSupportComplex]
  rw [← Category.assoc, ← Functor.map_comp,
    rationalSupportConeToAmbientInjectiveCone_connecting]
  rw [Functor.map_comp, Category.assoc]
  exact congrArg (fun k =>
    (shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) (-1)).map
      (CochainComplex.mappingCone.triangle
        (rationalRestrictionComplexInt X Z)).mor₃ ≫ k) <|
    by simpa only [Functor.comp_map, Functor.id_map] using
      (shiftFunctorCompIsoId (CochainComplex (AnalyticAdditiveSheaf X) ℤ)
        (1 : ℤ) (-1) (by simp)).hom.naturality (ambientRationalInjectiveAugmentation X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The injective-complex comparison carries a commutative square to the corresponding square
on hypercohomology and the cohomology of the complexes of global sections. -/
private lemma hypercohomologyIsoOfInjective_hom_naturality_of_comm
    {A B I J : CochainComplex.Plus (AnalyticAdditiveSheaf X)}
    [∀ i, Injective (I.obj.X i)] [∀ i, Injective (J.obj.X i)]
    (a : A ⟶ I) (b : B ⟶ J) (g : A ⟶ B) (h : I ⟶ J)
    (sq : g ≫ b = a ≫ h) (n : ℤ) :
    (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map g ≫
        (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map b ≫
        (TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat
          (TopCat.of (ComplexPoint X)) J n).hom =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map a ≫
        (TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat
          (TopCat.of (ComplexPoint X)) I n).hom ≫
        HomologicalComplex.homologyMap
          (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map h.hom) n := by
  rw [← Category.assoc, ← Functor.map_comp, sq, Functor.map_comp, Category.assoc]
  exact congrArg
    (fun k => (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map a ≫ k)
    (TopCat.Sheaf.hypercohomologyIsoOfInjective_hom_naturality
      AddCommGrpCat (TopCat.of (ComplexPoint X)) h n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the injective-model comparison for the support-forgetting square. -/
private lemma rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_naturality
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
        (forgetSupport X Z n x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n
        ((TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat
          (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveConePlus X Z hZ) n).hom
          ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
            (rationalSupportConeToAmbientInjectiveConePlus X Z hZ) x)) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let Γc := Γ.mapHomologicalComplex (.up ℤ)
  let F := ℍ[AddCommGrpCat]^n(Y)
  let A := constantFieldSheafComplexIntPlus ℚ X
  let I := ambientRationalInjectiveConePlus X Z hZ
  let J : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
    ⟨ambientRationalInjectiveComplex X, ⟨0, inferInstance⟩⟩
  let f := rationalSupportConeToAmbientInjectiveConePlus X Z hZ
  let g : rationalCohomologyWithSupportComplexPlus X Z ⟶ A :=
    ⟨forgetSupportComplex X Z⟩
  let a : A ⟶ J := ⟨ambientRationalInjectiveAugmentation X⟩
  let h : I ⟶ J := ⟨ambientRationalInjectiveForgetSupportComplex X Z hZ⟩
  let eI := TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y I n
  let eJ := TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y J n
  change eJ.hom (F.map a (F.map g x)) =
    HomologicalComplex.homologyMap (Γc.map h.hom) n (eI.hom (F.map f x))
  have hs : g ≫ a = f ≫ h := by
    apply ObjectProperty.hom_ext
    exact (rationalSupportConeToAmbientInjectiveConePlus_forgetSupport X Z hZ).symm
  exact ConcreteCategory.congr_hom
    (hypercohomologyIsoOfInjective_hom_naturality_of_comm X f a g h hs n) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unshifted cone morphism induces the connecting map after applying global sections. -/
private lemma globalSectionsAmbientRationalInjectiveForgetSupport_apply
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (y : ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).obj
        (ambientRationalInjectiveConePlus X Z hZ).obj |>.homology n) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n y =
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (ShiftedHom.map
          (CochainComplex.mappingCone.triangle
            (ambientRationalInjectiveRestriction X Z hZ)).mor₃
          ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)))
        (n - 1) n (by omega)
        ((let Γc := (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)
          let C := (CochainComplex.mappingCone.triangle
            (ambientRationalInjectiveRestriction X Z hZ)).obj₃
          let G := Γc.obj C
          let e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
              ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
            HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
          let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
              (-1) n (n - 1) (by omega)).app G
          (e₃ ≪≫ e₄).hom) y) := by
  let Γc := (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)
  let T := CochainComplex.mappingCone.triangle
    (ambientRationalInjectiveRestriction X Z hZ)
  let C := T.obj₃
  let f := T.mor₃
  let G := Γc.obj C
  let e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
  let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  change HomologicalComplex.homologyMap
      (Γc.map (f⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app T.obj₁)) n y =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map f Γc) (n - 1) n (by omega) ((e₃ ≪≫ e₄).hom y)
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.HomologyFunctor.map_rightUnshift Γc f n) y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the ambient injective model, forgetting support is the connecting homology map of the
restriction cone. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
      (forgetSupport X Z n x) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map
        (CochainComplex.mappingCone.triangle
          (ambientRationalInjectiveRestriction X Z hZ)).mor₃
        ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)))
      (n - 1) n (by omega)
      (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x) := by
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_naturality X Z hZ n]
  let Γc := (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)
  let C := (CochainComplex.mappingCone.triangle
    (ambientRationalInjectiveRestriction X Z hZ)).obj₃
  let G := Γc.obj C
  let e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
  let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  change HomologicalComplex.homologyMap
      (Γc.map (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n _ =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map
        (CochainComplex.mappingCone.triangle
          (ambientRationalInjectiveRestriction X Z hZ)).mor₃ Γc)
      (n - 1) n (by omega) ((e₃ ≪≫ e₄).hom _)
  exact globalSectionsAmbientRationalInjectiveForgetSupport_apply X Z hZ n _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison between the two global-section cones intertwines their connecting maps. -/
private lemma ambientRationalInjectiveGlobalCone_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
    let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
      (ambientRationalInjectiveComplex X)
    let b := ambientRationalInjectiveRestriction X Z hZ
    let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
    inv (HomologicalComplex.homologyMap c (n - 1)) ≫
        H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃
          (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃
          (n - 1) n (by omega) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  dsimp only
  have hc : HomologicalComplex.homologyMap c (n - 1) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃ (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) := by
    change (H.shift (n - 1)).map c ≫ _ = _
    rw [← Functor.shiftMap_comp', actualSupportConeToAmbientInjectiveGlobalCone_connecting]
  rw [← hc, IsIso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The shifted-lift comparison identifies the cone connecting map with the negated inclusion
from its first term. -/
private lemma mappingCocone_shiftedLift_connecting_apply
    (S : ShortComplex (CochainComplex AddCommGrpCat ℤ))
    (hS : S.ShortExact)
    (n : ℤ) (z : (CochainComplex.mappingCone S.g).homology (n - 1)) :
    letI := CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S hS
    HomologicalComplex.homologyMap S.f n
        (-((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
          1 (n - 1) n (by omega)).hom.app S.X₁
          ((inv (HomologicalComplex.homologyMap
            (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1))) z)) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) z := by
  let _ := CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S hS
  rw [map_neg]
  change ((-(inv (HomologicalComplex.homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)) ≫
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
      1 (n - 1) n (by omega)).hom.app S.X₁ ≫
    HomologicalComplex.homologyMap S.f n)) : _ ⟶ _) z = _
  exact ConcreteCategory.congr_hom
    (CochainComplex.mappingCocone.inv_homologyMap_shiftedLiftShortComplex_connecting
      S hS (n - 1) n (by omega)) z

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The connecting map of the ambient global-section cone agrees with the inclusion of the
supported-sections model. -/
private lemma ambientRationalInjectiveCone_connecting_eq_supportedSections
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (y : (TopCat.Sheaf.globalSectionsComplex AddCommGrpCat
      (TopCat.of (ComplexPoint X))
      (CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X Z hZ))).homology (n - 1)) :
    let Y := TopCat.of (ComplexPoint X)
    let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
    let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
      (ambientRationalInjectiveComplex X)
    letI : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
      CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
    let b := ambientRationalInjectiveRestriction X Z hZ
    let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
    let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
    H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
        (Γ.mapHomologicalComplex (.up ℤ))) (n - 1) n (by omega) y =
      HomologicalComplex.homologyMap S.f n
        (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
          ((inv (HomologicalComplex.homologyMap
            (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
            ((inv (HomologicalComplex.homologyMap c (n - 1)))
              (HomologicalComplex.homologyMap e.hom (n - 1) y))))) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℤ) 0
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
  let hS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤
    (ambientRationalInjectiveComplex X)
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S hS
  dsimp only
  have hc' := ambientRationalInjectiveGlobalCone_connecting X Z hZ n
  have he := CochainComplex.mappingCone.mapHomologicalComplexIso_homology_connecting
    b Γ (n - 1) n (by omega)
  let z := (inv (HomologicalComplex.homologyMap c (n - 1)))
    (HomologicalComplex.homologyMap e.hom (n - 1) y)
  exact ((ConcreteCategory.congr_hom he y).symm.trans
    (ConcreteCategory.congr_hom hc' (HomologicalComplex.homologyMap e.hom (n - 1) y)).symm).trans
      (mappingCocone_shiftedLift_connecting_apply S hS n z).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The support equivalence intertwines `forgetSupport` with the inclusion of supported
injective sections. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
      (forgetSupport X Z n x) =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).f n
      (rationalSupportAddEquivSupportedInjectiveHomology X Z hZ n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
  let y := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone]
  change H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
      (Γ.mapHomologicalComplex (.up ℤ))) (n - 1) n (by omega) y =
    HomologicalComplex.homologyMap S.f n
      (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y)))))
  exact ambientRationalInjectiveCone_connecting_eq_supportedSections X Z hZ n y

end AlgebraicGeometry.ComplexPoint
