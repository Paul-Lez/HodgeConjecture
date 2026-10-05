/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import Other.AlgebraicGeometry.Cohomology.SupportConeInjectiveModelLemmas
public import Other.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import Other.AlgebraicGeometry.Cohomology.HypercohomologyNaturality
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
      (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology n :=
  (constantModuleCohomologyToAdditiveEquiv ℚ X n).trans
    (TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective AddCommGrpCat
      (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveAugmentationPlus X)
      n).addCommGroupIsoToAddEquiv

/-- Ordinary rational cohomology computed by the forgotten module injective resolution. -/
def rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution (n : ℕ) :
    H^(n : ℤ)(X; ℚ) ≃+
      (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology (n : ℤ) :=
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ)
  letI K := moduleInjectiveResolutionForgetComplex ℚ X
  letI i := moduleInjectiveResolutionForgetAugmentationPlain ℚ X
  letI : (TopCat.Sheaf.injectiveResolutionComplex Y F).IsStrictlyGE 0 :=
    TopCat.Sheaf.injectiveResolutionComplex_isStrictlyGE Y F
  letI : QuasiIso (TopCat.Sheaf.resolutionToInjective Y F K i) :=
    TopCat.Sheaf.resolutionToInjective_quasiIso Y F K i
  letI : QuasiIso
      (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map
        (TopCat.Sheaf.resolutionToInjective Y F K i)) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      _ 0 0 (fun q => moduleInjectiveResolutionForget_isFlasque ℚ X q)
      (fun q => letI := TopCat.Sheaf.injectiveResolutionComplex_injective Y F q
        TopCat.Sheaf.injective_isFlasque Y _)
  (moduleGlobalSectionsHomologyToHypercohomology ℚ X n).symm.trans
    (asIso (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map
        (TopCat.Sheaf.resolutionToInjective Y F K i)) (n : ℤ))).addCommGroupIsoToAddEquiv

lemma rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution_moduleGlobalSections
    (n : ℕ)
    (x : (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
      (moduleInjectiveResolutionForgetComplex ℚ X)).homology n) :
    letI Y := TopCat.of (ComplexPoint X)
    letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ)
    letI K := moduleInjectiveResolutionForgetComplex ℚ X
    letI i := moduleInjectiveResolutionForgetAugmentationPlain ℚ X
    letI q := TopCat.Sheaf.resolutionToInjective Y F K i
    rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution X n
        (moduleGlobalSectionsHomologyToHypercohomology ℚ X n x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q)
        (n : ℤ) x := by
  dsimp only
  let Y : TopCat := TopCat.of (ComplexPoint X)
  let F : TopCat.Sheaf AddCommGrpCat Y :=
    (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ)
  let K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
    moduleInjectiveResolutionForgetComplex ℚ X
  let i := moduleInjectiveResolutionForgetAugmentationPlain ℚ X
  let q := TopCat.Sheaf.resolutionToInjective Y F K i
  let : (TopCat.Sheaf.injectiveResolutionComplex Y F).IsStrictlyGE 0 :=
    TopCat.Sheaf.injectiveResolutionComplex_isStrictlyGE Y F
  let : QuasiIso q := TopCat.Sheaf.resolutionToInjective_quasiIso Y F K i
  let : QuasiIso
      (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      _ 0 0 (fun j => moduleInjectiveResolutionForget_isFlasque ℚ X j)
      (fun j =>
        let : Injective ((TopCat.Sheaf.injectiveResolutionComplex Y F).X j) :=
          TopCat.Sheaf.injectiveResolutionComplex_injective Y F j
        TopCat.Sheaf.injective_isFlasque Y _)
  let g := ((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q
  change (asIso (HomologicalComplex.homologyMap g (n : ℤ))).hom
      ((moduleGlobalSectionsHomologyToHypercohomology ℚ X n).symm
        (moduleGlobalSectionsHomologyToHypercohomology ℚ X n x)) =
    HomologicalComplex.homologyMap g (n : ℤ) x
  rw [AddEquiv.symm_apply_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_moduleGlobalSections
    (n : ℕ)
    (x : (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
      (moduleInjectiveResolutionForgetComplex ℚ X)).homology n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ)
        (moduleGlobalSectionsHomologyToHypercohomology ℚ X n x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
            (TopCat.Sheaf.resolutionToInjective
              (TopCat.of (ComplexPoint X))
              ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
                (AddCommGrpCat.of ℚ))
              (moduleInjectiveResolutionForgetComplex ℚ X)
              (moduleInjectiveResolutionForgetAugmentationPlain ℚ X))) (n : ℤ) x := by
  let Y := TopCat.of (ComplexPoint X)
  let : HasDerivedCategory (ModuleCat ℚ) := HasDerivedCategory.standard _
  let : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _
  let : HasDerivedCategory (TopCat.Sheaf (ModuleCat ℚ) Y) := HasDerivedCategory.standard _
  let : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _
  let A := constantModuleSheafComplexIntPlus X ℚ
  let K := moduleInjectiveResolutionComplexPlus ℚ X
  let a := moduleInjectiveResolutionAugmentationPlus ℚ X
  let : QuasiIso a.hom := moduleInjectiveResolutionAugmentation_quasiIso ℚ X
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let P := moduleForgetSheaf ℚ X
  let : P.Additive := moduleForgetSheaf_additive ℚ X
  let : PreservesFiniteLimits P := moduleForgetSheaf_preservesFiniteLimits ℚ X
  let : PreservesFiniteColimits P := moduleForgetSheaf_preservesFiniteColimits ℚ X
  let : PreservesFiniteColimits (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology Y) F) :=
    moduleForgetSheaf_preservesFiniteColimits ℚ X
  let : P.PreservesInjectiveObjects := by
    change (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology Y) F).PreservesInjectiveObjects
    exact CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology Y) (CategoryTheory.Sheaf.intAlgebraMap_flat ℚ)
  let : (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology Y) F).PreservesInjectiveObjects :=
    ‹P.PreservesInjectiveObjects›
  let HM := TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℚ) Y (n : ℤ)
  let H := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat Y (n : ℤ)
  let h := TopCat.Sheaf.homologicalComplexChangeOfFunctorIso F (n : ℤ)
  let c := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := ℚ) Y (n : ℤ)
  let e := TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective
    (ModuleCat ℚ) Y a (n : ℤ)
  let j := constantModuleSheafForgetComplexIso X ℚ
  let q := TopCat.Sheaf.resolutionToInjective Y
    ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ))
    (moduleInjectiveResolutionForgetComplex ℚ X)
    (moduleInjectiveResolutionForgetAugmentationPlain ℚ X)
  let i :
      (CochainComplex.Plus.single₀ (TopCat.Sheaf AddCommGrpCat Y)).obj
          ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℚ)) ⟶
        P.mapCochainComplexPlus.obj K :=
    ⟨(constantFieldSheafComplexIntIsoSingle ℚ X).hom ≫
      moduleInjectiveResolutionForgetAugmentationPlain ℚ X⟩
  let q' : P.mapCochainComplexPlus.obj K ⟶ ambientRationalInjectiveComplexPlus X :=
    ⟨q⟩
  let g := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q)
      (n : ℤ)
  let eA := TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective
    AddCommGrpCat Y (ambientRationalInjectiveAugmentationPlus X) (n : ℤ)
  let G := ((TopCat.Sheaf.globalSections (ModuleCat ℚ) Y).mapHomologicalComplex ℤᵘᵖ).obj K.obj
  let ηM := TopCat.Sheaf.toHypercohomology (ModuleCat ℚ) Y (n : ℤ)
  let ηA := TopCat.Sheaf.toHypercohomology AddCommGrpCat Y (n : ℤ)
  have he : e.inv ≫ HM.map a = ηM.app K := by
    change ηM.app K ≫ inv (HM.map a) ≫ HM.map a = ηM.app K
    simp only [IsIso.inv_hom_id, Category.comp_id]
  have heA : eA.hom =
      H.map (ambientRationalInjectiveAugmentationPlus X) ≫
        inv (ηA.app (ambientRationalInjectiveComplexPlus X)) := by
    rfl
  have hc := c.hom.naturality a
  change F.map (HM.map a) ≫ c.hom.app K =
    c.hom.app A ≫ H.map (P.mapCochainComplexPlus.map a) at hc
  have hcompat := TopCat.Sheaf.toHypercohomology_changeOfFunctor F K (n : ℤ)
  change (h.app G).hom ≫ F.map (ηM.app K) ≫ c.hom.app K =
    ηA.app (P.mapCochainComplexPlus.obj K) at hcompat
  have hj : j.hom ≫ i = P.mapCochainComplexPlus.map a := by
    apply ObjectProperty.hom_ext
    let s := constantFieldSheafComplexIntIsoSingle ℚ X
    let f := (P.mapCochainComplexPlus.map a).hom
    change j.hom.hom ≫ s.hom ≫ s.inv ≫ j.inv.hom ≫ f = f
    have hjinv : j.hom.hom ≫ j.inv.hom = 𝟙 _ :=
      congrArg (fun k => k.hom) j.hom_inv_id
    calc
      _ = j.hom.hom ≫ j.inv.hom ≫ f :=
        congrArg (j.hom.hom ≫ ·) (s.hom_inv_id_assoc (j.inv.hom ≫ f))
      _ = (j.hom.hom ≫ j.inv.hom) ≫ f := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ f := congrArg (· ≫ f) hjinv
      _ = f := Category.id_comp f
  have hiq : i ≫ q' = ambientRationalInjectiveAugmentationPlus X := by
    apply ObjectProperty.hom_ext
    change (constantFieldSheafComplexIntIsoSingle ℚ X).hom ≫
      moduleInjectiveResolutionForgetAugmentationPlain ℚ X ≫ q =
      ambientRationalInjectiveAugmentation X
    rw [TopCat.Sheaf.comp_resolutionToInjective]
    dsimp only [constantFieldSheafComplexIntIsoSingle,
      TopCat.Sheaf.injectiveResolutionAugmentation,
      ambientRationalInjectiveAugmentation,
      TopCat.Sheaf.ambientConstantInjectiveResolution]
    erw [Iso.hom_inv_id_assoc]
  have hq := ηA.naturality q'
  change g ≫ ηA.app (ambientRationalInjectiveComplexPlus X) =
    ηA.app (P.mapCochainComplexPlus.obj K) ≫ H.map q' at hq
  have hjq : H.map j.hom ≫ H.map (ambientRationalInjectiveAugmentationPlus X) =
      H.map (P.mapCochainComplexPlus.map a) ≫ H.map q' := by
    have hjiq : j.hom ≫ ambientRationalInjectiveAugmentationPlus X =
        P.mapCochainComplexPlus.map a ≫ q' := calc
      _ = j.hom ≫ (i ≫ q') := congrArg (j.hom ≫ ·) hiq.symm
      _ = (j.hom ≫ i) ≫ q' := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ q') hj
    exact (H.map_comp j.hom _).symm.trans
      ((congrArg H.map hjiq).trans (H.map_comp _ _))
  have hcomp :
      (h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫
          H.map j.hom ≫ eA.hom = g := by
    let u := ηA.app (ambientRationalInjectiveComplexPlus X)
    let f := HM.map a
    calc
      _ = (h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫ H.map j.hom ≫
          H.map (ambientRationalInjectiveAugmentationPlus X) ≫ inv u :=
        congrArg (fun g => (h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫ H.map j.hom ≫ g) heA
      _ = (h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫
          H.map (P.mapCochainComplexPlus.map a) ≫ H.map q' ≫ inv u :=
        congrArg (fun g => (h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫ g)
          ((reassoc_of% hjq) (inv u))
      _ = (h.app G).hom ≫ F.map e.inv ≫ F.map f ≫ c.hom.app K ≫ H.map q' ≫ inv u :=
        congrArg (fun g => (h.app G).hom ≫ F.map e.inv ≫ g)
          ((reassoc_of% hc) (H.map q' ≫ inv u)).symm
      _ = (h.app G).hom ≫ F.map (e.inv ≫ f) ≫ c.hom.app K ≫ H.map q' ≫ inv u :=
        congrArg ((h.app G).hom ≫ ·)
          (F.map_comp_assoc e.inv f (c.hom.app K ≫ H.map q' ≫ inv u)).symm
      _ = (h.app G).hom ≫ F.map (ηM.app K) ≫ c.hom.app K ≫ H.map q' ≫ inv u :=
        congrArg (fun g => (h.app G).hom ≫ F.map g ≫ c.hom.app K ≫ H.map q' ≫ inv u) he
      _ = ηA.app (P.mapCochainComplexPlus.obj K) ≫ H.map q' ≫ inv u :=
        (reassoc_of% hcompat) (H.map q' ≫ inv u)
      _ = g ≫ u ≫ inv u :=
        ((reassoc_of% hq) (inv u)).symm
      _ = _ := by simp only [IsIso.hom_inv_id, Category.comp_id]
  change ConcreteCategory.hom
      ((h.app G).hom ≫ F.map e.inv ≫ c.hom.app A ≫
        H.map j.hom ≫ eA.hom) x = _
  exact ConcreteCategory.congr_hom hcomp x

lemma rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution_eq
    (n : ℕ) :
    rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution X n =
      rationalCohomologyAddEquivAmbientInjectiveHomology X (n : ℤ) := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (moduleGlobalSectionsHomologyToHypercohomology ℚ X n).surjective x
  exact
    (rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution_moduleGlobalSections
      X n y).trans
    (rationalCohomologyAddEquivAmbientInjectiveHomology_moduleGlobalSections
      X n y).symm

/-- Under the forgotten-module-resolution comparison,
`H_[Z]^n(X(ℂ); ℚ) → H^n(X(ℂ); ℚ)` is the map to the additive injective resolution. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℕ) (x : H_[Z]^n(X; ℚ)) :
    rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution X n
        (forgetSupport ℚ X Z n x) =
      forgetSupportToGlobalSectionsHomology ℚ X Z n x := by
  dsimp [forgetSupport]
  rw [rationalCohomologyAddEquivAmbientInjectiveHomologyOfModuleResolution_moduleGlobalSections]
  exact forgetSupportToModuleGlobalSectionsHomology_resolutionToInjective ℚ X Z n x

/-- The ambient injective-resolution comparison carries the derived unit to the map on the
cohomology of complexes of global sections. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_toHypercohomology
    (n : ℤ)
    (x : (TopCat.Sheaf.globalSectionsComplex
      (TopCat.of (ComplexPoint X))
      (constantFieldSheafComplexIntPlus ℚ X).obj).homology n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
        ((constantModuleCohomologyToAdditiveEquiv ℚ X n).symm
          (((TopCat.Sheaf.toHypercohomology AddCommGrpCat
            (TopCat.of (ComplexPoint X)) n).app
            (constantFieldSheafComplexIntPlus ℚ X)).hom x)) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
            (ambientRationalInjectiveAugmentation X)) n x := by
  let e := constantModuleCohomologyToAdditiveEquiv ℚ X n
  let f := TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective AddCommGrpCat
    (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveAugmentationPlus X) n
  dsimp [rationalCohomologyAddEquivAmbientInjectiveHomology]
  change f.hom (e (e.symm
    (((TopCat.Sheaf.toHypercohomology AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).app
      (constantFieldSheafComplexIntPlus ℚ X)).hom x))) = _
  rw [e.apply_symm_apply]
  exact ConcreteCategory.congr_hom
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
      forgetSupportComplex X Z ≫ (ambientRationalInjectiveAugmentationPlus X).hom := by
  dsimp only [rationalSupportConeToAmbientInjectiveConePlus,
    ambientRationalInjectiveForgetSupportComplex, forgetSupportComplex]
  rw [← Category.assoc, ← Functor.map_comp,
    rationalSupportConeToAmbientInjectiveCone_connecting,
    Functor.map_comp, Category.assoc]
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
          (((TopCat.Sheaf.globalSections AddCommGrpCat
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map h.hom) n := by
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
        (rationalForgetSupport X Z n x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
            (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n
        ((TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat
          (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveConePlus X Z hZ) n).hom
          ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
            (rationalSupportConeToAmbientInjectiveConePlus X Z hZ) x)) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
  let Γc := Γ.mapHomologicalComplex ℤᵘᵖ
  let F := ℍ[AddCommGrpCat]^n(Y)
  let A := constantFieldSheafComplexIntPlus ℚ X
  let I := ambientRationalInjectiveConePlus X Z hZ
  let J := ambientRationalInjectiveComplexPlus X
  let f := rationalSupportConeToAmbientInjectiveConePlus X Z hZ
  let g : rationalCohomologyWithSupportComplexPlus X Z ⟶ A :=
    ⟨forgetSupportComplex X Z⟩
  let a : A ⟶ J := ambientRationalInjectiveAugmentationPlus X
  let h : I ⟶ J := ⟨ambientRationalInjectiveForgetSupportComplex X Z hZ⟩
  let eI := TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y I n
  let eJ := TopCat.Sheaf.hypercohomologyIsoOfInjective AddCommGrpCat Y J n
  let e := constantModuleCohomologyToAdditiveEquiv ℚ X n
  change eJ.hom (F.map a (e (e.symm (F.map g x)))) =
    HomologicalComplex.homologyMap (Γc.map h.hom) n (eI.hom (F.map f x))
  rw [e.apply_symm_apply]
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
    (y : ((TopCat.Sheaf.globalSections AddCommGrpCat
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).obj
        (ambientRationalInjectiveConePlus X Z hZ).obj |>.homology n) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
            (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n y =
      (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftMap
        (ShiftedHom.map
          (CochainComplex.mappingCone.triangle
            (ambientRationalInjectiveRestriction X Z hZ)).mor₃
          ((TopCat.Sheaf.globalSections AddCommGrpCat
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ))
        (n - 1) n (by omega)
        ((letI Γc := (TopCat.Sheaf.globalSections AddCommGrpCat
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
          letI C := (CochainComplex.mappingCone.triangle
            (ambientRationalInjectiveRestriction X Z hZ)).obj₃
          letI G := Γc.obj C
          letI e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
              ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
            HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
          letI e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
            ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
              (-1) n (n - 1) (by omega)).app G
          (e₃ ≪≫ e₄).hom) y) := by
  let Γc := (TopCat.Sheaf.globalSections AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
  let T := CochainComplex.mappingCone.triangle
    (ambientRationalInjectiveRestriction X Z hZ)
  let C := T.obj₃
  let f := T.mor₃
  let G := Γc.obj C
  let e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
  let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅ G.homology (n - 1) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  change HomologicalComplex.homologyMap
      (Γc.map (f⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app T.obj₁)) n y =
    (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftMap
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
      (rationalForgetSupport X Z n x) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftMap
      (ShiftedHom.map
        (CochainComplex.mappingCone.triangle
          (ambientRationalInjectiveRestriction X Z hZ)).mor₃
        ((TopCat.Sheaf.globalSections AddCommGrpCat
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ))
      (n - 1) n (by omega)
      (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x) := by
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_naturality X Z hZ n]
  let Γc := (TopCat.Sheaf.globalSections AddCommGrpCat
    (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
  let C := (CochainComplex.mappingCone.triangle
    (ambientRationalInjectiveRestriction X Z hZ)).obj₃
  let G := Γc.obj C
  let e₃ : (Γc.obj ((shiftFunctor _ (-1 : ℤ)).obj C)).homology n ≅
      ((shiftFunctor _ (-1 : ℤ)).obj G).homology n :=
    HomologicalComplex.homologyMapIso ((Γc.commShiftIso (-1)).app C) n
  let e₄ : ((shiftFunctor _ (-1 : ℤ)).obj G).homology n ≅
      G.homology (n - 1) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
      (-1) n (n - 1) (by omega)).app G
  change HomologicalComplex.homologyMap
      (Γc.map (ambientRationalInjectiveForgetSupportComplex X Z hZ)) n _ =
    (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftMap
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
    letI Y := TopCat.of (ComplexPoint X)
    letI U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    letI Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
    letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
      (ambientRationalInjectiveComplex X)
    letI b := ambientRationalInjectiveRestriction X Z hZ
    letI c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
    letI H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0
    inv (HomologicalComplex.homologyMap c (n - 1)) ≫
        H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃
          (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex ℤᵘᵖ).map b)).mor₃
          (n - 1) n (by omega) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0
  dsimp only
  have hc : HomologicalComplex.homologyMap c (n - 1) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex ℤᵘᵖ).map b)).mor₃ (n - 1) n (by omega) =
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
        (-((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
          1 (n - 1) n (by omega)).hom.app S.X₁
          ((inv (HomologicalComplex.homologyMap
            (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1))) z)) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) z := by
  let _ := CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S hS
  rw [map_neg]
  change ((-(inv (HomologicalComplex.homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)) ≫
    ((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
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
    (y : (TopCat.Sheaf.globalSectionsComplex
      (TopCat.of (ComplexPoint X))
      (CochainComplex.mappingCone
        (ambientRationalInjectiveRestriction X Z hZ))).homology (n - 1)) :
    letI Y := TopCat.of (ComplexPoint X)
    letI U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
    letI Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
    letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
      (ambientRationalInjectiveComplex X)
    letI : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
      CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
    letI b := ambientRationalInjectiveRestriction X Z hZ
    letI c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
    letI H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0
    letI e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
    H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
        (Γ.mapHomologicalComplex ℤᵘᵖ)) (n - 1) n (by omega) y =
      HomologicalComplex.homologyMap S.f n
        (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
          ((inv (HomologicalComplex.homologyMap
            (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
            ((inv (HomologicalComplex.homologyMap c (n - 1)))
              (HomologicalComplex.homologyMap e.hom (n - 1) y))))) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} ℤᵘᵖ 0
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
      (rationalForgetSupport X Z n x) =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).f n
      (rationalSupportAddEquivSupportedInjectiveHomologyAmbient X Z hZ n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
  let y := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone]
  change H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
      (Γ.mapHomologicalComplex ℤᵘᵖ)) (n - 1) n (by omega) y =
    HomologicalComplex.homologyMap S.f n
      (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y)))))
  exact ambientRationalInjectiveCone_connecting_eq_supportedSections X Z hZ n y

end AlgebraicGeometry.ComplexPoint
