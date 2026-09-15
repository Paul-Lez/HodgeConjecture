/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.AlgebraicGeometry.Cohomology.RationalDegreeZero

/-!
# Constant classes in degree-zero rational cohomology

This file identifies constant cohomology classes under the degree-zero comparison and derives
the connected-space calculation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance rationalDegreeZeroPropertiesHasDerivedCategoryAddCommGrpCat :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

local instance rationalDegreeZeroPropertiesHasDerivedCategorySheaf :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option linter.auxLemma false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5
  TopCat.Sheaf.globalSectionsFunctor in
/-- The degree-zero comparison sends the constant class of `q` to the constant-sheaf morphism
induced by `n ↦ n q`. -/
@[simp] theorem rationalCohomologyZeroEquivSheafHom_class (q : ℚ) :
    rationalCohomologyZeroEquivSheafHom X (fieldCohomologyClass ℚ X q) =
      (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ q)) := by
  let Y := TopCat.of (ComplexPoint X)
  let K := constantFieldSheafComplexIntPlus ℚ X
  let F := ℍ[AddCommGrpCat]^0(Y)
  let G := CochainComplex.Plus.ι (AnalyticAdditiveSheaf X) ⋙
    (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let s := TopCat.Sheaf.integerConstantHomAddEquivGlobalSections
    𝓒(↧(ComplexPoint X); ℚ)
      ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
        (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ 1)))
  let t : G.obj K :=
    (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y
      𝓒(↧(ComplexPoint X); ℚ)).inv s
  let m := fieldScalarComplex ℚ X q
  let Z := 𝓒(↧(ComplexPoint X); ℤ)
  let Q := 𝓒(↧(ComplexPoint X); ℚ)
  let u : Z ⟶ Q := (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ q))
  let eQ : K.obj ≅ (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj Q :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Q 0 0 rfl
  let j : TopCat.Sheaf.integerConstantSingleComplex Y ⟶ K.obj :=
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map u ≫ eQ.inv
  have hj :
      (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom
        ((HomologicalComplex.homologyMapIso
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj) 0).hom
          ((CochainComplex.HomComplex.homologyAddEquiv _ K.obj 0).symm
            (CochainComplex.HomComplex.CohomologyClass.mk
              (CochainComplex.HomComplex.Cocycle.ofHom j)))) =
        TopCat.Sheaf.integerConstantHomAddEquivGlobalSections Q u := by
    let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
    let e := ComplexShape.embeddingUpNat
    let KN := (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).obj Q
    let E : (Γ.mapHomologicalComplex (.up ℤ)).obj K.obj ≅
        (HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (Γ.obj Q) :=
      HomologicalComplex.mapExtendCanonicalIso Γ KN e ≪≫
        (e.extendFunctor AddCommGrpCat).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app Q) ≪≫
        HomologicalComplex.extendSingleIso e (Γ.obj Q) 0 0 rfl
    let z := CochainComplex.HomComplex.Cocycle.ofHom j
    let H := CochainComplex.HomComplex
      (TopCat.Sheaf.integerConstantSingleComplex Y) K.obj
    let hD := CochainComplex.HomComplex.leftHomologyData
      (TopCat.Sheaf.integerConstantSingleComplex Y) K.obj 0
    let zD : hD.K := z
    let c : H.cycles 0 := hD.cyclesIso.inv zD
    have hw :
        (CochainComplex.HomComplex.homologyAddEquiv _ K.obj 0).symm
            (CochainComplex.HomComplex.CohomologyClass.mk z) =
          H.homologyπ 0 c := by
      change ConcreteCategory.hom (hD.π ≫ hD.homologyIso.inv) zD =
        ConcreteCategory.hom
          (hD.cyclesIso.inv ≫ (H.sc 0).homologyπ) zD
      exact ConcreteCategory.congr_hom hD.π_comp_homologyIso_inv zD
    rw [show CochainComplex.HomComplex.Cocycle.ofHom j = z from rfl, hw]
    dsimp only [HomologicalComplex.homologyMapIso]
    have hn := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj).hom 0) c
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hn]
    rw [show (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom =
      HomologicalComplex.homologyMap E.hom 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (Γ.obj Q)).hom from rfl]
    simp only [ConcreteCategory.comp_apply]
    let c' := (HomologicalComplex.cyclesMap
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj).hom 0) c
    have hnE := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality E.hom 0) c'
    simp only [ConcreteCategory.comp_apply] at hnE
    rw [hnE]
    let c'' := HomologicalComplex.cyclesMap E.hom 0 c'
    have hs := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom
        (C := AddCommGrpCat) (.up ℤ) 0 (Γ.obj Q)) c''
    simp only [ConcreteCategory.comp_apply] at hs
    rw [hs]
    change ConcreteCategory.hom
      (HomologicalComplex.cyclesMap
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj).hom 0 ≫
        HomologicalComplex.cyclesMap E.hom 0 ≫
        (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (Γ.obj Q)).hom) c = _
    rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
    rw [HomologicalComplex.cyclesMap_i_assoc,
      HomologicalComplex.cyclesMap_i_assoc]
    simp only [ConcreteCategory.comp_apply]
    have hc := ConcreteCategory.congr_hom
      hD.cyclesIso_inv_comp_iCycles zD
    simp only [ConcreteCategory.comp_apply] at hc
    have hc' :
        (H.iCycles 0).hom c = hD.i.hom zD := by
      change (H.iCycles 0).hom (hD.cyclesIso.inv.hom zD) = hD.i.hom zD
      exact hc
    rw [hc']
    change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Γ.obj Q)).hom.hom
      ((E.hom.f 0).hom
        (((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj).hom.f 0).hom
          (CochainComplex.HomComplex.Cocycle.ofHom j :
            CochainComplex.HomComplex.Cochain
              (TopCat.Sheaf.integerConstantSingleComplex Y) K.obj 0))) = _
    have hhci :
        ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj).hom.f 0).hom
            (CochainComplex.HomComplex.Cocycle.ofHom j :
              CochainComplex.HomComplex.Cochain
                (TopCat.Sheaf.integerConstantSingleComplex Y) K.obj 0) =
          TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.obj.X 0) (j.f 0) := by
      rfl
    rw [hhci]
    let f₀ : K.obj.X 0 ⟶ Q :=
      eQ.hom.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom
    have hE : E.hom.f 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Γ.obj Q)).hom =
        Γ.map f₀ := by
      dsimp only [E, f₀, eQ]
      simp only [Iso.trans_hom, HomologicalComplex.comp_f,
        HomologicalComplex.extendSingleIso_hom_f,
        Functor.map_comp, Category.assoc]
      simp only [Functor.mapIso_hom]
      have hB :
          ((e.extendFunctor AddCommGrpCat).map
              ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app Q).hom).f 0 =
            (HomologicalComplex.extendMap
              ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app Q) e).f 0 := rfl
      rw [hB]
      rw [HomologicalComplex.mapExtendCanonicalIso_hom_f Γ KN e
        (i := 0) (j := 0) rfl]
      rw [HomologicalComplex.extendMap_f _ e (i := 0) (i' := 0) rfl]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      dsimp only [KN, CochainComplex.single₀]
      simp
      rfl
    rw [← ConcreteCategory.comp_apply, hE]
    change f₀.hom.app (.op (⊤ : Opens Y))
      (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.obj.X 0) (j.f 0)) = _
    rw [← TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality]
    have hju : j.f 0 ≫ f₀ = u := by
      dsimp only [f₀, j]
      rw [HomologicalComplex.comp_f]
      let eQ₀ := (HomologicalComplex.eval (AnalyticAdditiveSheaf X) (.up ℤ) 0).mapIso eQ
      change ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map u).f 0 ≫
        eQ₀.inv ≫ eQ₀.hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom = u
      rw [Iso.inv_hom_id_assoc]
      rfl
    rw [hju]
  let Γ := TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y
  let v := fieldScalarSheaf ℚ X q
  let u₁ : Z ⟶ Q := (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ 1))
  have hu : u₁ ≫ v = u := by
    dsimp only [u₁, v, u, fieldScalarSheaf]
    rw [← Functor.map_comp]
    congr 1
    apply AddCommGrpCat.hom_ext
    ext
    simp
  have hmt :
      (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom
          (G.map m t) =
        TopCat.Sheaf.integerConstantHomAddEquivGlobalSections Q u := by
    have hn := ConcreteCategory.congr_hom
      (TopCat.Sheaf.globalSectionsSingle₀HomologyIso_hom_naturality
        AddCommGrpCat Y v) t
    simp only [ConcreteCategory.comp_apply] at hn
    change (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom
        (G.map m t) = Γ.map v
          ((TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom t) at hn
    rw [hn]
    have ht := ConcreteCategory.congr_hom
      (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).inv_hom_id s
    simp only [ConcreteCategory.comp_apply] at ht
    change (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom t = s at ht
    rw [ht]
    change v.hom.app (.op (⊤ : Opens Y)) s = _
    rw [← TopCat.Sheaf.integerConstantHomAddEquivGlobalSections_naturality]
    exact congrArg (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections Q) hu
  have hrepK :
      (HomologicalComplex.homologyMapIso
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj) 0).hom
          ((CochainComplex.HomComplex.homologyAddEquiv _ K.obj 0).symm
            (CochainComplex.HomComplex.CohomologyClass.mk
              (CochainComplex.HomComplex.Cocycle.ofHom j))) =
        G.map m t := by
    apply (ConcreteCategory.bijective_of_isIso
      (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y Q).hom).1
    rw [hj, hmt]
  let I := ambientRationalInjectiveComplex X
  let a : K.obj ⟶ I := ambientRationalInjectiveAugmentation X
  let A := TopCat.Sheaf.integerConstantSingleComplex Y
  let x := (CochainComplex.HomComplex.homologyAddEquiv A K.obj 0).symm
    (CochainComplex.HomComplex.CohomologyClass.mk
      (CochainComplex.HomComplex.Cocycle.ofHom j))
  let p := CochainComplex.HomComplex.postcompMap A a
  let hciK := TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K.obj
  let hciI := TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I
  let Γa := ((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y).mapHomologicalComplex
    (.up ℤ)).map a
  have hx :
      (CochainComplex.HomComplex.homologyAddEquiv A I 0).symm
          (CochainComplex.HomComplex.CohomologyClass.mk
            (CochainComplex.HomComplex.Cocycle.ofHom (j ≫ a))) =
        HomologicalComplex.homologyMap p 0 x := by
    apply (CochainComplex.HomComplex.homologyAddEquiv A I 0).injective
    rw [AddEquiv.apply_symm_apply,
      CochainComplex.HomComplex.homologyAddEquiv_postcompMap]
    rw [show (CochainComplex.HomComplex.homologyAddEquiv A K.obj 0) x =
      CochainComplex.HomComplex.CohomologyClass.mk
        (CochainComplex.HomComplex.Cocycle.ofHom j) by
        exact AddEquiv.apply_symm_apply _ _]
    rw [CochainComplex.HomComplex.postcompClass_mk]
    congr 1
    apply Subtype.ext
    exact CochainComplex.HomComplex.Cochain.ofHom_comp j a
  have hΓ := congrArg (fun g ↦ HomologicalComplex.homologyMap g 0)
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections_naturality Y a)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hΓ
  have hΓx := ConcreteCategory.congr_hom hΓ x
  have hrepI :
      (HomologicalComplex.homologyMapIso hciI 0).hom
          ((CochainComplex.HomComplex.homologyAddEquiv A I 0).symm
            (CochainComplex.HomComplex.CohomologyClass.mk
              (CochainComplex.HomComplex.Cocycle.ofHom (j ≫ a)))) =
        HomologicalComplex.homologyMap Γa 0 (G.map m t) := by
    rw [hx]
    change ConcreteCategory.hom (HomologicalComplex.homologyMap hciI.hom 0)
      (HomologicalComplex.homologyMap p 0 x) = _
    rw [← hrepK]
    exact hΓx
  have hderivedI :
      (derivedHomAddEquivGlobalSectionsKInjective X I 0).symm
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y).mapHomologicalComplex
              (.up ℤ)).map a) 0 (G.map m t)) =
        ShiftedHom.mk₀ 0 rfl (DerivedCategory.Q.map (j ≫ a)) := by
    rw [← hrepI]
    exact derivedHomAddEquivGlobalSectionsKInjective_symm_hom X I (j ≫ a)
  have hclass : fieldCohomologyClass ℚ X q =
      ((TopCat.Sheaf.toHypercohomology AddCommGrpCat Y 0).app K).hom (G.map m t) := by
    change F.map m
        (((TopCat.Sheaf.toHypercohomology AddCommGrpCat Y 0).app K).hom t) = _
    exact (ConcreteCategory.congr_hom
      ((TopCat.Sheaf.toHypercohomology AddCommGrpCat Y 0).naturality m) t).symm
  rw [hclass]
  dsimp only [rationalCohomologyZeroEquivSheafHom, AddEquiv.trans_apply]
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_toHypercohomology]
  simp only [Int.cast_ofNat_Int, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    Functor.mapIso_trans, Functor.mapIso_symm, isoHomCongrAddEquiv_apply, Iso.refl_inv,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv, Functor.map_inv,
    Functor.mapIso_hom, Category.id_comp]
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
      apply (Abelian.Ext.homEquiv (X := Z) (Y := Q)).injective
  set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
      change (Abelian.Ext.homEquiv (X := Z) (Y := Q))
        ((Abelian.Ext.homEquiv (X := Z) (Y := Q)).symm _) =
          (Abelian.Ext.mk₀ u).hom
  rw [Equiv.apply_symm_apply, Abelian.Ext.mk₀_hom]
  dsimp only [I, a, Y] at hderivedI
  set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
      rw [hderivedI]
  simp only [ShiftedHom.mk₀, Functor.map_comp, Category.assoc]
  let D := DerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))
  let z₀ := shiftFunctorZero' D (0 : ℤ) rfl
  have hn := z₀.inv.naturality
    (DerivedCategory.Q.map (ambientRationalInjectiveAugmentation X))
  simp only [Functor.id_map] at hn
  slice_lhs 2 3 =>
    rw [hn]
  have ha :
      (shiftFunctor D (0 : ℤ)).map
          (DerivedCategory.Q.map (ambientRationalInjectiveAugmentation X)) =
        (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) (0 : ℤ)).map
          (DerivedCategory.Q.map (ambientRationalInjectiveAugmentationPlus X).hom) := by
    set_option backward.isDefEq.respectTransparency.types true in
      set_option backward.isDefEq.respectTransparency true in
        rfl
  rw [ha]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
      rw [← z₀.inv.naturality]
  simp only [Functor.id_map]
  have hje : j ≫ eQ.hom =
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map u := by
    dsimp only [j]
    simp only [Category.assoc, Iso.inv_hom_id]
    simp
  have hQ := congrArg (fun f ↦ DerivedCategory.Q.map f) hje
  simp only [Functor.map_comp] at hQ
  slice_lhs 1 2 =>
    rw [hQ]
  set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
      rfl

/-- If the constant-sheaf functor is faithful, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective_of_constantSheaf_faithful
    [(TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).Faithful] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  intro a b hab
  have hs :
      (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
          (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ a)) =
        (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
          (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ b)) := by
    rw [← rationalCohomologyZeroEquivSheafHom_class,
      ← rationalCohomologyZeroEquivSheafHom_class, hab]
  have hm := (TopCat.Sheaf.constantFunctor
    ↧(ComplexPoint X)).map_injective hs
  simpa using ConcreteCategory.congr_hom hm (1 : ℤ)

/-- On a nonempty analytic complex-point space, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective
    [Nonempty (ComplexPoint X)] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  let : (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).Faithful :=
    TopCat.constantSheaf_faithful_of_nonempty _
  exact rationalCohomologyClass_injective_of_constantSheaf_faithful X

/-- On a connected analytic complex-point space, every degree-zero rational cohomology class is
a constant class. -/
theorem rationalCohomologyClass_surjective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Surjective (fieldCohomologyClass ℚ X) := by
  intro α
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  let ff := TopCat.constantSheafFullyFaithfulOfConnected
    (TopCat.of (ComplexPoint X))
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  let e := rationalCohomologyZeroEquivSheafHom X
  obtain ⟨f, hf⟩ := F.map_surjective (e α)
  let q : ℚ := f (1 : ℤ)
  refine ⟨q, e.injective ?_⟩
  rw [rationalCohomologyZeroEquivSheafHom_class, ← hf]
  change F.map (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ q)) = F.map f
  congr 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n ↦ ?_)
  change n • q = f n
  rw [show n = n • (1 : ℤ) by simp, map_zsmul]
  simp [q]

/-- Constant rational classes give a bijection onto degree-zero cohomology of a connected
analytic complex-point space. -/
theorem rationalCohomologyClass_bijective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Bijective (fieldCohomologyClass ℚ X) := by
  let : Nonempty (ComplexPoint X) := inferInstance
  exact ⟨rationalCohomologyClass_injective X,
    rationalCohomologyClass_surjective X⟩

/-- On a connected analytic complex-point space, rational constants are linearly equivalent to
degree-zero rational cohomology. -/
def rationalCohomologyClassLinearEquiv
    [ConnectedSpace (ComplexPoint X)] :
    ℚ ≃ₗ[ℚ] H^0(X; ℚ) :=
  LinearEquiv.ofBijective (fieldCohomologyClassLinear ℚ X)
    (rationalCohomologyClass_bijective X)

/-- On a connected analytic complex-point space, the rational cohomology unit spans all of
degree-zero rational cohomology. -/
theorem span_rationalCohomologyUnit_eq_top
    [ConnectedSpace (ComplexPoint X)] :
    Submodule.span ℚ {fieldCohomologyUnit ℚ X} = ⊤ := by
  apply le_antisymm le_top
  intro α _
  obtain ⟨q, rfl⟩ := rationalCohomologyClass_surjective X α
  have hq : fieldCohomologyClass ℚ X q =
      q • fieldCohomologyUnit ℚ X := by
    rw [field_smul_eq]
    rfl
  rw [hq]
  exact Submodule.smul_mem _ q (Submodule.subset_span (Set.mem_singleton _))

/-- The degree-zero rational cohomology unit is nonzero on a nonempty analytic complex-point
space. -/
theorem rationalCohomologyUnit_ne_zero
    [Nonempty (ComplexPoint X)] :
    fieldCohomologyUnit ℚ X ≠ 0 := by
  intro h
  have h1 : fieldCohomologyClass ℚ X 1 = fieldCohomologyUnit ℚ X := by
    unfold fieldCohomologyClass
    rw [fieldScalarComplex_one]
    exact ConcreteCategory.congr_hom
      ((TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X)) 0).map_id _) _
  have h10 : fieldCohomologyClass ℚ X 1 =
      fieldCohomologyClass ℚ X 0 := by
    rw [h1, fieldCohomologyClass_zero]
    exact h
  exact one_ne_zero (rationalCohomologyClass_injective X h10)

end AlgebraicGeometry.ComplexPoint
