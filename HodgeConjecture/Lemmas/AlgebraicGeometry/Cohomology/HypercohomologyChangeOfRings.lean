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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.Hypercohomology
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusExact
public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Change of rings for hypercohomology
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u w

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (X : TopCat.{w})

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat R)]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat S)]

section DerivedCategory

variable [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat S)]
  [EnoughInjectives (ModuleCat R)] [EnoughInjectives (ModuleCat S)]
  [HasDerivedCategory (TopCat.Sheaf (ModuleCat R) X)]
  [HasDerivedCategory (TopCat.Sheaf (ModuleCat S) X)]
  [EnoughInjectives (TopCat.Sheaf (ModuleCat R) X)]
  [EnoughInjectives (TopCat.Sheaf (ModuleCat S) X)]

noncomputable def globalSectionsChangeOfRingsIso :
    globalSections (ModuleCat S) X ⋙ ModuleCat.restrictScalars f ≅
      CategoryTheory.Sheaf.restrictScalars (Opens.grothendieckTopology X) f ⋙
        globalSections (ModuleCat R) X :=
  Iso.refl _

noncomputable def plusHomologyFactors (C : Type*) [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) :
    DerivedCategory.Plus.Qh (C := C) ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n :=
  Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C)
      (DerivedCategory.homologyFunctor C n) ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (DerivedCategory.homologyFunctorFactorsh C n)

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Abelian C]
  [Category.{v₂} D] [Abelian D]

section Generic

variable [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [EnoughInjectives D]

noncomputable def homologicalComplexChangeOfFunctorIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapHomologicalComplex ℤᵘᵖ ⋙ HomologicalComplex.homologyFunctor D ℤᵘᵖ n ≅
      HomologicalComplex.homologyFunctor C ℤᵘᵖ n ⋙ F :=
    Functor.isoWhiskerLeft (F.mapHomologicalComplex ℤᵘᵖ)
      (HomologicalComplex.homologyFunctorIso D ℤᵘᵖ n) ≪≫
    Functor.isoWhiskerRight
      (show F.mapHomologicalComplex ℤᵘᵖ ⋙ HomologicalComplex.shortComplexFunctor D ℤᵘᵖ n ≅
        HomologicalComplex.shortComplexFunctor C ℤᵘᵖ n ⋙ F.mapShortComplex from Iso.refl _)
      (ShortComplex.homologyFunctor D) ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C ℤᵘᵖ n)
      (ShortComplex.homologyFunctorIso F) ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.homologyFunctorIso C ℤᵘᵖ n).symm F

noncomputable def homotopyCategoryChangeOfFunctorIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapHomotopyCategory ℤᵘᵖ ⋙ HomotopyCategory.homologyFunctor D ℤᵘᵖ n ≅
      HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex ℤᵘᵖ)
        (HomotopyCategory.homologyFunctorFactors D ℤᵘᵖ n) ≪≫
      homologicalComplexChangeOfFunctorIso F n ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).symm F)

noncomputable def homotopyCategoryPlusChangeOfFunctorIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
        HomotopyCategory.homologyFunctor D ℤᵘᵖ n ≅
      HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompιIso F)
      (HomotopyCategory.homologyFunctor D ℤᵘᵖ n) ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (homotopyCategoryChangeOfFunctorIso F n)

noncomputable def homologyChangeOfFunctorIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
      DerivedCategory.Plus.homologyFunctor C n ⋙ F :=
  letI a :
      DerivedCategory.Plus.Qh (C := C) ⋙
          (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
        F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
          HomotopyCategory.homologyFunctor D ℤᵘᵖ n :=
    (Functor.associator (DerivedCategory.Plus.Qh (C := C)) F.mapDerivedCategoryPlus
      (DerivedCategory.Plus.homologyFunctor D n)).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryPlusFactorsh F)
        (DerivedCategory.Plus.homologyFunctor D n) ≪≫
      Functor.associator F.mapHomotopyCategoryPlus (DerivedCategory.Plus.Qh (C := D))
        (DerivedCategory.Plus.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
        (plusHomologyFactors D n)
  letI b := plusHomologyFactors C n
  letI α := a.symm.hom
  letI α' :
      HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F ⟶
        DerivedCategory.Plus.Qh (C := C) ⋙
          (DerivedCategory.Plus.homologyFunctor C n ⋙ F) :=
    Functor.whiskerRight b.inv F ≫
      (Functor.associator (DerivedCategory.Plus.Qh (C := C))
        (DerivedCategory.Plus.homologyFunctor C n) F).hom
  letI τ := homotopyCategoryPlusChangeOfFunctorIso F n
  letI :
      (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n).IsRightDerivedFunctor
        (L := DerivedCategory.Plus.Qh (C := C)) α (HomotopyCategory.Plus.quasiIso C) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
        HomotopyCategory.homologyFunctor D ℤᵘᵖ n)).isRightDerivedFunctor_of_isIso
      (L₂ := DerivedCategory.Plus.Qh (C := C)) α (fun K => by infer_instance)
  letI :
      (DerivedCategory.Plus.homologyFunctor C n ⋙ F).IsRightDerivedFunctor
        (L := DerivedCategory.Plus.Qh (C := C)) α' (HomotopyCategory.Plus.quasiIso C) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F)).isRightDerivedFunctor_of_isIso
      (L₂ := DerivedCategory.Plus.Qh (C := C)) α' (fun K => by infer_instance)
  Functor.rightDerivedNatIso _ _ (L := DerivedCategory.Plus.Qh (C := C)) α α'
    (HomotopyCategory.Plus.quasiIso C) τ

omit [EnoughInjectives D] in
/-- The change-of-coefficients comparison for homology is compatible with the maps from the
bounded-below homotopy category. -/
@[reassoc]
lemma homologyChangeOfFunctorIso_hom_fac
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    letI a :
        DerivedCategory.Plus.Qh (C := C) ⋙
            (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
          F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
            HomotopyCategory.homologyFunctor D ℤᵘᵖ n :=
      (Functor.associator (DerivedCategory.Plus.Qh (C := C)) F.mapDerivedCategoryPlus
        (DerivedCategory.Plus.homologyFunctor D n)).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryPlusFactorsh F)
          (DerivedCategory.Plus.homologyFunctor D n) ≪≫
        Functor.associator F.mapHomotopyCategoryPlus (DerivedCategory.Plus.Qh (C := D))
          (DerivedCategory.Plus.homologyFunctor D n) ≪≫
        Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
          (plusHomologyFactors D n)
    letI b := plusHomologyFactors C n
    a.symm.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (homologyChangeOfFunctorIso F n).hom =
      (homotopyCategoryPlusChangeOfFunctorIso F n).hom ≫
        Functor.whiskerRight b.inv F ≫
        (Functor.associator (DerivedCategory.Plus.Qh (C := C))
          (DerivedCategory.Plus.homologyFunctor C n) F).hom := by
  let a :
      DerivedCategory.Plus.Qh (C := C) ⋙
          (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
        F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
          HomotopyCategory.homologyFunctor D ℤᵘᵖ n :=
    (Functor.associator (DerivedCategory.Plus.Qh (C := C)) F.mapDerivedCategoryPlus
      (DerivedCategory.Plus.homologyFunctor D n)).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryPlusFactorsh F)
        (DerivedCategory.Plus.homologyFunctor D n) ≪≫
      Functor.associator F.mapHomotopyCategoryPlus (DerivedCategory.Plus.Qh (C := D))
        (DerivedCategory.Plus.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
        (plusHomologyFactors D n)
  let b := plusHomologyFactors C n
  let α := a.symm.hom
  let α' :
      HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F ⟶
        DerivedCategory.Plus.Qh (C := C) ⋙
          (DerivedCategory.Plus.homologyFunctor C n ⋙ F) :=
    Functor.whiskerRight b.inv F ≫
      (Functor.associator (DerivedCategory.Plus.Qh (C := C))
        (DerivedCategory.Plus.homologyFunctor C n) F).hom
  let :
      (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n).IsRightDerivedFunctor
        (L := DerivedCategory.Plus.Qh (C := C)) α (HomotopyCategory.Plus.quasiIso C) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
        HomotopyCategory.homologyFunctor D ℤᵘᵖ n)).isRightDerivedFunctor_of_isIso
      (L₂ := DerivedCategory.Plus.Qh (C := C)) α (fun K => by infer_instance)
  let :
      (DerivedCategory.Plus.homologyFunctor C n ⋙ F).IsRightDerivedFunctor
        (L := DerivedCategory.Plus.Qh (C := C)) α' (HomotopyCategory.Plus.quasiIso C) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C ℤᵘᵖ n ⋙ F)).isRightDerivedFunctor_of_isIso
      (L₂ := DerivedCategory.Plus.Qh (C := C)) α' (fun K => by infer_instance)
  exact Functor.rightDerivedNatTrans_fac
    (W := HomotopyCategory.Plus.quasiIso C) _ _ _ _ _

omit [EnoughInjectives D] in
/-- The inverse change-of-coefficients comparison for homology is compatible with the maps from
the bounded-below homotopy category. -/
@[reassoc]
lemma homologyChangeOfFunctorIso_inv_fac
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    letI a :
        DerivedCategory.Plus.Qh (C := C) ⋙
            (F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
          F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
            HomotopyCategory.homologyFunctor D ℤᵘᵖ n :=
      (Functor.associator (DerivedCategory.Plus.Qh (C := C)) F.mapDerivedCategoryPlus
        (DerivedCategory.Plus.homologyFunctor D n)).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryPlusFactorsh F)
          (DerivedCategory.Plus.homologyFunctor D n) ≪≫
        Functor.associator F.mapHomotopyCategoryPlus (DerivedCategory.Plus.Qh (C := D))
          (DerivedCategory.Plus.homologyFunctor D n) ≪≫
        Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
          (plusHomologyFactors D n)
    letI b := plusHomologyFactors C n
    (Functor.whiskerRight b.inv F ≫
        (Functor.associator (DerivedCategory.Plus.Qh (C := C))
          (DerivedCategory.Plus.homologyFunctor C n) F).hom) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (homologyChangeOfFunctorIso F n).inv =
      (homotopyCategoryPlusChangeOfFunctorIso F n).inv ≫ a.symm.hom := by
  apply (cancel_mono (Functor.whiskerLeft DerivedCategory.Plus.Qh
    (homologyChangeOfFunctorIso F n).hom)).1
  rw [Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.comp_id]
  rw [Category.assoc, homologyChangeOfFunctorIso_hom_fac]
  simp

end Generic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Change of coefficients carries the projection from cycles to homology to the
corresponding projection after applying the coefficient functor. -/
@[reassoc]
lemma homologicalComplexChangeOfFunctorIso_homologyπ
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) (n : ℤ) :
    ((F.mapHomologicalComplex ℤᵘᵖ).obj K).homologyπ n ≫
        (homologicalComplexChangeOfFunctorIso F n).hom.app K =
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) := by
  dsimp [TopCat.Sheaf.homologicalComplexChangeOfFunctorIso,
    HomologicalComplex.homologyFunctorIso, ShortComplex.homologyFunctorIso,
    HomologicalComplex.homologyFunctor, HomologicalComplex.shortComplexFunctor,
    ShortComplex.homologyFunctor]
  change ((K.sc n).map F).homologyπ ≫ 𝟙 _ ≫
    (ShortComplex.homologyMap (𝟙 ((K.sc n).map F)) ≫
      ((K.sc n).mapHomologyIso F).hom ≫ F.map (𝟙 (K.sc n).homology)) =
    ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.sc n).homologyπ
  simp only [ShortComplex.homologyMap_id, F.map_id, Category.id_comp, Category.comp_id]
  rw [(K.sc n).leftHomologyData.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change ((K.sc n).mapCyclesIso F).hom ≫
    F.map (K.sc n).leftHomologyπ ≫ F.map (K.sc n).leftHomologyData.homologyIso.inv = _
  rw [← Functor.map_comp]
  congr 2
  rw [ShortComplex.LeftHomologyData.homologyIso_leftHomologyData]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf in
/-- The degree-zero homology comparison sends a cycle to its global section. -/
@[reassoc]
lemma globalSectionsSingle₀HomologyIso_homologyπ
    (X : TopCat.{w}) [HasSheafify (Opens.grothendieckTopology X) C] (A : Sheaf C X) :
    letI K := ((CochainComplex.Plus.single₀ (Sheaf C X)).obj A).obj
    (globalSectionsComplex X K).homologyπ 0 ≫
        (globalSectionsSingle₀HomologyIso C X A).hom =
      (globalSectionsComplex X K).iCycles 0 ≫
        (globalSections C X).map
          ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).hom.f 0 ≫
            (HomologicalComplex.singleObjXSelf ℤᵘᵖ 0 A).hom) := by
  let Γ := globalSections C X
  let e := ComplexShape.embeddingUpNat
  let KN := (CochainComplex.single₀ (Sheaf C X)).obj A
  let E := HomologicalComplex.mapExtendCanonicalIso Γ KN e ≪≫
    (e.extendFunctor C).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app A) ≪≫
      HomologicalComplex.extendSingleIso e (Γ.obj A) 0 0 rfl
  change (globalSectionsComplex X (KN.extend e)).homologyπ 0 ≫
    HomologicalComplex.homologyMap E.hom 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso ℤᵘᵖ 0 (Γ.obj A)).hom = _
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i_assoc]
  congr 1
  dsimp only [E]
  simp only [Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_hom_f,
    Functor.map_comp, Category.assoc, Functor.mapIso_hom]
  have hB :
      ((e.extendFunctor C).map
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).app A).hom).f 0 =
        (HomologicalComplex.extendMap
          ((HomologicalComplex.singleMapHomologicalComplex Γ (.up ℕ) 0).hom.app A) e).f 0 := rfl
  rw [hB, HomologicalComplex.mapExtendCanonicalIso_hom_f Γ KN e
    (i := 0) (j := 0) rfl,
    HomologicalComplex.extendMap_f _ e (i := 0) (i' := 0) rfl,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  dsimp only [KN, CochainComplex.single₀]
  simp
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf globalSections in
/-- Applying an exact coefficient functor commutes with the degree-zero global-sections
comparison for a sheaf placed in degree zero. -/
@[reassoc]
lemma globalSectionsSingle₀HomologyIso_changeOfFunctor
    (X : TopCat.{w}) [HasSheafify (Opens.grothendieckTopology X) C]
    [HasSheafify (Opens.grothendieckTopology X) D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [(Opens.grothendieckTopology X).HasSheafCompose F]
    [hP : (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F).Additive]
    (A : Sheaf C X) :
    letI P : Sheaf C X ⥤ Sheaf D X :=
      CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
    letI : P.Additive := hP
    letI N := (CochainComplex.single₀ (Sheaf C X)).obj A
    letI δ := CochainComplex.Plus.mapSingle₀Iso P A
    HomologicalComplex.homologyMap
        (((globalSections D X).mapHomologicalComplex ℤᵘᵖ).map δ.hom.hom) 0 ≫
        (globalSectionsSingle₀HomologyIso D X (P.obj A)).hom =
      (homologicalComplexChangeOfFunctorIso F 0).hom.app
          (globalSectionsComplex X (N.extend ComplexShape.embeddingUpNat)) ≫
        F.map (globalSectionsSingle₀HomologyIso C X A).hom := by
  let P : Sheaf C X ⥤ Sheaf D X := CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
  let : P.Additive := hP
  let N := (CochainComplex.single₀ (Sheaf C X)).obj A
  let e := ComplexShape.embeddingUpNat
  let δ := CochainComplex.Plus.mapSingle₀Iso P A
  let G := globalSectionsComplex X (N.extend e)
  let T := (F.mapHomologicalComplex ℤᵘᵖ).obj G
  let GD := globalSectionsComplex X
    ((CochainComplex.Plus.single₀ (Sheaf D X)).obj (P.obj A)).obj
  let ψ : T ⟶ GD :=
    ((globalSections D X).mapHomologicalComplex ℤᵘᵖ).map δ.hom.hom
  change HomologicalComplex.homologyMap ψ 0 ≫
      (globalSectionsSingle₀HomologyIso D X (P.obj A)).hom =
    (homologicalComplexChangeOfFunctorIso F 0).hom.app G ≫
      F.map (globalSectionsSingle₀HomologyIso C X A).hom
  have hC := globalSectionsSingle₀HomologyIso_homologyπ X A
  change G.homologyπ 0 ≫ (globalSectionsSingle₀HomologyIso C X A).hom =
    G.iCycles 0 ≫ (globalSections C X).map _ at hC
  have hD := globalSectionsSingle₀HomologyIso_homologyπ X (P.obj A)
  change GD.homologyπ 0 ≫ (globalSectionsSingle₀HomologyIso D X (P.obj A)).hom =
    GD.iCycles 0 ≫ (globalSections D X).map _ at hD
  apply (cancel_epi (T.homologyπ 0)).1
  rw [homologicalComplexChangeOfFunctorIso_homologyπ_assoc, ← F.map_comp, hC,
    HomologicalComplex.homologyπ_naturality_assoc, hD, F.map_comp,
    HomologicalComplex.cyclesMap_i_assoc]
  have hF : ((G.sc 0).mapCyclesIso F).hom ≫ F.map (G.iCycles 0) = T.iCycles 0 :=
    (G.sc 0).mapCyclesIso_hom_iCycles F
  rw [reassoc_of% hF]
  congr 1
  change (globalSections D X).map (δ.hom.hom.f 0) ≫
      (globalSections D X).map _ =
    (globalSections D X).map (P.map
      ((HomologicalComplex.extendSingleIso e A 0 0 rfl).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf ℤᵘᵖ 0 A).hom))
  rw [← Functor.map_comp]
  congr 1
  dsimp only [δ, CochainComplex.Plus.mapSingle₀Iso]
  simp only [ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, Iso.trans_hom,
    HomologicalComplex.comp_f,
    Functor.mapIso_hom,
    HomologicalComplex.extendSingleIso_hom_f, Functor.map_comp, Category.assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_hom_f P N e (i := 0) (j := 0) rfl]
  have hB :
      ((e.extendFunctor (Sheaf D X)).map
        ((HomologicalComplex.singleMapHomologicalComplex P (.up ℕ) 0).app A).hom).f 0 =
      (HomologicalComplex.extendMap
        ((HomologicalComplex.singleMapHomologicalComplex P (.up ℕ) 0).hom.app A) e).f 0 := rfl
  rw [hB, HomologicalComplex.extendMap_f _ e (i := 0) (i' := 0) rfl,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  dsimp only [N, CochainComplex.single₀]
  simp

private lemma homotopyCategoryPlusChangeOfFunctorIso_inv_fac
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex.Plus C) (n : ℤ) :
    (homologicalComplexChangeOfFunctorIso F n).hom.app K.obj ≫
        F.map ((HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).inv.app K.obj) ≫
        (homotopyCategoryPlusChangeOfFunctorIso F n).inv.app
          ((HomotopyCategory.Plus.quotient C).obj K) =
      (HomotopyCategory.homologyFunctorFactors D ℤᵘᵖ n).inv.app
        ((F.mapHomologicalComplex ℤᵘᵖ).obj K.obj) := by
  simp [homotopyCategoryPlusChangeOfFunctorIso,
    homotopyCategoryChangeOfFunctorIso,
    Functor.mapHomotopyCategoryPlusCompιIso,
    ObjectProperty.liftCompιIso, HomotopyCategory.Plus.quotient,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
    Functor.mapIso, Iso.refl, Functor.whiskerLeft_app, ← Category.assoc]
  change
    (((homologicalComplexChangeOfFunctorIso F n).hom.app K.obj ≫
          F.map ((HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).inv.app K.obj)) ≫
        ((F.mapHomologicalComplex ℤᵘᵖ).isoWhiskerLeft
              (HomotopyCategory.homologyFunctorFactors D ℤᵘᵖ n) ≪≫
            homologicalComplexChangeOfFunctorIso F n ≪≫
            Functor.isoWhiskerRight
              (HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).symm F).inv.app K.obj) ≫ _ = _
  simp
  change _ ≫ (HomotopyCategory.homologyFunctor D ℤᵘᵖ n).map (𝟙 _) = _
  simp

section Generic

variable [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C]

variable {X : TopCat.{w}} [HasSheafify (Opens.grothendieckTopology X) C]
  [HasSheafify (Opens.grothendieckTopology X) D]
  [HasDerivedCategory (TopCat.Sheaf C X)] [HasDerivedCategory (TopCat.Sheaf D X)]
  [EnoughInjectives (TopCat.Sheaf C X)] [EnoughInjectives (TopCat.Sheaf D X)]

/-- An exact coefficient functor with an injective-preserving sheaf functor induces a
change-of-coefficients comparison for hypercohomology. -/
noncomputable def hypercohomologyChangeOfFunctorIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : TopCat.Sheaf C X ⥤ TopCat.Sheaf D X) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] [P.PreservesInjectiveObjects]
    (e : globalSections C X ⋙ F ≅ P ⋙ globalSections D X) (n : ℤ) :
    hypercohomologyFunctor C X n ⋙ F ≅
      P.mapCochainComplexPlus ⋙ hypercohomologyFunctor D X n :=
  letI d := Functor.mapDerivedCategoryPlus_rightDerivedFunctorPlus_natIso
    (globalSections C X) F P (globalSections D X) e
  letI h := homologyChangeOfFunctorIso F n
  letI p := Functor.mapDerivedCategoryPlusFactors P
  letI QC := DerivedCategory.Plus.Q (C := TopCat.Sheaf C X)
  letI QD := DerivedCategory.Plus.Q (C := TopCat.Sheaf D X)
  letI G₁ := derivedGlobalSectionsFunctor C X
  letI G₂ := derivedGlobalSectionsFunctor D X
  letI H₁ := DerivedCategory.Plus.homologyFunctor C n
  letI H₂ := DerivedCategory.Plus.homologyFunctor D n
  letI Pd := P.mapDerivedCategoryPlus
  letI Pc := P.mapCochainComplexPlus
  show (QC ⋙ G₁ ⋙ H₁ ⋙ F) ≅ Pc ⋙ QD ⋙ G₂ ⋙ H₂ from
    Functor.associator (QC ⋙ G₁) H₁ F ≪≫
      Functor.associator QC G₁ (H₁ ⋙ F) ≪≫
      Functor.isoWhiskerLeft QC (Functor.isoWhiskerLeft G₁ h.symm) ≪≫
      Functor.isoWhiskerLeft QC
        (Functor.associator G₁ F.mapDerivedCategoryPlus H₂).symm ≪≫
      Functor.isoWhiskerLeft QC (Functor.isoWhiskerRight d H₂) ≪≫
      Functor.isoWhiskerLeft QC (Functor.associator Pd G₂ H₂) ≪≫
      (Functor.associator QC Pd (G₂ ⋙ H₂)).symm ≪≫
      Functor.isoWhiskerRight p (G₂ ⋙ H₂) ≪≫
      Functor.associator Pc QD (G₂ ⋙ H₂) ≪≫
      Functor.isoWhiskerLeft Pc (Functor.associator QD G₂ H₂).symm ≪≫
      (Functor.associator Pc (QD ⋙ G₂) H₂).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator Pc QD G₂).symm H₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
theorem toHypercohomology_changeOfFunctor
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [(Opens.grothendieckTopology X).HasSheafCompose F]
    [hP : (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F).Additive]
    [hP₁ : PreservesFiniteLimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)]
    [hP₂ : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)]
    [hP₃ : (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) F).PreservesInjectiveObjects]
    (K : CochainComplex.Plus (TopCat.Sheaf C X)) (n : ℤ) :
    letI P : TopCat.Sheaf C X ⥤ TopCat.Sheaf D X :=
      CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
    letI : P.Additive := by
      change (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F).Additive
      exact hP
    letI : PreservesFiniteLimits P := by
      change PreservesFiniteLimits
        (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)
      exact hP₁
    letI : PreservesFiniteColimits P := by
      change PreservesFiniteColimits
        (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)
      exact hP₂
    letI : P.PreservesInjectiveObjects := by
      change (CategoryTheory.sheafCompose
        (Opens.grothendieckTopology X) F).PreservesInjectiveObjects
      exact hP₃
    (homologicalComplexChangeOfFunctorIso F n).hom.app
          (globalSectionsComplex X K.obj) ≫
      F.map ((toHypercohomology C X n).app K) ≫
      (hypercohomologyChangeOfFunctorIso F P (Iso.refl _) n).hom.app K =
      (toHypercohomology D X n).app (P.mapCochainComplexPlus.obj K) := by
  let P : TopCat.Sheaf C X ⥤ TopCat.Sheaf D X :=
    CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
  let : P.Additive := by
    change (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F).Additive
    exact hP
  let : PreservesFiniteLimits P := by
    change PreservesFiniteLimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)
    exact hP₁
  let : PreservesFiniteColimits P := by
    change PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)
    exact hP₂
  let : P.PreservesInjectiveObjects := by
    change (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) F).PreservesInjectiveObjects
    exact hP₃
  let QK := (HomotopyCategory.Plus.quotient (TopCat.Sheaf C X)).obj K
  let GK := (globalSections C X).mapHomotopyCategoryPlus.obj QK
  let KΓ := (globalSections C X).mapCochainComplexPlus.obj K
  have hhom := homotopyCategoryPlusChangeOfFunctorIso_inv_fac F KΓ n
  change (homologicalComplexChangeOfFunctorIso F n).hom.app KΓ.obj ≫
      F.map ((HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).inv.app KΓ.obj) ≫
      (homotopyCategoryPlusChangeOfFunctorIso F n).inv.app GK =
    (HomotopyCategory.homologyFunctorFactors D ℤᵘᵖ n).inv.app
      ((F.mapHomologicalComplex ℤᵘᵖ).obj KΓ.obj) at hhom
  have hh := congrArg (fun t => t.app GK)
    (homologyChangeOfFunctorIso_inv_fac F n)
  simp only [Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hh
  have hG :
      (homologicalComplexChangeOfFunctorIso F n).hom.app
          (globalSectionsComplex X K.obj) ≫
        F.map ((globalSectionsHomologyIso C X n).inv.app K) ≫
        (homologyChangeOfFunctorIso F n).inv.app
          (DerivedCategory.Plus.Qh.obj GK) =
      (globalSectionsHomologyIso D X n).inv.app
          (P.mapCochainComplexPlus.obj K) ≫
          (DerivedCategory.Plus.homologyFunctor D n).map
          (F.mapDerivedCategoryPlusFactorsh.inv.app GK) := by
    have h := congrArg (fun f =>
      (homologicalComplexChangeOfFunctorIso F n).hom.app KΓ.obj ≫
        F.map ((HomotopyCategory.homologyFunctorFactors C ℤᵘᵖ n).inv.app KΓ.obj) ≫ f) hh
    rw [reassoc_of% hhom] at h
    simp only [globalSectionsHomologyIso, plusHomologyFactors, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.refl_inv, NatTrans.id_app, Functor.comp_obj, Functor.map_comp,
      CategoryTheory.Functor.map_id, Category.id_comp,
      Category.assoc, KΓ, GK, QK] at h ⊢
    exact h
  have hd := congrArg (fun t => t.app QK)
    (CategoryTheory.Functor.mapDerivedCategoryPlus_rightDerivedFunctorPlus_natIso_hom_fac
      (globalSections C X) F P (globalSections D X) (Iso.refl _))
  dsimp only [Functor.rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit,
    Functor.mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hd
  have ht : (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (globalSections C X ⋙ F)) ≪≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (P ⋙ globalSections D X))).symm)
      DerivedCategory.Plus.Qh).hom.app QK = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D ℤᵘᵖ).map (𝟙 _) ≫
        (HomotopyCategory.quotient D ℤᵘᵖ).map (𝟙 _)) = 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ht] at hd
  erw [Category.id_comp] at hd
  let u := (globalSections C X).rightDerivedFunctorPlusUnit.app QK
  have hn := (homologyChangeOfFunctorIso F n).inv.naturality u
  simp only [Functor.comp_map] at hn
  unfold toHypercohomology hypercohomologyChangeOfFunctorIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map,
    Functor.comp_obj, derivedGlobalSectionsFunctor, hypercohomologyFunctor,
    DerivedCategory.Plus.Q]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [reassoc_of% hn, reassoc_of% hG]
  have hdH := congrArg (fun t =>
    (DerivedCategory.Plus.homologyFunctor D n).map t) hd
  simp only [Functor.map_comp, Category.assoc] at hdH
  rw [reassoc_of% hdH, ← P.mapDerivedCategoryPlusFactorsh_hom_app K]
  have hc := congrArg (fun f => (DerivedCategory.Plus.homologyFunctor D n).map
      ((globalSections D X).rightDerivedFunctorPlus.map f))
    (P.mapDerivedCategoryPlusFactorsh.inv_hom_id_app QK)
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [hc]
  erw [Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf in
/-- The map from global sections to degree-zero hypercohomology commutes with an exact
change of coefficients preserving injective sheaves. -/
@[reassoc]
theorem globalSectionsSingle₀_toHypercohomology_changeOfFunctor
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [(Opens.grothendieckTopology X).HasSheafCompose F]
    [hP : (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F).Additive]
    [hP₁ : PreservesFiniteLimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)]
    [hP₂ : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F)]
    [hP₃ : (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) F).PreservesInjectiveObjects]
    (A : Sheaf C X) :
    letI P : Sheaf C X ⥤ Sheaf D X :=
      CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
    letI : P.Additive := hP
    letI : PreservesFiniteLimits P := hP₁
    letI : PreservesFiniteColimits P := hP₂
    letI : P.PreservesInjectiveObjects := hP₃
    letI K := (CochainComplex.Plus.single₀ (Sheaf C X)).obj A
    letI δ := CochainComplex.Plus.mapSingle₀Iso P A
    F.map (globalSectionsSingle₀HomologyIso C X A).inv ≫
        F.map ((toHypercohomology C X 0).app K) ≫
        (hypercohomologyChangeOfFunctorIso F P (Iso.refl _) 0).hom.app K ≫
        (hypercohomologyFunctor D X 0).map δ.hom =
      (globalSectionsSingle₀HomologyIso D X (P.obj A)).inv ≫
        (toHypercohomology D X 0).app
          ((CochainComplex.Plus.single₀ (Sheaf D X)).obj (P.obj A)) := by
  let P : Sheaf C X ⥤ Sheaf D X :=
    CategoryTheory.sheafCompose (Opens.grothendieckTopology X) F
  let : P.Additive := hP
  let : PreservesFiniteLimits P := hP₁
  let : PreservesFiniteColimits P := hP₂
  let : P.PreservesInjectiveObjects := hP₃
  let K := (CochainComplex.Plus.single₀ (Sheaf C X)).obj A
  let δ := CochainComplex.Plus.mapSingle₀Iso P A
  apply (Iso.cancel_iso_hom_left
    ((homologicalComplexChangeOfFunctorIso F 0).app (globalSectionsComplex X K.obj) ≪≫
      F.mapIso (globalSectionsSingle₀HomologyIso C X A)) _ _).1
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  let η := toHypercohomology D X 0
  let L := (CochainComplex.Plus.single₀ (Sheaf D X)).obj (P.obj A)
  let g := HomologicalComplex.homologyMap
    (((globalSections D X).mapHomologicalComplex ℤᵘᵖ).map δ.hom.hom) 0
  let e := globalSectionsSingle₀HomologyIso D X (P.obj A)
  calc
    _ = η.app (P.mapCochainComplexPlus.obj K) ≫
        (hypercohomologyFunctor D X 0).map δ.hom :=
      (reassoc_of% (toHypercohomology_changeOfFunctor F K 0)) _
    _ = g ≫ η.app L := (η.naturality δ.hom).symm
    _ = (g ≫ e.hom) ≫ e.inv ≫ η.app L := by simp
    _ = _ := by
      have h := congrArg (fun f => f ≫ e.inv ≫ η.app L)
        (globalSectionsSingle₀HomologyIso_changeOfFunctor X F A)
      exact h.trans (Category.assoc _ _ _)

end Generic

/-- The forgetful functor from `K`-modules to abelian groups induces a hypercohomology comparison.
The sheaf functor must preserve injectives. -/
noncomputable def hypercohomologyForget₂Iso
    {K : Type u} [Ring K] (X : TopCat.{w}) (n : ℤ)
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat K)]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [(Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ (ModuleCat K) AddCommGrpCat)]
    [HasDerivedCategory (ModuleCat K)] [HasDerivedCategory AddCommGrpCat]
    [HasDerivedCategory (TopCat.Sheaf (ModuleCat K) X)]
    [HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X)]
    [EnoughInjectives (TopCat.Sheaf (ModuleCat K) X)]
    [EnoughInjectives (TopCat.Sheaf AddCommGrpCat X)]
    [((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat K) AddCommGrpCat))).Additive]
    [PreservesFiniteLimits (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat K) AddCommGrpCat))]
    [PreservesFiniteColimits (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat K) AddCommGrpCat))]
    [Functor.PreservesInjectiveObjects (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) (forget₂ (ModuleCat K) AddCommGrpCat))] :
    hypercohomologyFunctor (ModuleCat K) X n ⋙
        forget₂ (ModuleCat K) AddCommGrpCat ≅
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat K) AddCommGrpCat)).mapCochainComplexPlus ⋙
    hypercohomologyFunctor AddCommGrpCat X n :=
  letI : EnoughInjectives (ModuleCat K) := ModuleCat.enoughInjectives K
  letI P : TopCat.Sheaf (ModuleCat K) X ⥤ TopCat.Sheaf AddCommGrpCat X :=
    CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat K) AddCommGrpCat)
  letI : P.Additive := by
    change (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat K) AddCommGrpCat)).Additive
    infer_instance
  letI : PreservesFiniteLimits P := by
    change PreservesFiniteLimits (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) (forget₂ (ModuleCat K) AddCommGrpCat))
    infer_instance
  letI : PreservesFiniteColimits P := by
    change PreservesFiniteColimits (CategoryTheory.sheafCompose
      (Opens.grothendieckTopology X) (forget₂ (ModuleCat K) AddCommGrpCat))
    infer_instance
  letI : P.PreservesInjectiveObjects := by
    change (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat K) AddCommGrpCat)).PreservesInjectiveObjects
    infer_instance
  hypercohomologyChangeOfFunctorIso
    (forget₂ (ModuleCat K) AddCommGrpCat)
    P
    (Iso.refl _) n

/-- Restriction of scalars along a flat ring homomorphism commutes with hypercohomology. -/
noncomputable def hypercohomologyChangeOfRingsIso (n : ℤ)
    (hf : f.Flat) :
    hypercohomologyFunctor (ModuleCat S) X n ⋙ ModuleCat.restrictScalars f ≅
      (CategoryTheory.Sheaf.restrictScalars (Opens.grothendieckTopology X) f).mapCochainComplexPlus ⋙
        hypercohomologyFunctor (ModuleCat R) X n :=
  letI P : TopCat.Sheaf (ModuleCat S) X ⥤ TopCat.Sheaf (ModuleCat R) X :=
    CategoryTheory.Sheaf.restrictScalars (Opens.grothendieckTopology X) f
  letI : P.Additive :=
    CategoryTheory.Sheaf.restrictScalars_additive (Opens.grothendieckTopology X) f
  letI : PreservesFiniteLimits P := by
    change PreservesFiniteLimits
      (CategoryTheory.Sheaf.restrictScalars (Opens.grothendieckTopology X) f)
    infer_instance
  letI : PreservesFiniteColimits P := by
    change PreservesFiniteColimits
      (CategoryTheory.Sheaf.restrictScalars (Opens.grothendieckTopology X) f)
    exact CategoryTheory.Sheaf.restrictScalars_preservesFiniteColimits
      (Opens.grothendieckTopology X) f
  letI : P.PreservesInjectiveObjects := by
    change (CategoryTheory.Sheaf.restrictScalars
      (Opens.grothendieckTopology X) f).PreservesInjectiveObjects
    exact CategoryTheory.Sheaf.restrictScalars_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology X) f hf
  hypercohomologyChangeOfFunctorIso
    (ModuleCat.restrictScalars f)
    P
    (globalSectionsChangeOfRingsIso f X) n

end DerivedCategory

end TopCat.Sheaf
