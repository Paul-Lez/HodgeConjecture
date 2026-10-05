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

public import HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctorPlus
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNaturality
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact functors and bounded-below right derived functors
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃]
  [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]
  [HasDerivedCategory.{w₃} C₃]

/-- The composition of a bounded-below right derived functor with an exact functor. -/
noncomputable def rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit
    (G : C₁ ⥤ C₂) [G.Additive] [EnoughInjectives C₁]
    (F : C₂ ⥤ C₃) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    G.mapHomotopyCategoryPlus ⋙ F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus :=
  Functor.whiskerLeft G.mapHomotopyCategoryPlus (F.mapDerivedCategoryPlusFactorsh).inv ≫
    Functor.whiskerRight G.rightDerivedFunctorPlusUnit (F.mapDerivedCategoryPlus)

instance rightDerivedFunctorPlus_mapDerivedCategoryPlus_isRightDerivedFunctor
    (G : C₁ ⥤ C₂) [G.Additive] [EnoughInjectives C₁]
    (F : C₂ ⥤ C₃) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (G.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit G F)
      (HomotopyCategory.Plus.quasiIso C₁) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    (G.mapHomotopyCategoryPlus ⋙ F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso
    (rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit G F) (fun K => by
      dsimp [rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit]
      infer_instance)

/-- The composition of an exact functor with a bounded-below right derived functor. -/
noncomputable def mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit
    (P : C₁ ⥤ C₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesInjectiveObjects]
    (G : C₂ ⥤ C₃) [G.Additive] [EnoughInjectives C₁] [EnoughInjectives C₂] :
    P.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ P.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.whiskerLeft P.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (P.mapDerivedCategoryPlusFactorsh).inv
      G.rightDerivedFunctorPlus

instance mapDerivedCategoryPlus_rightDerivedFunctorPlus_isRightDerivedFunctor
    (P : C₁ ⥤ C₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesInjectiveObjects]
    (G : C₂ ⥤ C₃) [G.Additive] [EnoughInjectives C₁] [EnoughInjectives C₂] :
    (P.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit P G)
      (HomotopyCategory.Plus.quasiIso C₁) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    (P.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso
    (mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit P G) (fun K => by
      dsimp [mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit]
      apply IsIso.comp_isIso'
      · let K' := P.mapHomotopyCategoryPlus.obj
          ((InjectiveObject.ι C₁).mapHomotopyCategoryPlus.obj K)
        change IsIso (G.rightDerivedFunctorPlusUnit.app K')
        have h (Y : HomotopyCategory.Plus (InjectiveObject C₂)) :
            IsIso (G.rightDerivedFunctorPlusUnit.app
              ((InjectiveObject.ι C₂).mapHomotopyCategoryPlus.obj Y)) :=
          (HomotopyCategory.Plus.localizerMorphism_derives
            (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
            G.rightDerivedFunctorPlusUnit Y
        have hK' (n : ℤ) : Injective (K'.obj.as.X n) := by
          change Injective (P.obj (K.obj.as.X n).obj)
          exact P.injective_obj_of_injective (K.obj.as.X n).property
        obtain ⟨Y, ⟨e⟩⟩ :
            (InjectiveObject.ι C₂).mapHomotopyCategoryPlus.essImage K' := by
          obtain ⟨X, hX⟩ := K'
          obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective X
          refine ⟨(HomotopyCategory.Plus.quotient _).obj
            ((CochainComplex.Plus.fibrantObjectEquivalence C₂).inverse.obj
              ⟨⟨K', by simpa using hX⟩, ?_⟩), ⟨Iso.refl _⟩⟩
          dsimp [HomotopicalAlgebra.fibrantObjects]
          rw [CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff]
          exact hK'
        rw [← NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnit e]
        exact h Y
      · infer_instance)

/-- The comparison of the two exact/right-derived composites induced by an underived isomorphism. -/
noncomputable def mapDerivedCategoryPlus_rightDerivedFunctorPlus_natIso
    {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]
    (G₁ : C₁ ⥤ C₂) [G₁.Additive] [EnoughInjectives C₁]
    (F : C₂ ⥤ C₄) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : C₁ ⥤ C₃) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesInjectiveObjects]
    (G₂ : C₃ ⥤ C₄) [G₂.Additive] [EnoughInjectives C₃]
    (e : G₁ ⋙ F ≅ P ⋙ G₂) :
    G₁.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus ≅
      P.mapDerivedCategoryPlus ⋙ G₂.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso
    (G₁.rightDerivedFunctorPlus ⋙ F.mapDerivedCategoryPlus)
    (P.mapDerivedCategoryPlus ⋙ G₂.rightDerivedFunctorPlus)
    (rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit G₁ F)
    (mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit P G₂)
    (HomotopyCategory.Plus.quasiIso C₁)
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso e ≪≫
        (Functor.mapHomotopyCategoryPlusCompIso (F := P) (G := G₂) (H := P ⋙ G₂)
          (Iso.refl _)).symm)
      DerivedCategory.Plus.Qh)

/-- The comparison of exact/right-derived composites is compatible with the derived units. -/
@[reassoc]
lemma mapDerivedCategoryPlus_rightDerivedFunctorPlus_natIso_hom_fac
    {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]
    (G₁ : C₁ ⥤ C₂) [G₁.Additive] [EnoughInjectives C₁]
    (F : C₂ ⥤ C₄) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : C₁ ⥤ C₃) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesInjectiveObjects]
    (G₂ : C₃ ⥤ C₄) [G₂.Additive] [EnoughInjectives C₃]
    (e : G₁ ⋙ F ≅ P ⋙ G₂) :
    rightDerivedFunctorPlus_mapDerivedCategoryPlusUnit G₁ F ≫
        whiskerLeft DerivedCategory.Plus.Qh
          (mapDerivedCategoryPlus_rightDerivedFunctorPlus_natIso G₁ F P G₂ e).hom =
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryPlusCompIso e ≪≫
          (Functor.mapHomotopyCategoryPlusCompIso (F := P) (G := G₂) (H := P ⋙ G₂)
            (Iso.refl _)).symm)
        DerivedCategory.Plus.Qh).hom ≫
        mapDerivedCategoryPlus_rightDerivedFunctorPlusUnit P G₂ :=
  Functor.rightDerivedNatTrans_fac
    (W := HomotopyCategory.Plus.quasiIso C₁) _ _ _ _ _

end CategoryTheory.Functor
