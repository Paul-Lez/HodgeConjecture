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

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import HodgeConjecture.Mathlib.Algebra.Homology.CochainComplexPlus
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Exact functors on bounded-below derived categories
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace CategoryTheory.Functor

/-- The functor induced by an exact functor on bounded-below derived categories. -/
noncomputable def mapDerivedCategoryPlus :
    DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂ :=
  (DerivedCategory.TStructure.t (C := C₂)).plus.lift
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
      intro K
      obtain ⟨n, hK⟩ := K.2
      obtain ⟨L, e, hL⟩ := hK
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff] at hL
      have hQ : (DerivedCategory.Q.obj
          ((F.mapHomologicalComplex ℤᵘᵖ).obj L)).IsGE n := by
        rw [DerivedCategory.isGE_Q_obj_iff, CochainComplex.isGE_iff]
        intro i hi
        exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (hL i hi))
      exact ⟨(DerivedCategory.TStructure.t.ge n).prop_of_iso
        ((F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app L).symm) hQ.ge⟩)

/-- The inclusion of `mapDerivedCategoryPlus` into the full derived category. -/
noncomputable def mapDerivedCategoryPlusCompιIso :
    mapDerivedCategoryPlus F ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  (DerivedCategory.TStructure.t (C := C₂)).plus.liftCompιIso
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) _

instance mapDerivedCategoryPlus_additive : (mapDerivedCategoryPlus F).Additive := by
  let _ : (mapDerivedCategoryPlus F ⋙ DerivedCategory.Plus.ι).Additive :=
    Functor.additive_of_iso (mapDerivedCategoryPlusCompιIso F).symm
  exact Functor.additive_of_comp_faithful (mapDerivedCategoryPlus F)
    (DerivedCategory.Plus.ι (C := C₂))

/-- The inclusion of the bounded-below homotopy-category map into the full homotopy category. -/
noncomputable def mapHomotopyCategoryPlusCompιIso :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι C₂ ≅
      HomotopyCategory.Plus.ι C₁ ⋙ F.mapHomotopyCategory ℤᵘᵖ :=
  (HomotopyCategory.plus C₂).liftCompιIso
    (HomotopyCategory.Plus.ι C₁ ⋙ F.mapHomotopyCategory ℤᵘᵖ) _

/-- `mapDerivedCategoryPlus` is induced by the map on bounded-below complexes. -/
noncomputable def mapDerivedCategoryPlusFactors :
    DerivedCategory.Plus.Q ⋙ mapDerivedCategoryPlus F ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  letI e :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.Q (C := C₁))
        (mapDerivedCategoryPlusCompιIso F) ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIsoιCompQ C₁)
        F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι C₁)
        F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (F.mapCochainComplexPlusCompι).symm DerivedCategory.Q ≪≫
      (Functor.isoWhiskerLeft F.mapCochainComplexPlus
        (DerivedCategory.Plus.QCompιIsoιCompQ C₂)).symm
  NatIso.ofComponents
    (fun K => (DerivedCategory.TStructure.t (C := C₂)).plus.isoMk (e.app K))
    (fun f => by
      apply (DerivedCategory.TStructure.t (C := C₂)).plus.ι.map_injective
      exact e.hom.naturality f)

/-- `mapDerivedCategoryPlus` is induced by the map on bounded-below homotopy categories. -/
noncomputable def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ mapDerivedCategoryPlus F ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  letI e :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.Qh (C := C₁))
        (mapDerivedCategoryPlusCompιIso F) ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C₁)
        F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι C₁)
        F.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryPlusCompιIso F).symm DerivedCategory.Qh ≪≫
      (Functor.isoWhiskerLeft F.mapHomotopyCategoryPlus
        (DerivedCategory.Plus.QhCompιIsoιCompQh C₂)).symm
  NatIso.ofComponents
    (fun K => (DerivedCategory.TStructure.t (C := C₂)).plus.isoMk (e.app K))
    (fun f => by
      apply (DerivedCategory.TStructure.t (C := C₂)).plus.ι.map_injective
      exact e.hom.naturality f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma mapDerivedCategoryPlusFactorsh_hom_app
    (K : CochainComplex.Plus C₁) :
    F.mapDerivedCategoryPlusFactorsh.hom.app
        ((HomotopyCategory.Plus.quotient C₁).obj K) =
      F.mapDerivedCategoryPlusFactors.hom.app K := by
  apply ObjectProperty.hom_ext
  simp only [Functor.comp_obj, mapDerivedCategoryPlusFactorsh, NatIso.trans_app,
    mapDerivedCategoryPlusFactors, mapDerivedCategoryPlus, mapDerivedCategoryPlusCompιIso,
    mapHomotopyCategoryPlus, mapHomotopyCategoryPlusCompιIso,
    DerivedCategory.Plus.Qh,
    DerivedCategory.Plus.QhCompιIsoιCompQh, DerivedCategory.Plus.QCompιIsoιCompQ,
    mapCochainComplexPlusCompι,
    ObjectProperty.liftCompιIso,
    Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.map_id, Category.id_comp,
    ObjectProperty.ι_obj, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, ObjectProperty.homMk_hom,
    HomotopyCategory.Plus.quotient]
  simp [HomotopyCategory.Plus.quotientCompιIso, ObjectProperty.liftCompιIso]
  erw [F.mapDerivedCategory.map_id, (HomotopyCategory.quotient C₂ ℤᵘᵖ).map_id,
    DerivedCategory.Qh.map_id]
  change F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C₁ ℤᵘᵖ).obj K.obj) =
    𝟙 _ ≫ 𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app K.obj ≫ 𝟙 _ ≫ 𝟙 _
  have h := mapDerivedCategoryFactorsh_hom_app F K.obj
  change F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C₁ ℤᵘᵖ).obj K.obj) =
    F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app K.obj ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at h
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at h ⊢
  erw [Category.comp_id] at h
  exact h

end CategoryTheory.Functor
