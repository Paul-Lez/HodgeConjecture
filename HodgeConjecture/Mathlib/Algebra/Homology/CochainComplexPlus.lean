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

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Bounded-below cochain complexes

This file provides the degree-zero functor into bounded-below cochain complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CochainComplex.Plus

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The functor from `C` to bounded-below cochain complexes supported in degree zero. -/
noncomputable abbrev single₀ : C ⥤ CochainComplex.Plus C :=
  (CochainComplex.plus C).lift
    (CochainComplex.single₀ C ⋙ ComplexShape.embeddingUpNat.extendFunctor C)
    (fun A ↦ ⟨0, (inferInstance : CochainComplex.IsStrictlyGE
      (((CochainComplex.single₀ C).obj A).extend ComplexShape.embeddingUpNat) 0)⟩)

instance single₀_obj_isStrictlyGE (A : C) : ((single₀ C).obj A).obj.IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE
    (((CochainComplex.single₀ C).obj A).extend ComplexShape.embeddingUpNat) 0
  infer_instance

instance single₀_additive : (single₀ C).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (CochainComplex.single₀ C ⋙
      ComplexShape.embeddingUpNat.extendFunctor C).map_add

instance single₀_linear (R : Type*) [Semiring R] [Linear R C] :
    Functor.Linear R (single₀ C) where
  map_smul {X Y} f r := by
    apply ObjectProperty.hom_ext
    change HomologicalComplex.extendMap ((CochainComplex.single₀ C).map (r • f))
        ComplexShape.embeddingUpNat =
      r • HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f)
        ComplexShape.embeddingUpNat
    ext i
    by_cases hi : ∃ j, ComplexShape.embeddingUpNat.f j = i
    · obtain ⟨j, hj⟩ := hi
      rw [HomologicalComplex.extendMap_f _ _ hj]
      change _ = r •
        (HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f)
          ComplexShape.embeddingUpNat).f i
      rw [HomologicalComplex.extendMap_f _ _ hj]
      by_cases hj₀ : j = 0
      · subst j
        simp
      · let h := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 X j hj₀
        rw [h.eq_zero_of_tgt
          (HomologicalComplex.extendXIso ((CochainComplex.single₀ C).obj X)
            ComplexShape.embeddingUpNat hj).hom,
          zero_comp]
        simp
    · apply (((CochainComplex.single₀ C).obj _).isZero_extend_X
        ComplexShape.embeddingUpNat i (fun j hj ↦ hi ⟨j, hj⟩)).eq_of_src

/-- The canonical comparison for the image of a degree-zero single complex under an additive
functor. -/
def mapSingle₀Iso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] (A : C) :
    F.mapCochainComplexPlus.obj ((CochainComplex.Plus.single₀ C).obj A) ≅
      (CochainComplex.Plus.single₀ D).obj (F.obj A) :=
  ObjectProperty.isoMk (CochainComplex.plus D)
    (HomologicalComplex.mapExtendCanonicalIso F ((CochainComplex.single₀ C).obj A)
      ComplexShape.embeddingUpNat ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor D).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).app A))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison between mapping a degree-zero single complex and taking the degree-zero
single complex of the mapped object is natural. -/
@[reassoc]
lemma mapSingle₀Iso_hom_naturality {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {A B : C} (f : A ⟶ B) :
    F.mapCochainComplexPlus.map ((CochainComplex.Plus.single₀ C).map f) ≫
        (mapSingle₀Iso F B).hom =
      (mapSingle₀Iso F A).hom ≫
        (CochainComplex.Plus.single₀ D).map (F.map f) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  dsimp only [mapSingle₀Iso, Functor.mapCochainComplexPlus,
    CochainComplex.Plus.single₀, ObjectProperty.isoMk_hom, Iso.trans_hom,
    Functor.comp_map, ObjectProperty.homMk_hom, ObjectProperty.lift,
    ObjectProperty.homMk, ObjectProperty.isoMk, CochainComplex.Plus.ι,
    ComplexShape.Embedding.extendFunctor]
  simp only [ObjectProperty.ι_map, Functor.mapIso_hom]
  change (F.mapHomologicalComplex ℤᵘᵖ).map
      ((ComplexShape.embeddingUpNat.extendFunctor C).map
        ((CochainComplex.single₀ C).map f)) ≫
      (HomologicalComplex.mapExtendCanonicalIso F ((CochainComplex.single₀ C).obj B)
        ComplexShape.embeddingUpNat).hom ≫
      (ComplexShape.embeddingUpNat.extendFunctor D).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).app B).hom =
    ((HomologicalComplex.mapExtendCanonicalIso F ((CochainComplex.single₀ C).obj A)
        ComplexShape.embeddingUpNat).hom ≫
      (ComplexShape.embeddingUpNat.extendFunctor D).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).app A).hom) ≫
      (ComplexShape.embeddingUpNat.extendFunctor D).map
        ((CochainComplex.single₀ D).map (F.map f))
  rw [show (ComplexShape.embeddingUpNat.extendFunctor C).map
      ((CochainComplex.single₀ C).map f) =
    HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f)
      ComplexShape.embeddingUpNat from rfl]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  have hn := (ComplexShape.embeddingUpNat.extendFunctor D).congr_map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).hom.naturality f)
  rw [Functor.map_comp, Functor.map_comp] at hn
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inverse degree-zero comparison. -/
@[reassoc]
lemma mapSingle₀Iso_inv_naturality {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive] {A B : C} (f : A ⟶ B) :
    (CochainComplex.Plus.single₀ D).map (F.map f) ≫
        (mapSingle₀Iso F B).inv =
      (mapSingle₀Iso F A).inv ≫
        F.mapCochainComplexPlus.map ((CochainComplex.Plus.single₀ C).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, mapSingle₀Iso_hom_naturality,
    Iso.inv_hom_id_assoc]

end CochainComplex.Plus
