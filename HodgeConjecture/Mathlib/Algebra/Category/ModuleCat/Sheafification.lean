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

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Module-valued sheafification

Mathlib provides sheafification of module-valued presheaves. This file records the linearity and
forgetful-comparison properties needed by the Hodge Conjecture development.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

variable {C R : Type u} [Category.{u} C] [Ring R] (J : GrothendieckTopology C)

variable [HasSheafify J AddCommGrpCat.{u}]

namespace ModuleCatSheafification

noncomputable instance moduleCat_sheafCompose_additive :
    (sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).Additive := by
  constructor
  intro X Y f g
  apply (sheafToPresheaf J AddCommGrpCat.{u}).map_injective
  change (((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map (f.hom + g.hom)) = _
  rw [Functor.map_add]
  rfl

noncomputable instance moduleCat_sheafCompose_preservesFiniteLimits :
    PreservesFiniteLimits (sheafCompose J
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) := by
  let h : PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙
        sheafToPresheaf J AddCommGrpCat.{u}) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J (ModuleCat.{u} R) ⋙
        (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
    infer_instance
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _
    (sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
      (sheafToPresheaf J AddCommGrpCat.{u}) h
    (@reflectsFiniteLimits_of_reflectsIsomorphisms _ _ _ _
      (sheafToPresheaf J AddCommGrpCat.{u}) (by infer_instance) inferInstance inferInstance)

noncomputable instance moduleCat_sheafCompose_reflectsFiniteLimits :
    ReflectsFiniteLimits (sheafCompose J
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) := by
  exact @reflectsFiniteLimits_of_reflectsIsomorphisms _ _ _ _
    (sheafCompose J (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
      (by infer_instance) inferInstance inferInstance

section Linear

variable {S : Type u} [CommRing S]

instance moduleCat_const_linear :
    Functor.Linear S
      (Functor.const Cᵒᵖ : ModuleCat.{u} S ⥤ Cᵒᵖ ⥤ ModuleCat.{u} S) where
  map_smul := by
    intro X Y f r
    ext U x
    rfl

instance moduleCat_presheafToSheaf_linear :
    Functor.Linear S
      (presheafToSheaf J (ModuleCat.{u} S)) := by
  rw [Functor.linear_iff]
  intro P r
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext J
    ((presheafToSheaf J (ModuleCat.{u} S)).map (r • 𝟙 P)).hom
    ((r • 𝟙 ((presheafToSheaf J (ModuleCat.{u} S)).obj P)).hom)
    ((presheafToSheaf J (ModuleCat.{u} S)).obj P).property
  change toSheafify J P ≫ sheafifyMap J (r • 𝟙 P) = _
  rw [← toSheafify_naturality, Linear.smul_comp, Category.id_comp]
  ext U x
  rfl

noncomputable instance moduleCat_constantSheaf_linear :
    Functor.Linear S (constantSheaf J (ModuleCat.{u} S)) := by
  dsimp only [constantSheaf]
  infer_instance

end Linear

section Integers

noncomputable def integerForget_compAdjunction :
    Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ⊣
      sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse :=
  Sheaf.adjunction J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.toAdjunction

noncomputable def integerForget_compIso :
    Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ≅
      sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun X => @asIso _ _ _ _
      ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).counit.app
        ((sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).obj X))
      (isIso_sheafificationAdjunction_counit
        ((sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).obj X)))
    (fun f => (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).counit.naturality
      ((sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).map f))

noncomputable instance integerForget_sheafCompose_isLeftAdjoint :
    (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).IsLeftAdjoint :=
  ((integerForget_compAdjunction J).ofNatIsoLeft (integerForget_compIso J)).isLeftAdjoint

noncomputable instance integerForget_sheafCompose_preservesFiniteLimits :
    PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})) := by
  let h : PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ⋙
        sheafToPresheaf J AddCommGrpCat.{u}) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J (ModuleCat.{u} ℤ) ⋙
        (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
          (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}))
    infer_instance
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _
    (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}))
    (sheafToPresheaf J AddCommGrpCat.{u}) h
    (@reflectsFiniteLimits_of_reflectsIsomorphisms _ _ _ _
      (sheafToPresheaf J AddCommGrpCat.{u}) (by infer_instance) inferInstance inferInstance)

noncomputable instance integerForget_sheafCompose_preservesFiniteColimits :
    PreservesFiniteColimits
      (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})) := by
  infer_instance

noncomputable instance integerForget_sheafCompose_preservesHomology :
      (sheafCompose J (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})).PreservesHomology := by
  exact Functor.preservesHomologyOfExact _

end Integers

instance moduleCat_preservesSheafification :
    J.PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  CategoryTheory.GrothendieckTopology.instPreservesSheafification J _

end ModuleCatSheafification
