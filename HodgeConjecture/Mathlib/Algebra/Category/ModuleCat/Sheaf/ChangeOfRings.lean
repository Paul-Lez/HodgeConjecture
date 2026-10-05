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

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Change of rings for sheaves of modules

For a homomorphism `f : R →+* S` of commutative rings, restriction of scalars gives a functor
between sheaves of modules. Its left adjoint is obtained by sheafifying extension of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

universe u₁ u₂ v w

variable {C : Type w} [Category.{v} C]
variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
variable (J : GrothendieckTopology C) (f : R →+* S)

/-- Restriction of scalars on sheaves of modules. -/
noncomputable def restrictScalars :
    Sheaf J (ModuleCat.{max v u₂} S) ⥤ Sheaf J (ModuleCat.{max v u₂} R) :=
  sheafCompose J (ModuleCat.restrictScalars.{max v u₂} f)

section HasSheafifyTarget

variable [HasSheafify J (ModuleCat.{max v u₂} S)]

/-- Sheafified extension of scalars on sheaves of modules. -/
noncomputable def extendScalars :
    Sheaf J (ModuleCat.{max v u₂} R) ⥤ Sheaf J (ModuleCat.{max v u₂} S) :=
  Sheaf.composeAndSheafify J
    (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)

/-- The sheaf-level extension–restriction adjunction. -/
noncomputable def extendRestrictScalarsAdj :
    extendScalars J f ⊣ restrictScalars J f :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj f)

end HasSheafifyTarget

instance restrictScalars_additive : (restrictScalars J f).Additive := by
  constructor
  intro X Y a b
  apply (sheafToPresheaf J _).map_injective
  change (((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max v u₂} S)
    (ModuleCat.{max v u₂} R)).obj (ModuleCat.restrictScalars f)).map (a.hom + b.hom)) = _
  rw [Functor.map_add]
  rfl

instance restrictScalars_reflectsIsomorphisms :
    (restrictScalars J f).ReflectsIsomorphisms := by
  dsimp only [restrictScalars]
  infer_instance

section HasSheafifySource

variable [HasSheafify J (ModuleCat.{max v u₂} R)]
  [HasSheafify J (ModuleCat.{max v u₂} S)]

instance restrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (restrictScalars J f) :=
  (inferInstance : PreservesFiniteLimits
    (sheafCompose J (ModuleCat.restrictScalars.{max v u₂} f)))

instance restrictScalars_preservesMonomorphisms :
    (restrictScalars J f).PreservesMonomorphisms := inferInstance

/-- Sheafification of coefficient restriction agrees with pointwise restriction on sheaves. -/
noncomputable def composeAndSheafifyRestrictScalarsIso :
    Sheaf.composeAndSheafify J (ModuleCat.restrictScalars.{max v u₂} f) ≅
      restrictScalars J f :=
  NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _
      ((sheafificationAdjunction J (ModuleCat.{max v u₂} R)).counit.app
        ((restrictScalars J f).obj X))
      (isIso_sheafificationAdjunction_counit ((restrictScalars J f).obj X)))
    (fun g ↦ (sheafificationAdjunction J (ModuleCat.{max v u₂} R)).counit.naturality
      ((restrictScalars J f).map g))

noncomputable instance restrictScalars_isLeftAdjoint :
    (restrictScalars J f).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (composeAndSheafifyRestrictScalarsIso J f)

noncomputable instance restrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (restrictScalars J f) := inferInstance

end HasSheafifySource

section Exact

variable [HasSheafify J (ModuleCat.{max v u₂} R)]
  [HasSheafify J (ModuleCat.{max v u₂} S)]

/-- Restriction of scalars on sheaves preserves homology. -/
noncomputable instance restrictScalars_preservesHomology :
    (restrictScalars J f).PreservesHomology :=
  ((Functor.exact_tfae (restrictScalars J f)).out 3 2).mp
    (show PreservesFiniteLimits (restrictScalars J f) ∧
      PreservesFiniteColimits (restrictScalars J f) from ⟨inferInstance, inferInstance⟩)

/-- Restriction of scalars on sheaves preserves exact sequences. -/
lemma restrictScalars_map_exact
    (T : ShortComplex (Sheaf J (ModuleCat.{max v u₂} S))) (hT : T.Exact) :
    (T.map (restrictScalars J f)).Exact := by
  have h := ((Functor.exact_tfae (restrictScalars J f)).out 3 1).mp
    (show PreservesFiniteLimits (restrictScalars J f) ∧
      PreservesFiniteColimits (restrictScalars J f) from ⟨inferInstance, inferInstance⟩)
  exact h T hT

end Exact

/-- Extension of scalars along a flat ring homomorphism preserves finite limits. -/
lemma moduleCatExtendScalars_preservesFiniteLimits_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f) := by
  algebraize [f]
  let : (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  have hExact : ∀ (T : ShortComplex (ModuleCat.{max v u₂} R)), T.Exact →
      (T.map (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)).Exact := by
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact S hT
  have h := ((Functor.exact_tfae
    (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)).out 1 3).mp hExact
  exact h.1

/-- The canonical map `ℤ → K` is flat for a field `K` of characteristic zero. -/
lemma intAlgebraMap_flat (K : Type u₂) [Field K] [CharZero K] :
    (algebraMap ℤ K).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

section AddCommGrp

universe t

variable [HasSheafify J (ModuleCat.{t} ℤ)]
  [HasSheafify J AddCommGrpCat.{t}]
  [J.HasSheafCompose
    (forget₂ (ModuleCat.{t} ℤ) AddCommGrpCat.{t})]

private noncomputable instance moduleIntForget_preservesInjectiveObjects :
    (sheafCompose J
      (forget₂ (ModuleCat.{t} ℤ) AddCommGrpCat.{t})).PreservesInjectiveObjects := by
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Sheaf.adjunction J
      (forget₂ (ModuleCat.{t} ℤ) AddCommGrpCat.{t}).asEquivalence.symm.toAdjunction)

end AddCommGrp

private instance whiskeringRightExtendScalars_preservesFiniteLimits
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)] :
    PreservesFiniteLimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max v u₂} R)
        (ModuleCat.{max v u₂} S)).obj
          (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)) where
  preservesFiniteLimits K _ _ :=
    whiskeringRight_preservesLimitsOfShape
      (C := Cᵒᵖ) (J := K) (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)

section HasSheafifyTarget

variable [HasSheafify J (ModuleCat.{max v u₂} S)]

private lemma extendScalars_preservesFiniteLimits_of_moduleCat
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)] :
    PreservesFiniteLimits (extendScalars J f) := by
  let : PreservesFiniteLimits
      (((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{max v u₂} R)
        (ModuleCat.{max v u₂} S)).obj
          (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f)) ⋙
        presheafToSheaf J (ModuleCat.{max v u₂} S)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

/-- Sheafified extension of scalars along a flat ring homomorphism preserves finite limits. -/
lemma extendScalars_preservesFiniteLimits_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars J f) := by
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f) :=
    moduleCatExtendScalars_preservesFiniteLimits_of_flat f hf
  exact extendScalars_preservesFiniteLimits_of_moduleCat J f

/-- Sheafified extension of scalars along a flat ring homomorphism preserves monomorphisms. -/
lemma extendScalars_preservesMonomorphisms_of_flat (hf : f.Flat) :
    (extendScalars J f).PreservesMonomorphisms := by
  let : PreservesFiniteLimits (extendScalars J f) :=
    extendScalars_preservesFiniteLimits_of_flat J f hf
  infer_instance

/-- Restriction of scalars along a flat ring homomorphism preserves injective sheaves. -/
theorem restrictScalars_preservesInjectiveObjects_of_flat (hf : f.Flat) :
    (restrictScalars J f).PreservesInjectiveObjects :=
  let : (extendScalars J f).PreservesMonomorphisms :=
    extendScalars_preservesMonomorphisms_of_flat J f hf
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extendRestrictScalarsAdj J f)

end HasSheafifyTarget

section ModuleForget

variable {S : Type u₂} [CommRing S]
  [HasSheafify J (ModuleCat.{max v u₂} S)]
  [HasSheafify J (ModuleCat.{max v u₂} ℤ)]
  [HasSheafify J AddCommGrpCat.{max v u₂}]
  [J.HasSheafCompose
    (forget₂ (ModuleCat.{max v u₂} S) AddCommGrpCat.{max v u₂})]
  [J.HasSheafCompose
    (forget₂ (ModuleCat.{max v u₂} ℤ) AddCommGrpCat.{max v u₂})]

omit [HasSheafify J (ModuleCat.{max v u₂} S)]
  [HasSheafify J AddCommGrpCat.{max v u₂}] in
theorem moduleForget_preservesFiniteColimits
    (h : PreservesFiniteColimits (sheafCompose J
      (forget₂ (ModuleCat.{max v u₂} ℤ) AddCommGrpCat.{max v u₂}))) :
    PreservesFiniteColimits (sheafCompose J
      (forget₂ (ModuleCat.{max v u₂} S) AddCommGrpCat.{max v u₂})) := by
  change PreservesFiniteColimits (restrictScalars J (algebraMap ℤ S) ⋙
    sheafCompose J (forget₂ (ModuleCat.{max v u₂} ℤ) AddCommGrpCat.{max v u₂}))
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ (inferInstance) h

/-- Forgetting the module structure of a flat module sheaf preserves injective objects. -/
theorem moduleForget_preservesInjectiveObjects_of_flat (hf : (algebraMap ℤ S).Flat) :
    (sheafCompose J
      (forget₂ (ModuleCat.{max v u₂} S)
        AddCommGrpCat.{max v u₂})).PreservesInjectiveObjects := by
  change (restrictScalars J (algebraMap ℤ S) ⋙
    sheafCompose J
      (forget₂ (ModuleCat.{max v u₂} ℤ)
        AddCommGrpCat.{max v u₂})).PreservesInjectiveObjects
  let : (restrictScalars J (algebraMap ℤ S)).PreservesInjectiveObjects :=
    restrictScalars_preservesInjectiveObjects_of_flat J (algebraMap ℤ S) hf
  infer_instance

end ModuleForget

end CategoryTheory.Sheaf
