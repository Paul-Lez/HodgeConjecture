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

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Exterior powers of presheaves of modules

This file constructs exterior powers of a presheaf of modules over a presheaf of commutative
rings. Restriction maps are semilinear because the coefficient ring varies with the open set. The
map on an exterior power is therefore built directly from its universal alternating map, with the
target restricted along the corresponding ring homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u vC uC

namespace PresheafOfModules

variable {C : Type uC} [Category.{vC} C]
variable {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))

local instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

/-- The alternating map which applies a restriction map to every input and then takes their
exterior product. -/
def exteriorRestrictionAlternatingMap (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (M.obj X).AlternatingMap
      ((ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower p)) p where
  toFun x := ModuleCat.exteriorPower.mk (M := M.obj Y)
    (fun i ↦ (M.map f (x i) : M.obj Y))
  map_update_add' x i a b := by
    let F := ModuleCat.exteriorPower.mk (M := M.obj Y) (n := p)
    change F (fun k ↦ (M.map f (Function.update x i (a + b) k) : M.obj Y)) =
      F (fun k ↦ (M.map f (Function.update x i a k) : M.obj Y)) +
        F (fun k ↦ (M.map f (Function.update x i b k) : M.obj Y))
    have hab : (fun k ↦ (M.map f (Function.update x i (a + b) k) : M.obj Y)) =
        Function.update (fun k ↦ (M.map f (x k) : M.obj Y)) i
          ((M.map f a : M.obj Y) + M.map f b) := by
      funext k
      by_cases h : k = i <;> simp [h]
    have ha : (fun k ↦ (M.map f (Function.update x i a k) : M.obj Y)) =
        Function.update (fun k ↦ (M.map f (x k) : M.obj Y)) i (M.map f a : M.obj Y) := by
      funext k
      by_cases h : k = i <;> simp [h]
    have hb : (fun k ↦ (M.map f (Function.update x i b k) : M.obj Y)) =
        Function.update (fun k ↦ (M.map f (x k) : M.obj Y)) i (M.map f b : M.obj Y) := by
      funext k
      by_cases h : k = i <;> simp [h]
    rw [hab, ha, hb]
    exact F.map_update_add _ _ _ _
  map_update_smul' x i r a := by
    let F := ModuleCat.exteriorPower.mk (M := M.obj Y) (n := p)
    change F (fun k ↦ (M.map f (Function.update x i (r • a) k) : M.obj Y)) =
      R.map f r • F (fun k ↦ (M.map f (Function.update x i a k) : M.obj Y))
    have hra : (fun k ↦ (M.map f (Function.update x i (r • a) k) : M.obj Y)) =
        Function.update (fun k ↦ (M.map f (x k) : M.obj Y)) i
          (R.map f r • (M.map f a : M.obj Y)) := by
      funext k
      by_cases h : k = i <;> simp [h, M.map_smul]
    have ha : (fun k ↦ (M.map f (Function.update x i a k) : M.obj Y)) =
        Function.update (fun k ↦ (M.map f (x k) : M.obj Y)) i (M.map f a : M.obj Y) := by
      funext k
      by_cases h : k = i <;> simp [h]
    rw [hra, ha]
    exact F.map_update_smul _ _ _ _
  map_eq_zero_of_eq' x i j hij hne := by
    apply (ModuleCat.exteriorPower.mk (M := M.obj Y)).map_eq_zero_of_eq
    · exact congrArg (fun a ↦ (M.map f a : M.obj Y)) hij
    · exact hne

/-- The restriction map on an exterior power. -/
def exteriorPowerMap (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (M.obj X).exteriorPower p ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower p) :=
  ModuleCat.exteriorPower.desc (exteriorRestrictionAlternatingMap (M := M) p f)

@[simp]
lemma exteriorPowerMap_mk (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : Fin p → M.obj X) :
    exteriorPowerMap (M := M) p f (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (M := M.obj Y)
        (fun i ↦ (M.map f (x i) : M.obj Y)) := by
  apply ModuleCat.exteriorPower.desc_mk

/-- The `p`th exterior power of a presheaf of modules over a presheaf of commutative rings. -/
def exteriorPower (p : ℕ) :
    PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := (M.obj X).exteriorPower p
  map f := exteriorPowerMap (M := M) p f
  map_id X := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    simp only [ModuleCat.AlternatingMap.postcomp_apply]
    erw [exteriorPowerMap_mk]
    simp
    rfl
  map_comp f g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    simp only [ModuleCat.AlternatingMap.postcomp_apply, ConcreteCategory.comp_apply]
    rw [exteriorPowerMap_mk]
    rw [ModuleCat.restrictScalars.map_apply]
    rw [exteriorPowerMap_mk]
    erw [exteriorPowerMap_mk]
    simp
    congr 1

end PresheafOfModules
