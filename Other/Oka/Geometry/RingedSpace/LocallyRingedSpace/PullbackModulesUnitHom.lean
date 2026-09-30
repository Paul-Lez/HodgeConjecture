/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Pullback of morphisms out of the structure sheaf

Let `f : Y ⟶ X` be a morphism of locally ringed spaces and `H` a sheaf of `𝒪_X`-modules.
Morphisms `𝒪_X ⟶ H` are global sections of `H`, and under the adjunction `f^* ⊣ f_*` the map
`f^* : (𝒪_X ⟶ H) → (f^* 𝒪_X ⟶ f^* H)` becomes composition with the unit `H ⟶ f_* f^* H`. Hence
it is bijective as soon as the unit is bijective on global sections
(`AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_pullbackModules_map_unit`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- Composition with `φ : M ⟶ N` is bijective on morphisms out of the structure sheaf if `φ` is
bijective on global sections. -/
lemma bijective_comp_of_bijective_app_top {M N : SheafOfModules.{u} X.ringSheaf} (φ : M ⟶ N)
    (h : Function.Bijective (φ.val.app (op ⊤))) :
    Function.Bijective (fun g : SheafOfModules.unit X.ringSheaf ⟶ M ↦ g ≫ φ) := by
  let hT : IsTerminal (⊤ : Opens X.toPresheafedSpace) := isTerminalTop
  let e (P : SheafOfModules.{u} X.ringSheaf) : P.sections ≃ P.val.obj (op ⊤) :=
    { toFun s := PresheafOfModules.sections.eval s (op ⊤)
      invFun b := SheafOfModules.sectionOfTerminal hT P b
      left_inv s := SheafOfModules.sectionOfTerminal_eval hT P s
      right_inv b := by
        change PresheafOfModules.sections.eval (SheafOfModules.sectionOfTerminal hT P b)
          (op ⊤) = b
        rw [SheafOfModules.sectionOfTerminal_val]
        rw [show hT.from ⊤ = 𝟙 _ from hT.hom_ext _ _, op_id, P.val.map_id]
        rfl }
  have hs : SheafOfModules.sectionsMap φ = (e N).symm ∘ φ.val.app (op ⊤) ∘ e M := by
    funext s
    conv_lhs => rw [← SheafOfModules.sectionOfTerminal_eval hT M s]
    exact SheafOfModules.sectionsMap_sectionOfTerminal hT φ _
  have hc : (fun g : SheafOfModules.unit X.ringSheaf ⟶ M ↦ g ≫ φ) =
      N.unitHomEquiv.symm ∘ SheafOfModules.sectionsMap φ ∘ M.unitHomEquiv := by
    funext g
    apply N.unitHomEquiv.injective
    simp [SheafOfModules.unitHomEquiv_comp_apply]
  rw [hc, hs]
  exact N.unitHomEquiv.symm.bijective.comp
    (((e N).symm.bijective.comp (h.comp (e M).bijective)).comp M.unitHomEquiv.bijective)

/-- **Pullback of morphisms out of `𝒪_X`**: `f^* : (𝒪_X ⟶ H) → (f^* 𝒪_X ⟶ f^* H)` is bijective if
the unit `H ⟶ f_* f^* H` is bijective on global sections. -/
lemma Hom.bijective_pullbackModules_map_unit {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (H : SheafOfModules.{u} X.ringSheaf)
    (h : Function.Bijective ((f.pullbackModulesAdj.unit.app H).val.app (op ⊤))) :
    Function.Bijective
      (f.pullbackModules.map : (SheafOfModules.unit X.ringSheaf ⟶ H) → _) := by
  have hc : (f.pullbackModules.map : (SheafOfModules.unit X.ringSheaf ⟶ H) → _) =
      (f.pullbackModulesAdj.homEquiv _ _).symm ∘
        (fun g : SheafOfModules.unit X.ringSheaf ⟶ H ↦ g ≫ f.pullbackModulesAdj.unit.app H) := by
    funext g
    apply (f.pullbackModulesAdj.homEquiv _ _).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (f.pullbackModulesAdj.unit.naturality g).symm
  rw [hc]
  exact (f.pullbackModulesAdj.homEquiv _ _).symm.bijective.comp
    (bijective_comp_of_bijective_app_top _ h)

end AlgebraicGeometry.LocallyRingedSpace

end
