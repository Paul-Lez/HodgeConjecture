/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheaf

/-!
# Pullback of the sheaf of homomorphisms

Let `f : X ⟶ Y` be a morphism of locally ringed spaces and `F`, `G` sheaves of `𝒪_Y`-modules.
Pulling back morphisms defines a morphism of sheaves of `𝒪_Y`-modules
`𝓗om(F, G) ⟶ f_* 𝓗om(f^* F, f^* G)` (`AlgebraicGeometry.LocallyRingedSpace.homSheafPullback`),
and by adjunction the comparison morphism
`f^* 𝓗om(F, G) ⟶ 𝓗om(f^* F, f^* G)` (`AlgebraicGeometry.LocallyRingedSpace.homSheafPullbackComp`).
On global sections, the former sends a morphism `φ : F ⟶ G` to `f^* φ`
(`AlgebraicGeometry.LocallyRingedSpace.homSheafGlobalEquiv_homSheafPullback`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

section Push

lemma Hom.c_app_restrictOpen {U V : Opens Y.toPresheafedSpace} (h : U ≤ V)
    (r : Y.presheaf.obj (op V)) :
    f.c.app (op U) (TopCat.Presheaf.restrictOpen r U h) =
      X.presheaf.map (homOfLE ((Opens.map f.base).monotone h)).op (f.c.app (op V) r) :=
  congrArg (fun φ ↦ φ r) (congrArg CommRingCat.Hom.hom (f.c.naturality (homOfLE h).op))

variable {f} {G : SheafOfModules.{u} Y.ringSheaf} {G' : SheafOfModules.{u} X.ringSheaf}

/-- A morphism `ψ : G ⟶ f_* G'` induces `G_U ⟶ f_* (G'_{f⁻¹ U})`. -/
def restrictExtendPush (ψ : G ⟶ (SheafOfModules.pushforward f.toRingSheafHom).obj G')
    (U : Opens Y.toPresheafedSpace) :
    restrictExtend G U ⟶ (SheafOfModules.pushforward f.toRingSheafHom).obj
      (restrictExtend G' ((Opens.map f.base).obj U)) :=
  modHomMk (fun W ↦
      { toFun x := (ψ.val.app (op (W ⊓ U)) (restrictExtendSec x) :)
        map_zero' := map_zero (ψ.val.app (op (W ⊓ U))).hom
        map_add' x y := map_add (ψ.val.app (op (W ⊓ U))).hom (restrictExtendSec x)
          (restrictExtendSec y) })
    (fun W r x ↦ by
      change ψ.val.app (op (W ⊓ U)) (TopCat.Presheaf.restrictOpen r (W ⊓ U) inf_le_left •
          restrictExtendSec x) = _
      rw [modHom_smul]
      change (show X.presheaf.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
            f.c.app (op (W ⊓ U)) (TopCat.Presheaf.restrictOpen r (W ⊓ U) inf_le_left)) •
          (show G'.val.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
            ψ.val.app (op (W ⊓ U)) (restrictExtendSec x)) =
        (show X.presheaf.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
          X.presheaf.map (homOfLE ((Opens.map f.base).monotone (inf_le_left : W ⊓ U ≤ W))).op
            (f.c.app (op W) r)) •
          (show G'.val.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
            ψ.val.app (op (W ⊓ U)) (restrictExtendSec x))
      rw [Hom.c_app_restrictOpen])
    (fun W W' h x ↦ by
      change ψ.val.app (op (W' ⊓ U)) (modRes (restrictExtendSec x) (W' ⊓ U)
          (inf_le_inf_right U h)) = _
      rw [modHom_modRes]
      rfl)

lemma restrictExtendPush_app (ψ : G ⟶ (SheafOfModules.pushforward f.toRingSheafHom).obj G')
    (U W : Opens Y.toPresheafedSpace) (x : (restrictExtend G U).val.obj (op W)) :
    restrictExtendSec ((restrictExtendPush ψ U).val.app (op W) x) =
      ψ.val.app (op (W ⊓ U)) (restrictExtendSec x) :=
  rfl

end Push
section HomSheafPullback

variable (F G : SheafOfModules.{u} Y.ringSheaf)

/-- The base change morphism `f^* (G_U) ⟶ (f^* G)_{f⁻¹ U}`, adjoint to `G_U ⟶ f_* (f^* G)_{f⁻¹ U}`
induced by the unit `G ⟶ f_* f^* G`. -/
def pullbackRestrictExtend (U : Opens Y.toPresheafedSpace) :
    f.pullbackModules.obj (restrictExtend G U) ⟶
      restrictExtend (f.pullbackModules.obj G) ((Opens.map f.base).obj U) :=
  (f.pullbackModulesAdj.homEquiv (restrictExtend G U)
    (restrictExtend (f.pullbackModules.obj G) ((Opens.map f.base).obj U))).symm
    (restrictExtendPush (G' := f.pullbackModules.obj G) (f.pullbackModulesAdj.unit.app G) U)

lemma homEquiv_pullbackRestrictExtend (U : Opens Y.toPresheafedSpace) :
    f.pullbackModulesAdj.homEquiv _ _ (pullbackRestrictExtend f G U) =
      restrictExtendPush (G' := f.pullbackModules.obj G) (f.pullbackModulesAdj.unit.app G) U :=
  Equiv.apply_symm_apply _ _

lemma pullbackModules_map_toRestrictExtend_comp (U : Opens Y.toPresheafedSpace) :
    f.pullbackModules.map (toRestrictExtend G U) ≫ pullbackRestrictExtend f G U =
      toRestrictExtend (f.pullbackModules.obj G) ((Opens.map f.base).obj U) := by
  apply (f.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackRestrictExtend,
    Adjunction.homEquiv_unit]
  refine modHom_ext fun W x ↦ ?_
  exact modHom_modRes (f.pullbackModulesAdj.unit.app G) inf_le_left x

lemma pullbackModules_map_restrictExtendRes_comp {U V : Opens Y.toPresheafedSpace} (h : V ≤ U) :
    f.pullbackModules.map (restrictExtendRes G h) ≫ pullbackRestrictExtend f G V =
      pullbackRestrictExtend f G U ≫
        restrictExtendRes (f.pullbackModules.obj G) ((Opens.map f.base).monotone h) := by
  apply (f.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackRestrictExtend, homEquiv_pullbackRestrictExtend]
  refine modHom_ext fun W x ↦ ?_
  exact modHom_modRes (f.pullbackModulesAdj.unit.app G) (inf_le_inf_left W h)
    (restrictExtendSec x)

lemma pullbackModules_map_restrictExtendSMul_comp (U : Opens Y.toPresheafedSpace)
    (a : Y.presheaf.obj (op U)) :
    f.pullbackModules.map (restrictExtendSMul G U a) ≫ pullbackRestrictExtend f G U =
      pullbackRestrictExtend f G U ≫
        restrictExtendSMul (f.pullbackModules.obj G) ((Opens.map f.base).obj U)
          (f.c.app (op U) a) := by
  apply (f.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackRestrictExtend]
  refine modHom_ext fun W x ↦ ?_
  refine (modHom_smul (f.pullbackModulesAdj.unit.app G) _ (restrictExtendSec x)).trans ?_
  change (show X.presheaf.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
      f.c.app (op (W ⊓ U)) (TopCat.Presheaf.restrictOpen a (W ⊓ U) inf_le_right)) •
      (show (f.pullbackModules.obj G).val.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
        (f.pullbackModulesAdj.unit.app G).val.app (op (W ⊓ U)) (restrictExtendSec x)) =
    (show X.presheaf.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
      X.presheaf.map (homOfLE ((Opens.map f.base).monotone (inf_le_right : W ⊓ U ≤ U))).op
        (f.c.app (op U) a)) •
      (show (f.pullbackModules.obj G).val.obj (op ((Opens.map f.base).obj (W ⊓ U))) from
        (f.pullbackModulesAdj.unit.app G).val.app (op (W ⊓ U)) (restrictExtendSec x))
  rw [Hom.c_app_restrictOpen]

/-- Pulling back sections of `𝓗om(F, G)` over `U` along `f`. -/
def homSheafPullbackApp (U : Opens Y.toPresheafedSpace) :
    HomSec F G U →+ HomSec (f.pullbackModules.obj F) (f.pullbackModules.obj G)
      ((Opens.map f.base).obj U) :=
  haveI : f.pullbackModules.IsLeftAdjoint := f.pullbackModulesAdj.isLeftAdjoint
  haveI : (SheafOfModules.pushforward f.toRingSheafHom).Additive := { map_add := rfl }
  haveI : f.pullbackModules.Additive := f.pullbackModulesAdj.left_adjoint_additive
  { toFun h := f.pullbackModules.map h ≫
      pullbackRestrictExtend f G U
    map_zero' := by
      change f.pullbackModules.map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp]
    map_add' h h' := (congrArg (· ≫ pullbackRestrictExtend f G U)
      (f.pullbackModules.map_add (X := F) (Y := restrictExtend G U) (f := h) (g := h'))).trans
        (Preadditive.add_comp _ _ _ _ _ _) }

lemma homSheafPullbackApp_apply (U : Opens Y.toPresheafedSpace) (h : HomSec F G U) :
    homSheafPullbackApp f F G U h =
      f.pullbackModules.map (show F ⟶ restrictExtend G U from h) ≫
        pullbackRestrictExtend f G U :=
  rfl

/-- **Pulling back morphisms**, `𝓗om(F, G) ⟶ f_* 𝓗om(f^* F, f^* G)`. -/
def homSheafPullback : homSheaf F G ⟶ (SheafOfModules.pushforward f.toRingSheafHom).obj
    (homSheaf (f.pullbackModules.obj F) (f.pullbackModules.obj G)) :=
  modHomMk (fun U ↦ homSheafPullbackApp f F G U)
    (fun U a h ↦ by
      change f.pullbackModules.map ((show F ⟶ restrictExtend G U from h) ≫
          restrictExtendSMul G U a) ≫ pullbackRestrictExtend f G U =
        (f.pullbackModules.map (show F ⟶ restrictExtend G U from h) ≫
          pullbackRestrictExtend f G U) ≫
          restrictExtendSMul (f.pullbackModules.obj G) ((Opens.map f.base).obj U)
            (f.c.app (op U) a)
      rw [Functor.map_comp, Category.assoc, Category.assoc,
        pullbackModules_map_restrictExtendSMul_comp])
    (fun U V hVU h ↦ by
      change f.pullbackModules.map ((show F ⟶ restrictExtend G U from h) ≫
          restrictExtendRes G hVU) ≫ pullbackRestrictExtend f G V =
        (f.pullbackModules.map (show F ⟶ restrictExtend G U from h) ≫
          pullbackRestrictExtend f G U) ≫
          restrictExtendRes (f.pullbackModules.obj G) ((Opens.map f.base).monotone hVU)
      rw [Functor.map_comp, Category.assoc, Category.assoc,
        pullbackModules_map_restrictExtendRes_comp])

/-- The comparison morphism `f^* 𝓗om(F, G) ⟶ 𝓗om(f^* F, f^* G)`. -/
def homSheafPullbackComp : f.pullbackModules.obj (homSheaf F G) ⟶
    homSheaf (f.pullbackModules.obj F) (f.pullbackModules.obj G) :=
  (f.pullbackModulesAdj.homEquiv _ _).symm (homSheafPullback f F G)

lemma unit_comp_homSheafPullbackComp :
    f.pullbackModulesAdj.unit.app (homSheaf F G) ≫
      (SheafOfModules.pushforward f.toRingSheafHom).map (homSheafPullbackComp f F G) =
    homSheafPullback f F G := by
  exact (f.pullbackModulesAdj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **On global sections, `𝓗om(F, G) ⟶ f_* 𝓗om(f^* F, f^* G)` is `φ ↦ f^* φ`.** -/
lemma homSheafGlobalEquiv_homSheafPullback (φ : F ⟶ G) :
    homSheafGlobalEquiv (f.pullbackModules.obj F) (f.pullbackModules.obj G)
      ((homSheafPullback f F G).val.app (op ⊤) ((homSheafGlobalEquiv F G).symm φ)) =
    f.pullbackModules.map φ := by
  change (f.pullbackModules.map (φ ≫ (restrictExtendTopIso G).hom) ≫ pullbackRestrictExtend f G ⊤) ≫
    (restrictExtendTopIso (f.pullbackModules.obj G)).inv = _
  refine (Iso.comp_inv_eq _).2 ?_
  rw [Functor.map_comp, Category.assoc, restrictExtendTopIso_hom,
    pullbackModules_map_toRestrictExtend_comp]
  rfl

end HomSheafPullback

end AlgebraicGeometry.LocallyRingedSpace

end
