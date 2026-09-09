/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenSheafRestriction
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalk normalization for actual open restriction

Restriction here means precomposition with the open-image functor, not an independently
chosen inverse-image model. Its stalk comparison sends the germ of a section on an open
subset of the subspace to the same section's ambient germ.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u

namespace TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{u}} (U : Opens X) (F : X.Presheaf AddCommGrpCat.{u})
  (y : (Opens.toTopCat X).obj U)

/-- Actual presheaf restriction to the open subspace. -/
abbrev openRestriction : ((Opens.toTopCat X).obj U).Presheaf AddCommGrpCat.{u} :=
  U.isOpenEmbedding.functor.op ⋙ F

/-- An open-subspace germ has its ambient germ on the same image open. -/
def openRestrictionStalkHom : (openRestriction U F).stalk y ⟶ F.stalk y.val :=
  colimit.desc ((OpenNhds.inclusion (X := (Opens.toTopCat X).obj U) y).op ⋙ openRestriction U F)
    { pt := F.stalk y.val
      ι :=
        { app V := F.germ (U.isOpenEmbedding.functor.obj V.unop.1) y.val
            (Set.mem_image_of_mem U.inclusion' V.unop.2)
          naturality {V W} a := by
            exact F.germ_res' (U.isOpenEmbedding.functor.map a.unop).op y.val
              (Set.mem_image_of_mem U.inclusion' W.unop.2) } }

@[reassoc (attr := simp)]
lemma germ_openRestrictionStalkHom (V : Opens ((Opens.toTopCat X).obj U)) (hy : y ∈ V) :
    (openRestriction U F).germ V y hy ≫ openRestrictionStalkHom U F y =
      F.germ (U.isOpenEmbedding.functor.obj V) y.val
        (Set.mem_image_of_mem U.inclusion' hy) :=
  colimit.ι_desc _ _

/-- Restricting an ambient section to its intersection with the subspace gives the inverse
map on germs. -/
def openRestrictionStalkInv : F.stalk y.val ⟶ (openRestriction U F).stalk y :=
  colimit.desc ((OpenNhds.inclusion (X := X) y.val).op ⋙ F)
    { pt := (openRestriction U F).stalk y
      ι :=
        { app V := F.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V.unop.1).op ≫
            (openRestriction U F).germ ((Opens.map U.inclusion').obj V.unop.1) y V.unop.2
          naturality {V W} a := by
            simp only [Functor.comp_map, Functor.const_obj_map]
            rw [← Category.assoc, ← F.map_comp]
            have h := (openRestriction U F).germ_res'
              ((Opens.map U.inclusion').map a.unop).op y W.unop.2
            change F.map (U.isOpenEmbedding.functor.map
                ((Opens.map U.inclusion').map a.unop)).op ≫
              (openRestriction U F).germ ((Opens.map U.inclusion').obj W.unop.1) y W.unop.2 =
              (openRestriction U F).germ ((Opens.map U.inclusion').obj V.unop.1) y V.unop.2 at h
            rw [← h, ← Category.assoc, ← F.map_comp]
            congr 1 } }

@[reassoc (attr := simp)]
lemma germ_openRestrictionStalkInv (V : Opens X) (hy : y.val ∈ V) :
    F.germ V y.val hy ≫ openRestrictionStalkInv U F y =
      F.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op ≫
        (openRestriction U F).germ ((Opens.map U.inclusion').obj V) y hy :=
  colimit.ι_desc _ _

/-- The canonical open-restriction stalk isomorphism, with explicit germ normalization. -/
def openRestrictionStalkIso : (openRestriction U F).stalk y ≅ F.stalk y.val where
  hom := openRestrictionStalkHom U F y
  inv := openRestrictionStalkInv U F y
  hom_inv_id := by
    apply stalk_hom_ext
    intro V hy
    rw [germ_openRestrictionStalkHom_assoc, germ_openRestrictionStalkInv, Category.comp_id]
    have h := (openRestriction U F).germ_res'
      (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op y hy
    change F.map (U.isOpenEmbedding.functor.map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V)).op ≫
      (openRestriction U F).germ V y hy =
      (openRestriction U F).germ ((Opens.map U.inclusion').obj
        (U.isOpenEmbedding.functor.obj V)) y _ at h
    rw [← h, ← Category.assoc, ← F.map_comp]
    convert Category.id_comp ((openRestriction U F).germ V y hy) using 1
    rw [← F.map_id]
    congr 1
  inv_hom_id := by
    apply stalk_hom_ext
    intro V hy
    rw [germ_openRestrictionStalkInv_assoc, germ_openRestrictionStalkHom, Category.comp_id]
    exact F.germ_res' _ y.val _

@[reassoc]
lemma openRestrictionStalkHom_naturality {F G : X.Presheaf AddCommGrpCat.{u}}
    (a : F ⟶ G) :
    (stalkFunctor AddCommGrpCat.{u} y).map
        (Functor.whiskerLeft U.isOpenEmbedding.functor.op a) ≫
      openRestrictionStalkHom U G y =
        openRestrictionStalkHom U F y ≫ (stalkFunctor AddCommGrpCat.{u} y.val).map a := by
  apply stalk_hom_ext
  intro V hy
  simp only [stalkFunctor_map_germ_assoc, Functor.whiskerLeft_app,
    germ_openRestrictionStalkHom, germ_openRestrictionStalkHom_assoc, stalkFunctor_map_germ]
  rfl

end TopCat.Presheaf
