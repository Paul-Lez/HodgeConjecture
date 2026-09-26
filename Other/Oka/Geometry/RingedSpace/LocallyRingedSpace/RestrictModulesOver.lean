/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Topology.Sheaves.Module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp
public import Other.Oka.Topology.Sheaves.Module

/-!
# Restriction to an open subspace and restriction to a slice

The standard equivalence between sheaves on the slice over an open and sheaves on the open
subspace identifies slice restriction with pullback along the open immersion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u}) (V : Opens Y.toPresheafedSpace)

/-- Sheaves of modules over `Y.ringSheaf.over V` are equivalent to sheaves of modules on the open
subspace `Y|_V`. -/
def restrictOverEquiv :
    SheafOfModules.{u} (Y.ringSheaf.over V) ≌
      SheafOfModules.{u} (Y.restrict V.isOpenEmbedding).ringSheaf :=
  V.sheafOfModulesEquivOver Y.ringSheaf

/-- Restriction to the slice followed by this equivalence is left adjoint to the corresponding
pushforward. -/
def overRestrictAdj :
    SheafOfModules.overFunctor Y.ringSheaf V ⋙ (restrictOverEquiv Y V).functor ⊣
      (restrictOverEquiv Y V).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := Y.ringSheaf) V) :=
  (SheafOfModules.overPushforwardOverAdj V).comp (restrictOverEquiv Y V).toAdjunction

/-- The composite from opens of `Y` through the slice over `V` is the preimage functor of the
open immersion. -/
def starOverEquivalenceIso :
    (Over.star V ⋙ V.overEquivalence.symm.inverse) ≅
      (Opens.map (Y.ofRestrict V.isOpenEmbedding).base :
        Opens Y.toPresheafedSpace ⥤ Opens ↥V) :=
  NatIso.ofComponents (fun U => eqToIso (by
    ext x
    change x.1 ∈ ((Over.star V).obj U).left ↔ x.1 ∈ U
    simp)) (by intros; rfl)

/-- The right adjoint in `overRestrictAdj` is pushforward along the open immersion. -/
def restrictOverInverseIso :
    (restrictOverEquiv Y V).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := Y.ringSheaf) V) ≅
      SheafOfModules.pushforward.{u} (Y.ofRestrict V.isOpenEmbedding).toRingSheafHom := by
  letI hcomp : (Over.star V ⋙ V.overEquivalence.symm.inverse).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology _).over V) _
  letI hmap : (Opens.map (Y.ofRestrict V.isOpenEmbedding).base :
      Opens Y.toPresheafedSpace ⥤ Opens ↥V).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V) :=
    inferInstanceAs ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace)
      (Opens.grothendieckTopology (Y.restrict V.isOpenEmbedding).toPresheafedSpace))
  refine (SheafOfModules.pushforwardComp _ _).trans ?_
  refine (@SheafOfModules.pushforwardNatIso _ _ _ _
    (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V)
    (Opens.map (Y.ofRestrict V.isOpenEmbedding).base)
    (Over.star V ⋙ V.overEquivalence.symm.inverse) _ _ hmap hcomp _
    (starOverEquivalenceIso Y V).symm).trans ?_
  refine @SheafOfModules.pushforwardCongr _ _ _ _
    (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V)
    (Opens.map (Y.ofRestrict V.isOpenEmbedding).base) _ _ hmap _ _ ?_
  ext U x
  simp only [ringSheaf, SheafOfModules.pushforwardOver, Functor.comp_map,
    Opens.sheafRestrictSheafEquivOver, Opens.overPullbackSheafEquivOver, Iso.app_inv, Iso.symm_inv,
    Iso.isoCompInverse_hom_app, Iso.refl_hom, NatTrans.id_app, Functor.map_comp,
    starOverEquivalenceIso, Iso.symm_hom, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Opens.sheafEquivOver_unitIso_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Over.forget_obj, Quiver.Hom.unop_op,
    Over.forget_map, Opens.overEquivalence_unitIso_inv_app_left, eqToHom_op,
    Opens.sheafEquivOver_inverse_map_hom_app, ObjectProperty.FullSubcategory.id_hom,
    Functor.whiskerRight_app, NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv,
    Opens.sheafRestrict_obj_obj_map, eqToHom_unop, RingCat.hom_comp,
    CommRingCat.forgetToRingCat_map_hom, RingHom.coe_comp, Function.comp_apply,
    Hom.toRingSheafHom]
  have key : ∀ {A B C D : (Opens Y.toPresheafedSpace)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
      (h : C ⟶ D) (k : A ⟶ D) (x : Y.presheaf.obj A),
      Y.presheaf.map h (Y.presheaf.map g (Y.presheaf.map f x)) = Y.presheaf.map k x :=
    fun f g h k x => by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, Subsingleton.elim (f ≫ g ≫ h) k]
  exact key _ _ _ _ x

/-- Slice restriction, transported to the open subspace, is pullback along its inclusion. -/
def overFunctorCompRestrictOverEquivIso :
    SheafOfModules.overFunctor Y.ringSheaf V ⋙ (restrictOverEquiv Y V).functor ≅
      Y.restrictModules V :=
  ((overRestrictAdj Y V).ofNatIsoRight (restrictOverInverseIso Y V)).leftAdjointUniq
    (Y.ofRestrict V.isOpenEmbedding).pullbackModulesAdj

/-- The pullback restriction of `M` corresponds to its slice restriction. -/
def restrictModulesObjIso (M : SheafOfModules.{u} Y.ringSheaf) :
    (Y.restrictModules V).obj M ≅ (restrictOverEquiv Y V).functor.obj (M.over V) :=
  ((overFunctorCompRestrictOverEquivIso Y V).app M).symm

/-- Coherence on a slice is equivalent to coherence after transport to the open subspace. -/
theorem isCoherent_over_iff_isCoherent_restrictModules
    (M : SheafOfModules.{u} Y.ringSheaf) :
    (M.over V).IsCoherent ↔ ((Y.restrictModules V).obj M).IsCoherent := by
  rw [← V.isCoherent_sheafOfModulesEquivOver_functor_obj_iff Y.ringSheaf]
  constructor
  · intro h
    exact SheafOfModules.IsCoherent.of_iso.{u}
      (M := (V.sheafOfModulesEquivOver Y.ringSheaf).functor.obj (M.over V))
      (restrictModulesObjIso Y V M).symm
  · intro h
    exact SheafOfModules.IsCoherent.of_iso.{u} (M := (Y.restrictModules V).obj M)
      (restrictModulesObjIso Y V M)

/-- Coherence can be checked after restriction to an open neighborhood of every point. -/
theorem isCoherent_of_isCoherent_restrictModules (M : SheafOfModules.{u} Y.ringSheaf)
    (h : ∀ y : Y, ∃ (V : Opens Y.toPresheafedSpace) (_ : y ∈ V),
      ((Y.restrictModules V).obj M).IsCoherent) :
    M.IsCoherent := by
  choose V hV hcoh using h
  haveI (y : Y) : (M.over (V y)).IsCoherent :=
    (isCoherent_over_iff_isCoherent_restrictModules Y (V y) M).2 (hcoh y)
  refine SheafOfModules.IsCoherent.of_coversTop M V ((Opens.coversTop_iff _ V).2 ?_)
  exact eq_top_iff.2 fun y _ ↦ Opens.mem_iSup.2 ⟨y, hV y⟩

end AlgebraicGeometry.LocallyRingedSpace
