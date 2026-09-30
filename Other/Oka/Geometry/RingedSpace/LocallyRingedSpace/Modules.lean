/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Other.Oka.Topology.Category.TopCat.Opens

/-!
# Sheaves of modules over a locally ringed space

This file supplies the structure sheaf as a `RingCat`-valued sheaf and the pullback functor for
modules along a morphism of locally ringed spaces. Mathlib already provides the underlying
general pullback construction for sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure sheaf of a locally ringed space, viewed as a sheaf of rings. -/
def ringSheaf :
    Sheaf (Opens.grothendieckTopology ↑Y.toPresheafedSpace) RingCat.{u} :=
  ⟨Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget₂ CommRingCat.{u} RingCat.{u}) Y.presheaf).1 Y.IsSheaf⟩

/-- Sheafification at the site used by `ringSheaf`. -/
instance hasSheafify_toPresheafedSpace :
    HasSheafify (Opens.grothendieckTopology ↑Y.toPresheafedSpace) AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology ↑Y.toTopCat) AddCommGrpCat.{u})

variable {Y} in
/-- The morphism of sheaves of rings induced by a morphism of locally ringed spaces. -/
def Hom.toRingSheafHom {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    Y.ringSheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj X.ringSheaf where
  hom := Functor.whiskerRight f.c _

local instance {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u} f.toRingSheafHom.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top f.toRingSheafHom.hom)

local instance {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction f.toRingSheafHom).isRightAdjoint

variable {Y} in
/-- Pullback of modules along a morphism of locally ringed spaces. -/
def Hom.pullbackModules {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ SheafOfModules.{u} X.ringSheaf :=
  SheafOfModules.pullback.{u} f.toRingSheafHom

variable {Y} in
/-- Pullback of modules is left adjoint to pushforward. -/
def Hom.pullbackModulesAdj {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules ⊣ SheafOfModules.pushforward.{u} f.toRingSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} f.toRingSheafHom

variable {Y} in
/-- The canonical map from the pullback of the structure sheaf to the structure sheaf. -/
def Hom.pullbackModulesUnitToUnit {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules.obj (SheafOfModules.unit Y.ringSheaf) ⟶ SheafOfModules.unit X.ringSheaf :=
  SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingSheafHom

variable {Y} in
/-- The canonical map from the pullback of the structure sheaf is an isomorphism. -/
instance isIso_pullbackModulesUnitToUnit {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    IsIso (Hom.pullbackModulesUnitToUnit.{u} f) :=
  inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingSheafHom))

variable {Y} in
/-- The pullback of the structure sheaf is the structure sheaf. -/
def Hom.pullbackModulesUnitIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules.obj (SheafOfModules.unit Y.ringSheaf) ≅ SheafOfModules.unit X.ringSheaf :=
  asIso (Hom.pullbackModulesUnitToUnit.{u} f)

variable {Y} in
/-- Pullback preserves free sheaves of modules. -/
def Hom.pullbackModulesFreeIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (I : Type u) :
    f.pullbackModules.obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  SheafOfModules.pullbackObjFreeIso.{u} f.toRingSheafHom I

variable {Y} in
/-- Pullback commutes with the free-sheaf functor. -/
def Hom.freeFunctorCompPullbackModulesIso {X : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) :
    SheafOfModules.freeFunctor ⋙ f.pullbackModules ≅ SheafOfModules.freeFunctor :=
  SheafOfModules.freeFunctorCompPullbackIso.{u} f.toRingSheafHom

end AlgebraicGeometry.LocallyRingedSpace
