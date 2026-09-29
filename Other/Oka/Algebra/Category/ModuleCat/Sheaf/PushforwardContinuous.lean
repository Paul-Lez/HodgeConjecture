/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Restriction of sheaves of modules to slice sites -/

@[expose] public noncomputable section

universe w v' u' u

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

instance (X : C) : (overFunctor.{w} R X).IsLeftAdjoint :=
  inferInstanceAs (pushforward.{w} (𝟙 (R.over X))).IsLeftAdjoint

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to a slice preserves a free sheaf. -/
def overFreeIso (I : Type u) (X : C) :
    free (R := R.over X) I ≅ (free (R := R) I).over X :=
  mapFreeIso (overFunctor R X) I (Iso.refl _)

end


section


variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to a slice commutes with binary biproducts. -/
def overBiprodIso (M N : SheafOfModules.{u} R) (X : C) :
    (M ⊞ N).over X ≅ (M.over X) ⊞ (N.over X) :=
  (overFunctor R X).mapIso (biprod.isoCoprod M N) ≪≫
    (PreservesColimitPair.iso (overFunctor R X) M N).symm ≪≫ (biprod.isoCoprod _ _).symm

end


section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Sheaves of modules on an iterated slice are equivalent to sheaves on the flattened slice. -/
def overOverEquivalence (X : C) (Y : Over X) :
    SheafOfModules.{u} (R.over Y.left) ≌ SheafOfModules.{u} ((R.over X).over Y) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over X).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

/-- The iterated-slice equivalence is compatible with restriction. -/
def overOverEquivalenceObjIso (M : SheafOfModules.{u} R) (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (M.over Y.left) ≅ (M.over X).over Y := by
  exact Iso.refl _

/-- The iterated-slice equivalence sends the unit to the unit. -/
def overOverEquivalenceUnitIso (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (unit (R.over Y.left)) ≅
      unit ((R.over X).over Y) := by
  exact Iso.refl _

/-- The inverse iterated-slice equivalence sends the unit to the unit. -/
def overOverEquivalenceInverseUnitIso (X : C) (Y : Over X) :
    unit (R.over Y.left) ≅
      (overOverEquivalence (R := R) X Y).inverse.obj (unit ((R.over X).over Y)) := by
  exact Iso.refl _

/-- The inverse iterated-slice equivalence is compatible with restriction. -/
def overOverEquivalenceInverseObjIso (M : SheafOfModules.{u} R) (X : C)
    (Y : Over X) :
    (overOverEquivalence (R := R) X Y).inverse.obj ((M.over X).over Y) ≅ M.over Y.left := by
  exact ((overOverEquivalence (R := R) X Y).unitIso.app (M.over Y.left)).symm

end


section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance (X : C) :
    (PresheafOfModules.pushforward.{u}
      (𝟙 (R.over X) : R.over X ⟶ R.over X).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top
      (𝟙 (R.over X) : R.over X ⟶ R.over X).hom)

instance (X : C) : (overFunctor.{u} R X).IsRightAdjoint :=
  (PullbackConstruction.adjunction (𝟙 (R.over X))).isRightAdjoint

variable [HasSheafify J AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to a slice commutes with kernels. -/
def overKernelIso {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (X : C) :
    (kernel φ).over X ≅ kernel (φ.over X) :=
  PreservesKernel.iso (overFunctor R X) φ

end


end SheafOfModules
