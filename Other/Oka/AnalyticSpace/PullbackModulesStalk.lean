/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.PullbackExact
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules

/-!
# Stalks of pullbacks of modules on locally ringed spaces

The stalk of `f⁺ M` at `x` is obtained from the stalk of `M` at `f x` by extension of scalars.
Flat stalk maps therefore make pullback left exact.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure presheaf is a sheaf after forgetting commutativity. -/
theorem isSheaf_ringSheaf :
    TopCat.Presheaf.IsSheaf (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget₂ CommRingCat.{u} RingCat.{u}) Y.presheaf).1 Y.IsSheaf

/-- `ringSheaf` agrees definitionally with the generic construction from a commutative-ring
presheaf. -/
theorem ringSheaf_eq_ofCommRingCat :
    Y.ringSheaf = SheafOfModules.ofCommRingCat Y.presheaf Y.isSheaf_ringSheaf :=
  rfl

/-- The stalk of a sheaf of modules on a locally ringed space. -/
def stalkFunctor (y : Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ ModuleCat.{u} (Y.presheaf.stalk y) :=
  SheafOfModules.stalkFunctor (hR := Y.isSheaf_ringSheaf) y

variable {Y}

/-- The bundled ring-sheaf morphism agrees definitionally with the generic construction. -/
theorem toRingSheafHom_eq_sheafRingHom {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.toRingSheafHom = SheafOfModules.sheafRingHom
      (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c :=
  rfl

/-- The generic map on ring stalks is the stalk map of a locally ringed-space morphism. -/
theorem ringStalkMap_eq_stalkMap {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    PresheafOfModules.ringStalkMap f.base f.c x = f.stalkMap x :=
  rfl

/-- The stalk of a pullback is extension of scalars along the stalk map. -/
def Hom.pullbackModulesStalkIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    f.pullbackModules ⋙ X.stalkFunctor x ≅
      Y.stalkFunctor (f.base x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  SheafOfModules.pullbackStalkIso
    (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c x

/-- Pullback along a morphism with flat stalk maps preserves finite limits. -/
theorem Hom.preservesFiniteLimits_pullbackModules {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hflat : ∀ x : X, ((f.stalkMap x).hom).Flat) :
    Limits.PreservesFiniteLimits f.pullbackModules :=
  SheafOfModules.preservesFiniteLimits_pullback
    (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c hflat

end AlgebraicGeometry.LocallyRingedSpace
