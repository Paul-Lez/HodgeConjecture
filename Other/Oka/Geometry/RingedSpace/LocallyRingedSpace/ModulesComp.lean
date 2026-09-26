/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules

/-!
# Composition of pullbacks of modules

Pullback of modules along locally ringed-space morphisms is pseudofunctorial. Restriction to an
open subspace is the corresponding pullback along the open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z T : LocallyRingedSpace.{u}}

local instance {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u} f.toRingSheafHom.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top f.toRingSheafHom.hom)

local instance {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction f.toRingSheafHom).isRightAdjoint

/-- Pullback of modules is compatible with composition. -/
def Hom.pullbackModulesComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    g.pullbackModules ⋙ f.pullbackModules ≅ (f ≫ g).pullbackModules :=
  SheafOfModules.pullbackComp.{u} g.toRingSheafHom f.toRingSheafHom

/-- Pullbacks along equal morphisms are naturally isomorphic. -/
def Hom.pullbackModulesCongr {f g : X ⟶ Y} (h : f = g) :
    f.pullbackModules ≅ g.pullbackModules :=
  eqToIso (h ▸ rfl)

/-- A commutative square gives an isomorphism between the two composite pullbacks. -/
def Hom.pullbackModulesCommSqIso {a : X ⟶ Y} {b : Y ⟶ T} {c : X ⟶ Z}
    {d : Z ⟶ T} (h : a ≫ b = c ≫ d) :
    b.pullbackModules ⋙ a.pullbackModules ≅ d.pullbackModules ⋙ c.pullbackModules :=
  Hom.pullbackModulesComp a b ≪≫ Hom.pullbackModulesCongr h ≪≫
    (Hom.pullbackModulesComp c d).symm

variable (Y) in
/-- Restriction of modules to an open subspace. -/
abbrev restrictModules (U : Opens Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ SheafOfModules.{u} (Y.restrict U.isOpenEmbedding).ringSheaf :=
  (Y.ofRestrict U.isOpenEmbedding).pullbackModules

end AlgebraicGeometry.LocallyRingedSpace
