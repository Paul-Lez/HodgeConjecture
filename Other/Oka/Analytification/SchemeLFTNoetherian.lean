/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes locally of finite type over `ℂ` are locally noetherian
-/

@[expose] public section

universe u

namespace ComplexAnalytic

/-- A scheme locally of finite type over `ℂ` is locally noetherian. -/
instance SchemeLFTℂ.isLocallyNoetherian (Y : SchemeLFTℂ.{u}) :
    AlgebraicGeometry.IsLocallyNoetherian Y.obj.left :=
  haveI : AlgebraicGeometry.LocallyOfFiniteType Y.obj.hom := Y.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom

end ComplexAnalytic

end
