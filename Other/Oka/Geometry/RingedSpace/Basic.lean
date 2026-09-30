/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# A section is a unit on any open subset of its basic open

Material for `Mathlib/Geometry/RingedSpace/Basic.lean`; see `README.md` on the mirror tree.

Mathlib's `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen` says that a section `f` over `U`
becomes a unit when restricted to `X.basicOpen f`, and that is the only form of the statement
there. What a consumer usually holds instead is an open `V` which is merely *contained* in
`X.basicOpen f` ; the open comes from somewhere else and the non-vanishing of `f` on it is a
hypothesis ; and restricting a unit again keeps it a unit, so the general form is one rewrite
away from Mathlib's.

The rewrite is the only content: `Opens X` is a preorder category, so the composite of the two
restriction maps and the direct one are the same morphism by `Subsingleton.elim`.

## Main results

- `AlgebraicGeometry.RingedSpace.isUnit_res_of_le_basicOpen`: **a section is a unit on every open
  subset of its basic open.**
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **A section is a unit on every open subset of its basic open.**

`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen` is the case `V = X.basicOpen f`; this is
that restricted once more, along `V ≤ X.basicOpen f`. -/
lemma isUnit_res_of_le_basicOpen (X : RingedSpace.{u}) {U V : Opens X}
    (f : X.presheaf.obj (op U)) (hVU : V ≤ U) (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have h1 := (X.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE h ≫ homOfLE (X.basicOpen_le f)) (homOfLE hVU)] at h1

end AlgebraicGeometry.RingedSpace

end
