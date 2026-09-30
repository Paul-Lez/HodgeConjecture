/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Two missing lemmas about stalks

`TopCat.Presheaf.stalkPushforward C g F x : (g _* F).stalk (g x) ⟶ F.stalk x` is natural in `F`.
Mathlib has the definition and its compatibility with germs, identities and composites of `g`,
but not this naturality square, which is what one needs to move a morphism of presheaves on the
source space through a stalk computation on the target space.

`TopCat.Presheaf.stalkCongr F e : F.stalk x ≅ F.stalk y` for inseparable `x` and `y` likewise
has its compatibility with germs in Mathlib only as an equality of morphisms, for
`stalkSpecializes`; `TopCat.Presheaf.stalkCongr_hom_germ` is the applied form, which is what one
needs after `AlgebraicGeometry.SheafedSpace.hom_stalk_ext` puts such a transport into a goal.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Other/Oka/Topology/` mirror of the Mathlib directory tree for that reason.

## Main results

- `TopCat.Presheaf.stalkPushforward_naturality`
- `TopCat.Presheaf.stalkCongr_hom_germ`
- `TopCat.Presheaf.isIso_stalkSpecializes_of_eq`
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [HasColimits C]

set_option backward.isDefEq.respectTransparency.types false in
/-- The map on stalks induced by a pushforward is natural in the presheaf: pushing a morphism
`T : F ⟶ G` of presheaves on `X` forward along `g : X ⟶ Y` and then descending to the stalk at
`x` is the same as descending first and applying `T` on stalks. -/
lemma stalkPushforward_naturality {X Y : TopCat.{v}} (g : X ⟶ Y) {F G : X.Presheaf C}
    (T : F ⟶ G) (x : X) :
    (stalkFunctor C (g x)).map ((pushforward C g).map T) ≫ G.stalkPushforward C g x =
      F.stalkPushforward C g x ≫ (stalkFunctor C x).map T := by
  refine TopCat.Presheaf.stalk_hom_ext ((pushforward C g).obj F) fun U hU ↦ ?_
  -- `rw` cannot see through the definition of `TopCat.Presheaf` here, hence `erw`.
  erw [stalkFunctor_map_germ_assoc]
  simp only [pushforward_map_app, stalkFunctor_obj, stalkPushforward_germ,
    stalkPushforward_germ_assoc]
  exact (stalkFunctor_map_germ (C := C) ((Opens.map g).obj U) x hU T).symm

/-- **The specialization map between the stalks at two points which are in fact equal is an
isomorphism.**

`TopCat.Presheaf.stalkCongr` says this for `Inseparable` points and returns an isomorphism; this
is the `IsIso` form for a specialization arising from an equality, which is the shape in which it
is needed after `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom`; that lemma produces a
`stalkSpecializes` whose proof argument is manufactured from an equation between morphisms, and
one cannot name the resulting proof term in advance. -/
lemma isIso_stalkSpecializes_of_eq {X : TopCat.{v}} (F : X.Presheaf C) {a b : X} (h : a ⤳ b)
    (h' : b = a) : IsIso (F.stalkSpecializes h) := by
  subst h'
  have hid : F.stalkSpecializes h = 𝟙 _ := by simp
  rw [hid]
  infer_instance

section Concrete

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]

/-- **Transporting a germ between the stalks at two inseparable points is the germ at the other
point.**

Mathlib has `TopCat.Presheaf.germ_stalkSpecializes` as an equality of morphisms; this is the
applied form for the isomorphism `TopCat.Presheaf.stalkCongr`, which is what one needs after
`AlgebraicGeometry.SheafedSpace.hom_stalk_ext` puts a `stalkCongr` transport into the goal.

Note that the membership `hy` is an argument rather than derived from `hx`: any proof will do,
and taking it as given is what lets the caller write the germ at `y` in whatever form the
surrounding statement already produced. -/
lemma stalkCongr_hom_germ {X : TopCat.{v}} (F : X.Presheaf C) {x y : X} (e : Inseparable x y)
    (U : Opens X) (hx : x ∈ U) (hy : y ∈ U) (s : ToType (F.obj (op U))) :
    ConcreteCategory.hom (F.stalkCongr e).hom (F.germ U x hx s) = F.germ U y hy s :=
  (ConcreteCategory.comp_apply (F.germ U x hx) (F.stalkSpecializes e.ge) s).symm.trans
    (ConcreteCategory.congr_hom (F.germ_stalkSpecializes (h := e.ge) (U := U) (hy := hx)) s)

end Concrete

end TopCat.Presheaf

end
