/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# The stalk of a presheaf of modules, as a functor

Material for `Mathlib/Algebra/Category/ModuleCat/Stalk.lean`.

Mathlib's file of that name puts a `Module (R.stalk x)` structure on the stalk of a presheaf of
modules over a presheaf of commutative rings `R`, with `PresheafOfModules.germ_smul` as the
characterising lemma. **It stops at the object.** This file is the functor:

```
PresheafOfModules.stalkFunctor x :
  PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat (R.stalk x)
```

together with the germ description of what it does to a morphism.

## Why `CommRingCat` and not `RingCat`

Mathlib's `Module (R.stalk x)` instance comes in both flavours, and the `RingCat` one is more
general. This file takes the `CommRingCat` one because **its consumer needs commutative stalks**:
the base-change theorem `PresheafOfModules.pullbackStalkIso` is stated with
`ModuleCat.extendScalars`, which Mathlib provides only for a ring map between *commutative*
rings. It is also the spelling `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` produces, since
`Y.presheaf` is `CommRingCat`-valued and `ringSheaf` is it composed with `forget₂`.

## Main definitions

- `PresheafOfModules.stalkFunctor`: the stalk at `x`, as a functor to modules over the stalk of
  the presheaf of rings.

## Main results

- `PresheafOfModules.stalkFunctor_map_germ`: it sends a germ to a germ.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

@[expose] public noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}} (x : X)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a presheaf of modules at a point, as a functor. -/
def stalkFunctor :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
      ModuleCat.{u} (R.stalk x) where
  obj M := ModuleCat.of (R.stalk x) (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
  map {M N} f := ModuleCat.ofHom
    { toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map f)
      map_add' a b := map_add _ a b
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
        obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
        rw [← TopCat.Presheaf.germ_res_apply R (homOfLE (inf_le_left : U ⊓ V ≤ U)) x
              ⟨hxU, hxV⟩ r,
            ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (inf_le_right : U ⊓ V ≤ V)) x
              ⟨hxU, hxV⟩ m,
            ← germ_smul]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u})
              (F := M.presheaf) (G := N.presheaf) (U ⊓ V) x ⟨hxU, hxV⟩ ((toPresheaf _).map f),
            TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u})
              (F := M.presheaf) (G := N.presheaf) (U ⊓ V) x ⟨hxU, hxV⟩ ((toPresheaf _).map f)]
        rw [RingHom.id_apply, ← germ_smul]
        congr 1
        exact (Hom.app f (op (U ⊓ V))).hom.map_smul _ _ }
  map_id M := by
    ext m
    change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map (𝟙 M)))) m = m
    erw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {M N P} f g := by
    ext m
    change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map (f ≫ g)))) m = _
    erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ConcreteCategory.comp_apply]

/- Not `@[simp]`: the `simpNF` linter rejects the left-hand side, which simplifies further under
`PresheafOfModules.presheaf_obj_coe`. It is used by `rw`, which is what its consumers want. -/
lemma stalkFunctor_map_germ (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (f : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    (stalkFunctor x).map f (TopCat.Presheaf.germ M.presheaf U x hx m) =
      TopCat.Presheaf.germ N.presheaf U x hx (Hom.app f (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u})
    (F := M.presheaf) (G := N.presheaf) U x hx ((toPresheaf _).map f) m

end PresheafOfModules
