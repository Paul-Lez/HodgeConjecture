/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Comparing the two transports of a pushforward along equal maps

`TopCat.Presheaf.pushforwardEq` moves a presheaf pushed forward along `f` to the same presheaf
pushed forward along `g`, given `f = g`. `AlgebraicGeometry.PresheafedSpace.ext` produces the
same transport by a different route, as `Functor.whiskerRight (eqToHom _) F`. This file says the
two agree, and that they therefore cancel.

There is nothing to it: a natural transformation `(Opens.map f).op ⟶ (Opens.map g).op` has
components in `(Opens X)ᵒᵖ`, which is a poset, so there is at most one of them. The statement
is worth having because it is the step where a proof about `PresheafedSpace.ext` meets a
construction phrased with `pushforwardEq`.

It is the *cancellation*, not the identification, that tactics cannot do. `rw` and `simp` apply
`whiskerRight_eq_pushforwardEq_hom` and reassociate the composite without complaint; what fails
is the last step, cancelling the `inv ≫ hom` they are left with. `TopCat.Presheaf` is a `def`
for a functor category, so on `(α ≫ β ≫ (pushforwardEq h F).inv) ≫ (pushforwardEq h F).hom =
α ≫ β` the rewrite `Iso.inv_hom_id` reports "did not find an occurrence of the pattern", with a
note that the target is not type-correct under the `instances` transparency level; after
reassociating, `Category.comp_id` fails the same way on `α ≫ β ≫ 𝟙 _ = α ≫ β`, and
`simp only [Category.comp_id]` reports the lemma as unused and leaves the goal open.

`TopCat.Presheaf.comp_pushforwardEq_inv_comp_whiskerRight` therefore does that cancellation once,
in term mode, and is stated in the exact shape a composite of two morphisms produces: it is meant
to be applied by `exact`, which unifies up to definitional equality, rather than rewritten with.

## Main results

- `TopCat.Presheaf.whiskerRight_eq_pushforwardEq_hom`
- `TopCat.Presheaf.comp_pushforwardEq_inv_comp_whiskerRight`
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe v u w

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- **Any natural transformation between the pullback-of-opens functors of two equal maps induces
the transport of `TopCat.Presheaf.pushforwardEq`**, because its components live in a poset and
so are unique. -/
lemma whiskerRight_eq_pushforwardEq_hom (h : f = g) (F : X.Presheaf C)
    (e : (Opens.map f).op ⟶ (Opens.map g).op) :
    Functor.whiskerRight e F = (pushforwardEq h F).hom := by
  ext U
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The transport inserted by `AlgebraicGeometry.PresheafedSpace.ext` cancels against
`TopCat.Presheaf.pushforwardEq`.

Stated for a composite `α ≫ β ≫ _` rather than for the pair alone, because that is the shape the
`c`-component of a composition of morphisms of presheafed spaces has, and because a caller given
only the pair form could not finish with it: `rw` reassociates and applies it happily, and then
cannot cancel the identity it is left with. See the module docstring. -/
lemma comp_pushforwardEq_inv_comp_whiskerRight (h : f = g) (F : X.Presheaf C)
    {P Q : Y.Presheaf C} (α : P ⟶ Q) (β : Q ⟶ g _* F)
    (e : (Opens.map f).op ⟶ (Opens.map g).op) :
    (α ≫ β ≫ (pushforwardEq h F).inv) ≫ Functor.whiskerRight e F = α ≫ β :=
  have hcancel : (pushforwardEq h F).inv ≫ Functor.whiskerRight e F = 𝟙 _ :=
    (congrArg (fun z ↦ (pushforwardEq h F).inv ≫ z)
      (whiskerRight_eq_pushforwardEq_hom h F e)).trans (pushforwardEq h F).inv_hom_id
  (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ α ≫ z)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ β ≫ z) hcancel).trans (Category.comp_id β))))

end TopCat.Presheaf

end
