/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import Mathlib.Topology.Sheaves.Functors

/-!
# Restriction of constant sheaves along a continuous map

For a continuous map `f : X → Y` and an abelian group `A`, this is the morphism `A_Y → f_* A_X` of
constant sheaves, with its identity and composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

open _root_.Opens

@[inherit_doc grothendieckTopology]
scoped notation "𝓖[" X "]" => grothendieckTopology X

/-- Constant sheaves restrict along a continuous map. -/
def constantRestriction {X Y : TopCat.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    𝓒[Y; A] ⟶ (pushforward _ f).obj 𝓒[X; A] :=
  ⟨sheafifyLift 𝓖[Y] (Functor.whiskerLeft (Opens.map f).op (toSheafify 𝓖[X] 𝓒ᵖ[X; A]))
    ((pushforward AddCommGrpCat f).obj 𝓒[X; A]).property⟩

@[reassoc]
lemma toSheafify_constantRestriction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : AddCommGrpCat.{u}) :
    toSheafify 𝓖[Y] 𝓒ᵖ[Y; A] ≫
        (constantRestriction f A).hom =
      Functor.whiskerLeft (Opens.map f).op
        (toSheafify 𝓖[X] 𝓒ᵖ[X; A]) :=
  toSheafify_sheafifyLift _ _ _

@[simp]
lemma constantRestriction_id (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    constantRestriction (𝟙 X) A = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact 𝓒[X; A].property
  · exact (toSheafify_constantRestriction (𝟙 X) A).trans (by rfl)

lemma constantRestriction_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : AddCommGrpCat.{u}) :
    constantRestriction (f ≫ g) A =
      constantRestriction g A ≫ (pushforward AddCommGrpCat g).map (constantRestriction f A) := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact ((pushforward AddCommGrpCat (f ≫ g)).obj 𝓒[X; A]).property
  · change _ = _ ≫ (constantRestriction g A).hom ≫
      Functor.whiskerLeft (Opens.map g).op (constantRestriction f A).hom
    rw [toSheafify_constantRestriction]
    erw [← Category.assoc, toSheafify_constantRestriction]
    ext U : 2
    exact (NatTrans.congr_app (toSheafify_constantRestriction f A)
      ((Opens.map g).op.obj U)).symm

end TopCat.Sheaf
