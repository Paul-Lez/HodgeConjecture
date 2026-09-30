/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithfully flat stalk maps

Faithful flatness of stalk maps is stable under composition and holds for stalk isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

/-- An isomorphism of commutative rings is faithfully flat. -/
theorem _root_.CommRingCat.faithfullyFlat_hom_of_isIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsIso f] : f.hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.of_bijective (ConcreteCategory.bijective_of_isIso f)

/-- Faithfully flat stalk maps compose. -/
theorem faithfullyFlat_stalkMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hf : (f.stalkMap x).hom.FaithfullyFlat) (hg : (g.stalkMap (f.base x)).hom.FaithfullyFlat) :
    ((f ≫ g).stalkMap x).hom.FaithfullyFlat := by
  rw [stalkMap_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition (g.stalkMap (f.base x)).hom
    (f.stalkMap x).hom hg hf

/-- A stalk isomorphism is faithfully flat. -/
theorem faithfullyFlat_stalkMap_of_isIso (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    (f.stalkMap x).hom.FaithfullyFlat :=
  CommRingCat.faithfullyFlat_hom_of_isIso _

/-- An open immersion has faithfully flat stalk maps. -/
theorem faithfullyFlat_stalkMap_of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] (x : X) : (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso f x

/-- An isomorphism of locally ringed spaces has faithfully flat stalk maps. -/
theorem faithfullyFlat_stalkMap_of_isIso_hom (f : X ⟶ Y) [IsIso f] (x : X) :
    (f.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isOpenImmersion f x

/-- The forward map of an isomorphism has faithfully flat stalk maps. -/
theorem faithfullyFlat_stalkMap_iso_hom (e : X ≅ Y) (x : X) :
    (e.hom.stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isIso_hom e.hom x

/-- Cancel a stalk isomorphism on the left of a faithfully flat composite. -/
theorem faithfullyFlat_stalkMap_of_comp (ι : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    [IsIso (ι.stalkMap x)] (h : ((ι ≫ f).stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  have e : f.stalkMap (ι.base x) = (ι ≫ f).stalkMap x ≫ inv (ι.stalkMap x) := by
    rw [stalkMap_comp]
    simp
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition ((ι ≫ f).stalkMap x).hom
    (inv (ι.stalkMap x)).hom h (CommRingCat.faithfullyFlat_hom_of_isIso _)

/-- Cancel a stalk isomorphism from a composite identified with another morphism. -/
theorem faithfullyFlat_stalkMap_of_comp_eq (ι : X ⟶ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (e : ι ≫ f = g) (x : X) [IsIso (ι.stalkMap x)]
    (h : (g.stalkMap x).hom.FaithfullyFlat) :
    (f.stalkMap (ι.base x)).hom.FaithfullyFlat := by
  subst e
  exact faithfullyFlat_stalkMap_of_comp ι f x h

/-- Cancel a stalk isomorphism on the right of a faithfully flat composite. -/
theorem faithfullyFlat_stalkMap_of_comp_eq_right (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ Z)
    (e : f ≫ j = g) (x : X) [IsIso (j.stalkMap (f.base x))]
    (h : (g.stalkMap x).hom.FaithfullyFlat) : (f.stalkMap x).hom.FaithfullyFlat := by
  subst e
  have e : f.stalkMap x = inv (j.stalkMap (f.base x)) ≫ (f ≫ j).stalkMap x := by
    rw [stalkMap_comp]
    simp
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition (inv (j.stalkMap (f.base x))).hom
    ((f ≫ j).stalkMap x).hom (CommRingCat.faithfullyFlat_hom_of_isIso _) h

end AlgebraicGeometry.LocallyRingedSpace
