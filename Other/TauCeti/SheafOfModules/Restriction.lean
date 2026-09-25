/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Other.TauCeti.SheafOfModules.LocalTriviality
public import Other.TauCeti.SheafOfModules.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restricting local trivializations

This file is adapted from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/Restriction.lean` at Tau Ceti commit
`6b10e2573adea2abab44b08630b9c69e73048090`. See `Other/TauCeti/README.md` for provenance.

A local trivialization of a sheaf of modules over an object `X` remains a trivialization after
restriction along a morphism `f : Y ⟶ X`. This is the refinement interface needed to compare
local trivializations after inverse-image constructions such as analytification.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction along `f : Y ⟶ X` carries the standard free rank-one sheaf over `X` to the
standard free rank-one sheaf over `Y`. -/
def overMapFreePUnitIso {X Y : C} (f : Y ⟶ X) :
    (_root_.SheafOfModules.overMap R f).obj
        (_root_.SheafOfModules.free (R := R.over X) PUnit) ≅
      _root_.SheafOfModules.free (R := R.over Y) PUnit :=
  (_root_.SheafOfModules.overMap R f).mapIso
      (freePUnitIsoUnit (R.over X) :
        _root_.SheafOfModules.free (R := R.over X) PUnit ≅
          _root_.SheafOfModules.unit (R.over X)) ≪≫
    _root_.SheafOfModules.overMapUnitIso (R := R) f ≪≫
      (freePUnitIsoUnit (R.over Y) :
        _root_.SheafOfModules.free (R := R.over Y) PUnit ≅
          _root_.SheafOfModules.unit (R.over Y)).symm

namespace LocalTrivializations

variable {M : SheafOfModules.{u} R}

/-- Restrict one member of a local trivialization atlas along a morphism into its covering
object. The resulting isomorphism trivializes `M` over the source of that morphism. -/
def isoOver (t : LocalTrivializations M) (i : t.I) {Y : C} (f : Y ⟶ t.X i) :
    _root_.SheafOfModules.free (R := R.over Y) PUnit ≅ M.over Y :=
  (overMapFreePUnitIso (R := R) f).symm ≪≫
    (_root_.SheafOfModules.overMap R f).mapIso (t.iso i) ≪≫
      (_root_.SheafOfModules.overFunctorMap R f).app M

/-- Replace the cover of a local trivialization atlas by a refining cover. -/
def ofRefinement (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    LocalTrivializations M where
  I := I
  X := Y
  coversTop := coversTop
  iso j := t.isoOver (index j) (map j)

@[simp]
lemma ofRefinement_I (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    (t.ofRefinement Y coversTop index map).I = I :=
  (rfl)

@[simp]
lemma ofRefinement_X (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    (t.ofRefinement Y coversTop index map).X =
      fun j ↦ Y ((ofRefinement_I t Y coversTop index map).mp j) :=
  (rfl)

@[simp]
lemma ofRefinement_iso (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j))
    (j : (t.ofRefinement Y coversTop index map).I) :
    (t.ofRefinement Y coversTop index map).iso j =
      cast (by rw [ofRefinement_X])
        (t.isoOver (index ((ofRefinement_I t Y coversTop index map).mp j))
          (map ((ofRefinement_I t Y coversTop index map).mp j))) :=
  (rfl)

end LocalTrivializations

end SheafOfModules

end

end TauCeti
