/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.TauCeti.SheafOfModules.Restriction

/-!
# Čech transitions of local module trivializations

A pair of local frames induces an automorphism of the standard free rank-one sheaf on every
common refinement.  These automorphisms satisfy the identity, inverse, and cocycle laws.  The
construction is site-theoretic, so analytic and algebraic line-bundle atlases use the same API.
-/

public section

open CategoryTheory

namespace TauCeti.SheafOfModules.LocalTrivializations

universe u v u₁

noncomputable section

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

/-- Change from frame `i` to frame `j` after restricting both frames to the same object `Y`. -/
def transitionIsoOver (t : LocalTrivializations M) (i j : t.I) {Y : C}
    (f : Y ⟶ t.X i) (g : Y ⟶ t.X j) :
    _root_.SheafOfModules.free (R := R.over Y) PUnit ≅
      _root_.SheafOfModules.free (R := R.over Y) PUnit :=
  t.isoOver i f ≪≫ (t.isoOver j g).symm

/-- Changing from a frame to itself over the same restriction is the identity. -/
@[simp]
theorem transitionIsoOver_self (t : LocalTrivializations M) (i : t.I) {Y : C}
    (f : Y ⟶ t.X i) : t.transitionIsoOver i i f f = Iso.refl _ := by
  ext
  simp [transitionIsoOver]

/-- Reversing a change of frame gives its inverse. -/
@[simp]
theorem transitionIsoOver_symm (t : LocalTrivializations M) (i j : t.I) {Y : C}
    (f : Y ⟶ t.X i) (g : Y ⟶ t.X j) :
    (t.transitionIsoOver i j f g).symm = t.transitionIsoOver j i g f := by
  ext
  simp [transitionIsoOver]

/-- Changes of frame obey the Čech cocycle law on a common refinement. -/
@[simp]
theorem transitionIsoOver_trans (t : LocalTrivializations M) (i j k : t.I) {Y : C}
    (f : Y ⟶ t.X i) (g : Y ⟶ t.X j) (h : Y ⟶ t.X k) :
    t.transitionIsoOver i j f g ≪≫ t.transitionIsoOver j k g h =
      t.transitionIsoOver i k f h := by
  ext
  simp [transitionIsoOver]

end

end TauCeti.SheafOfModules.LocalTrivializations
