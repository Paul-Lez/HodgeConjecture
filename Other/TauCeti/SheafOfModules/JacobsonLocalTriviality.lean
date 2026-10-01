/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.TauCeti.SheafOfModules.LocalTriviality
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.JacobsonSpace
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocallyFree

/-!
# Local triviality from neighbourhoods of closed points

On a Jacobson space, rank-one trivializations near every closed point form a cover of the whole
space.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace TauCeti.SheafOfModules.LocalTrivializations

universe u v u₁

variable {T : Type u₁} [TopologicalSpace T] [JacobsonSpace T]
  {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [∀ U : Opens T, HasWeakSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{u}]
  [∀ U : Opens T,
    ((Opens.grothendieckTopology T).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : _root_.SheafOfModules.{u} R}

/-- Rank-one trivializations near all closed points give a global local-trivialization atlas. -/
def ofClosedPoints (U : closedPoints T → Opens T)
    (hU : ∀ x : closedPoints T, x.1 ∈ U x)
    (e : ∀ x : closedPoints T,
      _root_.SheafOfModules.free (R := R.over (U x)) PUnit ≅ M.over (U x)) :
    LocalTrivializations M where
  I := closedPoints T
  X := U
  coversTop := (Opens.coversTop_iff T U).2 <| IsOpenCover.of_sets
    (fun x ↦ (U x).isOpen) <| by
      let W : Set T := ⋃ x, (U x : Set T)
      have hWopen : IsOpen W := isOpen_iUnion fun x ↦ (U x).isOpen
      have hclosed : closedPoints T ⊆ W := by
        intro x hx
        exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hU ⟨x, hx⟩⟩
      apply Set.eq_univ_iff_forall.2
      intro x
      by_contra hx
      obtain ⟨y, hyW, hyclosed⟩ := nonempty_inter_closedPoints
        (Z := Wᶜ) ⟨x, hx⟩ hWopen.isClosed_compl.isLocallyClosed
      exact hyW (hclosed hyclosed)
  iso := e

end TauCeti.SheafOfModules.LocalTrivializations

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

/-- A coherent sheaf whose closed-point stalks have rank one is invertible on a Jacobson locally
ringed space. -/
theorem isInvertible_of_isCoherent_of_basis_closedPoints
    (Y : LocallyRingedSpace.{u}) [JacobsonSpace Y]
    (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent]
    (h : ∀ y : closedPoints Y,
      Nonempty (Module.Basis PUnit.{u + 1}
        (Y.presheaf.stalk y.1) ((Y.stalkFunctor y.1).obj M))) :
    TauCeti.SheafOfModules.IsInvertible.{u, u, u} M := by
  classical
  choose U hyU eU using fun y : closedPoints Y ↦
    exists_restrictModules_iso_free_of_basis M y.1 (h y).some
  let eOver (y : closedPoints Y) :
      SheafOfModules.free (R := Y.ringSheaf.over (U y)) PUnit.{u + 1} ≅ M.over (U y) := by
    let Y' := Y.restrict (U y).isOpenEmbedding
    let E := restrictOverEquiv Y (U y)
    let eFree : E.functor.obj
          (SheafOfModules.free (R := Y.ringSheaf.over (U y)) PUnit.{u + 1}) ≅
        SheafOfModules.free (R := Y'.ringSheaf) PUnit.{u + 1} :=
      E.functor.mapIso (SheafOfModules.overFreeIso PUnit.{u + 1} (U y)) ≪≫
        (restrictModulesObjIso Y (U y) (SheafOfModules.free PUnit.{u + 1})).symm ≪≫
          (Y.ofRestrict (U y).isOpenEmbedding).pullbackModulesFreeIso PUnit.{u + 1}
    exact E.functor.preimageIso
      (eFree ≪≫ (eU y).some.symm ≪≫ restrictModulesObjIso Y (U y) M)
  exact (TauCeti.SheafOfModules.LocalTrivializations.ofClosedPoints U hyU eOver).isInvertible

end AlgebraicGeometry.LocallyRingedSpace
