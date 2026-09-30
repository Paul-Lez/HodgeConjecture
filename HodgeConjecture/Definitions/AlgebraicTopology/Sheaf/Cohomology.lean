/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Cohomology sheaves

This file sheafifies contravariant cohomology functors on topological spaces.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- The sheafification of a presheaf of abelian groups on `X`. -/
def cohomologySheafOfPresheaf (P : TopCat.Presheaf AddCommGrpCat X) :
    TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P

/-- The canonical map from a presheaf to its associated sheaf. -/
def cohomologySheafOfPresheafToSheaf (P : TopCat.Presheaf AddCommGrpCat X) :
    P ⟶ (cohomologySheafOfPresheaf X P).obj :=
  toSheafify (Opens.grothendieckTopology X) P

/-- The sheaf associated to a contravariant cohomology functor on topological spaces. -/
def CohomologySheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  cohomologySheafOfPresheaf X ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat)

/-- The canonical map from the cohomology presheaf to its associated sheaf. -/
def cohomologySheafToSheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat) ⟶
      (CohomologySheaf X F).obj :=
  cohomologySheafOfPresheafToSheaf X _

/-- The sheaf associated to a contravariant cohomology functor on the opens of `X`. -/
def CohomologySheafOfOpens (F : Opens X ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  cohomologySheafOfPresheaf X (F.op ⋙ unopUnop AddCommGrpCat)

/-- Restricting the topological-space functor gives the open-set construction. -/
def cohomologySheafRestrictionIso (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    CohomologySheaf X F ≅
      CohomologySheafOfOpens X (TopologicalSpace.Opens.toTopCat X ⋙ F) :=
  Iso.refl _

/-- The canonical map from an open-set cohomology functor to its associated sheaf. -/
def cohomologySheafOfOpensToSheaf (F : Opens X ⥤ AddCommGrpCatᵒᵖ) :
    F.op ⋙ unopUnop AddCommGrpCat ⟶ (CohomologySheafOfOpens X F).obj :=
  cohomologySheafOfPresheafToSheaf X _

/-- The generic cohomology-sheaf map after restriction to the opens of `X`. -/
def cohomologySheafRestrictionToSheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat) ⟶
      (CohomologySheafOfOpens X (TopologicalSpace.Opens.toTopCat X ⋙ F)).obj :=
  cohomologySheafToSheaf X F ≫ (cohomologySheafRestrictionIso X F).hom.hom

@[simp]
theorem cohomologySheafRestrictionToSheaf_eq (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    cohomologySheafRestrictionToSheaf X F =
      cohomologySheafOfOpensToSheaf X (TopologicalSpace.Opens.toTopCat X ⋙ F) := by
  rfl

section Supported

variable (S : Set X)

/-- The sheafification of a restriction-natural local cohomology theory with support in `S`. -/
def SupportedCohomologySheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCatᵒᵖ) (n : ℕ) : Sheaf AddCommGrpCat X :=
  CohomologySheafOfOpens X (F S n)

/-- The canonical map from a local cohomology theory with support to its sheafification. -/
def supportedCohomologyToSheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCatᵒᵖ) (n : ℕ) :
    (F S n).op ⋙ unopUnop AddCommGrpCat ⟶ (SupportedCohomologySheaf X S F n).obj :=
  cohomologySheafOfOpensToSheaf X (F S n)

end Supported

end TopCat.Sheaf

end
