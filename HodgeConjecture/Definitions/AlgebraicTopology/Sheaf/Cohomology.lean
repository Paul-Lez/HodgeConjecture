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

/-- For a presheaf `P` of abelian groups on `X`, this is its associated sheaf. -/
def cohomologySheafOfPresheaf (P : TopCat.Presheaf AddCommGrpCat X) :
    TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P

/-- For a presheaf `P`, this is the canonical map from `P` to its associated sheaf. -/
def cohomologySheafOfPresheafToSheaf (P : TopCat.Presheaf AddCommGrpCat X) :
    P ⟶ (cohomologySheafOfPresheaf X P).obj :=
  toSheafify (Opens.grothendieckTopology X) P

/-- For a contravariant functor `F` on topological spaces, this is the sheafification of the
presheaf `V ↦ F(V)` on `X`. -/
def CohomologySheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  cohomologySheafOfPresheaf X ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat)

/-- For a contravariant functor `F` on topological spaces, this is the canonical map from the
presheaf `V ↦ F(V)` on `X` to its associated sheaf. -/
def cohomologySheafToSheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat) ⟶
      (CohomologySheaf X F).obj :=
  cohomologySheafOfPresheafToSheaf X _

/-- For a contravariant functor `F` on the opens of `X`, this is the sheafification of the presheaf
`V ↦ F(V)`. -/
def CohomologySheafOfOpens (F : Opens X ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  cohomologySheafOfPresheaf X (F.op ⋙ unopUnop AddCommGrpCat)

/-- The constructions from all topological spaces and from the opens of `X` agree after restricting
`F` to the opens of `X`. -/
def cohomologySheafRestrictionIso (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    CohomologySheaf X F ≅
      CohomologySheafOfOpens X (TopologicalSpace.Opens.toTopCat X ⋙ F) :=
  Iso.refl _

/-- For a contravariant functor `F` on the opens of `X`, this is the canonical map from the
presheaf `V ↦ F(V)` to its associated sheaf. -/
def cohomologySheafOfOpensToSheaf (F : Opens X ⥤ AddCommGrpCatᵒᵖ) :
    F.op ⋙ unopUnop AddCommGrpCat ⟶ (CohomologySheafOfOpens X F).obj :=
  cohomologySheafOfPresheafToSheaf X _

/-- For a contravariant functor `F` on topological spaces, this is the canonical map from the
restricted presheaf `V ↦ F(V)` to its associated sheaf. -/
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

/-- For a local cohomology theory `F` with support in `S` and degree `n`, this is the sheafification
of the presheaf `V ↦ F(S,n,V)`. -/
def SupportedCohomologySheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCatᵒᵖ) (n : ℕ) : Sheaf AddCommGrpCat X :=
  CohomologySheafOfOpens X (F S n)

/-- For the local theory `F` with support in `S` and degree `n`, this is the canonical map from the
presheaf `V ↦ F(S,n,V)` to its associated sheaf. -/
def supportedCohomologyToSheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCatᵒᵖ) (n : ℕ) :
    (F S n).op ⋙ unopUnop AddCommGrpCat ⟶ (SupportedCohomologySheaf X S F n).obj :=
  cohomologySheafOfOpensToSheaf X (F S n)

end Supported

end TopCat.Sheaf

end
