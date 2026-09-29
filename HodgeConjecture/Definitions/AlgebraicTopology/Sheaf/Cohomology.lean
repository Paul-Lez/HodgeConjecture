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

/-- The sheaf associated to a contravariant cohomology functor on topological spaces. -/
def CohomologySheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat)

/-- The canonical map from the cohomology presheaf to its associated sheaf. -/
def cohomologySheafToSheaf (F : TopCat ⥤ AddCommGrpCatᵒᵖ) :
    ((TopologicalSpace.Opens.toTopCat X ⋙ F).op ⋙ unopUnop AddCommGrpCat) ⟶
      (CohomologySheaf X F).obj :=
  toSheafify (Opens.grothendieckTopology X) _

/-- The sheaf associated to a contravariant cohomology functor on the opens of `X`. -/
def CohomologySheafOfOpens (F : Opens X ⥤ AddCommGrpCatᵒᵖ) : TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (F.op ⋙ unopUnop AddCommGrpCat)

/-- The canonical map from an open-set cohomology functor to its associated sheaf. -/
def cohomologySheafOfOpensToSheaf (F : Opens X ⥤ AddCommGrpCatᵒᵖ) :
    F.op ⋙ unopUnop AddCommGrpCat ⟶ (CohomologySheafOfOpens X F).obj :=
  toSheafify (Opens.grothendieckTopology X) _

end TopCat.Sheaf

end
