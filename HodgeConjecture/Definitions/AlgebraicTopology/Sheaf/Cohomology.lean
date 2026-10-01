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

universe u v

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- For a contravariant functor `F` on the opens of `X`, this is the sheafification of the presheaf
`V ↦ F(V)`. -/
def CohomologySheafOfOpens (F : Opens X ⥤ AddCommGrpCat.{v}ᵒᵖ)
    [h : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (F.op ⋙ unopUnop AddCommGrpCat)

/-- For a contravariant functor `F` on the opens of `X`, this is the canonical map from the
presheaf `V ↦ F(V)` to its associated sheaf. -/
def cohomologySheafOfOpensToSheaf (F : Opens X ⥤ AddCommGrpCat.{v}ᵒᵖ)
    [h : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    F.op ⋙ unopUnop AddCommGrpCat ⟶ (CohomologySheafOfOpens X F).obj :=
  toSheafify (Opens.grothendieckTopology X) _

section Supported

variable (S : Set X)

/-- For a local cohomology theory `F` with support in `S` and degree `n`, this is the sheafification
of the presheaf `V ↦ F(S,n,V)`. -/
def SupportedCohomologySheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCat.{v}ᵒᵖ) (n : ℕ)
    [h : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    Sheaf AddCommGrpCat.{v} X :=
  CohomologySheafOfOpens X (F S n) (h := h)

/-- For the local theory `F` with support in `S` and degree `n`, this is the canonical map from the
presheaf `V ↦ F(S,n,V)` to its associated sheaf. -/
def supportedCohomologyToSheaf
    (F : Set X → ℕ → Opens X ⥤ AddCommGrpCat.{v}ᵒᵖ) (n : ℕ)
    [h : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    (F S n).op ⋙ unopUnop AddCommGrpCat ⟶ (SupportedCohomologySheaf X S F n).obj :=
  toSheafify (Opens.grothendieckTopology X) _

end Supported

end TopCat.Sheaf

end
