/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainOpenRestriction
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.GlobalRestriction

/-! # Singular cochains compute sheafified cochains on an arbitrary open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R] (X : TopCat.{0})

/-- Let `R` be a commutative ring, `X` a topological space, and `V ⊆ X` open. This is the complex of
abelian groups `C^*(V; R)`, whose degree-`n` elements are `R`-linear functions on singular
`n`-chains of `V` and whose differential is dual to the boundary. -/
def openRawSingularCochainComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainPresheafComplex R X)

/-- Let `R` be a commutative ring, `X` a topological space, and `V ⊆ X` open. This is the complex of
sections over `V` of the sheaves obtained by sheafifying `U ↦ C^n(U; R)` on `X`. The
differential is induced by singular coboundaries. -/
def openSingularCochainSheafComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainSheafComplex R X)

/-- Let `R` be a commutative ring, `X` a topological space, and `V ⊆ X` open. This complex map sends
each singular cochain on `V` to the section it represents in the sheafification of `U ↦ C^n(U;
R)`. It commutes with the coboundary. -/
def openRawToSingularCochainSheafComplex (V : Opens X) :
    openRawSingularCochainComplex R X V ⟶ openSingularCochainSheafComplex R X V :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).map
    (singularCochainSheafificationUnit R X)

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. This map
`C^*(V; R) → C^*(W; R)` restricts a singular cochain to simplices whose images lie in `W`. -/
def openRawSingularRestriction {V W : Opens X} (i : W ⟶ V) :
    openRawSingularCochainComplex R X V ⟶ openRawSingularCochainComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (singularCochainPresheafComplex R X)

/-- Let `R` be a commutative ring and `W ⊆ V` open subsets of a topological space `X`. This map
restricts sections of the sheafified singular cochain complex from `V` to `W` in every
nonnegative degree. -/
def openSingularSheafRestriction {V W : Opens X} (i : W ⟶ V) :
    openSingularCochainSheafComplex R X V ⟶ openSingularCochainSheafComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex (.up ℕ)).obj
        (singularCochainSheafComplex R X))

end AlgebraicTopology.Singular
