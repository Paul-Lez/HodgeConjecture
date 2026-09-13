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

variable (R : Type) [Field R] (X : TopCat.{0})

/-- Raw singular cochains evaluated on an ambient open. -/
def openRawSingularCochainComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainPresheafComplex R X)

/-- Sections on an ambient open of the actual singular cochain sheaf complex. -/
def openSingularCochainSheafComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainSheafComplex R X)

/-- The actual singular-cochain sheafification unit evaluated on an ambient open. -/
def openRawToSingularCochainSheafComplex (V : Opens X) :
    openRawSingularCochainComplex R X V ⟶ openSingularCochainSheafComplex R X V :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).map
    (singularCochainSheafificationUnit R X)

/-- Actual restriction of raw cochains between two ambient opens. -/
def openRawSingularRestriction {V W : Opens X} (i : W ⟶ V) :
    openRawSingularCochainComplex R X V ⟶ openRawSingularCochainComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (singularCochainPresheafComplex R X)

/-- Actual restriction of sections of the singular cochain sheaf. -/
def openSingularSheafRestriction {V W : Opens X} (i : W ⟶ V) :
    openSingularCochainSheafComplex R X V ⟶ openSingularCochainSheafComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex (.up ℕ)).obj
        (singularCochainSheafComplex R X))

end AlgebraicTopology.Singular
