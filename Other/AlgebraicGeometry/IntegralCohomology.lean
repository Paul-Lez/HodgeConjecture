/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Integral coefficients and change to rational coefficients
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (X : Over (Spec ↧ℂ))

local instance integralCohomologyTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The ordinary sheaf-cohomology presentation of Ext from the plain constant integer sheaf. -/
def sheafCohomologyEquivExt (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Sheaf.H F n ≃+ Abelian.Ext.{0} (𝓒(↧(ComplexPoint X); ℤ)) F n :=
  let e := (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).mapIso
    (show AddCommGrpCat.of (ULift ℤ) ≅ AddCommGrpCat.of ℤ from
      (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso)
  (((Abelian.extFunctor n).mapIso e.op).app F).addCommGroupIsoToAddEquiv.symm

/-- The canonical change from integral to rational coefficients. -/
def integralToRationalCohomology (n : ℕ) :
    H^n(X; ℤ) →+ H^n(X; ℚ) :=
  Sheaf.H.map (integerToFieldConstantSheaf ℚ X 1) n

end AlgebraicGeometry.ComplexPoint
