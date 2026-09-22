/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-!
# Supported singular cochains on a smooth projective variety

`Γ_S(C^•)` is the complex of sections supported in the closed set `S` of the sheafified rational
singular cochains on `X(ℂ)`. It is bounded below and termwise flasque, and its open-section
cohomology is relative singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `S` a closed subset of its analytic
space `X(ℂ)`. This complex has in each degree the subsheaf of the sheafified rational singular
cochains consisting of sections that vanish off `S`. -/
def complexSupportSingularComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  -- `Γ_S(C^•)`, the `S`-supported subsheaves of the singular cochains on `X(ℂ)`.
  supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl

instance complexSupportSingularComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportSingularComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportSingularComplex, supportedRationalSingularCochainComplex]
  infer_instance

instance complexSupportSingularComplex_isFlasque (S : Closeds (ComplexPoint X)) (n : ℤ) :
    ((complexSupportSingularComplex X S).X n).IsFlasque :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque (TopCat.of (ComplexPoint X)) S.compl
    ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X n)

end AlgebraicGeometry.ComplexPoint
