/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueExtendNat
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution

/-!
# The sheafified singular cochains as a flasque complex

On a hereditarily paracompact Hausdorff space the sheafified rational singular cochains form a
bounded-below complex of flasque sheaves. Its subcomplex of sections vanishing on an open set
is the supported model of cohomology with support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

/-- Let `X` be a topological space. This complex of sheaves is obtained by sheafifying the
presheaves of rational singular cochains degree by degree. Its differential is induced by the
singular coboundary, and it is extended by zero to negative integer degrees. -/
def rationalSingularCochainComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  (singularCochainSheafComplex ℚ X).extend ComplexShape.embeddingUpNat

instance rationalSingularCochainComplex_isStrictlyGE :
    (rationalSingularCochainComplex X).IsStrictlyGE 0 := by
  dsimp [rationalSingularCochainComplex]
  infer_instance

/-- Let `X` be a topological space and `U ⊆ X` open. In each nonnegative degree, take the kernel of
restriction of the sheafified rational singular cochains to `U`. These are the sheaf sections
supported in the closed set `X \ U`. Singular coboundaries give the differentials, and
negative-degree terms are zero. -/
def supportedRationalSingularCochainComplex (U : Opens X) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  -- `Γ_{X \ U}` applied to the sheaf complex of rational singular cochains.
  ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
    -- The sheaf complex `C^•_sing(-; ℚ)`.
    (rationalSingularCochainComplex X)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

instance rationalSingularCochainComplex_isFlasque (n : ℤ) :
    ((rationalSingularCochainComplex X).X n).IsFlasque := by
  apply TopCat.Sheaf.extendNat_term_isFlasque
  intro m
  change (singularCochainSheaf ℚ X m).IsFlasque
  infer_instance

end AlgebraicTopology.Singular
