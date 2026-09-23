/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import Other.AlgebraicTopology.Support.SingularCohomologySheafComparison

/-! # Local normalization of the supported singular cohomology sheaf -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance complexSupportCohomologySheafNormalizationParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- The cohomology-sheaf comparison takes the canonical section to the relative sheafification
unit. -/
@[reassoc]
lemma complexSupportSingularCohomologySheafIsoRelative_section
    (S : Closeds (ComplexPoint X)) (n : ℕ) (V : Opens (ComplexPoint X)) :
    sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportSingularComplex X S) (n : ℤ) V ≫
        (supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint X)) S S.isClosed
          n).hom.hom.app (op V) =
    (complexSupportSingularSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V) :=
  supportedSingularCohomologySheafIsoRelative_section (TopCat.of (ComplexPoint X)) S S.isClosed n V

/-- The normalization equation on a local class. -/
lemma complexSupportSingularCohomologySheafIsoRelative_section_apply
    (S : Closeds (ComplexPoint X)) (n : ℕ) (V : Opens (ComplexPoint X))
    (z : ((((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportSingularComplex X S))).homology (n : ℤ)) :
    (supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint X)) S S.isClosed
        n).hom.hom.app (op V)
      (sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportSingularComplex X S) (n : ℤ) V z) =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V)
      (complexSupportSingularSectionCohomologyEquiv X S V n z) :=
  ConcreteCategory.congr_hom (complexSupportSingularCohomologySheafIsoRelative_section X S n V) z

end AlgebraicGeometry.ComplexPoint
