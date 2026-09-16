/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

/-!
# Cohomology-sheaf concentration for smooth closed supports

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.CohomologySheaf`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Actual open-section cohomology of the supported injective model is relative
singular cohomology of the same literal local support pair. -/
def complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint X))
    (V : Opens (ComplexPoint X)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n :=
  letI : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  (complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed V n)

end AlgebraicGeometry.ComplexPoint

end
