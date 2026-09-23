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

/-- Let `X` be a smooth integral projective scheme over `ℂ`, `Y = X(ℂ)` with its analytic topology,
`S ⊆ Y` closed, and `V ⊆ Y` open. This additive equivalence identifies `H^n(Γ_S(V, C^•))` with
relative singular cohomology `H^n(V, V \ S; ℚ)`. -/
def complexSupportSingularSectionCohomologyEquiv (S : Closeds (ComplexPoint X))
    (V : Opens (ComplexPoint X)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportSingularComplex X S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n :=
  letI : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  supportedRationalSingularSectionCohomologyEquivSupportComplement
    (TopCat.of (ComplexPoint X)) S S.isClosed V n

end AlgebraicGeometry.ComplexPoint

end
