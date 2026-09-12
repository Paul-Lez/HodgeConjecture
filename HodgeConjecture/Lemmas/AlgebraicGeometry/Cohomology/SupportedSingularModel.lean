/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel

/-!
# Supported singular models on smooth projective complex varieties

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom]

variable [IsProjective X.hom]

/-- The same comparison computes supported cohomology on every actual analytic
open, with no locally supplied comparison or acyclicity input. -/
theorem complexSupportedSingularToAmbientInjective_onOpen_quasiIso
    (U V : Opens (ComplexPoint X)) :
    QuasiIso (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex (.up ℤ)).map
        (complexSupportedSingularToAmbientInjective X U)) := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W :=
    openParacompactSpace X
  exact supportedSingularToInjectiveComplex_onOpen_quasiIso
    (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X) U V

end AlgebraicGeometry.ComplexPoint
