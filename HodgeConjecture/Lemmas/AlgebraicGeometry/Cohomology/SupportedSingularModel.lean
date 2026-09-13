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

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom]

/-- The actual singular-to-injective resolution map, using proved local
contractibility of the analytic space. -/
def complexSingularToAmbientInjective :
    rationalSingularCochainComplex (TopCat.of (ComplexPoint X)) ⟶
      ambientRationalInjectiveComplex X :=
  singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X)

instance complexSingularToAmbientInjective_quasiIso :
    QuasiIso (complexSingularToAmbientInjective X) :=
  singularToConstantInjectiveComplex_quasiIso _ _

variable [IsProjective X.hom]

/-- Local supported singular cohomology and the literal supported injective
model are canonically isomorphic in every integer degree. -/
def complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (ComplexPoint X)) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
            (ambientRationalInjectiveComplex X)))).homology n := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W :=
    openParacompactSpace X
  exact supportedSingularInjectiveHomologyIso (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X) U V n

end AlgebraicGeometry.ComplexPoint

end

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
