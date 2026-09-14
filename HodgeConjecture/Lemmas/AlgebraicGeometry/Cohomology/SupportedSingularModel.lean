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

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- The actual singular-to-injective resolution map, using proved local
contractibility of the analytic space. -/
def complexSingularToAmbientInjective :
    rationalSingularCochainComplex (TopCat.of (Point ℂ X)) ⟶
      ambientRationalInjectiveComplex X :=
  singularToConstantInjectiveComplex (TopCat.of (Point ℂ X))
    (exists_contractibleOpen_le X)

instance complexSingularToAmbientInjective_quasiIso :
    QuasiIso (complexSingularToAmbientInjective X) :=
  singularToConstantInjectiveComplex_quasiIso _ _

variable [IsProjective X.hom]

/-- Local supported singular cohomology and the literal supported injective
model are canonically isomorphic in every integer degree. -/
def complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (Point ℂ X)) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (Point ℂ X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (supportedRationalSingularCochainComplex (TopCat.of (Point ℂ X)) U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (Point ℂ X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (Point ℂ X)) U).mapHomologicalComplex (.up ℤ)).obj
            (ambientRationalInjectiveComplex X)))).homology n :=
  letI : ∀ W : Opens (Point ℂ X), ParacompactSpace W :=
    openParacompactSpace X
  supportedSingularInjectiveHomologyIso (TopCat.of (Point ℂ X))
    (exists_contractibleOpen_le X) U V n

end AlgebraicGeometry.ComplexPoint

end
