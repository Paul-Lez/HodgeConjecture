/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularFlasqueModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-!
# Supported singular models on smooth projective complex varieties

The generic supported singular/injective comparison is specialized using the
constructed analytic contractible neighborhoods and hereditary paracompactness
of smooth projective analytifications. Only the geometric scheme hypotheses
remain: no purity, fundamental class, or comparison equivalence is an input.
The target is literally the ambient injective complex used by the derived
rational support comparison.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom]

/-- Its actual supported version for any open complement, not just a smooth support. -/
def complexSupportedSingularToAmbientInjective
    (U : Opens (ComplexPoint X)) :
    supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) U ⟶
      ((TopCat.Sheaf.sheafSectionsSupportedOutside
        (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
          (ambientRationalInjectiveComplex X) :=
  supportedSingularToInjectiveComplex (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X) U

variable [IsProjective X.hom]

/-- The constructed supported comparison is a sheaf quasi-isomorphism under
the usual smooth projective geometry hypotheses alone. -/
instance complexSupportedSingularToAmbientInjective_quasiIso
    (U : Opens (ComplexPoint X)) :
    QuasiIso (complexSupportedSingularToAmbientInjective X U) := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V :=
    openParacompactSpace X
  exact supportedSingularToInjectiveComplex_quasiIso
    (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X) U

end AlgebraicGeometry.ComplexPoint
