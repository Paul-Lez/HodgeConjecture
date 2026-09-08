/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.SingularFlasqueSupportModel
public import HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact

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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth structureMap]

/-- The actual singular-to-injective resolution map, using proved local
contractibility of the analytic space. -/
def complexSingularToAmbientInjective :
    rationalSingularCochainComplex (TopCat.of (ComplexPoint X structureMap)) ⟶
      ambientRationalInjectiveComplex structureMap :=
  singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X structureMap))
    (exists_contractibleOpen_le structureMap)

instance complexSingularToAmbientInjective_quasiIso :
    QuasiIso (complexSingularToAmbientInjective structureMap) :=
  singularToConstantInjectiveComplex_quasiIso _ _

/-- Its actual supported version for any open complement, not just a smooth support. -/
def complexSupportedSingularToAmbientInjective
    (U : Opens (ComplexPoint X structureMap)) :
    supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X structureMap)) U ⟶
      ((TopCat.Sheaf.sheafSectionsSupportedOutside
        (TopCat.of (ComplexPoint X structureMap)) U).mapHomologicalComplex (.up ℤ)).obj
          (ambientRationalInjectiveComplex structureMap) :=
  supportedSingularToInjectiveComplex (TopCat.of (ComplexPoint X structureMap))
    (exists_contractibleOpen_le structureMap) U

variable [IsProjective structureMap]

/-- The constructed supported comparison is a sheaf quasi-isomorphism under
the usual smooth projective geometry hypotheses alone. -/
instance complexSupportedSingularToAmbientInjective_quasiIso
    (U : Opens (ComplexPoint X structureMap)) :
    QuasiIso (complexSupportedSingularToAmbientInjective structureMap U) := by
  let : ∀ V : Opens (ComplexPoint X structureMap), ParacompactSpace V :=
    openParacompactSpace structureMap
  exact supportedSingularToInjectiveComplex_quasiIso
    (TopCat.of (ComplexPoint X structureMap)) (exists_contractibleOpen_le structureMap) U

/-- The same comparison computes supported cohomology on every actual analytic
open, with no locally supplied comparison or acyclicity input. -/
theorem complexSupportedSingularToAmbientInjective_onOpen_quasiIso
    (U V : Opens (ComplexPoint X structureMap)) :
    QuasiIso (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X structureMap)) V).mapHomologicalComplex (.up ℤ)).map
        (complexSupportedSingularToAmbientInjective structureMap U)) := by
  let : ∀ W : Opens (ComplexPoint X structureMap), ParacompactSpace W :=
    openParacompactSpace structureMap
  exact supportedSingularToInjectiveComplex_onOpen_quasiIso
    (TopCat.of (ComplexPoint X structureMap)) (exists_contractibleOpen_le structureMap) U V

/-- Local supported singular cohomology and the literal supported injective
model are canonically isomorphic in every integer degree. -/
def complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (ComplexPoint X structureMap)) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X structureMap)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X structureMap)) U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X structureMap)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (ComplexPoint X structureMap)) U).mapHomologicalComplex (.up ℤ)).obj
            (ambientRationalInjectiveComplex structureMap)))).homology n := by
  let : ∀ W : Opens (ComplexPoint X structureMap), ParacompactSpace W :=
    openParacompactSpace structureMap
  exact supportedSingularInjectiveHomologyIso (TopCat.of (ComplexPoint X structureMap))
    (exists_contractibleOpen_le structureMap) U V n

end AlgebraicGeometry.ComplexPoint
