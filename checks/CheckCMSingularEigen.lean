import Other.AlgebraicGeometry.HolomorphicDeRhamPullback
import Other.AlgebraicGeometry.ExplicitEllipticCMDeRhamEigen
import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsAdditivity
import Other.AlgebraicGeometry.PlainHypercohomologyGlobalSectionsNaturality
import Other.AlgebraicGeometry.SingularCochainMapNaturality

@[expose] noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint AlgebraicTopology

#check curveVarietyCMEnd
#check curveCMAnalyticMap
#check curveCMGlobalHolomorphicDifferential_eq_i_smul
#check holomorphicFormPullback_algebraicFormToHolomorphicForm
#check plainHypercohomologyEquivGlobalSections_naturality
#check complexSingularCochainHypercohomologyEquivGlobalSections
#check complexSingularCochainHypercohomologyEquivCohomology
#check ComplexPoint.constantsToHolomorphicDeRhamComplexInt_naturality
#check Singular.constantsToSingularCochainSheafComplexInt_naturality

set_option pp.universes false in
#check holomorphicFormPullbackSheaf

set_option backward.isDefEq.respectTransparency false in
example :
    (holomorphicFormPullbackSheaf curveVariety curveVariety
      curveVarietyCMEnd 1 1 1).hom.app (.op ⊤)
        curveGlobalHolomorphicDifferential =
      curveCMGlobalHolomorphicDifferential := by
  sorry

example (X : Over (Spec (.of ℂ)))
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    complexSingularCochainHypercohomologyEquivGlobalSections X n =
      hypercohomologyEquivGlobalSections X
        (singularCochainSheafComplexInt X ℂ) 0
        (complexSingularCochainSheafComplexInt_isFlasque X) n := by
  rfl

end AlgebraicGeometry.ExplicitEllipticCandidate
