import Other.AlgebraicGeometry.ComplexSingularCohomologyMapNaturality
import Other.AlgebraicGeometry.HolomorphicDeRhamPullback
import Other.AlgebraicGeometry.ExplicitEllipticCMTopology
import Other.AlgebraicTopology.ClosedEmbeddingSheafExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Other.AlgebraicTopology.SheafPushforwardHomeomorphism

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

#check @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso

local instance curveCMAnalyticMap_isIso_check : IsIso curveCMAnalyticMap := by
  apply IsIso.mk
  refine ⟨curveCMAnalyticMap ≫ curveCMAnalyticMap ≫ curveCMAnalyticMap, ?_, ?_⟩
  · simpa only [Category.assoc] using curveCMAnalyticMap_four
  · simpa only [Category.assoc] using curveCMAnalyticMap_four

lemma curveCMAnalyticMap_isClosedEmbedding_check :
    IsClosedEmbedding curveCMAnalyticMap := by
  exact (TopCat.homeoOfIso (asIso curveCMAnalyticMap)).isClosedEmbedding

#synth (TopCat.Sheaf.pushforward AddCommGrpCat curveCMAnalyticMap).IsRightAdjoint

local instance curveCMPushforward_isEquivalence_check :
    (TopCat.Sheaf.pushforward AddCommGrpCat curveCMAnalyticMap).IsEquivalence :=
  TopCat.Sheaf.pushforward_isEquivalence_of_iso AddCommGrpCat
    (asIso curveCMAnalyticMap)

#synth (TopCat.Sheaf.pushforward AddCommGrpCat curveCMAnalyticMap).PreservesInjectiveObjects

example : QuasiIso
  (((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticMapTopCat curveVariety curveVariety curveVarietyCMEnd)
    ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (constantsToHolomorphicDeRhamComplexInt curveVariety)) := by
  letI : QuasiIso (constantsToHolomorphicDeRhamComplexInt curveVariety) :=
    constantsToHolomorphicDeRhamComplexInt_quasiIso curveVariety
  have _hcheck : QuasiIso (constantsToHolomorphicDeRhamComplexInt curveVariety) :=
    inferInstance
  exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
    _ _ curveCMAnalyticMap curveCMAnalyticMap_isClosedEmbedding_check
    ℤ (ComplexShape.up ℤ) _ _
    (constantsToHolomorphicDeRhamComplexInt curveVariety) _hcheck

example : QuasiIso
  (((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticMapTopCat curveVariety curveVariety curveVarietyCMEnd)
    ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (complexToSingularCochainComplexInt curveVariety)) := by
  letI : QuasiIso (complexToSingularCochainComplexInt curveVariety) :=
    complexToSingularCochainComplexInt_quasiIso curveVariety
  have _hcheck : QuasiIso (complexToSingularCochainComplexInt curveVariety) :=
    inferInstance
  exact @TopCat.Sheaf.closedEmbeddingPushforward_map_quasiIso
    _ _ curveCMAnalyticMap curveCMAnalyticMap_isClosedEmbedding_check
    ℤ (ComplexShape.up ℤ) _ _
    (complexToSingularCochainComplexInt curveVariety) _hcheck

end AlgebraicGeometry.ExplicitEllipticCandidate
