/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
public import Other.AlgebraicGeometry.DivisorClassComparisonSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance supportSingularTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-- The pair map induced by enlarging a support, on one ambient open. -/
def neighborhoodSupportSupportInclusionPairMap
    {S T : Set (ComplexPoint X)} (hST : S ⊆ T) (V : Opens (ComplexPoint X)) :
    neighborhoodSupportComplementPair (V : Set (ComplexPoint X)) T ⟶
      neighborhoodSupportComplementPair (V : Set (ComplexPoint X)) S :=
  supportInclusionPairMap (TopCat.of V)
    (show {w : V | (w : ComplexPoint X) ∈ S} ⊆ {w : V | (w : ComplexPoint X) ∈ T} from
      fun _w hw => hST hw)

/-- The supported singular cochain map induced by enlarging a closed support. -/
def supportedSingularComplexMap
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T) :
    supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl ⟶
      supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) T.compl :=
  (NatTrans.mapHomologicalComplex
    (TopCat.Sheaf.sheafSectionsSupportedOutsideMap (TopCat.of (ComplexPoint X))
      (show T.compl ≤ S.compl from fun _ hzS hzT => hzS (hST hzT))) ℤᵘᵖ).app
    (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))

omit [IsProjective X.hom] in
/-- The singular comparison map commutes with support enlargement. -/
theorem supportedSingularComplexMap_comp
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T) :
    supportedSingularComplexMap X hST ≫ complexSupportedSingularToAmbientInjective X T.compl =
      complexSupportedSingularToAmbientInjective X S.compl ≫ supportedInjectiveComplexMap X hST := by
  change
    (NatTrans.mapHomologicalComplex
      (TopCat.Sheaf.sheafSectionsSupportedOutsideMap (TopCat.of (ComplexPoint X))
        (show T.compl ≤ S.compl from fun _ hzS hzT => hzS (hST hzT))) ℤᵘᵖ).app
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X))) ≫
        ((TopCat.Sheaf.sheafSectionsSupportedOutside (TopCat.of (ComplexPoint X)) T.compl).mapHomologicalComplex
          ℤᵘᵖ).map (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
            (exists_contractibleOpen_le X)) =
      ((TopCat.Sheaf.sheafSectionsSupportedOutside (TopCat.of (ComplexPoint X)) S.compl).mapHomologicalComplex
          ℤᵘᵖ).map (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
            (exists_contractibleOpen_le X)) ≫
        (NatTrans.mapHomologicalComplex
          (TopCat.Sheaf.sheafSectionsSupportedOutsideMap (TopCat.of (ComplexPoint X))
            (show T.compl ≤ S.compl from fun _ hzS hzT => hzS (hST hzT))) ℤᵘᵖ).app
          (rationalConstantInjectiveComplex (TopCat.of (ComplexPoint X)))
  exact ((NatTrans.mapHomologicalComplex
      (TopCat.Sheaf.sheafSectionsSupportedOutsideMap (TopCat.of (ComplexPoint X))
        (show T.compl ≤ S.compl from fun _ hzS hzT => hzS (hST hzT))) ℤᵘᵖ).naturality
      (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
        (exists_contractibleOpen_le X))).symm

end AlgebraicGeometry.ComplexPoint
