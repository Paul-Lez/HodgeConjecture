/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.FilteredSupportLocalizationBoundary
public import Other.AlgebraicGeometry.DerivedSupportRationalConeComparison

/-!
# The filtered-to-full map on fixed supported injective models

The filtered and full holomorphic de Rham complexes are replaced by the same
coefficient-natural choice of injective model.  Applying the literal
sections-with-support kernel termwise gives a strict map of sheaf complexes.
This is the map whose local cohomology sheaves receive the normal-coordinate
residue classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance filteredSupportInjectiveComparisonSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance filteredSupportInjectiveComparisonGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

local instance holomorphicDeRhamComplexInt_isStrictlyGE_zero :
    (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
  unfold holomorphicDeRhamComplexInt
  infer_instance

local instance ambientRationalInjectiveAugmentation_mono :
    Mono (ambientRationalInjectiveAugmentation X) := by
  let I := TopCat.Sheaf.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)
  letI : Mono I.ι := HomologicalComplex.mono_of_mono_f I.ι (fun _ ↦ inferInstance)
  exact CochainComplex.mono_extendMap_nat I.ι

/-- The fixed termwise-injective model of the full holomorphic de Rham
complex. -/
abbrev deRhamInjectiveComplex :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  globalHypercohomologyInjectiveComplex X (holomorphicDeRhamComplexInt X)

/-- The strict lift of filtration inclusion between the fixed injective
models. -/
abbrev filteredDeRhamInjectiveToDeRham (p : ℕ) :
    filteredDeRhamInjectiveComplex X p ⟶ deRhamInjectiveComplex X :=
  globalHypercohomologyInjectiveMapMap X
    (hodgeFilteredDeRhamInclusion X (p : ℤ))

/-- The normalized rational-to-de Rham coefficient morphism, lifted strictly
from the repository's ambient rational injective resolution to the fixed full
de Rham injective model. -/
def rationalInjectiveToDeRham :
    ambientRationalInjectiveComplex X ⟶ deRhamInjectiveComplex X := by
  letI : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE (-1) := by
    letI : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
      unfold constantFieldSheafComplexInt
      infer_instance
    exact (constantFieldSheafComplexInt ℚ X).isStrictlyGE_of_ge (-1) 0 (by omega)
  letI : (ambientRationalInjectiveComplex X).IsStrictlyGE (-1) :=
    (ambientRationalInjectiveComplex X).isStrictlyGE_of_ge (-1) 0 (by omega)
  exact CochainComplex.liftToInjectiveAt (-1)
    (ambientRationalInjectiveAugmentation X)
    (fieldToHolomorphicDeRhamComplexInt ℚ X ≫
      globalHypercohomologyInjectiveMap X (holomorphicDeRhamComplexInt X))
    (fun _ ↦ inferInstance)

/-- The rational injective comparison is normalized by the actual
rational-to-holomorphic-de Rham coefficient map. -/
@[reassoc (attr := simp)]
theorem ambientRationalInjectiveAugmentation_comp_toDeRham :
    ambientRationalInjectiveAugmentation X ≫ rationalInjectiveToDeRham X =
      fieldToHolomorphicDeRhamComplexInt ℚ X ≫
        globalHypercohomologyInjectiveMap X (holomorphicDeRhamComplexInt X) := by
  letI : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE (-1) := by
    letI : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
      unfold constantFieldSheafComplexInt
      infer_instance
    exact (constantFieldSheafComplexInt ℚ X).isStrictlyGE_of_ge (-1) 0 (by omega)
  letI : (ambientRationalInjectiveComplex X).IsStrictlyGE (-1) :=
    (ambientRationalInjectiveComplex X).isStrictlyGE_of_ge (-1) 0 (by omega)
  exact CochainComplex.comp_liftToInjectiveAt (-1)
    (ambientRationalInjectiveAugmentation X)
    (fieldToHolomorphicDeRhamComplexInt ℚ X ≫
      globalHypercohomologyInjectiveMap X (holomorphicDeRhamComplexInt X))
    (fun _ ↦ inferInstance)

/-- The sheaf complex of sections of the fixed filtered injective model with
support in `Z`. -/
abbrev filteredDeRhamSupportInjectiveComplex
    (Z : Closeds (ComplexPoint X)) (p : ℕ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((TopCat.Sheaf.sheafSectionsWithClosedSupport
    (TopCat.of (ComplexPoint X)) Z).mapHomologicalComplex (.up ℤ)).obj
      (filteredDeRhamInjectiveComplex X p)

/-- The sheaf complex of sections of the fixed full de Rham injective model
with support in `Z`. -/
abbrev deRhamSupportInjectiveComplex
    (Z : Closeds (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((TopCat.Sheaf.sheafSectionsWithClosedSupport
    (TopCat.of (ComplexPoint X)) Z).mapHomologicalComplex (.up ℤ)).obj
      (deRhamInjectiveComplex X)

/-- The sheaf complex of sections of the ambient rational injective
resolution with support in `Z`. -/
abbrev rationalSupportInjectiveComplex
    (Z : Closeds (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((TopCat.Sheaf.sheafSectionsWithClosedSupport
    (TopCat.of (ComplexPoint X)) Z).mapHomologicalComplex (.up ℤ)).obj
      (ambientRationalInjectiveComplex X)

/-- Filtration inclusion on the literal sheaf complexes with support. -/
def filteredSupportInjectiveToDeRham
    (Z : Closeds (ComplexPoint X)) (p : ℕ) :
    filteredDeRhamSupportInjectiveComplex X Z p ⟶
      deRhamSupportInjectiveComplex X Z :=
  ((TopCat.Sheaf.sheafSectionsWithClosedSupport
    (TopCat.of (ComplexPoint X)) Z).mapHomologicalComplex (.up ℤ)).map
      (filteredDeRhamInjectiveToDeRham X p)

/-- Rational coefficient comparison on the literal sheaf complexes with
support. -/
def rationalSupportInjectiveToDeRham
    (Z : Closeds (ComplexPoint X)) :
    rationalSupportInjectiveComplex X Z ⟶
      deRhamSupportInjectiveComplex X Z :=
  ((TopCat.Sheaf.sheafSectionsWithClosedSupport
    (TopCat.of (ComplexPoint X)) Z).mapHomologicalComplex (.up ℤ)).map
      (rationalInjectiveToDeRham X)

/-- The coefficient augmentation commutes strictly with the lifted
filtered-to-full map before taking support. -/
@[reassoc (attr := simp)]
theorem filteredDeRhamInjectiveMap_comp_toDeRham (p : ℕ) :
    globalHypercohomologyInjectiveMap X
        (hodgeFilteredDeRhamComplex X (p : ℤ)) ≫
      filteredDeRhamInjectiveToDeRham X p =
    hodgeFilteredDeRhamInclusion X (p : ℤ) ≫
      globalHypercohomologyInjectiveMap X
        (holomorphicDeRhamComplexInt X) :=
  globalHypercohomologyInjectiveMap_comp_map X
    (hodgeFilteredDeRhamInclusion X (p : ℤ))

/-- The local cohomology-sheaf map induced by filtration inclusion. -/
abbrev filteredSupportInjectiveCohomologySheafToDeRham
    (Z : Closeds (ComplexPoint X)) (p : ℕ) (n : ℤ) :
    (filteredDeRhamSupportInjectiveComplex X Z p).homology n ⟶
      (deRhamSupportInjectiveComplex X Z).homology n :=
  HomologicalComplex.homologyMap
    (filteredSupportInjectiveToDeRham X Z p) n

/-- The normalized rational-to-de Rham map on local supported cohomology
sheaves. -/
abbrev rationalSupportInjectiveCohomologySheafToDeRham
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    (rationalSupportInjectiveComplex X Z).homology n ⟶
      (deRhamSupportInjectiveComplex X Z).homology n :=
  HomologicalComplex.homologyMap
    (rationalSupportInjectiveToDeRham X Z) n

/-- The map on sections over an open set, obtained from the same strict
supported coefficient map. -/
abbrev filteredSupportInjectiveSectionToDeRham
    (Z : Closeds (ComplexPoint X)) (p : ℕ)
    (U : Opens (ComplexPoint X)) :
    ((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
        (filteredDeRhamSupportInjectiveComplex X Z p) ⟶
    ((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
        (deRhamSupportInjectiveComplex X Z) :=
  ((TopCat.Sheaf.supportEvaluation
    (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).map
      (filteredSupportInjectiveToDeRham X Z p)

end AlgebraicGeometry.ComplexPoint
