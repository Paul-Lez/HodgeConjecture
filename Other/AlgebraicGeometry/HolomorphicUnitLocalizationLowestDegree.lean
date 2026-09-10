/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticDerivedSupportLocalizationExact
public import Other.AlgebraicGeometry.SupportedHolomorphicUnitLocalization
public import Other.AlgebraicTopology.LowestFlasqueCohomology
public import Other.AlgebraicTopology.CohomologySheafSectionNaturality
public import Other.AlgebraicTopology.CohomologySheafSectionRestriction
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Lowest-degree normalization for localization of holomorphic units

The fixed injective model of the units complex has its first section
cohomology canonically identified with actual holomorphic units on every open.
The identification commutes with restriction.  This turns exactness of the
derived-support localization sequence into an extension criterion for units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance holomorphicUnitLocalizationLowestSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance holomorphicUnitLocalizationLowestGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

local instance holomorphicUnitsComplexInt_isStrictlyGE_zero_lowestLocalization :
    (holomorphicUnitsComplexInt X).IsStrictlyGE 0 :=
  (holomorphicUnitsComplexInt X).isStrictlyGE_of_ge 0 1 (by omega)

/-- The degree-one cohomology sheaf of the single units complex is the units
sheaf itself. -/
def holomorphicUnitsComplexIntHomologyOneIso :
    (holomorphicUnitsComplexInt X).homology 1 ≅
      holomorphicUnitsSheaf X (dim X.left) := by
  unfold holomorphicUnitsComplexInt
  exact HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 1 _

/-- The degree-one cohomology sheaf of the fixed injective replacement is the
actual sheaf of holomorphic units. -/
def holomorphicUnitsInjectiveCohomologySheafIso :
    (globalHypercohomologyInjectiveComplex X
        (holomorphicUnitsComplexInt X)).homology 1 ≅
      holomorphicUnitsSheaf X (dim X.left) :=
  (asIso (HomologicalComplex.homologyMap
    (globalHypercohomologyInjectiveMap X (holomorphicUnitsComplexInt X)) 1)).symm ≪≫
      holomorphicUnitsComplexIntHomologyOneIso X

/-- The injective replacement has no cohomology sheaves below the degree in
which the units sheaf is placed. -/
theorem holomorphicUnitsInjectiveCohomology_isZero_below_one
    (j : ℤ) (hj : j < 1) :
    IsZero ((globalHypercohomologyInjectiveComplex X
      (holomorphicUnitsComplexInt X)).homology j) := by
  have hsource : IsZero ((holomorphicUnitsComplexInt X).homology j) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      ((holomorphicUnitsComplexInt X).isZero_of_isStrictlyGE 1 j hj)
  exact hsource.of_iso (asIso (HomologicalComplex.homologyMap
    (globalHypercohomologyInjectiveMap X (holomorphicUnitsComplexInt X)) j)).symm

/-- First cohomology of sections of the fixed units injective model on `U` is
canonically the group of actual holomorphic units on `U`. -/
def holomorphicUnitsInjectiveSectionCohomologyIso
    (U : Opens (TopCat.of (ComplexPoint X))) :
    (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
        (globalHypercohomologyInjectiveComplex X
          (holomorphicUnitsComplexInt X))).homology 1 ≅
      (holomorphicUnitsSheaf X (dim X.left)).obj.obj (.op U) :=
  TopCat.Sheaf.lowestSectionCohomologyIso
      (TopCat.of (ComplexPoint X))
      (globalHypercohomologyInjectiveComplex X
        (holomorphicUnitsComplexInt X)) (-1) 1
      (holomorphicUnitsInjectiveCohomology_isZero_below_one X)
      (fun _ ↦ TopCat.Sheaf.injective_isFlasque _ _) U ≪≫
    (TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) U).mapIso
        (holomorphicUnitsInjectiveCohomologySheafIso X)

/-- The preceding first-cohomology identification commutes with literal
restriction of opens. -/
theorem holomorphicUnitsInjectiveSectionCohomologyIso_restriction
    {U V : Opens (TopCat.of (ComplexPoint X))} (a : U ⟶ V) :
    HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction
          (TopCat.of (ComplexPoint X)) (.up ℤ)
          (globalHypercohomologyInjectiveComplex X
            (holomorphicUnitsComplexInt X)) a) 1 ≫
      (holomorphicUnitsInjectiveSectionCohomologyIso X U).hom =
    (holomorphicUnitsInjectiveSectionCohomologyIso X V).hom ≫
      (holomorphicUnitsSheaf X (dim X.left)).obj.map a.op := by
  unfold holomorphicUnitsInjectiveSectionCohomologyIso
  simp only [Iso.trans_hom, TopCat.Sheaf.lowestSectionCohomologyIso_hom,
    Category.assoc]
  rw [TopCat.Sheaf.sectionCohomologyToSheafSection_restriction_assoc]
  simp only [Functor.mapIso_hom, Category.assoc]
  congr 1
  exact (holomorphicUnitsInjectiveCohomologySheafIso X).hom.hom.naturality a.op

end AlgebraicGeometry.ComplexPoint
