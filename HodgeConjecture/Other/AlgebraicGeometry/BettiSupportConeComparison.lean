/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic
public import HodgeConjecture.Other.AlgebraicGeometry.BettiSupportSingularComparison

/-!
# Betti support-cone comparison

The natural singular-cochain restriction strictly extends restriction of rational constants.
Consequently, replacement of the constant source by its natural singular resolution induces a
quasi-isomorphism between the associated support cones.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

local instance bettiSupportConeComparisonTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

local instance bettiSupportConeComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction through the natural singular resolution agrees strictly with restriction of
rational constants before extending the complexes to integer degrees. -/
lemma rationalToSingular_comp_naturalSingularResolutionRestrictionNat
    [SmoothOfRelativeDimension d structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    constantsToSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X structureMap)) ≫
        naturalSingularResolutionRestrictionNat structureMap d Z hZ =
      rationalRestrictionComplexNat structureMap Z := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      dsimp only [naturalSingularResolutionRestrictionNat]
      rw [HomologicalComplex.comp_f]
      unfold rationalRestrictionComplexNat
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      rw [show (constantsToSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X structureMap))).f 0 =
            constantsToSingularCochainZeroSheaf ℚ
              (TopCat.of (ComplexPoint X structureMap)) by
        rfl]
      change constantsToSingularCochainZeroSheaf ℚ
            (TopCat.of (ComplexPoint X structureMap)) ≫
          singularRestrictionSheaf ℚ
              (analyticComplementInclusion structureMap Z) 0 ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat
              (analyticComplementInclusion structureMap Z)).map
                ((complementSingularToInjectiveResolution structureMap d Z hZ).f 0)) = _
      rw [← Category.assoc,
        constantsToSingularCochainZeroSheaf_comp_singularRestriction structureMap Z,
        Category.assoc]
      rw [← Functor.map_comp]
      have hcomp := HomologicalComplex.congr_hom
        (complementConstants_comp_singularToInjectiveResolution
          structureMap d Z hZ) 0
      change constantsToSingularCochainZeroSheaf ℚ
          (TopCat.of (AnalyticComplement structureMap Z)) ≫
            (complementSingularToInjectiveResolution structureMap d Z hZ).f 0 =
          (complementConstantRationalInjectiveResolution structureMap Z).ι.f 0 at hcomp
      rw [hcomp]
      rfl
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (constantFieldSheaf ℚ structureMap) (n + 1) (by lia)).eq_of_src _ _

/-- Restriction through the integer-indexed natural singular resolution agrees strictly with
restriction of rational constants. -/
lemma rationalToSingular_comp_naturalSingularResolutionRestriction
    [SmoothOfRelativeDimension d structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    rationalToSingularCochainComplexInt structureMap ≫
        naturalSingularResolutionRestriction structureMap d Z hZ =
      rationalRestrictionComplexInt structureMap Z := by
  unfold rationalToSingularCochainComplexInt constantsToSingularCochainComplexInt
    naturalSingularResolutionRestriction rationalRestrictionComplexInt
  calc
    _ = HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex ℚ
            (TopCat.of (ComplexPoint X structureMap)) ≫
          naturalSingularResolutionRestrictionNat structureMap d Z hZ)
        ComplexShape.embeddingUpNat :=
      (HomologicalComplex.extendMap_comp _ _ ComplexShape.embeddingUpNat).symm
    _ = _ := congrArg
      (fun f ↦ HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
      (rationalToSingular_comp_naturalSingularResolutionRestrictionNat
        structureMap d Z hZ)

/-- Replacing rational constants by the natural singular-cochain resolution induces a map of
support cones. -/
def rationalSupportConeToNaturalSingularCone
    [SmoothOfRelativeDimension d structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplex structureMap Z ⟶
      CochainComplex.mappingCone
        (naturalSingularResolutionRestriction structureMap d Z hZ) :=
  CochainComplex.mappingCone.map
    (rationalRestrictionComplexInt structureMap Z)
    (naturalSingularResolutionRestriction structureMap d Z hZ)
    (rationalToSingularCochainComplexInt structureMap) (𝟙 _)
    (by rw [Category.comp_id,
      rationalToSingular_comp_naturalSingularResolutionRestriction structureMap d Z hZ])

/-- The natural singular-resolution replacement map between support cones is a
quasi-isomorphism. -/
noncomputable instance rationalSupportConeToNaturalSingularCone_quasiIso
    [SmoothOfRelativeDimension d structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToNaturalSingularCone structureMap d Z hZ) := by
  let _ : QuasiIso (rationalToSingularCochainComplexInt structureMap) :=
    rationalToSingularCochainComplexInt_quasiIso structureMap d
  change QuasiIso (CochainComplex.mappingCone.map
    (rationalRestrictionComplexInt structureMap Z)
    (naturalSingularResolutionRestriction structureMap d Z hZ)
    (rationalToSingularCochainComplexInt structureMap) (𝟙 _)
    (by rw [Category.comp_id,
      rationalToSingular_comp_naturalSingularResolutionRestriction structureMap d Z hZ]))
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso
    (rationalRestrictionComplexInt structureMap Z)
    (naturalSingularResolutionRestriction structureMap d Z hZ)
    (rationalToSingularCochainComplexInt structureMap) (𝟙 _) _

end AlgebraicGeometry.ComplexPoint
