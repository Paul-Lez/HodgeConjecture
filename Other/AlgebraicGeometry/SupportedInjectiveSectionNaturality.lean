/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.DivisorClassComparisonSupport
public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SectionRestrictionCone

/-! # Naturality of supported injective local sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance supportedInjectiveSectionNaturalityTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable {X}

@[reassoc]
lemma sectionComplexRestriction_comp_supportedInjectiveComplexMap
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (V : Opens (ComplexPoint X)) :
    TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
        (complexSupportInjectiveComplex X S) (homOfLE (show V ≤ ⊤ from le_top)) ≫
      (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
        (.up ℤ)).map (supportedInjectiveComplexMap X h)) =
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (supportedInjectiveComplexMap X h)) ≫
      TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
        (complexSupportInjectiveComplex X T) (homOfLE (show V ≤ ⊤ from le_top)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((complexSupportInjectiveComplex X S).X n).obj.map
      (homOfLE (show V ≤ ⊤ from le_top)).op ≫
      ((supportedInjectiveComplexMap X h).f n).hom.app (op V) =
    ((supportedInjectiveComplexMap X h).f n).hom.app (op ⊤) ≫
      ((complexSupportInjectiveComplex X T).X n).obj.map
        (homOfLE (show V ≤ ⊤ from le_top)).op
  exact ((supportedInjectiveComplexMap X h).f n).hom.naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op

@[reassoc]
lemma supportedInjectiveComplexMap_sectionCohomologyToSheafSection
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ) (V : Opens (ComplexPoint X)) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
          (.up ℤ)).map (supportedInjectiveComplexMap X h)) n ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X T) n V =
    TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) n V ≫
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X h) n).hom.app (op V) :=
  TopCat.Sheaf.sectionCohomologyToSheafSection_naturality (TopCat.of (ComplexPoint X))
    (supportedInjectiveComplexMap X h) n V

lemma supportedInjectiveComplexMap_section_apply
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ) (V : Opens (ComplexPoint X))
    (a : ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X S))).homology n) :
    (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X T) n V)
      (HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
          (.up ℤ)).map (supportedInjectiveComplexMap X h)) n a) =
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X h) n).hom.app (op V)
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) n V a) := by
  exact ConcreteCategory.congr_hom
    (supportedInjectiveComplexMap_sectionCohomologyToSheafSection (X := X) h n V) a

end AlgebraicGeometry.ComplexPoint
