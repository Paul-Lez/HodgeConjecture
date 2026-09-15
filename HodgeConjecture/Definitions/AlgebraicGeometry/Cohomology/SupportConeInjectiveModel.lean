/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenInjectiveResolution
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.HypercohomologyNaturality
/-!
# Normalized injective models for the rational support cone

The existing rational support object resolves constants on the complement
independently of the ambient space. This file connects that model with the
actual restriction of an ambient injective resolution. All comparison maps
extend the given constant restriction, rather than choosing an abstract
equivalence between cohomology groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The standard ambient rational injective resolution in integer degrees. -/
def ambientRationalInjectiveComplex :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (TopCat.Sheaf.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).cocomplex.extend
      ComplexShape.embeddingUpNat

/-- Its actual constant augmentation. -/
def ambientRationalInjectiveAugmentation :
    (constantFieldSheafComplexIntPlus ℚ X).obj ⟶
      ambientRationalInjectiveComplex X :=
  HomologicalComplex.extendMap
    (TopCat.Sheaf.ambientConstantInjectiveResolution
      (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).ι
    ComplexShape.embeddingUpNat

instance ambientRationalInjectiveAugmentation_quasiIso :
    QuasiIso (ambientRationalInjectiveAugmentation X) := by
  let I := TopCat.Sheaf.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)
  let : QuasiIso I.ι := I.quasiIso
  exact (HomologicalComplex.quasiIso_extendMap_iff I.ι _).mpr inferInstance

instance ambientRationalInjectiveComplex_injective (q : ℤ) :
    Injective ((ambientRationalInjectiveComplex X).X q) :=
  CochainComplex.injective_extend_nat _
    (TopCat.Sheaf.ambientConstantInjectiveResolution
      (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).injective q

instance ambientRationalInjectiveComplex_isStrictlyGE :
    (ambientRationalInjectiveComplex X).IsStrictlyGE 0 := by
  dsimp only [ambientRationalInjectiveComplex]
  infer_instance

/-- The ambient rational injective resolution as a bounded-below complex. -/
abbrev ambientRationalInjectiveComplexPlus :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨ambientRationalInjectiveComplex X,
    ⟨0, ambientRationalInjectiveComplex_isStrictlyGE X⟩⟩

/-- The rational constant-sheaf augmentation as a map of bounded-below complexes. -/
def ambientRationalInjectiveAugmentationPlus :
    constantFieldSheafComplexIntPlus ℚ X ⟶ ambientRationalInjectiveComplexPlus X :=
  ⟨ambientRationalInjectiveAugmentation X⟩

instance ambientRationalInjectiveComplexPlus_isKInjective :
    (ambientRationalInjectiveComplexPlus X).obj.IsKInjective := by
  change (ambientRationalInjectiveComplex X).IsKInjective
  exact CochainComplex.isKInjective_of_injective (ambientRationalInjectiveComplex X) 0

instance ambientRationalInjectiveAugmentationPlus_quasiIso :
    QuasiIso (ambientRationalInjectiveAugmentationPlus X).hom := by
  change QuasiIso (ambientRationalInjectiveAugmentation X)
  infer_instance

end AlgebraicGeometry.ComplexPoint
