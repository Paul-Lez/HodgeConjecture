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

The rational support object resolves constants on the complement
independently of the ambient space. This file connects that model with the
restriction of an ambient injective resolution. All comparison maps extend the given constant
restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- Let `X` be a scheme over `ℂ`. This is the complex `I^•` of sheaves of abelian groups in a chosen
injective resolution `ℚ → I^•` on the analytic space `X(ℂ)`. It is indexed by integers and is
zero in negative degrees. -/
def ambientRationalInjectiveComplex :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  -- An injective resolution `ℚ_{X(ℂ)} → I^•`.
  (TopCat.Sheaf.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)).cocomplex.extend
      ComplexShape.embeddingUpNat

/-- Let `X` be a scheme over `ℂ`. This is the augmentation `ℚ[0] → I^•` of the chosen injective
resolution of the constant rational sheaf on the analytic space `X(ℂ)`, with both complexes
indexed by integers. -/
def ambientRationalInjectiveAugmentation :
    constantFieldSheafComplexInt ℚ X ⟶
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

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

end AlgebraicGeometry.ComplexPoint
