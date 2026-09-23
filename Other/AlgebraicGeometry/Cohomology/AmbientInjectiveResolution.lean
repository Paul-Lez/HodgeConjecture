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

public import Other.AlgebraicTopology.Sheaf.OpenInjectiveResolution
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# The chosen injective resolution of the constant rational sheaf

`ℚ → I^•` is a chosen injective resolution of the constant rational sheaf on the analytic space
`X(ℂ)`, indexed by integers. It is K-injective.
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

/-- The augmentation `ℚ[0] → I^•`, with the source the constant sheaf placed in degree zero. -/
def ambientRationalInjectiveSingleAugmentation :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); ℚ) ⟶
      ambientRationalInjectiveComplex X :=
  (constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ ambientRationalInjectiveAugmentation X

instance ambientRationalInjectiveSingleAugmentation_quasiIso :
    QuasiIso (ambientRationalInjectiveSingleAugmentation X) := by
  dsimp only [ambientRationalInjectiveSingleAugmentation]
  infer_instance


end AlgebraicGeometry.ComplexPoint

end
