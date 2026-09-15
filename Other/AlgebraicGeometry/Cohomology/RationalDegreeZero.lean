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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Other.AlgebraicTopology.Sheaf.ConstantDegreeZero
public import Other.AlgebraicGeometry.Cohomology.SupportConeForget
public import Other.AlgebraicGeometry.Hodge.Filtration

/-!
# Degree-zero rational constant-sheaf cohomology

This file identifies degree-zero rational constant-sheaf cohomology with morphisms from the
constant integer sheaf to the constant rational sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance rationalDegreeZeroHasDerivedCategoryAddCommGrpCat :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

local instance rationalDegreeZeroHasDerivedCategorySheaf :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Degree-zero rational cohomology is the morphism group from the constant integer sheaf to
the constant rational sheaf. -/
def rationalCohomologyZeroEquivSheafHom :
    H^0(X; ℚ) ≃+ (𝓒(↧(ComplexPoint X); ℤ) ⟶ 𝓒(↧(ComplexPoint X); ℚ)) :=
  let I := ambientRationalInjectiveComplexPlus X
  let eTarget : DerivedCategory.Q.obj I.obj ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) 0).obj
          𝓒(↧(ComplexPoint X); ℚ)) :=
    (asIso (DerivedCategory.Q.map
      (ambientRationalInjectiveAugmentationPlus X).hom)).symm ≪≫
      DerivedCategory.Q.mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          𝓒(↧(ComplexPoint X); ℚ) 0 0 rfl)
  let e₁ := rationalCohomologyAddEquivAmbientInjectiveHomology X 0
  let e₂ := (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective
    (TopCat.of (ComplexPoint X)) I.obj 0).symm
  let e₃ := isoHomCongrAddEquiv (Iso.refl _)
    ((shiftFunctor _ (0 : ℤ)).mapIso eTarget)
  e₁.trans <| e₂.trans <| e₃.trans <|
    (Abelian.Ext.homAddEquiv (X := 𝓒(↧(ComplexPoint X); ℤ))
      (Y := 𝓒(↧(ComplexPoint X); ℚ))).symm.trans Abelian.Ext.addEquiv₀

end AlgebraicGeometry.ComplexPoint
