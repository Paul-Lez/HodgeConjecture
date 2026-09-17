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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The Hodge filtration

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticHasDerivedCategory

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- A rational number as a morphism from the integer to the rational constant sheaf. -/
def integerToFieldConstantSheaf (q : K) :
    𝓒(↧(ComplexPoint X); ℤ) ⟶ 𝓒(↧(ComplexPoint X); K) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (zmultiplesAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_zero :
    integerToFieldConstantSheaf K X 0 = 0 := by
  unfold integerToFieldConstantSheaf
  rw [map_zero (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_add (a b : K) :
    integerToFieldConstantSheaf K X (a + b) =
      integerToFieldConstantSheaf K X a +
        integerToFieldConstantSheaf K X b := by
  unfold integerToFieldConstantSheaf
  rw [map_add (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom
      (zmultiplesAddHom K a + zmultiplesAddHom K b) =
      AddCommGrpCat.ofHom (zmultiplesAddHom K a) +
        AddCommGrpCat.ofHom (zmultiplesAddHom K b) :=
    AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_add]
  rfl

/-- A rational number as a morphism of constant complexes. -/
def integerToFieldConstantSheafComplexInt (q : K) :
    constantIntegerSheafComplexInt X ⟶
      constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (integerToFieldConstantSheaf K X q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheafComplexInt_zero :
    integerToFieldConstantSheafComplexInt K X 0 = 0 := by
  unfold integerToFieldConstantSheafComplexInt
  rw [integerToFieldConstantSheaf_zero, Functor.map_zero,
    HomologicalComplex.extendMap_zero]

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheafComplexInt_add (a b : K) :
    integerToFieldConstantSheafComplexInt K X (a + b) =
      integerToFieldConstantSheafComplexInt K X a +
        integerToFieldConstantSheafComplexInt K X b := by
  unfold integerToFieldConstantSheafComplexInt
  rw [integerToFieldConstantSheaf_add, Functor.map_add,
    HomologicalComplex.extendMap_add]

/-- The source object of Mathlib's sheaf cohomology mapped to the constant integer sheaf. -/
def uliftIntegerToIntegerConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ 𝓒(↧(ComplexPoint X); ℤ) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)

/-- The constant rational class `q` in degree-zero rational cohomology. -/
def fieldCohomologyClass (q : K) : H^0(X; K) :=
  Abelian.Ext.mk₀ (uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf K X q)

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_zero :
    fieldCohomologyClass K X 0 = 0 := by
  rw [fieldCohomologyClass, integerToFieldConstantSheaf_zero]
  exact (congrArg Abelian.Ext.mk₀
    (Limits.comp_zero (f := uliftIntegerToIntegerConstantSheaf X))).trans
    (Abelian.Ext.mk₀_zero _ _)

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_add (a b : K) :
    fieldCohomologyClass K X (a + b) =
      fieldCohomologyClass K X a + fieldCohomologyClass K X b := by
  rw [fieldCohomologyClass, fieldCohomologyClass, fieldCohomologyClass,
    integerToFieldConstantSheaf_add]
  exact (congrArg Abelian.Ext.mk₀ (Preadditive.comp_add _ _ _ (uliftIntegerToIntegerConstantSheaf X)
    (integerToFieldConstantSheaf K X a) (integerToFieldConstantSheaf K X b))).trans
    (Abelian.Ext.mk₀_add _ _)

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticHasDerivedCategory

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_zero : fieldScalarSheaf K X 0 = 0 := by
  unfold fieldScalarSheaf
  rw [AddMonoidHom.mulLeft_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_zero : fieldScalarComplex K X 0 = 0 := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma hypercohomologyMap_zero
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (0 : K ⟶ L) n = 0 := by
  refine AddMonoidHom.ext fun α ↦ ?_
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  unfold hypercohomologyMap
  simp [Localization.SmallShiftedHom.equiv_comp,
    hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma hypercohomologyMap_id
    {K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun α ↦ ?_
  let eK : Hypercohomology X K n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  change α.comp
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl (𝟙 K))
      (zero_add n) = α
  apply eK.injective
  simp [eK]

@[simp] lemma deRhamConjSemilinear_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : DeRhamHypercohomology X n) :
    deRhamConjSemilinear X n α = deRhamConj X n α := rfl

/-! #### Real coefficient fields

The hypothesis `hK` below says conjugation fixes the image of `K` in `ℂ`, equivalently that
`K → ℂ` lands in `ℝ`. It holds for `ℚ` and fails for `ℚ(i) ⊆ ℂ`. -/

end AlgebraicGeometry.ComplexPoint
