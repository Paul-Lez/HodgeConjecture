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

public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import HodgeConjecture.Definitions.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# The Hodge filtration

This file defines rational sheaf cohomology and holomorphic de Rham hypercohomology on the
analytic complex-point space of a smooth complex scheme. Hypercohomology is expressed with
Mathlib's small shifted morphisms in the localization at quasi-isomorphisms. This avoids exposing
a noncanonical choice of derived category in the public types.

The stupid truncation of the holomorphic de Rham complex in form degrees at least `p` maps into
the full complex. Its image on hypercohomology is the Hodge filtration `F^p`. A rational Hodge
class is then a rational class whose de Rham image belongs to `F^p`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

local instance hodgeFiltrationTopology :
    TopologicalSpace (ComplexPoint X) := analyticTopology

/-- Sheaves of additive groups on the analytic complex-point space. -/
abbrev AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))

local instance analyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The constant rational sheaf on the analytic complex-point space. -/
def constantFieldSheaf : AnalyticAdditiveSheaf X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of K)

/-- The inclusion of the rational constant sheaf into the complex constant sheaf. -/
def fieldToComplexConstantSheaf :
    constantFieldSheaf K X ⟶ constantComplexSheaf X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)

/-- The inclusion of `K` into `ℂ`, regarded as a rational-linear map. -/
def fieldToComplexLinear : K →ₗ[K] ℂ :=
  Algebra.linearMap K ℂ

/-- A rational-linear retraction of the inclusion `K → ℂ`. Such a retraction exists because an
injective linear map of vector spaces over a field splits. -/
noncomputable def complexToFieldLinear : ℂ →ₗ[K] K :=
  Classical.choose <| (fieldToComplexLinear K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

/-- The chosen rational-linear retraction is a left inverse to `K → ℂ`. -/
lemma complexToFieldLinear_comp_fieldToComplexLinear :
    complexToFieldLinear K ∘ₗ fieldToComplexLinear K = LinearMap.id :=
  Classical.choose_spec <| (fieldToComplexLinear K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

@[simp] lemma complexToFieldLinear_algebraMap (q : K) :
    complexToFieldLinear K (algebraMap K ℂ q) = q := by
  have h := LinearMap.congr_fun (complexToFieldLinear_comp_fieldToComplexLinear K) q
  simpa [fieldToComplexLinear] using h

/-- The chosen rational-linear retraction, applied to the complex constant sheaf. -/
def complexToFieldConstantSheaf :
    constantComplexSheaf X ⟶ constantFieldSheaf K X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom)

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf :
    fieldToComplexConstantSheaf K X ≫
      complexToFieldConstantSheaf K X = 𝟙 _ := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom =
      𝟙 (AddCommGrpCat.of K) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro q
    exact complexToFieldLinear_algebraMap K q
  rw [h]
  exact (constantSheaf J AddCommGrpCat).map_id (AddCommGrpCat.of K)

/-- The constant rational sheaf complex, extended by zero to integer degrees. -/
def constantFieldSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
    (constantFieldSheaf K X)).extend ComplexShape.embeddingUpNat

/-- Extension of rational constants to complex constants as a map of integer complexes. -/
def fieldToComplexConstantSheafComplexInt :
    constantFieldSheafComplexInt K X ⟶
      constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat

/-- The chosen retraction from the complex constant sheaf complex to the rational one. -/
def complexToFieldConstantSheafComplexInt :
    constantComplexSheafComplexInt X ⟶
      constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (complexToFieldConstantSheaf K X)) ComplexShape.embeddingUpNat

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexToField :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexToFieldConstantSheafComplexInt K X = 𝟙 _ := by
  unfold fieldToComplexConstantSheafComplexInt
    complexToFieldConstantSheafComplexInt constantFieldSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf]
  have hmap : (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (𝟙 (constantFieldSheaf K X)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        (constantFieldSheaf K X)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_id _
  rw [hmap]
  exact HomologicalComplex.extendMap_id _ _

/-- Rational constants mapped canonically into the holomorphic de Rham complex. -/
def fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    constantFieldSheafComplexInt K X ⟶
      holomorphicDeRhamComplexInt X :=
  fieldToComplexConstantSheafComplexInt K X ≫
    constantsToHolomorphicDeRhamComplexInt X

/-- The constant integer sheaf on the analytic complex-point space. -/
def constantIntegerSheaf : AnalyticAdditiveSheaf X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The constant integer sheaf complex, extended by zero to integer degrees. -/
def constantIntegerSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
    (constantIntegerSheaf X)).extend ComplexShape.embeddingUpNat

/-- The additive map `n ↦ n q` from the integers to the rationals. -/
def integerMultipleAddHom (q : K) : ℤ →+ K where
  toFun n := n * q
  map_zero' := by simp
  map_add' a b := by push_cast; ring

omit [Algebra K ℂ] in
@[simp] lemma integerMultipleAddHom_zero : integerMultipleAddHom K 0 = 0 := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom]

omit [Algebra K ℂ] in
@[simp] lemma integerMultipleAddHom_add (a b : K) :
    integerMultipleAddHom K (a + b) = integerMultipleAddHom K a + integerMultipleAddHom K b := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom, mul_add]

/-- A rational number as a morphism from the integer to the rational constant sheaf. -/
def integerToFieldConstantSheaf (q : K) :
    constantIntegerSheaf X ⟶ constantFieldSheaf K X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).map (AddCommGrpCat.ofHom (integerMultipleAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_zero :
    integerToFieldConstantSheaf K X 0 = 0 := by
  unfold integerToFieldConstantSheaf
  rw [integerMultipleAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ K) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_add (a b : K) :
    integerToFieldConstantSheaf K X (a + b) =
      integerToFieldConstantSheaf K X a +
        integerToFieldConstantSheaf K X b := by
  unfold integerToFieldConstantSheaf
  rw [integerMultipleAddHom_add]
  have h : AddCommGrpCat.ofHom
      (integerMultipleAddHom K a + integerMultipleAddHom K b) =
      AddCommGrpCat.ofHom (integerMultipleAddHom K a) +
        AddCommGrpCat.ofHom (integerMultipleAddHom K b) := by
    apply AddCommGrpCat.hom_ext
    rfl
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
  rfl

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheafComplexInt_add (a b : K) :
    integerToFieldConstantSheafComplexInt K X (a + b) =
      integerToFieldConstantSheafComplexInt K X a +
        integerToFieldConstantSheafComplexInt K X b := by
  unfold integerToFieldConstantSheafComplexInt
  rw [integerToFieldConstantSheaf_add, Functor.map_add,
    HomologicalComplex.extendMap_add]
  rfl

/-- Multiplication by a rational scalar as an additive endomorphism of `K`. -/
def fieldScalarAddHom (q : K) : K →+ K :=
  DistribSMul.toAddMonoidHom K q

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_apply (q x : K) :
    fieldScalarAddHom K q x = q * x := rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_zero : fieldScalarAddHom K 0 = 0 := by
  ext
  simp

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_one : fieldScalarAddHom K 1 = AddMonoidHom.id K := by
  ext
  simp

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_add (a b : K) :
    fieldScalarAddHom K (a + b) = fieldScalarAddHom K a + fieldScalarAddHom K b := by
  ext
  simp [add_mul]

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_mul (a b : K) :
    fieldScalarAddHom K (a * b) =
      (fieldScalarAddHom K a).comp (fieldScalarAddHom K b) := by
  ext
  simp [fieldScalarAddHom, mul_assoc]

/-- Scalar multiplication on the rational constant sheaf. -/
def fieldScalarSheaf (q : K) :
    constantFieldSheaf K X ⟶ constantFieldSheaf K X :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (fieldScalarAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_zero : fieldScalarSheaf K X 0 = 0 := by
  unfold fieldScalarSheaf
  rw [fieldScalarAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_one : fieldScalarSheaf K X 1 = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.id K) = 𝟙 (AddCommGrpCat.of K) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map (AddCommGrpCat.ofHom (fieldScalarAddHom K 1)) =
    𝟙 ((constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).obj (AddCommGrpCat.of K))
  rw [fieldScalarAddHom_one, h]
  exact (constantSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).map_id (AddCommGrpCat.of K)

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_add (a b : K) :
    fieldScalarSheaf K X (a + b) =
      fieldScalarSheaf K X a + fieldScalarSheaf K X b := by
  have h : AddCommGrpCat.ofHom (fieldScalarAddHom K a + fieldScalarAddHom K b) =
      AddCommGrpCat.ofHom (fieldScalarAddHom K a) +
        AddCommGrpCat.ofHom (fieldScalarAddHom K b) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (fieldScalarAddHom K (a + b))) = _
  rw [fieldScalarAddHom_add, h, Functor.map_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_mul (a b : K) :
    fieldScalarSheaf K X (a * b) =
      fieldScalarSheaf K X b ≫ fieldScalarSheaf K X a := by
  have h : AddCommGrpCat.ofHom
      ((fieldScalarAddHom K a).comp (fieldScalarAddHom K b)) =
      AddCommGrpCat.ofHom (fieldScalarAddHom K b) ≫
        AddCommGrpCat.ofHom (fieldScalarAddHom K a) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (fieldScalarAddHom K (a * b))) = _
  rw [fieldScalarAddHom_mul, h, Functor.map_comp]
  rfl

/-- The inclusion of rational constants into complex constants commutes with scalar
multiplication. -/
lemma fieldToComplexConstantSheaf_scalar (q : K) :
    fieldToComplexConstantSheaf K X ≫
      complexScalarSheaf X (algebraMap K ℂ q) =
    fieldScalarSheaf K X q ≫
      fieldToComplexConstantSheaf K X := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf X (algebraMap K ℂ q)) =
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (fieldScalarAddHom K q)) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (complexScalarAddHom (algebraMap K ℂ q))) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro r
  change algebraMap K ℂ q * algebraMap K ℂ r = algebraMap K ℂ (q * r)
  rw [map_mul]

omit [Algebra K ℂ] in
/-- Applying a rational scalar after the constant class `r` gives the constant class `q * r`. -/
lemma integerToFieldConstantSheaf_comp_fieldScalarSheaf (q r : K) :
    integerToFieldConstantSheaf K X r ≫
      fieldScalarSheaf K X q =
        integerToFieldConstantSheaf K X (q * r) := by
  unfold integerToFieldConstantSheaf fieldScalarSheaf
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom K r)) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (fieldScalarAddHom K q)) =
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom K (q * r)))
  rw [← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom, fieldScalarAddHom]
  ring

/-- Scalar multiplication on the rational constant sheaf complex. -/
def fieldScalarComplex (q : K) :
    constantFieldSheafComplexInt K X ⟶
      constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_zero : fieldScalarComplex K X 0 = 0 := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_one : fieldScalarComplex K X 1 = 𝟙 _ := by
  unfold fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldScalarSheaf K X 1)) ComplexShape.embeddingUpNat =
    𝟙 (HomologicalComplex.extend
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        (constantFieldSheaf K X)) ComplexShape.embeddingUpNat)
  rw [fieldScalarSheaf_one]
  have hm : (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (𝟙 (constantFieldSheaf K X)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        (constantFieldSheaf K X)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_id _
  rw [hm]
  exact HomologicalComplex.extendMap_id _ _

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_add (a b : K) :
    fieldScalarComplex K X (a + b) =
      fieldScalarComplex K X a + fieldScalarComplex K X b := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_add, Functor.map_add, HomologicalComplex.extendMap_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_mul (a b : K) :
    fieldScalarComplex K X (a * b) =
      fieldScalarComplex K X b ≫ fieldScalarComplex K X a := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_mul, Functor.map_comp, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed inclusion of rational constants into complex constants commutes with
scalar multiplication. -/
lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexScalarComplexInt X (algebraMap K ℂ q) =
    fieldScalarComplex K X q ≫
      fieldToComplexConstantSheafComplexInt K X := by
  unfold fieldToComplexConstantSheafComplexInt complexScalarComplexInt
    fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (complexScalarSheaf X (algebraMap K ℂ q))) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ← Functor.map_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_scalar]

/-- The rational-to-de Rham comparison of complexes commutes with rational scalar
multiplication. -/
lemma fieldToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (q : K) :
    fieldToHolomorphicDeRhamComplexInt K X ≫
      scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q) =
    fieldScalarComplex K X q ≫
      fieldToHolomorphicDeRhamComplexInt K X := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar]
  rw [← Category.assoc,
    fieldToComplexConstantSheafComplexInt_scalar, Category.assoc]

omit [Algebra K ℂ] in
/-- Scalar multiplication after an integer-to-rational constant-complex map multiplies its
rational coefficient. -/
lemma integerToFieldConstantSheafComplexInt_comp_fieldScalarComplex (q r : K) :
    integerToFieldConstantSheafComplexInt K X r ≫
      fieldScalarComplex K X q =
        integerToFieldConstantSheafComplexInt K X (q * r) := by
  unfold integerToFieldConstantSheafComplexInt fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (integerToFieldConstantSheaf K X r)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
        (integerToFieldConstantSheaf K X (q * r))) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    integerToFieldConstantSheaf_comp_fieldScalarSheaf]

/-- Quasi-isomorphisms of analytic sheaf complexes. -/
abbrev analyticQuasiIsomorphisms :=
  HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) (.up ℤ)

noncomputable instance analyticHasSmallLocalizedShiftedHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (analyticQuasiIsomorphisms X) ℤ K L := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization
    (analyticQuasiIsomorphisms X) DerivedCategory.Q

/-- Hypercohomology of an analytic sheaf complex in integer degree `n`. -/
abbrev Hypercohomology
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) : Type 1 :=
  Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
    (constantIntegerSheafComplexInt X) K n

/-- Rational constant-sheaf cohomology in integer degree `n`. -/
abbrev FieldCohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (constantFieldSheafComplexInt K X) n

/-- Complex constant-sheaf cohomology in integer degree `n`. -/
abbrev ComplexConstantCohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (constantComplexSheafComplexInt X) n

noncomputable instance hypercohomologyAddCommGroup
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    AddCommGroup (Hypercohomology X K n) := by
  exact (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).addCommGroup

lemma hypercohomologyEquiv_zero
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (0 : Hypercohomology X K n) = 0 := by
  unfold hypercohomologyAddCommGroup
  simp [Equiv.zero_def]

lemma hypercohomologyEquiv_add
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (α β : Hypercohomology X K n) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) (α + β) =
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) α +
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) β := by
  unfold hypercohomologyAddCommGroup
  simp [Equiv.add_def]

/-- The constant rational class `q` in degree-zero rational cohomology. -/
def fieldCohomologyClass (q : K) : FieldCohomology K X 0 :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
    (integerToFieldConstantSheafComplexInt K X q)

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_zero :
    fieldCohomologyClass K X 0 = 0 := by
  let e : FieldCohomology K X 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K X)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  simp [e, fieldCohomologyClass, hypercohomologyEquiv_zero,
    integerToFieldConstantSheafComplexInt_zero]

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_add (a b : K) :
    fieldCohomologyClass K X (a + b) =
      fieldCohomologyClass K X a + fieldCohomologyClass K X b := by
  let e : FieldCohomology K X 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K X)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  simp [e, fieldCohomologyClass, hypercohomologyEquiv_add,
    integerToFieldConstantSheafComplexInt_add]

/-- Rational constants as an additive map into degree-zero rational cohomology. -/
def fieldCohomologyClassAddHom : K →+ FieldCohomology K X 0 where
  toFun := fieldCohomologyClass K X
  map_zero' := fieldCohomologyClass_zero K X
  map_add' := fieldCohomologyClass_add K X

/-- The unit in degree-zero rational cohomology. -/
def fieldCohomologyUnit : FieldCohomology K X 0 :=
  fieldCohomologyClass K X 1

/-- Hypercohomology of the holomorphic de Rham complex in integer degree `n`. -/
abbrev DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) : Type 1 :=
  Hypercohomology X (holomorphicDeRhamComplexInt X) n

/-- A proved constant-to-holomorphic-de Rham quasi-isomorphism induces the corresponding
equivalence on hypercohomology. -/
def complexConstantCohomologyDeRhamEquiv
    [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X)) (n : ℤ) :
    ComplexConstantCohomology X n ≃
      DeRhamHypercohomology X n :=
  Localization.SmallShiftedHom.postcompEquiv
    (constantsToHolomorphicDeRhamComplexInt X) h

/-- Postcomposition on hypercohomology by a map of complexes. -/
def hypercohomologyMap
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ) :
    Hypercohomology X K n →+ Hypercohomology X L n where
  toFun α := α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n)
  map_zero' := by
    let eL : Hypercohomology X L n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
          (DerivedCategory.Q.obj L) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q
    apply eL.injective
    simp only [eL, Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]

  map_add' α β := by
    let eL : Hypercohomology X L n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
          (DerivedCategory.Q.obj L) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q
    apply eL.injective
    simp only [eL, Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma hypercohomologyMap_zero
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (0 : K ⟶ L) n = 0 := by
  apply AddMonoidHom.ext
  intro α
  let eL : Hypercohomology X L n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj L) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  change (hypercohomologyMap X (0 : K ⟶ L) n) α = 0
  apply eL.injective
  unfold hypercohomologyMap
  simp [eL, Localization.SmallShiftedHom.equiv_comp,
    hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma hypercohomologyMap_id
    {K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro α
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
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [eK]

lemma complexConstantCohomologyDeRhamEquiv_apply
    [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X)) (n : ℤ)
    (α : ComplexConstantCohomology X n) :
    complexConstantCohomologyDeRhamEquiv X h n α =
      hypercohomologyMap X
        (constantsToHolomorphicDeRhamComplexInt X) n α :=
  rfl

/-- Extension of coefficients from rational to complex constant-sheaf cohomology. -/
def fieldToComplexCohomology (n : ℤ) :
    FieldCohomology K X n →+ ComplexConstantCohomology X n :=
  hypercohomologyMap X
    (fieldToComplexConstantSheafComplexInt K X) n

/-- The cohomological retraction induced by the chosen rational-linear retraction `ℂ → K`. -/
def complexToFieldCohomology (n : ℤ) :
    ComplexConstantCohomology X n →+ FieldCohomology K X n :=
  hypercohomologyMap X
    (complexToFieldConstantSheafComplexInt K X) n

lemma smallShiftedHomMkZero_comp
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) (0 : ℤ) rfl (f ≫ g) =
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) (0 : ℤ) rfl f).comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms X) (0 : ℤ) rfl g)
          (zero_add (0 : ℤ)) := by
  let e : Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms X) K M (0 : ℤ) ≃
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [e, Functor.map_comp]

/-- Postcomposition on hypercohomology respects composition of complex maps. -/
lemma hypercohomologyMap_comp_apply
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X (f ≫ g) n α =
      hypercohomologyMap X g n
        (hypercohomologyMap X f n α) := by
  unfold hypercohomologyMap
  dsimp
  rw [smallShiftedHomMkZero_comp X]
  let β : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms X) K L (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (analyticQuasiIsomorphisms X) (0 : ℤ) rfl f
  let γ : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms X) L M (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (analyticQuasiIsomorphisms X) (0 : ℤ) rfl g
  change α.comp (β.comp γ (zero_add (0 : ℤ))) (zero_add n) =
    (α.comp β (zero_add n)).comp γ (zero_add n)
  simpa only using
    (Localization.SmallShiftedHom.comp_assoc
      (analyticQuasiIsomorphisms X) α β γ
      (zero_add n) (zero_add (0 : ℤ)) (zero_add n)).symm

/-- The rational-to-complex cohomology map has the displayed cohomological left inverse. -/
lemma complexToFieldCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToFieldCohomology K X n)
      (fieldToComplexCohomology K X n) := by
  intro α
  unfold complexToFieldCohomology fieldToComplexCohomology
  rw [← hypercohomologyMap_comp_apply X,
    fieldToComplexConstantSheafComplexInt_comp_complexToField,
    hypercohomologyMap_id]
  rfl

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma fieldToComplexCohomology_injective (n : ℤ) :
    Function.Injective (fieldToComplexCohomology K X n) :=
  (complexToFieldCohomology_leftInverse K X n).injective

/-- The rational action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
def fieldCohomologySMul (n : ℤ) (q : K)
    (α : FieldCohomology K X n) : FieldCohomology K X n :=
  hypercohomologyMap X (fieldScalarComplex K X q) n α

noncomputable instance fieldCohomologySMulInstance (n : ℤ) :
    SMul K (FieldCohomology K X n) :=
  ⟨fieldCohomologySMul K X n⟩

omit [Algebra K ℂ] in
lemma field_smul_eq (n : ℤ) (q : K) (α : FieldCohomology K X n) :
    q • α = hypercohomologyMap X
      (fieldScalarComplex K X q) n α := rfl

omit [Algebra K ℂ] in
lemma field_smul_add (n : ℤ) (q : K)
    (α β : FieldCohomology K X n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap X
    (fieldScalarComplex K X q) n).map_add α β

omit [Algebra K ℂ] in
lemma field_add_smul (n : ℤ) (a b : K)
    (α : FieldCohomology K X n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap X
      (fieldScalarComplex K X (a + b)) n α =
    hypercohomologyMap X (fieldScalarComplex K X a) n α +
      hypercohomologyMap X (fieldScalarComplex K X b) n α
  rw [fieldScalarComplex_add]
  let e : FieldCohomology K X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

omit [Algebra K ℂ] in
lemma field_one_smul (n : ℤ) (α : FieldCohomology K X n) :
    (1 : K) • α = α := by
  rw [field_smul_eq, fieldScalarComplex_one]
  let e : FieldCohomology K X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

omit [Algebra K ℂ] in
lemma field_mul_smul (n : ℤ) (a b : K)
    (α : FieldCohomology K X n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap X
      (fieldScalarComplex K X (a * b)) n α =
    hypercohomologyMap X (fieldScalarComplex K X a) n
      (hypercohomologyMap X (fieldScalarComplex K X b) n α)
  rw [fieldScalarComplex_mul]
  exact hypercohomologyMap_comp_apply X _ _ n α

/-- Rational constant-sheaf cohomology is canonically a rational vector space. -/
noncomputable instance fieldCohomologyModule (n : ℤ) :
    Module K (FieldCohomology K X n) :=
  Module.ofMinimalAxioms
    (field_smul_add K X n)
    (field_add_smul K X n)
    (field_mul_smul K X n)
    (field_one_smul K X n)

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
def deRhamComplexSMul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    DeRhamHypercohomology X n :=
  hypercohomologyMap X
    (scalarHolomorphicDeRhamComplexInt X c) n α

noncomputable instance deRhamComplexSMulInstance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul ℂ (DeRhamHypercohomology X n) :=
  ⟨deRhamComplexSMul X n⟩

lemma deRham_complex_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    c • α = hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X c) n α :=
  rfl

lemma deRham_complex_smul_add [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α β : DeRhamHypercohomology X n) :
    c • (α + β) = c • α + c • β := by
  exact (hypercohomologyMap X
    (scalarHolomorphicDeRhamComplexInt X c) n).map_add α β

lemma deRham_complex_add_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (a b : ℂ) (α : DeRhamHypercohomology X n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (a + b)) n α =
    hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X a) n α +
      hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X b) n α
  rw [scalarHolomorphicDeRhamComplexInt_add]
  let e : DeRhamHypercohomology X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

lemma deRham_complex_one_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (α : DeRhamHypercohomology X n) :
    (1 : ℂ) • α = α := by
  rw [deRham_complex_smul_eq, scalarHolomorphicDeRhamComplexInt_one]
  let e : DeRhamHypercohomology X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma deRham_complex_mul_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (a b : ℂ) (α : DeRhamHypercohomology X n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (a * b)) n α =
    hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X a) n
      (hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X b) n α)
  rw [scalarHolomorphicDeRhamComplexInt_mul]
  exact hypercohomologyMap_comp_apply X _ _ n α

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance deRhamHypercohomologyComplexModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module ℂ (DeRhamHypercohomology X n) :=
  Module.ofMinimalAxioms
    (deRham_complex_smul_add X n)
    (deRham_complex_add_smul X n)
    (deRham_complex_mul_smul X n)
    (deRham_complex_one_smul X n)

/-- The rational action on de Rham hypercohomology, induced by multiplication by the corresponding
complex scalar on the de Rham complex. -/
def deRhamFieldSMul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α : DeRhamHypercohomology X n) :
    DeRhamHypercohomology X n :=
  hypercohomologyMap X
    (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)) n α

noncomputable instance deRhamFieldSMulInstance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul K (DeRhamHypercohomology X n) :=
  ⟨deRhamFieldSMul K X n⟩

lemma deRham_field_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α : DeRhamHypercohomology X n) :
    q • α = hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)) n α :=
  rfl

lemma deRham_field_smul_add [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α β : DeRhamHypercohomology X n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap X
    (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)) n).map_add α β

lemma deRham_field_add_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (a b : K) (α : DeRhamHypercohomology X n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ (a + b))) n α =
    hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ a)) n α +
      hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ b)) n α
  rw [map_add, scalarHolomorphicDeRhamComplexInt_add]
  let e : DeRhamHypercohomology X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

lemma deRham_field_one_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (α : DeRhamHypercohomology X n) :
    (1 : K) • α = α := by
  rw [deRham_field_smul_eq, map_one,
    scalarHolomorphicDeRhamComplexInt_one]
  let e : DeRhamHypercohomology X n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma deRham_field_mul_smul [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (a b : K) (α : DeRhamHypercohomology X n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ (a * b))) n α =
    hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ a)) n
      (hypercohomologyMap X
        (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ b)) n α)
  rw [map_mul, scalarHolomorphicDeRhamComplexInt_mul]
  exact hypercohomologyMap_comp_apply X _ _ n α

/-- Holomorphic de Rham hypercohomology is canonically a rational vector space. -/
noncomputable instance deRhamHypercohomologyModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module K (DeRhamHypercohomology X n) :=
  Module.ofMinimalAxioms
    (deRham_field_smul_add K X n)
    (deRham_field_add_smul K X n)
    (deRham_field_mul_smul K X n)
    (deRham_field_one_smul K X n)

/-- The independently constructed rational and complex scalar actions on de Rham
hypercohomology agree through the canonical embedding `K → ℂ`. -/
lemma deRham_field_smul_eq_complex_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (q : K) (α : DeRhamHypercohomology X n) :
    q • α = (algebraMap K ℂ q) • α :=
  rfl

/-- Rational, complex, and de Rham scalar multiplication form the expected scalar tower. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ (DeRhamHypercohomology X n) :=
  IsScalarTower.of_algebraMap_smul fun q α =>
    deRham_field_smul_eq_complex_smul K X n q α

omit [Algebra K ℂ] in
/-- Constant degree-zero cohomology classes respect rational scalar multiplication. -/
lemma fieldCohomologyClass_mul (q r : K) :
    fieldCohomologyClass K X (q * r) =
      q • fieldCohomologyClass K X r := by
  rw [field_smul_eq]
  unfold fieldCohomologyClass hypercohomologyMap
  dsimp
  rw [← smallShiftedHomMkZero_comp X,
    integerToFieldConstantSheafComplexInt_comp_fieldScalarComplex]

/-- Rational constants map rational-linearly to degree-zero rational cohomology. -/
def fieldCohomologyClassLinear : K →ₗ[K] FieldCohomology K X 0 where
  toFun := fieldCohomologyClass K X
  map_add' := fieldCohomologyClass_add K X
  map_smul' q r := fieldCohomologyClass_mul K X q r

/-- The derived comparison from rational cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FieldCohomology K X n →+ DeRhamHypercohomology X n :=
  hypercohomologyMap X
    (fieldToHolomorphicDeRhamComplexInt K X) n

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma fieldToDeRhamCohomology_factor
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FieldCohomology K X n) :
    fieldToDeRhamCohomology K X n α =
      hypercohomologyMap X
        (constantsToHolomorphicDeRhamComplexInt X) n
        (fieldToComplexCohomology K X n α) := by
  unfold fieldToDeRhamCohomology fieldToComplexCohomology
    fieldToHolomorphicDeRhamComplexInt
  exact hypercohomologyMap_comp_apply X
    (fieldToComplexConstantSheafComplexInt K X)
    (constantsToHolomorphicDeRhamComplexInt X) n α

/-- Once the analytic Poincare comparison is proved to be a quasi-isomorphism, the
rational-to-de Rham comparison is injective. This uses the explicit splitting of `K → ℂ`, not a
finite-dimensionality assumption. -/
lemma fieldToDeRhamCohomology_injective_of_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X)) (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) := by
  intro α β hαβ
  apply fieldToComplexCohomology_injective K X n
  apply (complexConstantCohomologyDeRhamEquiv X h n).injective
  simpa only [complexConstantCohomologyDeRhamEquiv_apply,
    fieldToDeRhamCohomology_factor K X n] using hαβ

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit coefficient splitting proves that extending
scalars from `K` to `ℂ` is injective. -/
lemma fieldToDeRhamCohomology_injective
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) :=
  fieldToDeRhamCohomology_injective_of_quasiIso K X inferInstance n

/-- The rational-to-de Rham comparison is compatible with rational scalar multiplication. -/
lemma fieldToDeRhamCohomology_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (q : K) (α : FieldCohomology K X n) :
    fieldToDeRhamCohomology K X n (q • α) =
      q • fieldToDeRhamCohomology K X n α := by
  rw [field_smul_eq, deRham_field_smul_eq]
  unfold fieldToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [fieldToHolomorphicDeRhamComplexInt_scalar]

/-- The rational-to-de Rham comparison as a rational-linear map. -/
def fieldToDeRhamCohomologyLinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FieldCohomology K X n →ₗ[K]
      DeRhamHypercohomology X n where
  toFun := fieldToDeRhamCohomology K X n
  map_add' := (fieldToDeRhamCohomology K X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K X n

/-- The balanced map that extends rational-to-de Rham comparison after scalar extension from
`K` to `ℂ`. -/
def fieldToDeRhamComplexificationBilinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ℂ →ₗ[ℂ] FieldCohomology K X n →ₗ[K]
      DeRhamHypercohomology X n where
  toFun c := c • (fieldToDeRhamCohomologyLinear K X n)
  map_add' a b := by
    ext α
    simp [add_smul]
  map_smul' a b := by
    ext α
    simp [mul_smul]

/-- The canonical complex-linear comparison from the complexification of rational
constant-sheaf cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamComplexification
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ℂ ⊗[K] FieldCohomology K X n →ₗ[ℂ]
      DeRhamHypercohomology X n :=
  TensorProduct.AlgebraTensorModule.lift
    (fieldToDeRhamComplexificationBilinear K X n)

@[simp] lemma fieldToDeRhamComplexification_tmul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (c : ℂ) (α : FieldCohomology K X n) :
    fieldToDeRhamComplexification K X n (c ⊗ₜ[K] α) =
      c • fieldToDeRhamCohomology K X n α :=
  rfl

/-- On the rational lattice, the complexified comparison agrees with the original map. -/
@[simp] lemma fieldToDeRhamComplexification_ofField
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FieldCohomology K X n) :
    fieldToDeRhamComplexification K X n (1 ⊗ₜ[K] α) =
      fieldToDeRhamCohomology K X n α := by
  simp

/-- The de Rham complex with only form degrees at least `p` retained. -/
def hodgeFilteredDeRhamComplex [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (holomorphicDeRhamComplexInt X).stupidTrunc
    (ComplexShape.embeddingUpIntGE p)

/-- The part of the holomorphic de Rham complex in form degrees at least `p` is zero when `p`
is above the complex dimension. -/
lemma hodgeFilteredDeRhamComplex_isZero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    IsZero (hodgeFilteredDeRhamComplex X p) := by
  rw [hodgeFilteredDeRhamComplex,
    HomologicalComplex.isZero_stupidTrunc_iff]
  refine ⟨fun n => ?_⟩
  change IsZero ((holomorphicDeRhamComplexInt X).X (p + n))
  exact (holomorphicDeRhamComplexInt X).isZero_of_isStrictlyLE
    (dim X.left) (p + n) (by lia)

/-- Inclusion of the degree-at-least-`p` de Rham complex into the full complex. -/
def hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    hodgeFilteredDeRhamComplex X p ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamComplexInt X) (ComplexShape.embeddingUpIntGE p)

/-- Above the complex dimension the filtered-to-full inclusion has zero source and hence is the
zero morphism. -/
lemma hodgeFilteredDeRhamInclusion_eq_zero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    hodgeFilteredDeRhamInclusion X p = 0 :=
  (hodgeFilteredDeRhamComplex_isZero_of_lt X hp).eq_of_src _ _

/-- Rational scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamScalar [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) (q : K) :
    hodgeFilteredDeRhamComplex X p ⟶
      hodgeFilteredDeRhamComplex X p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q))
    (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamComplexScalar [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplex X p ⟶
      hodgeFilteredDeRhamComplex X p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt X c)
    (ComplexShape.embeddingUpIntGE p)

/-- Scalar multiplication on the filtered complex commutes with its inclusion into the full de
Rham complex. -/
lemma hodgeFilteredDeRhamScalar_comp_inclusion
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (q : K) :
    hodgeFilteredDeRhamScalar K X p q ≫
      hodgeFilteredDeRhamInclusion X p =
    hodgeFilteredDeRhamInclusion X p ≫
      scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q) := by
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q))

/-- Complex scalar multiplication on the filtered complex commutes with inclusion into the full
de Rham complex. -/
lemma hodgeFilteredDeRhamComplexScalar_comp_inclusion
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar X p c ≫
      hodgeFilteredDeRhamInclusion X p =
    hodgeFilteredDeRhamInclusion X p ≫
      scalarHolomorphicDeRhamComplexInt X c := by
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt X c)

/-- Hypercohomology of the degree-at-least-`p` part of the de Rham complex. -/
abbrev FilteredDeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Type 1 :=
  Hypercohomology X (hodgeFilteredDeRhamComplex X p) n

/-- The map from filtered to full de Rham hypercohomology. -/
def filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    FilteredDeRhamHypercohomology X p n →+
      DeRhamHypercohomology X n :=
  hypercohomologyMap X (hodgeFilteredDeRhamInclusion X p) n

/-- The Hodge filtration `F^p` on de Rham hypercohomology. -/
def hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    AddSubgroup (DeRhamHypercohomology X n) :=
  (filteredToDeRhamCohomology X p n).range

/-- The Hodge filtration is zero above the complex dimension. -/
lemma hodgeFiltration_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    hodgeFiltration X p n = ⊥ := by
  rw [hodgeFiltration]
  change (hypercohomologyMap X
    (hodgeFilteredDeRhamInclusion X p) n).range = ⊥
  rw [hodgeFilteredDeRhamInclusion_eq_zero_of_lt X hp,
    hypercohomologyMap_zero]
  simp

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma hodgeFiltration_complex_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (c : ℂ) {α : DeRhamHypercohomology X n}
    (hα : α ∈ hodgeFiltration X p n) :
    c • α ∈ hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨hypercohomologyMap X
    (hodgeFilteredDeRhamComplexScalar X p c) n β, ?_⟩
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

/-- The Hodge filtration bundled as a complex subspace of de Rham hypercohomology. -/
def hodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology X n) where
  carrier := hodgeFiltration X p n
  zero_mem' := (hodgeFiltration X p n).zero_mem
  add_mem' := (hodgeFiltration X p n).add_mem
  smul_mem' := fun c _ h => hodgeFiltration_complex_smul_mem X p n c h

/-- Pull back the de Rham Hodge filtration to the actual complexification of rational
constant-sheaf cohomology. This definition uses the canonical comparison map rather than
identifying the two cohomology theories without proof. -/
def complexifiedFieldHodgeFiltration [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) :
    Submodule ℂ (ℂ ⊗[K] FieldCohomology K X n) :=
  (hodgeFiltrationComplexSubmodule X p n).comap
    (fieldToDeRhamComplexification K X n)

/-- The Hodge filtration is stable under rational scalar multiplication. -/
lemma hodgeFiltration_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (q : K) {α : DeRhamHypercohomology X n}
    (hα : α ∈ hodgeFiltration X p n) :
    q • α ∈ hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨hypercohomologyMap X
    (hodgeFilteredDeRhamScalar K X p q) n β, ?_⟩
  rw [deRham_field_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamScalar_comp_inclusion]

/-- The Hodge filtration bundled as a rational subspace of de Rham hypercohomology. -/
def hodgeFiltrationSubmodule [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    Submodule K (DeRhamHypercohomology X n) where
  carrier := hodgeFiltration X p n
  zero_mem' := (hodgeFiltration X p n).zero_mem
  add_mem' := (hodgeFiltration X p n).add_mem
  smul_mem' := fun q _ h => hodgeFiltration_smul_mem K X p n q h

/-- In degree filtration `F⁰`, the filtered and full de Rham hypercohomology groups are
canonically equivalent. -/
def hodgeFiltrationZeroEquiv [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FilteredDeRhamHypercohomology X 0 n ≃
      DeRhamHypercohomology X n := by
  letI : (holomorphicDeRhamComplexInt X).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  letI : IsIso (hodgeFilteredDeRhamInclusion X 0) := by
    unfold hodgeFilteredDeRhamInclusion hodgeFilteredDeRhamComplex
    infer_instance
  exact Localization.SmallShiftedHom.postcompEquiv
    (hodgeFilteredDeRhamInclusion X 0)
    (by
      change QuasiIso (hodgeFilteredDeRhamInclusion X 0)
      infer_instance)

lemma filteredToDeRhamCohomology_zero_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FilteredDeRhamHypercohomology X 0 n) :
    filteredToDeRhamCohomology X 0 n α =
      hodgeFiltrationZeroEquiv X n α := rfl

/-- The zeroth Hodge filtration is the whole de Rham hypercohomology group. -/
lemma hodgeFiltration_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltration X 0 n = ⊤ := by
  ext α
  simp only [hodgeFiltration, AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
  exact ⟨(hodgeFiltrationZeroEquiv X n).symm α,
    filteredToDeRhamCohomology_zero_apply X n _ |>.trans
      ((hodgeFiltrationZeroEquiv X n).apply_symm_apply α)⟩

/-- The rational submodule underlying `F⁰` is the whole de Rham hypercohomology group. -/
lemma hodgeFiltrationSubmodule_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltrationSubmodule K X 0 n = ⊤ := by
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration X 0 n ↔ α ∈ (⊤ :
    Submodule K (DeRhamHypercohomology X n))
  rw [hodgeFiltration_zero_eq_top X n]
  simp

/-- Rational cohomology classes whose de Rham images lie in `F^p H^{2p}`, bundled as an additive
subgroup.

The Hodge filtration is indexed by a relative dimension, but the dimension is not a choice: it is
`dim X.left`, recovered from the scheme itself. -/
def hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (FieldCohomology K X (2 * p)) :=
  (hodgeFiltrationSubmodule K X p (2 * p)).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))

/-- `Hdg^p(K; f)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is presented by its
structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" K "; " f ")" => hodgeClasses K f p

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma hodgeClasses_eq_ker_of_lt [IsIntegral X.left] [Smooth X.hom] {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) =
      LinearMap.ker (fieldToDeRhamCohomologyLinear K X (2 * p)) := by
  rw [hodgeClasses, ← Submodule.comap_bot]
  congr 1
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration X (p : ℤ) (2 * (p : ℤ)) ↔ α ∈ (⊥ :
    Submodule ℂ (DeRhamHypercohomology X (2 * (p : ℤ))))
  rw [hodgeFiltration_eq_bot_of_lt X (by exact_mod_cast hp)]
  rfl

/-- If the analytic constant-to-holomorphic de Rham comparison is a quasi-isomorphism, rational
Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt_of_quasiIso [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X))
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) = ⊥ := by
  rw [hodgeClasses_eq_ker_of_lt K X hp]
  apply LinearMap.ker_eq_bot.mpr
  exact fieldToDeRhamCohomology_injective_of_quasiIso K X h (2 * p)

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt
    [IsIntegral X.left] [Smooth X.hom]
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) = ⊥ :=
  hodgeClasses_eq_bot_of_lt_of_quasiIso K X inferInstance hp

/-- Rational Hodge classes described through the rational lattice inside its actual
complexification. -/
def hodgeClassesViaComplexification
    [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (FieldCohomology K X (2 * p)) :=
  Submodule.comap
    (HodgeStructure.ofBase K (FieldCohomology K X (2 * p)))
    ((complexifiedFieldHodgeFiltration K X p (2 * p)).restrictScalars K)

/-- The direct definition of rational Hodge classes agrees with the definition using the
complexified rational lattice. -/
lemma hodgeClassesViaComplexification_eq [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    hodgeClassesViaComplexification K X p =
      Hdg^p(K; X) := by
  ext α
  change fieldToDeRhamComplexification K X (2 * (p : ℤ))
      (HodgeStructure.ofBase K
        (FieldCohomology K X (2 * (p : ℤ))) α) ∈
        hodgeFiltration X p (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgeFiltration X p (2 * (p : ℤ))
  rw [HodgeStructure.ofBase_apply,
    fieldToDeRhamComplexification_ofField]

/-- A rational cohomology class is a Hodge class of codimension `p` when it belongs to the
canonical subgroup of rational Hodge classes. -/
def IsHodgeClass [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (α : FieldCohomology K X (2 * p)) : Prop :=
  α ∈ Hdg^p(K; X)

lemma mem_hodgeClasses_iff [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) (α : FieldCohomology K X (2 * p)) :
    α ∈ Hdg^p(K; X) ↔
      IsHodgeClass K X p α :=
  Iff.rfl

/-- Every rational degree-zero cohomology class belongs to the rational Hodge subgroup. -/
lemma hodgeClasses_zero_eq_top [IsIntegral X.left] [Smooth X.hom]
    :
    Hdg^0(K; X) = ⊤ := by
  apply SetLike.ext
  intro α
  change fieldToDeRhamCohomology K X (2 * (0 : ℕ)) α ∈
      hodgeFiltration X (0 : ℕ) (2 * (0 : ℕ)) ↔ True
  simp only [Nat.cast_zero]
  rw [hodgeFiltration_zero_eq_top]
  trivial

/-- Every rational degree-zero class has Hodge type `(0,0)`. -/
lemma isHodgeClass_zero [IsIntegral X.left] [Smooth X.hom]
    (α : FieldCohomology K X 0) :
    IsHodgeClass K X 0 α := by
  change α ∈ Hdg^0(K; X)
  rw [hodgeClasses_zero_eq_top]
  trivial

end AlgebraicGeometry.ComplexPoint
