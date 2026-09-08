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

public import HodgeConjecture.Mathlib.Algebra.Category.Grp.Basic
public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Definitions.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.TensorProduct.Map

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

variable (K : Type) [Field K] [Algebra K ℂ]
variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

local instance hodgeFiltrationTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

local instance hodgeFiltrationChartedSpace [SmoothOfRelativeDimension d structureMap] :
    ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
  analyticChartedSpace structureMap d

/-- Sheaves of additive groups on the analytic complex-point space. -/
abbrev AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))

local instance analyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

/-- The constant rational sheaf on the analytic complex-point space. -/
def constantFieldSheaf : AnalyticAdditiveSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of K)

/-- The inclusion of the rational constant sheaf into the complex constant sheaf. -/
def fieldToComplexConstantSheaf :
    constantFieldSheaf K structureMap ⟶ constantComplexSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
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
    constantComplexSheaf structureMap ⟶ constantFieldSheaf K structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom)

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf :
    fieldToComplexConstantSheaf K structureMap ≫
      complexToFieldConstantSheaf K structureMap = 𝟙 _ := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
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
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
    (constantFieldSheaf K structureMap)).extend ComplexShape.embeddingUpNat

/-- Extension of rational constants to complex constants as a map of integer complexes. -/
def fieldToComplexConstantSheafComplexInt :
    constantFieldSheafComplexInt K structureMap ⟶
      constantComplexSheafComplexInt structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (fieldToComplexConstantSheaf K structureMap)) ComplexShape.embeddingUpNat

/-- The chosen retraction from the complex constant sheaf complex to the rational one. -/
def complexToFieldConstantSheafComplexInt :
    constantComplexSheafComplexInt structureMap ⟶
      constantFieldSheafComplexInt K structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (complexToFieldConstantSheaf K structureMap)) ComplexShape.embeddingUpNat

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexToField :
    fieldToComplexConstantSheafComplexInt K structureMap ≫
      complexToFieldConstantSheafComplexInt K structureMap = 𝟙 _ := by
  unfold fieldToComplexConstantSheafComplexInt
    complexToFieldConstantSheafComplexInt constantFieldSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf]
  have hmap : (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (𝟙 (constantFieldSheaf K structureMap)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantFieldSheaf K structureMap)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map_id _
  rw [hmap]
  exact HomologicalComplex.extendMap_id _ _

/-- Rational constants mapped canonically into the holomorphic de Rham complex. -/
def fieldToHolomorphicDeRhamComplexInt [SmoothOfRelativeDimension d structureMap] :
    constantFieldSheafComplexInt K structureMap ⟶
      holomorphicDeRhamComplexInt structureMap d :=
  fieldToComplexConstantSheafComplexInt K structureMap ≫
    constantsToHolomorphicDeRhamComplexInt structureMap d

/-- The constant integer sheaf on the analytic complex-point space. -/
def constantIntegerSheaf : AnalyticAdditiveSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The constant integer sheaf complex, extended by zero to integer degrees. -/
def constantIntegerSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
    (constantIntegerSheaf structureMap)).extend ComplexShape.embeddingUpNat

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
    constantIntegerSheaf structureMap ⟶ constantFieldSheaf K structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map (AddCommGrpCat.ofHom (integerMultipleAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_zero :
    integerToFieldConstantSheaf K structureMap 0 = 0 := by
  unfold integerToFieldConstantSheaf
  rw [integerMultipleAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ K) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheaf_add (a b : K) :
    integerToFieldConstantSheaf K structureMap (a + b) =
      integerToFieldConstantSheaf K structureMap a +
        integerToFieldConstantSheaf K structureMap b := by
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
    constantIntegerSheafComplexInt structureMap ⟶
      constantFieldSheafComplexInt K structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (integerToFieldConstantSheaf K structureMap q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheafComplexInt_zero :
    integerToFieldConstantSheafComplexInt K structureMap 0 = 0 := by
  unfold integerToFieldConstantSheafComplexInt
  rw [integerToFieldConstantSheaf_zero, Functor.map_zero,
    HomologicalComplex.extendMap_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma integerToFieldConstantSheafComplexInt_add (a b : K) :
    integerToFieldConstantSheafComplexInt K structureMap (a + b) =
      integerToFieldConstantSheafComplexInt K structureMap a +
        integerToFieldConstantSheafComplexInt K structureMap b := by
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
    constantFieldSheaf K structureMap ⟶ constantFieldSheaf K structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (fieldScalarAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_zero : fieldScalarSheaf K structureMap 0 = 0 := by
  unfold fieldScalarSheaf
  rw [fieldScalarAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_one : fieldScalarSheaf K structureMap 1 = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.id K) = 𝟙 (AddCommGrpCat.of K) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map (AddCommGrpCat.ofHom (fieldScalarAddHom K 1)) =
    𝟙 ((constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).obj (AddCommGrpCat.of K))
  rw [fieldScalarAddHom_one, h]
  exact (constantSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    AddCommGrpCat).map_id (AddCommGrpCat.of K)

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_add (a b : K) :
    fieldScalarSheaf K structureMap (a + b) =
      fieldScalarSheaf K structureMap a + fieldScalarSheaf K structureMap b := by
  have h : AddCommGrpCat.ofHom (fieldScalarAddHom K a + fieldScalarAddHom K b) =
      AddCommGrpCat.ofHom (fieldScalarAddHom K a) +
        AddCommGrpCat.ofHom (fieldScalarAddHom K b) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (fieldScalarAddHom K (a + b))) = _
  rw [fieldScalarAddHom_add, h, Functor.map_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_mul (a b : K) :
    fieldScalarSheaf K structureMap (a * b) =
      fieldScalarSheaf K structureMap b ≫ fieldScalarSheaf K structureMap a := by
  have h : AddCommGrpCat.ofHom
      ((fieldScalarAddHom K a).comp (fieldScalarAddHom K b)) =
      AddCommGrpCat.ofHom (fieldScalarAddHom K b) ≫
        AddCommGrpCat.ofHom (fieldScalarAddHom K a) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (fieldScalarAddHom K (a * b))) = _
  rw [fieldScalarAddHom_mul, h, Functor.map_comp]
  rfl

/-- The inclusion of rational constants into complex constants commutes with scalar
multiplication. -/
lemma fieldToComplexConstantSheaf_scalar (q : K) :
    fieldToComplexConstantSheaf K structureMap ≫
      complexScalarSheaf structureMap (algebraMap K ℂ q) =
    fieldScalarSheaf K structureMap q ≫
      fieldToComplexConstantSheaf K structureMap := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf structureMap (algebraMap K ℂ q)) =
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
    integerToFieldConstantSheaf K structureMap r ≫
      fieldScalarSheaf K structureMap q =
        integerToFieldConstantSheaf K structureMap (q * r) := by
  unfold integerToFieldConstantSheaf fieldScalarSheaf
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
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
    constantFieldSheafComplexInt K structureMap ⟶
      constantFieldSheafComplexInt K structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (fieldScalarSheaf K structureMap q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_zero : fieldScalarComplex K structureMap 0 = 0 := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_one : fieldScalarComplex K structureMap 1 = 𝟙 _ := by
  unfold fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (fieldScalarSheaf K structureMap 1)) ComplexShape.embeddingUpNat =
    𝟙 (HomologicalComplex.extend
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantFieldSheaf K structureMap)) ComplexShape.embeddingUpNat)
  rw [fieldScalarSheaf_one]
  have hm : (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (𝟙 (constantFieldSheaf K structureMap)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantFieldSheaf K structureMap)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map_id _
  rw [hm]
  exact HomologicalComplex.extendMap_id _ _

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_add (a b : K) :
    fieldScalarComplex K structureMap (a + b) =
      fieldScalarComplex K structureMap a + fieldScalarComplex K structureMap b := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_add, Functor.map_add, HomologicalComplex.extendMap_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_mul (a b : K) :
    fieldScalarComplex K structureMap (a * b) =
      fieldScalarComplex K structureMap b ≫ fieldScalarComplex K structureMap a := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_mul, Functor.map_comp, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed inclusion of rational constants into complex constants commutes with
scalar multiplication. -/
lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    fieldToComplexConstantSheafComplexInt K structureMap ≫
      complexScalarComplexInt structureMap (algebraMap K ℂ q) =
    fieldScalarComplex K structureMap q ≫
      fieldToComplexConstantSheafComplexInt K structureMap := by
  unfold fieldToComplexConstantSheafComplexInt complexScalarComplexInt
    fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (fieldToComplexConstantSheaf K structureMap)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (complexScalarSheaf structureMap (algebraMap K ℂ q))) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (fieldScalarSheaf K structureMap q)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (fieldToComplexConstantSheaf K structureMap)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ← Functor.map_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_scalar]

/-- The rational-to-de Rham comparison of complexes commutes with rational scalar
multiplication. -/
lemma fieldToHolomorphicDeRhamComplexInt_scalar
    [SmoothOfRelativeDimension d structureMap] (q : K) :
    fieldToHolomorphicDeRhamComplexInt K structureMap d ≫
      scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q) =
    fieldScalarComplex K structureMap q ≫
      fieldToHolomorphicDeRhamComplexInt K structureMap d := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar]
  rw [← Category.assoc,
    fieldToComplexConstantSheafComplexInt_scalar, Category.assoc]

omit [Algebra K ℂ] in
/-- Scalar multiplication after an integer-to-rational constant-complex map multiplies its
rational coefficient. -/
lemma integerToFieldConstantSheafComplexInt_comp_fieldScalarComplex (q r : K) :
    integerToFieldConstantSheafComplexInt K structureMap r ≫
      fieldScalarComplex K structureMap q =
        integerToFieldConstantSheafComplexInt K structureMap (q * r) := by
  unfold integerToFieldConstantSheafComplexInt fieldScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (integerToFieldConstantSheaf K structureMap r)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (fieldScalarSheaf K structureMap q)) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (integerToFieldConstantSheaf K structureMap (q * r))) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    integerToFieldConstantSheaf_comp_fieldScalarSheaf]

/-- Quasi-isomorphisms of analytic sheaf complexes. -/
abbrev analyticQuasiIsomorphisms :=
  HomologicalComplex.quasiIso (AnalyticAdditiveSheaf structureMap) (.up ℤ)

noncomputable instance analyticHasSmallLocalizedShiftedHom
    (K L : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (analyticQuasiIsomorphisms structureMap) ℤ K L := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization
    (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q

/-- Hypercohomology of an analytic sheaf complex in integer degree `n`. -/
abbrev Hypercohomology
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) (n : ℤ) : Type 1 :=
  Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms structureMap)
    (constantIntegerSheafComplexInt structureMap) K n

/-- Rational constant-sheaf cohomology in integer degree `n`. -/
abbrev FieldCohomology (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (constantFieldSheafComplexInt K structureMap) n

/-- Complex constant-sheaf cohomology in integer degree `n`. -/
abbrev ComplexConstantCohomology (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (constantComplexSheafComplexInt structureMap) n

noncomputable instance hypercohomologyAddCommGroup
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) (n : ℤ) :
    AddCommGroup (Hypercohomology structureMap K n) := by
  exact (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q).addCommGroup

lemma hypercohomologyEquiv_zero
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) (n : ℤ) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q)
        (0 : Hypercohomology structureMap K n) = 0 := by
  unfold hypercohomologyAddCommGroup
  simp [Equiv.zero_def]

lemma hypercohomologyEquiv_add
    (K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ) (n : ℤ)
    (α β : Hypercohomology structureMap K n) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) (α + β) =
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) α +
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q) β := by
  unfold hypercohomologyAddCommGroup
  simp [Equiv.add_def]

/-- The constant rational class `q` in degree-zero rational cohomology. -/
def fieldCohomologyClass (q : K) : FieldCohomology K structureMap 0 :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms structureMap) 0 rfl
    (integerToFieldConstantSheafComplexInt K structureMap q)

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_zero :
    fieldCohomologyClass K structureMap 0 = 0 := by
  let e : FieldCohomology K structureMap 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K structureMap)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, fieldCohomologyClass, hypercohomologyEquiv_zero,
    integerToFieldConstantSheafComplexInt_zero]

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_add (a b : K) :
    fieldCohomologyClass K structureMap (a + b) =
      fieldCohomologyClass K structureMap a + fieldCohomologyClass K structureMap b := by
  let e : FieldCohomology K structureMap 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K structureMap)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, fieldCohomologyClass, hypercohomologyEquiv_add,
    integerToFieldConstantSheafComplexInt_add]

/-- Rational constants as an additive map into degree-zero rational cohomology. -/
def fieldCohomologyClassAddHom : K →+ FieldCohomology K structureMap 0 where
  toFun := fieldCohomologyClass K structureMap
  map_zero' := fieldCohomologyClass_zero K structureMap
  map_add' := fieldCohomologyClass_add K structureMap

/-- The unit in degree-zero rational cohomology. -/
def fieldCohomologyUnit : FieldCohomology K structureMap 0 :=
  fieldCohomologyClass K structureMap 1

/-- Hypercohomology of the holomorphic de Rham complex in integer degree `n`. -/
abbrev DeRhamHypercohomology [SmoothOfRelativeDimension d structureMap] (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (holomorphicDeRhamComplexInt structureMap d) n

/-- A proved constant-to-holomorphic-de Rham quasi-isomorphism induces the corresponding
equivalence on hypercohomology. -/
def complexConstantCohomologyDeRhamEquiv
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d)) (n : ℤ) :
    ComplexConstantCohomology structureMap n ≃
      DeRhamHypercohomology structureMap d n :=
  Localization.SmallShiftedHom.postcompEquiv
    (constantsToHolomorphicDeRhamComplexInt structureMap d) h

/-- Postcomposition on hypercohomology by a map of complexes. -/
def hypercohomologyMap
    {K L : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ} (f : K ⟶ L) (n : ℤ) :
    Hypercohomology structureMap K n →+ Hypercohomology structureMap L n where
  toFun α := α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms structureMap) 0 rfl f)
      (zero_add n)
  map_zero' := by
    let eL : Hypercohomology structureMap L n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj L) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    apply eL.injective
    rw [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero structureMap K n,
      hypercohomologyEquiv_zero structureMap L n]
    simp

  map_add' α β := by
    let eK : Hypercohomology structureMap K n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj K) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    let eL : Hypercohomology structureMap L n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj L) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    apply eL.injective
    rw [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add structureMap K n,
      hypercohomologyEquiv_add structureMap L n,
      Localization.SmallShiftedHom.equiv_comp,
      Localization.SmallShiftedHom.equiv_comp]
    simp

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma hypercohomologyMap_zero
    {K L : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ} (n : ℤ) :
    hypercohomologyMap structureMap (0 : K ⟶ L) n = 0 := by
  apply AddMonoidHom.ext
  intro α
  let eL : Hypercohomology structureMap L n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj L) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  change (hypercohomologyMap structureMap (0 : K ⟶ L) n) α = 0
  apply eL.injective
  unfold hypercohomologyMap
  simp [eL, Localization.SmallShiftedHom.equiv_comp,
    hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma hypercohomologyMap_id
    {K : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ} (n : ℤ) :
    hypercohomologyMap structureMap (𝟙 K) n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro α
  let eK : Hypercohomology structureMap K n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  change α.comp
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms structureMap) 0 rfl (𝟙 K))
      (zero_add n) = α
  apply eK.injective
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [eK]

lemma complexConstantCohomologyDeRhamEquiv_apply
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d)) (n : ℤ)
    (α : ComplexConstantCohomology structureMap n) :
    complexConstantCohomologyDeRhamEquiv structureMap d h n α =
      hypercohomologyMap structureMap
        (constantsToHolomorphicDeRhamComplexInt structureMap d) n α :=
  rfl

/-- Extension of coefficients from rational to complex constant-sheaf cohomology. -/
def fieldToComplexCohomology (n : ℤ) :
    FieldCohomology K structureMap n →+ ComplexConstantCohomology structureMap n :=
  hypercohomologyMap structureMap
    (fieldToComplexConstantSheafComplexInt K structureMap) n

/-- The cohomological retraction induced by the chosen rational-linear retraction `ℂ → K`. -/
def complexToFieldCohomology (n : ℤ) :
    ComplexConstantCohomology structureMap n →+ FieldCohomology K structureMap n :=
  hypercohomologyMap structureMap
    (complexToFieldConstantSheafComplexInt K structureMap) n

lemma smallShiftedHomMkZero_comp
    {K L M : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms structureMap) (0 : ℤ) rfl (f ≫ g) =
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms structureMap) (0 : ℤ) rfl f).comp
        (Localization.SmallShiftedHom.mk₀
          (analyticQuasiIsomorphisms structureMap) (0 : ℤ) rfl g)
          (zero_add (0 : ℤ)) := by
  let e : Localization.SmallShiftedHom
        (analyticQuasiIsomorphisms structureMap) K M (0 : ℤ) ≃
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [e, Functor.map_comp]

/-- Postcomposition on hypercohomology respects composition of complex maps. -/
lemma hypercohomologyMap_comp_apply
    {K L M : CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ)
    (α : Hypercohomology structureMap K n) :
    hypercohomologyMap structureMap (f ≫ g) n α =
      hypercohomologyMap structureMap g n
        (hypercohomologyMap structureMap f n α) := by
  unfold hypercohomologyMap
  dsimp
  rw [smallShiftedHomMkZero_comp structureMap]
  let β : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms structureMap) K L (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (analyticQuasiIsomorphisms structureMap) (0 : ℤ) rfl f
  let γ : Localization.SmallShiftedHom
      (analyticQuasiIsomorphisms structureMap) L M (0 : ℤ) :=
    Localization.SmallShiftedHom.mk₀
      (analyticQuasiIsomorphisms structureMap) (0 : ℤ) rfl g
  change α.comp (β.comp γ (zero_add (0 : ℤ))) (zero_add n) =
    (α.comp β (zero_add n)).comp γ (zero_add n)
  simpa only using
    (Localization.SmallShiftedHom.comp_assoc
      (analyticQuasiIsomorphisms structureMap) α β γ
      (zero_add n) (zero_add (0 : ℤ)) (zero_add n)).symm

/-- The rational-to-complex cohomology map has the displayed cohomological left inverse. -/
lemma complexToFieldCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToFieldCohomology K structureMap n)
      (fieldToComplexCohomology K structureMap n) := by
  intro α
  unfold complexToFieldCohomology fieldToComplexCohomology
  rw [← hypercohomologyMap_comp_apply structureMap,
    fieldToComplexConstantSheafComplexInt_comp_complexToField,
    hypercohomologyMap_id]
  rfl

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma fieldToComplexCohomology_injective (n : ℤ) :
    Function.Injective (fieldToComplexCohomology K structureMap n) :=
  (complexToFieldCohomology_leftInverse K structureMap n).injective

/-- The rational action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
def fieldCohomologySMul (n : ℤ) (q : K)
    (α : FieldCohomology K structureMap n) : FieldCohomology K structureMap n :=
  hypercohomologyMap structureMap (fieldScalarComplex K structureMap q) n α

noncomputable instance fieldCohomologySMulInstance (n : ℤ) :
    SMul K (FieldCohomology K structureMap n) :=
  ⟨fieldCohomologySMul K structureMap n⟩

omit [Algebra K ℂ] in
lemma field_smul_eq (n : ℤ) (q : K) (α : FieldCohomology K structureMap n) :
    q • α = hypercohomologyMap structureMap
      (fieldScalarComplex K structureMap q) n α := rfl

omit [Algebra K ℂ] in
lemma field_smul_add (n : ℤ) (q : K)
    (α β : FieldCohomology K structureMap n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap structureMap
    (fieldScalarComplex K structureMap q) n).map_add α β

omit [Algebra K ℂ] in
lemma field_add_smul (n : ℤ) (a b : K)
    (α : FieldCohomology K structureMap n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap structureMap
      (fieldScalarComplex K structureMap (a + b)) n α =
    hypercohomologyMap structureMap (fieldScalarComplex K structureMap a) n α +
      hypercohomologyMap structureMap (fieldScalarComplex K structureMap b) n α
  rw [fieldScalarComplex_add]
  let e : FieldCohomology K structureMap n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K structureMap)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

omit [Algebra K ℂ] in
lemma field_one_smul (n : ℤ) (α : FieldCohomology K structureMap n) :
    (1 : K) • α = α := by
  rw [field_smul_eq, fieldScalarComplex_one]
  let e : FieldCohomology K structureMap n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt K structureMap)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

omit [Algebra K ℂ] in
lemma field_mul_smul (n : ℤ) (a b : K)
    (α : FieldCohomology K structureMap n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap structureMap
      (fieldScalarComplex K structureMap (a * b)) n α =
    hypercohomologyMap structureMap (fieldScalarComplex K structureMap a) n
      (hypercohomologyMap structureMap (fieldScalarComplex K structureMap b) n α)
  rw [fieldScalarComplex_mul]
  exact hypercohomologyMap_comp_apply structureMap _ _ n α

/-- Rational constant-sheaf cohomology is canonically a rational vector space. -/
noncomputable instance fieldCohomologyModule (n : ℤ) :
    Module K (FieldCohomology K structureMap n) :=
  Module.ofMinimalAxioms
    (field_smul_add K structureMap n)
    (field_add_smul K structureMap n)
    (field_mul_smul K structureMap n)
    (field_one_smul K structureMap n)

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
def deRhamComplexSMul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology structureMap d n) :
    DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d c) n α

noncomputable instance deRhamComplexSMulInstance
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    SMul ℂ (DeRhamHypercohomology structureMap d n) :=
  ⟨deRhamComplexSMul structureMap d n⟩

lemma deRham_complex_smul_eq [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology structureMap d n) :
    c • α = hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d c) n α :=
  rfl

lemma deRham_complex_smul_add [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (c : ℂ) (α β : DeRhamHypercohomology structureMap d n) :
    c • (α + β) = c • α + c • β := by
  exact (hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d c) n).map_add α β

lemma deRham_complex_add_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : ℂ) (α : DeRhamHypercohomology structureMap d n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (a + b)) n α =
    hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d a) n α +
      hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d b) n α
  rw [scalarHolomorphicDeRhamComplexInt_add]
  let e : DeRhamHypercohomology structureMap d n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt structureMap d)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

lemma deRham_complex_one_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (α : DeRhamHypercohomology structureMap d n) :
    (1 : ℂ) • α = α := by
  rw [deRham_complex_smul_eq, scalarHolomorphicDeRhamComplexInt_one]
  let e : DeRhamHypercohomology structureMap d n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt structureMap d)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma deRham_complex_mul_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : ℂ) (α : DeRhamHypercohomology structureMap d n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (a * b)) n α =
    hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d a) n
      (hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d b) n α)
  rw [scalarHolomorphicDeRhamComplexInt_mul]
  exact hypercohomologyMap_comp_apply structureMap _ _ n α

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance deRhamHypercohomologyComplexModule
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Module ℂ (DeRhamHypercohomology structureMap d n) :=
  Module.ofMinimalAxioms
    (deRham_complex_smul_add structureMap d n)
    (deRham_complex_add_smul structureMap d n)
    (deRham_complex_mul_smul structureMap d n)
    (deRham_complex_one_smul structureMap d n)

/-- The rational action on de Rham hypercohomology, induced by multiplication by the corresponding
complex scalar on the de Rham complex. -/
def deRhamFieldSMul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : K) (α : DeRhamHypercohomology structureMap d n) :
    DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q)) n α

noncomputable instance deRhamFieldSMulInstance
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    SMul K (DeRhamHypercohomology structureMap d n) :=
  ⟨deRhamFieldSMul K structureMap d n⟩

lemma deRham_field_smul_eq [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : K) (α : DeRhamHypercohomology structureMap d n) :
    q • α = hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q)) n α :=
  rfl

lemma deRham_field_smul_add [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : K) (α β : DeRhamHypercohomology structureMap d n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q)) n).map_add α β

lemma deRham_field_add_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : K) (α : DeRhamHypercohomology structureMap d n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ (a + b))) n α =
    hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ a)) n α +
      hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ b)) n α
  rw [map_add, scalarHolomorphicDeRhamComplexInt_add]
  let e : DeRhamHypercohomology structureMap d n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt structureMap d)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

lemma deRham_field_one_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (α : DeRhamHypercohomology structureMap d n) :
    (1 : K) • α = α := by
  rw [deRham_field_smul_eq, map_one,
    scalarHolomorphicDeRhamComplexInt_one]
  let e : DeRhamHypercohomology structureMap d n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt structureMap d)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma deRham_field_mul_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : K) (α : DeRhamHypercohomology structureMap d n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ (a * b))) n α =
    hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ a)) n
      (hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ b)) n α)
  rw [map_mul, scalarHolomorphicDeRhamComplexInt_mul]
  exact hypercohomologyMap_comp_apply structureMap _ _ n α

/-- Holomorphic de Rham hypercohomology is canonically a rational vector space. -/
noncomputable instance deRhamHypercohomologyModule
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Module K (DeRhamHypercohomology structureMap d n) :=
  Module.ofMinimalAxioms
    (deRham_field_smul_add K structureMap d n)
    (deRham_field_add_smul K structureMap d n)
    (deRham_field_mul_smul K structureMap d n)
    (deRham_field_one_smul K structureMap d n)

/-- The independently constructed rational and complex scalar actions on de Rham
hypercohomology agree through the canonical embedding `K → ℂ`. -/
lemma deRham_field_smul_eq_complex_smul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (q : K) (α : DeRhamHypercohomology structureMap d n) :
    q • α = (algebraMap K ℂ q) • α :=
  rfl

/-- Rational, complex, and de Rham scalar multiplication form the expected scalar tower. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    IsScalarTower K ℂ (DeRhamHypercohomology structureMap d n) :=
  IsScalarTower.of_algebraMap_smul fun q α =>
    deRham_field_smul_eq_complex_smul K structureMap d n q α

omit [Algebra K ℂ] in
/-- Constant degree-zero cohomology classes respect rational scalar multiplication. -/
lemma fieldCohomologyClass_mul (q r : K) :
    fieldCohomologyClass K structureMap (q * r) =
      q • fieldCohomologyClass K structureMap r := by
  rw [field_smul_eq]
  unfold fieldCohomologyClass hypercohomologyMap
  dsimp
  rw [← smallShiftedHomMkZero_comp structureMap,
    integerToFieldConstantSheafComplexInt_comp_fieldScalarComplex]

/-- Rational constants map rational-linearly to degree-zero rational cohomology. -/
def fieldCohomologyClassLinear : K →ₗ[K] FieldCohomology K structureMap 0 where
  toFun := fieldCohomologyClass K structureMap
  map_add' := fieldCohomologyClass_add K structureMap
  map_smul' q r := fieldCohomologyClass_mul K structureMap q r

/-- The derived comparison from rational cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamCohomology [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    FieldCohomology K structureMap n →+ DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap
    (fieldToHolomorphicDeRhamComplexInt K structureMap d) n

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma fieldToDeRhamCohomology_factor
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : FieldCohomology K structureMap n) :
    fieldToDeRhamCohomology K structureMap d n α =
      hypercohomologyMap structureMap
        (constantsToHolomorphicDeRhamComplexInt structureMap d) n
        (fieldToComplexCohomology K structureMap n α) := by
  unfold fieldToDeRhamCohomology fieldToComplexCohomology
    fieldToHolomorphicDeRhamComplexInt
  exact hypercohomologyMap_comp_apply structureMap
    (fieldToComplexConstantSheafComplexInt K structureMap)
    (constantsToHolomorphicDeRhamComplexInt structureMap d) n α

/-- Once the analytic Poincare comparison is proved to be a quasi-isomorphism, the
rational-to-de Rham comparison is injective. This uses the explicit splitting of `K → ℂ`, not a
finite-dimensionality assumption. -/
lemma fieldToDeRhamCohomology_injective_of_quasiIso
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d)) (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K structureMap d n) := by
  intro α β hαβ
  apply fieldToComplexCohomology_injective K structureMap n
  apply (complexConstantCohomologyDeRhamEquiv structureMap d h n).injective
  simpa only [complexConstantCohomologyDeRhamEquiv_apply,
    fieldToDeRhamCohomology_factor K structureMap d n] using hαβ

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit coefficient splitting proves that extending
scalars from `K` to `ℂ` is injective. -/
lemma fieldToDeRhamCohomology_injective
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K structureMap d n) :=
  fieldToDeRhamCohomology_injective_of_quasiIso K structureMap d inferInstance n

/-- The rational-to-de Rham comparison is compatible with rational scalar multiplication. -/
lemma fieldToDeRhamCohomology_smul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (q : K) (α : FieldCohomology K structureMap n) :
    fieldToDeRhamCohomology K structureMap d n (q • α) =
      q • fieldToDeRhamCohomology K structureMap d n α := by
  rw [field_smul_eq, deRham_field_smul_eq]
  unfold fieldToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [fieldToHolomorphicDeRhamComplexInt_scalar]

/-- The rational-to-de Rham comparison as a rational-linear map. -/
def fieldToDeRhamCohomologyLinear
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    FieldCohomology K structureMap n →ₗ[K]
      DeRhamHypercohomology structureMap d n where
  toFun := fieldToDeRhamCohomology K structureMap d n
  map_add' := (fieldToDeRhamCohomology K structureMap d n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K structureMap d n

/-- The balanced map that extends rational-to-de Rham comparison after scalar extension from
`K` to `ℂ`. -/
def fieldToDeRhamComplexificationBilinear
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    ℂ →ₗ[ℂ] FieldCohomology K structureMap n →ₗ[K]
      DeRhamHypercohomology structureMap d n where
  toFun c := c • (fieldToDeRhamCohomologyLinear K structureMap d n)
  map_add' a b := by
    ext α
    simp [add_smul]
  map_smul' a b := by
    ext α
    simp [mul_smul]

/-- The canonical complex-linear comparison from the complexification of rational
constant-sheaf cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamComplexification
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    ℂ ⊗[K] FieldCohomology K structureMap n →ₗ[ℂ]
      DeRhamHypercohomology structureMap d n :=
  TensorProduct.AlgebraTensorModule.lift
    (fieldToDeRhamComplexificationBilinear K structureMap d n)

@[simp] lemma fieldToDeRhamComplexification_tmul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (c : ℂ) (α : FieldCohomology K structureMap n) :
    fieldToDeRhamComplexification K structureMap d n (c ⊗ₜ[K] α) =
      c • fieldToDeRhamCohomology K structureMap d n α :=
  rfl

/-- On the rational lattice, the complexified comparison agrees with the original map. -/
@[simp] lemma fieldToDeRhamComplexification_ofField
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : FieldCohomology K structureMap n) :
    fieldToDeRhamComplexification K structureMap d n (1 ⊗ₜ[K] α) =
      fieldToDeRhamCohomology K structureMap d n α := by
  simp

/-- The de Rham complex with only form degrees at least `p` retained. -/
def hodgeFilteredDeRhamComplex [SmoothOfRelativeDimension d structureMap] (p : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  (holomorphicDeRhamComplexInt structureMap d).stupidTrunc
    (ComplexShape.embeddingUpIntGE p)

/-- The part of the holomorphic de Rham complex in form degrees at least `p` is zero when `p`
is above the complex dimension. -/
lemma hodgeFilteredDeRhamComplex_isZero_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℤ} (hp : (d : ℤ) < p) :
    IsZero (hodgeFilteredDeRhamComplex structureMap d p) := by
  rw [hodgeFilteredDeRhamComplex,
    HomologicalComplex.isZero_stupidTrunc_iff]
  refine ⟨fun n => ?_⟩
  change IsZero ((holomorphicDeRhamComplexInt structureMap d).X (p + n))
  exact (holomorphicDeRhamComplexInt structureMap d).isZero_of_isStrictlyLE
    d (p + n) (by lia)

/-- Inclusion of the degree-at-least-`p` de Rham complex into the full complex. -/
def hodgeFilteredDeRhamInclusion [SmoothOfRelativeDimension d structureMap] (p : ℤ) :
    hodgeFilteredDeRhamComplex structureMap d p ⟶
      holomorphicDeRhamComplexInt structureMap d :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamComplexInt structureMap d) (ComplexShape.embeddingUpIntGE p)

/-- Above the complex dimension the filtered-to-full inclusion has zero source and hence is the
zero morphism. -/
lemma hodgeFilteredDeRhamInclusion_eq_zero_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℤ} (hp : (d : ℤ) < p) :
    hodgeFilteredDeRhamInclusion structureMap d p = 0 :=
  (hodgeFilteredDeRhamComplex_isZero_of_lt structureMap d hp).eq_of_src _ _

/-- Rational scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamScalar [SmoothOfRelativeDimension d structureMap]
    (p : ℤ) (q : K) :
    hodgeFilteredDeRhamComplex structureMap d p ⟶
      hodgeFilteredDeRhamComplex structureMap d p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q))
    (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamComplexScalar [SmoothOfRelativeDimension d structureMap]
    (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplex structureMap d p ⟶
      hodgeFilteredDeRhamComplex structureMap d p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt structureMap d c)
    (ComplexShape.embeddingUpIntGE p)

/-- Scalar multiplication on the filtered complex commutes with its inclusion into the full de
Rham complex. -/
lemma hodgeFilteredDeRhamScalar_comp_inclusion
    [SmoothOfRelativeDimension d structureMap] (p : ℤ) (q : K) :
    hodgeFilteredDeRhamScalar K structureMap d p q ≫
      hodgeFilteredDeRhamInclusion structureMap d p =
    hodgeFilteredDeRhamInclusion structureMap d p ≫
      scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q) := by
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt structureMap d (algebraMap K ℂ q))

/-- Complex scalar multiplication on the filtered complex commutes with inclusion into the full
de Rham complex. -/
lemma hodgeFilteredDeRhamComplexScalar_comp_inclusion
    [SmoothOfRelativeDimension d structureMap] (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar structureMap d p c ≫
      hodgeFilteredDeRhamInclusion structureMap d p =
    hodgeFilteredDeRhamInclusion structureMap d p ≫
      scalarHolomorphicDeRhamComplexInt structureMap d c := by
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt structureMap d c)

/-- Hypercohomology of the degree-at-least-`p` part of the de Rham complex. -/
abbrev FilteredDeRhamHypercohomology [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) : Type 1 :=
  Hypercohomology structureMap (hodgeFilteredDeRhamComplex structureMap d p) n

/-- The map from filtered to full de Rham hypercohomology. -/
def filteredToDeRhamCohomology [SmoothOfRelativeDimension d structureMap] (p n : ℤ) :
    FilteredDeRhamHypercohomology structureMap d p n →+
      DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap (hodgeFilteredDeRhamInclusion structureMap d p) n

/-- The Hodge filtration `F^p` on de Rham hypercohomology. -/
def hodgeFiltration [SmoothOfRelativeDimension d structureMap] (p n : ℤ) :
    AddSubgroup (DeRhamHypercohomology structureMap d n) :=
  (filteredToDeRhamCohomology structureMap d p n).range

/-- The Hodge filtration is zero above the complex dimension. -/
lemma hodgeFiltration_eq_bot_of_lt [SmoothOfRelativeDimension d structureMap]
    {p : ℤ} (hp : (d : ℤ) < p) (n : ℤ) :
    hodgeFiltration structureMap d p n = ⊥ := by
  rw [hodgeFiltration]
  change (hypercohomologyMap structureMap
    (hodgeFilteredDeRhamInclusion structureMap d p) n).range = ⊥
  rw [hodgeFilteredDeRhamInclusion_eq_zero_of_lt structureMap d hp,
    hypercohomologyMap_zero]
  simp

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma hodgeFiltration_complex_smul_mem [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) (c : ℂ) {α : DeRhamHypercohomology structureMap d n}
    (hα : α ∈ hodgeFiltration structureMap d p n) :
    c • α ∈ hodgeFiltration structureMap d p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨hypercohomologyMap structureMap
    (hodgeFilteredDeRhamComplexScalar structureMap d p c) n β, ?_⟩
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

/-- The Hodge filtration bundled as a complex subspace of de Rham hypercohomology. -/
def hodgeFiltrationComplexSubmodule [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology structureMap d n) where
  carrier := hodgeFiltration structureMap d p n
  zero_mem' := (hodgeFiltration structureMap d p n).zero_mem
  add_mem' := (hodgeFiltration structureMap d p n).add_mem
  smul_mem' := fun c _ h => hodgeFiltration_complex_smul_mem structureMap d p n c h

/-- Pull back the de Rham Hodge filtration to the actual complexification of rational
constant-sheaf cohomology. This definition uses the canonical comparison map rather than
identifying the two cohomology theories without proof. -/
def complexifiedFieldHodgeFiltration [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) :
    Submodule ℂ (ℂ ⊗[K] FieldCohomology K structureMap n) :=
  (hodgeFiltrationComplexSubmodule structureMap d p n).comap
    (fieldToDeRhamComplexification K structureMap d n)

/-- The Hodge filtration is stable under rational scalar multiplication. -/
lemma hodgeFiltration_smul_mem [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) (q : K) {α : DeRhamHypercohomology structureMap d n}
    (hα : α ∈ hodgeFiltration structureMap d p n) :
    q • α ∈ hodgeFiltration structureMap d p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨hypercohomologyMap structureMap
    (hodgeFilteredDeRhamScalar K structureMap d p q) n β, ?_⟩
  rw [deRham_field_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamScalar_comp_inclusion]

/-- The Hodge filtration bundled as a rational subspace of de Rham hypercohomology. -/
def hodgeFiltrationSubmodule [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) : Submodule K (DeRhamHypercohomology structureMap d n) where
  carrier := hodgeFiltration structureMap d p n
  zero_mem' := (hodgeFiltration structureMap d p n).zero_mem
  add_mem' := (hodgeFiltration structureMap d p n).add_mem
  smul_mem' := fun q _ h => hodgeFiltration_smul_mem K structureMap d p n q h

/-- In degree filtration `F⁰`, the filtered and full de Rham hypercohomology groups are
canonically equivalent. -/
def hodgeFiltrationZeroEquiv [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    FilteredDeRhamHypercohomology structureMap d 0 n ≃
      DeRhamHypercohomology structureMap d n := by
  letI : (holomorphicDeRhamComplexInt structureMap d).IsStrictlyGE 0 := by
    unfold holomorphicDeRhamComplexInt
    infer_instance
  letI : IsIso (hodgeFilteredDeRhamInclusion structureMap d 0) := by
    unfold hodgeFilteredDeRhamInclusion hodgeFilteredDeRhamComplex
    infer_instance
  exact Localization.SmallShiftedHom.postcompEquiv
    (hodgeFilteredDeRhamInclusion structureMap d 0)
    (by
      change QuasiIso (hodgeFilteredDeRhamInclusion structureMap d 0)
      infer_instance)

lemma filteredToDeRhamCohomology_zero_apply
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : FilteredDeRhamHypercohomology structureMap d 0 n) :
    filteredToDeRhamCohomology structureMap d 0 n α =
      hodgeFiltrationZeroEquiv structureMap d n α := rfl

/-- The zeroth Hodge filtration is the whole de Rham hypercohomology group. -/
lemma hodgeFiltration_zero_eq_top [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    hodgeFiltration structureMap d 0 n = ⊤ := by
  ext α
  simp only [hodgeFiltration, AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
  exact ⟨(hodgeFiltrationZeroEquiv structureMap d n).symm α,
    filteredToDeRhamCohomology_zero_apply structureMap d n _ |>.trans
      ((hodgeFiltrationZeroEquiv structureMap d n).apply_symm_apply α)⟩

/-- The rational submodule underlying `F⁰` is the whole de Rham hypercohomology group. -/
lemma hodgeFiltrationSubmodule_zero_eq_top
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    hodgeFiltrationSubmodule K structureMap d 0 n = ⊤ := by
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration structureMap d 0 n ↔ α ∈ (⊤ :
    Submodule K (DeRhamHypercohomology structureMap d n))
  rw [hodgeFiltration_zero_eq_top structureMap d n]
  simp

/-- Rational cohomology classes whose de Rham images lie in `F^p H^{2p}`, bundled as an additive
subgroup. -/
def hodgeClasses [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    Submodule K (FieldCohomology K structureMap (2 * p)) :=
  (hodgeFiltrationSubmodule K structureMap d p (2 * p)).comap
    (fieldToDeRhamCohomologyLinear K structureMap d (2 * p))

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma hodgeClasses_eq_ker_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    hodgeClasses K structureMap d p =
      LinearMap.ker (fieldToDeRhamCohomologyLinear K structureMap d (2 * p)) := by
  rw [hodgeClasses, ← Submodule.comap_bot]
  congr 1
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration structureMap d (p : ℤ) (2 * (p : ℤ)) ↔ α ∈ (⊥ :
    Submodule ℂ (DeRhamHypercohomology structureMap d (2 * (p : ℤ))))
  rw [hodgeFiltration_eq_bot_of_lt structureMap d (by exact_mod_cast hp)]
  rfl

/-- If the analytic constant-to-holomorphic de Rham comparison is a quasi-isomorphism, rational
Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt_of_quasiIso
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d))
    {p : ℕ} (hp : d < p) :
    hodgeClasses K structureMap d p = ⊥ := by
  rw [hodgeClasses_eq_ker_of_lt K structureMap d hp]
  apply LinearMap.ker_eq_bot.mpr
  exact fieldToDeRhamCohomology_injective_of_quasiIso K structureMap d h (2 * p)

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    hodgeClasses K structureMap d p = ⊥ :=
  hodgeClasses_eq_bot_of_lt_of_quasiIso K structureMap d inferInstance hp

/-- Rational Hodge classes described through the rational lattice inside its actual
complexification. -/
def hodgeClassesViaComplexification
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    Submodule K (FieldCohomology K structureMap (2 * p)) :=
  Submodule.comap
    (HodgeStructure.ofBase K (FieldCohomology K structureMap (2 * p)))
    ((complexifiedFieldHodgeFiltration K structureMap d p (2 * p)).restrictScalars K)

/-- The direct definition of rational Hodge classes agrees with the definition using the
complexified rational lattice. -/
lemma hodgeClassesViaComplexification_eq
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    hodgeClassesViaComplexification K structureMap d p =
      hodgeClasses K structureMap d p := by
  ext α
  change fieldToDeRhamComplexification K structureMap d (2 * (p : ℤ))
      (HodgeStructure.ofBase K
        (FieldCohomology K structureMap (2 * (p : ℤ))) α) ∈
        hodgeFiltration structureMap d p (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K structureMap d (2 * (p : ℤ)) α ∈
      hodgeFiltration structureMap d p (2 * (p : ℤ))
  rw [HodgeStructure.ofBase_apply,
    fieldToDeRhamComplexification_ofField]

/-- A rational cohomology class is a Hodge class of codimension `p` when it belongs to the
canonical subgroup of rational Hodge classes. -/
def IsHodgeClass [SmoothOfRelativeDimension d structureMap] (p : ℕ)
    (α : FieldCohomology K structureMap (2 * p)) : Prop :=
  α ∈ hodgeClasses K structureMap d p

lemma mem_hodgeClasses_iff [SmoothOfRelativeDimension d structureMap]
    (p : ℕ) (α : FieldCohomology K structureMap (2 * p)) :
    α ∈ hodgeClasses K structureMap d p ↔
      IsHodgeClass K structureMap d p α :=
  Iff.rfl

/-- Every rational degree-zero cohomology class belongs to the rational Hodge subgroup. -/
lemma hodgeClasses_zero_eq_top [SmoothOfRelativeDimension d structureMap] :
    hodgeClasses K structureMap d 0 = ⊤ := by
  apply SetLike.ext
  intro α
  change fieldToDeRhamCohomology K structureMap d (2 * (0 : ℕ)) α ∈
      hodgeFiltration structureMap d (0 : ℕ) (2 * (0 : ℕ)) ↔ True
  simp only [Nat.cast_zero]
  rw [hodgeFiltration_zero_eq_top]
  trivial

/-- Every rational degree-zero class has Hodge type `(0,0)`. -/
lemma isHodgeClass_zero [SmoothOfRelativeDimension d structureMap]
    (α : FieldCohomology K structureMap 0) :
    IsHodgeClass K structureMap d 0 α := by
  change α ∈ hodgeClasses K structureMap d 0
  rw [hodgeClasses_zero_eq_top]
  trivial

end AlgebraicGeometry.ComplexPoint
