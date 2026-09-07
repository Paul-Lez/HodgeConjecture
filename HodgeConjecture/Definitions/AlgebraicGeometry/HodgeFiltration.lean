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
public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Definitions.LinearAlgebra.HodgeStructure
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

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

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
def constantRationalSheaf : AnalyticAdditiveSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℚ)

/-- The inclusion of the rational constant sheaf into the complex constant sheaf. -/
def rationalToComplexConstantSheaf :
    constantRationalSheaf structureMap ⟶ constantComplexSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom)

/-- The inclusion of `ℚ` into `ℂ`, regarded as a rational-linear map. -/
def rationalToComplexLinear : ℚ →ₗ[ℚ] ℂ :=
  Algebra.linearMap ℚ ℂ

/-- A rational-linear retraction of the inclusion `ℚ → ℂ`. Such a retraction exists because an
injective linear map of vector spaces over a field splits. -/
noncomputable def complexToRationalLinear : ℂ →ₗ[ℚ] ℚ :=
  Classical.choose <| (rationalToComplexLinear).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Rat.cast_injective)

/-- The chosen rational-linear retraction is a left inverse to `ℚ → ℂ`. -/
lemma complexToRationalLinear_comp_rationalToComplexLinear :
    complexToRationalLinear ∘ₗ rationalToComplexLinear = LinearMap.id :=
  Classical.choose_spec <| (rationalToComplexLinear).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Rat.cast_injective)

@[simp] lemma complexToRationalLinear_cast (q : ℚ) :
    complexToRationalLinear (q : ℂ) = q := by
  have h := LinearMap.congr_fun complexToRationalLinear_comp_rationalToComplexLinear q
  simpa [rationalToComplexLinear] using h

/-- The chosen rational-linear retraction, applied to the complex constant sheaf. -/
def complexToRationalConstantSheaf :
    constantComplexSheaf structureMap ⟶ constantRationalSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom complexToRationalLinear.toAddMonoidHom)

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma rationalToComplexConstantSheaf_comp_complexToRationalConstantSheaf :
    rationalToComplexConstantSheaf structureMap ≫
      complexToRationalConstantSheaf structureMap = 𝟙 _ := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom complexToRationalLinear.toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom complexToRationalLinear.toAddMonoidHom =
      𝟙 (AddCommGrpCat.of ℚ) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro q
    exact complexToRationalLinear_cast q
  rw [h]
  exact (constantSheaf J AddCommGrpCat).map_id (AddCommGrpCat.of ℚ)

/-- The constant rational sheaf complex, extended by zero to integer degrees. -/
def constantRationalSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
    (constantRationalSheaf structureMap)).extend ComplexShape.embeddingUpNat

/-- Extension of rational constants to complex constants as a map of integer complexes. -/
def rationalToComplexConstantSheafComplexInt :
    constantRationalSheafComplexInt structureMap ⟶
      constantComplexSheafComplexInt structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (rationalToComplexConstantSheaf structureMap)) ComplexShape.embeddingUpNat

/-- The chosen retraction from the complex constant sheaf complex to the rational one. -/
def complexToRationalConstantSheafComplexInt :
    constantComplexSheafComplexInt structureMap ⟶
      constantRationalSheafComplexInt structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (complexToRationalConstantSheaf structureMap)) ComplexShape.embeddingUpNat

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma rationalToComplexConstantSheafComplexInt_comp_complexToRational :
    rationalToComplexConstantSheafComplexInt structureMap ≫
      complexToRationalConstantSheafComplexInt structureMap = 𝟙 _ := by
  unfold rationalToComplexConstantSheafComplexInt
    complexToRationalConstantSheafComplexInt constantRationalSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    rationalToComplexConstantSheaf_comp_complexToRationalConstantSheaf]
  have hmap : (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (𝟙 (constantRationalSheaf structureMap)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantRationalSheaf structureMap)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map_id _
  rw [hmap]
  exact HomologicalComplex.extendMap_id _ _

/-- Rational constants mapped canonically into the holomorphic de Rham complex. -/
def rationalToHolomorphicDeRhamComplexInt [SmoothOfRelativeDimension d structureMap] :
    constantRationalSheafComplexInt structureMap ⟶
      holomorphicDeRhamComplexInt structureMap d :=
  rationalToComplexConstantSheafComplexInt structureMap ≫
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
def integerMultipleAddHom (q : ℚ) : ℤ →+ ℚ where
  toFun n := n * q
  map_zero' := by simp
  map_add' a b := by push_cast; ring

@[simp] lemma integerMultipleAddHom_zero : integerMultipleAddHom 0 = 0 := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom]

@[simp] lemma integerMultipleAddHom_add (a b : ℚ) :
    integerMultipleAddHom (a + b) = integerMultipleAddHom a + integerMultipleAddHom b := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom, mul_add]

/-- A rational number as a morphism from the integer to the rational constant sheaf. -/
def integerToRationalConstantSheaf (q : ℚ) :
    constantIntegerSheaf structureMap ⟶ constantRationalSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map (AddCommGrpCat.ofHom (integerMultipleAddHom q))

@[simp] lemma integerToRationalConstantSheaf_zero :
    integerToRationalConstantSheaf structureMap 0 = 0 := by
  unfold integerToRationalConstantSheaf
  rw [integerMultipleAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ ℚ) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

@[simp] lemma integerToRationalConstantSheaf_add (a b : ℚ) :
    integerToRationalConstantSheaf structureMap (a + b) =
      integerToRationalConstantSheaf structureMap a +
        integerToRationalConstantSheaf structureMap b := by
  unfold integerToRationalConstantSheaf
  rw [integerMultipleAddHom_add]
  have h : AddCommGrpCat.ofHom
      (integerMultipleAddHom a + integerMultipleAddHom b) =
      AddCommGrpCat.ofHom (integerMultipleAddHom a) +
        AddCommGrpCat.ofHom (integerMultipleAddHom b) := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_add]
  rfl

/-- A rational number as a morphism of constant complexes. -/
def integerToRationalConstantSheafComplexInt (q : ℚ) :
    constantIntegerSheafComplexInt structureMap ⟶
      constantRationalSheafComplexInt structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (integerToRationalConstantSheaf structureMap q)) ComplexShape.embeddingUpNat

@[simp] lemma integerToRationalConstantSheafComplexInt_zero :
    integerToRationalConstantSheafComplexInt structureMap 0 = 0 := by
  unfold integerToRationalConstantSheafComplexInt
  rw [integerToRationalConstantSheaf_zero, Functor.map_zero,
    HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma integerToRationalConstantSheafComplexInt_add (a b : ℚ) :
    integerToRationalConstantSheafComplexInt structureMap (a + b) =
      integerToRationalConstantSheafComplexInt structureMap a +
        integerToRationalConstantSheafComplexInt structureMap b := by
  unfold integerToRationalConstantSheafComplexInt
  rw [integerToRationalConstantSheaf_add, Functor.map_add,
    HomologicalComplex.extendMap_add]
  rfl

/-- Multiplication by a rational scalar as an additive endomorphism of `ℚ`. -/
def rationalScalarAddHom (q : ℚ) : ℚ →+ ℚ :=
  DistribSMul.toAddMonoidHom ℚ q

@[simp] lemma rationalScalarAddHom_apply (q x : ℚ) :
    rationalScalarAddHom q x = q * x := rfl

@[simp] lemma rationalScalarAddHom_zero : rationalScalarAddHom 0 = 0 := by
  ext
  simp

@[simp] lemma rationalScalarAddHom_one : rationalScalarAddHom 1 = AddMonoidHom.id ℚ := by
  ext
  simp

@[simp] lemma rationalScalarAddHom_add (a b : ℚ) :
    rationalScalarAddHom (a + b) = rationalScalarAddHom a + rationalScalarAddHom b := by
  ext
  simp [add_mul]

@[simp] lemma rationalScalarAddHom_mul (a b : ℚ) :
    rationalScalarAddHom (a * b) =
      (rationalScalarAddHom a).comp (rationalScalarAddHom b) := by
  ext
  simp [rationalScalarAddHom, mul_assoc]

/-- Scalar multiplication on the rational constant sheaf. -/
def rationalScalarSheaf (q : ℚ) :
    constantRationalSheaf structureMap ⟶ constantRationalSheaf structureMap :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).map
    (AddCommGrpCat.ofHom (rationalScalarAddHom q))

@[simp] lemma rationalScalarSheaf_zero : rationalScalarSheaf structureMap 0 = 0 := by
  unfold rationalScalarSheaf
  rw [rationalScalarAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : ℚ →+ ℚ) = 0 := by
    apply AddCommGrpCat.hom_ext
    rfl
  rw [h, Functor.map_zero]
  rfl

@[simp] lemma rationalScalarSheaf_one : rationalScalarSheaf structureMap 1 = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.id ℚ) = 𝟙 (AddCommGrpCat.of ℚ) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map (AddCommGrpCat.ofHom (rationalScalarAddHom 1)) =
    𝟙 ((constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).obj (AddCommGrpCat.of ℚ))
  rw [rationalScalarAddHom_one, h]
  exact (constantSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    AddCommGrpCat).map_id (AddCommGrpCat.of ℚ)

@[simp] lemma rationalScalarSheaf_add (a b : ℚ) :
    rationalScalarSheaf structureMap (a + b) =
      rationalScalarSheaf structureMap a + rationalScalarSheaf structureMap b := by
  have h : AddCommGrpCat.ofHom (rationalScalarAddHom a + rationalScalarAddHom b) =
      AddCommGrpCat.ofHom (rationalScalarAddHom a) +
        AddCommGrpCat.ofHom (rationalScalarAddHom b) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (rationalScalarAddHom (a + b))) = _
  rw [rationalScalarAddHom_add, h, Functor.map_add]
  rfl

@[simp] lemma rationalScalarSheaf_mul (a b : ℚ) :
    rationalScalarSheaf structureMap (a * b) =
      rationalScalarSheaf structureMap b ≫ rationalScalarSheaf structureMap a := by
  have h : AddCommGrpCat.ofHom
      ((rationalScalarAddHom a).comp (rationalScalarAddHom b)) =
      AddCommGrpCat.ofHom (rationalScalarAddHom b) ≫
        AddCommGrpCat.ofHom (rationalScalarAddHom a) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
        (AddCommGrpCat.ofHom (rationalScalarAddHom (a * b))) = _
  rw [rationalScalarAddHom_mul, h, Functor.map_comp]
  rfl

/-- The inclusion of rational constants into complex constants commutes with scalar
multiplication. -/
lemma rationalToComplexConstantSheaf_scalar (q : ℚ) :
    rationalToComplexConstantSheaf structureMap ≫
      complexScalarSheaf structureMap (q : ℂ) =
    rationalScalarSheaf structureMap q ≫
      rationalToComplexConstantSheaf structureMap := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf structureMap (q : ℂ)) =
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (rationalScalarAddHom q)) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom)
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (Rat.castHom ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (complexScalarAddHom (q : ℂ))) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro r
  change (q : ℂ) * (r : ℂ) = ((q * r : ℚ) : ℂ)
  push_cast
  rfl

/-- Applying a rational scalar after the constant class `r` gives the constant class `q * r`. -/
lemma integerToRationalConstantSheaf_comp_rationalScalarSheaf (q r : ℚ) :
    integerToRationalConstantSheaf structureMap r ≫
      rationalScalarSheaf structureMap q =
        integerToRationalConstantSheaf structureMap (q * r) := by
  unfold integerToRationalConstantSheaf rationalScalarSheaf
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom r)) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (rationalScalarAddHom q)) =
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom (q * r)))
  rw [← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom, rationalScalarAddHom]
  ring

/-- Scalar multiplication on the rational constant sheaf complex. -/
def rationalScalarComplex (q : ℚ) :
    constantRationalSheafComplexInt structureMap ⟶
      constantRationalSheafComplexInt structureMap :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (rationalScalarSheaf structureMap q)) ComplexShape.embeddingUpNat

@[simp] lemma rationalScalarComplex_zero : rationalScalarComplex structureMap 0 = 0 := by
  unfold rationalScalarComplex
  rw [rationalScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma rationalScalarComplex_one : rationalScalarComplex structureMap 1 = 𝟙 _ := by
  unfold rationalScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (rationalScalarSheaf structureMap 1)) ComplexShape.embeddingUpNat =
    𝟙 (HomologicalComplex.extend
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantRationalSheaf structureMap)) ComplexShape.embeddingUpNat)
  rw [rationalScalarSheaf_one]
  have hm : (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (𝟙 (constantRationalSheaf structureMap)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantRationalSheaf structureMap)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map_id _
  rw [hm]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma rationalScalarComplex_add (a b : ℚ) :
    rationalScalarComplex structureMap (a + b) =
      rationalScalarComplex structureMap a + rationalScalarComplex structureMap b := by
  unfold rationalScalarComplex
  rw [rationalScalarSheaf_add, Functor.map_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma rationalScalarComplex_mul (a b : ℚ) :
    rationalScalarComplex structureMap (a * b) =
      rationalScalarComplex structureMap b ≫ rationalScalarComplex structureMap a := by
  unfold rationalScalarComplex
  rw [rationalScalarSheaf_mul, Functor.map_comp, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed inclusion of rational constants into complex constants commutes with
scalar multiplication. -/
lemma rationalToComplexConstantSheafComplexInt_scalar (q : ℚ) :
    rationalToComplexConstantSheafComplexInt structureMap ≫
      complexScalarComplexInt structureMap (q : ℂ) =
    rationalScalarComplex structureMap q ≫
      rationalToComplexConstantSheafComplexInt structureMap := by
  unfold rationalToComplexConstantSheafComplexInt complexScalarComplexInt
    rationalScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (rationalToComplexConstantSheaf structureMap)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (complexScalarSheaf structureMap (q : ℂ))) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (rationalScalarSheaf structureMap q)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (rationalToComplexConstantSheaf structureMap)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ← Functor.map_comp, ← Functor.map_comp,
    rationalToComplexConstantSheaf_scalar]

/-- The rational-to-de Rham comparison of complexes commutes with rational scalar
multiplication. -/
lemma rationalToHolomorphicDeRhamComplexInt_scalar
    [SmoothOfRelativeDimension d structureMap] (q : ℚ) :
    rationalToHolomorphicDeRhamComplexInt structureMap d ≫
      scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ) =
    rationalScalarComplex structureMap q ≫
      rationalToHolomorphicDeRhamComplexInt structureMap d := by
  unfold rationalToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar]
  rw [← Category.assoc,
    rationalToComplexConstantSheafComplexInt_scalar, Category.assoc]

/-- Scalar multiplication after an integer-to-rational constant-complex map multiplies its
rational coefficient. -/
lemma integerToRationalConstantSheafComplexInt_comp_rationalScalarComplex (q r : ℚ) :
    integerToRationalConstantSheafComplexInt structureMap r ≫
      rationalScalarComplex structureMap q =
        integerToRationalConstantSheafComplexInt structureMap (q * r) := by
  unfold integerToRationalConstantSheafComplexInt rationalScalarComplex
  change HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (integerToRationalConstantSheaf structureMap r)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (rationalScalarSheaf structureMap q)) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      ((CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
        (integerToRationalConstantSheaf structureMap (q * r))) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    integerToRationalConstantSheaf_comp_rationalScalarSheaf]

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
abbrev RationalCohomology (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (constantRationalSheafComplexInt structureMap) n

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
def rationalCohomologyClass (q : ℚ) : RationalCohomology structureMap 0 :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms structureMap) 0 rfl
    (integerToRationalConstantSheafComplexInt structureMap q)

@[simp] lemma rationalCohomologyClass_zero :
    rationalCohomologyClass structureMap 0 = 0 := by
  let e : RationalCohomology structureMap 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, rationalCohomologyClass, hypercohomologyEquiv_zero,
    integerToRationalConstantSheafComplexInt_zero]

@[simp] lemma rationalCohomologyClass_add (a b : ℚ) :
    rationalCohomologyClass structureMap (a + b) =
      rationalCohomologyClass structureMap a + rationalCohomologyClass structureMap b := by
  let e : RationalCohomology structureMap 0 ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) (0 : ℤ) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, rationalCohomologyClass, hypercohomologyEquiv_add,
    integerToRationalConstantSheafComplexInt_add]

/-- Rational constants as an additive map into degree-zero rational cohomology. -/
def rationalCohomologyClassAddHom : ℚ →+ RationalCohomology structureMap 0 where
  toFun := rationalCohomologyClass structureMap
  map_zero' := rationalCohomologyClass_zero structureMap
  map_add' := rationalCohomologyClass_add structureMap

/-- The unit in degree-zero rational cohomology. -/
def rationalCohomologyUnit : RationalCohomology structureMap 0 :=
  rationalCohomologyClass structureMap 1

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
def rationalToComplexCohomology (n : ℤ) :
    RationalCohomology structureMap n →+ ComplexConstantCohomology structureMap n :=
  hypercohomologyMap structureMap
    (rationalToComplexConstantSheafComplexInt structureMap) n

/-- The cohomological retraction induced by the chosen rational-linear retraction `ℂ → ℚ`. -/
def complexToRationalCohomology (n : ℤ) :
    ComplexConstantCohomology structureMap n →+ RationalCohomology structureMap n :=
  hypercohomologyMap structureMap
    (complexToRationalConstantSheafComplexInt structureMap) n

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
lemma complexToRationalCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToRationalCohomology structureMap n)
      (rationalToComplexCohomology structureMap n) := by
  intro α
  unfold complexToRationalCohomology rationalToComplexCohomology
  rw [← hypercohomologyMap_comp_apply structureMap,
    rationalToComplexConstantSheafComplexInt_comp_complexToRational,
    hypercohomologyMap_id]
  rfl

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma rationalToComplexCohomology_injective (n : ℤ) :
    Function.Injective (rationalToComplexCohomology structureMap n) :=
  (complexToRationalCohomology_leftInverse structureMap n).injective

/-- The rational action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
def rationalCohomologySMul (n : ℤ) (q : ℚ)
    (α : RationalCohomology structureMap n) : RationalCohomology structureMap n :=
  hypercohomologyMap structureMap (rationalScalarComplex structureMap q) n α

noncomputable instance rationalCohomologySMulInstance (n : ℤ) :
    SMul ℚ (RationalCohomology structureMap n) :=
  ⟨rationalCohomologySMul structureMap n⟩

lemma rational_smul_eq (n : ℤ) (q : ℚ) (α : RationalCohomology structureMap n) :
    q • α = hypercohomologyMap structureMap
      (rationalScalarComplex structureMap q) n α := rfl

lemma rational_smul_add (n : ℤ) (q : ℚ)
    (α β : RationalCohomology structureMap n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap structureMap
    (rationalScalarComplex structureMap q) n).map_add α β

lemma rational_add_smul (n : ℤ) (a b : ℚ)
    (α : RationalCohomology structureMap n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap structureMap
      (rationalScalarComplex structureMap (a + b)) n α =
    hypercohomologyMap structureMap (rationalScalarComplex structureMap a) n α +
      hypercohomologyMap structureMap (rationalScalarComplex structureMap b) n α
  rw [rationalScalarComplex_add]
  let e : RationalCohomology structureMap n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  rw [hypercohomologyEquiv_add]
  simp [e, hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

lemma rational_one_smul (n : ℤ) (α : RationalCohomology structureMap n) :
    (1 : ℚ) • α = α := by
  rw [rational_smul_eq, rationalScalarComplex_one]
  let e : RationalCohomology structureMap n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma rational_mul_smul (n : ℤ) (a b : ℚ)
    (α : RationalCohomology structureMap n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap structureMap
      (rationalScalarComplex structureMap (a * b)) n α =
    hypercohomologyMap structureMap (rationalScalarComplex structureMap a) n
      (hypercohomologyMap structureMap (rationalScalarComplex structureMap b) n α)
  rw [rationalScalarComplex_mul]
  exact hypercohomologyMap_comp_apply structureMap _ _ n α

/-- Rational constant-sheaf cohomology is canonically a rational vector space. -/
noncomputable instance rationalCohomologyModule (n : ℤ) :
    Module ℚ (RationalCohomology structureMap n) :=
  Module.ofMinimalAxioms
    (rational_smul_add structureMap n)
    (rational_add_smul structureMap n)
    (rational_mul_smul structureMap n)
    (rational_one_smul structureMap n)

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
def deRhamRationalSMul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : ℚ) (α : DeRhamHypercohomology structureMap d n) :
    DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ)) n α

noncomputable instance deRhamRationalSMulInstance
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    SMul ℚ (DeRhamHypercohomology structureMap d n) :=
  ⟨deRhamRationalSMul structureMap d n⟩

lemma deRham_rational_smul_eq [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : ℚ) (α : DeRhamHypercohomology structureMap d n) :
    q • α = hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ)) n α :=
  rfl

lemma deRham_rational_smul_add [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (q : ℚ) (α β : DeRhamHypercohomology structureMap d n) :
    q • (α + β) = q • α + q • β := by
  exact (hypercohomologyMap structureMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ)) n).map_add α β

lemma deRham_rational_add_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : ℚ) (α : DeRhamHypercohomology structureMap d n) :
    (a + b) • α = a • α + b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d ((a + b : ℚ) : ℂ)) n α =
    hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (a : ℂ)) n α +
      hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (b : ℂ)) n α
  rw [Rat.cast_add, scalarHolomorphicDeRhamComplexInt_add]
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

lemma deRham_rational_one_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (α : DeRhamHypercohomology structureMap d n) :
    (1 : ℚ) • α = α := by
  rw [deRham_rational_smul_eq, Rat.cast_one,
    scalarHolomorphicDeRhamComplexInt_one]
  let e : DeRhamHypercohomology structureMap d n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt structureMap d)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  apply e.injective
  simp [e, hypercohomologyMap]

lemma deRham_rational_mul_smul [SmoothOfRelativeDimension d structureMap]
    (n : ℤ) (a b : ℚ) (α : DeRhamHypercohomology structureMap d n) :
    (a * b) • α = a • b • α := by
  change hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d ((a * b : ℚ) : ℂ)) n α =
    hypercohomologyMap structureMap
      (scalarHolomorphicDeRhamComplexInt structureMap d (a : ℂ)) n
      (hypercohomologyMap structureMap
        (scalarHolomorphicDeRhamComplexInt structureMap d (b : ℂ)) n α)
  rw [Rat.cast_mul, scalarHolomorphicDeRhamComplexInt_mul]
  exact hypercohomologyMap_comp_apply structureMap _ _ n α

/-- Holomorphic de Rham hypercohomology is canonically a rational vector space. -/
noncomputable instance deRhamHypercohomologyModule
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Module ℚ (DeRhamHypercohomology structureMap d n) :=
  Module.ofMinimalAxioms
    (deRham_rational_smul_add structureMap d n)
    (deRham_rational_add_smul structureMap d n)
    (deRham_rational_mul_smul structureMap d n)
    (deRham_rational_one_smul structureMap d n)

/-- The independently constructed rational and complex scalar actions on de Rham
hypercohomology agree through the canonical embedding `ℚ → ℂ`. -/
lemma deRham_rational_smul_eq_complex_smul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (q : ℚ) (α : DeRhamHypercohomology structureMap d n) :
    q • α = (q : ℂ) • α :=
  rfl

/-- Rational, complex, and de Rham scalar multiplication form the expected scalar tower. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    IsScalarTower ℚ ℂ (DeRhamHypercohomology structureMap d n) :=
  IsScalarTower.of_algebraMap_smul fun q α =>
    deRham_rational_smul_eq_complex_smul structureMap d n q α

/-- Constant degree-zero cohomology classes respect rational scalar multiplication. -/
lemma rationalCohomologyClass_mul (q r : ℚ) :
    rationalCohomologyClass structureMap (q * r) =
      q • rationalCohomologyClass structureMap r := by
  rw [rational_smul_eq]
  unfold rationalCohomologyClass hypercohomologyMap
  dsimp
  rw [← smallShiftedHomMkZero_comp structureMap,
    integerToRationalConstantSheafComplexInt_comp_rationalScalarComplex]

/-- Rational constants map rational-linearly to degree-zero rational cohomology. -/
def rationalCohomologyClassLinear : ℚ →ₗ[ℚ] RationalCohomology structureMap 0 where
  toFun := rationalCohomologyClass structureMap
  map_add' := rationalCohomologyClass_add structureMap
  map_smul' q r := rationalCohomologyClass_mul structureMap q r

/-- The derived comparison from rational cohomology to holomorphic de Rham hypercohomology. -/
def rationalToDeRhamCohomology [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    RationalCohomology structureMap n →+ DeRhamHypercohomology structureMap d n :=
  hypercohomologyMap structureMap
    (rationalToHolomorphicDeRhamComplexInt structureMap d) n

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma rationalToDeRhamCohomology_factor
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : RationalCohomology structureMap n) :
    rationalToDeRhamCohomology structureMap d n α =
      hypercohomologyMap structureMap
        (constantsToHolomorphicDeRhamComplexInt structureMap d) n
        (rationalToComplexCohomology structureMap n α) := by
  unfold rationalToDeRhamCohomology rationalToComplexCohomology
    rationalToHolomorphicDeRhamComplexInt
  exact hypercohomologyMap_comp_apply structureMap
    (rationalToComplexConstantSheafComplexInt structureMap)
    (constantsToHolomorphicDeRhamComplexInt structureMap d) n α

/-- Once the analytic Poincare comparison is proved to be a quasi-isomorphism, the
rational-to-de Rham comparison is injective. This uses the explicit splitting of `ℚ → ℂ`, not a
finite-dimensionality assumption. -/
lemma rationalToDeRhamCohomology_injective_of_quasiIso
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d)) (n : ℤ) :
    Function.Injective (rationalToDeRhamCohomology structureMap d n) := by
  intro α β hαβ
  apply rationalToComplexCohomology_injective structureMap n
  apply (complexConstantCohomologyDeRhamEquiv structureMap d h n).injective
  simpa only [complexConstantCohomologyDeRhamEquiv_apply,
    rationalToDeRhamCohomology_factor structureMap d n] using hαβ

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit coefficient splitting proves that extending
scalars from `ℚ` to `ℂ` is injective. -/
lemma rationalToDeRhamCohomology_injective
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Function.Injective (rationalToDeRhamCohomology structureMap d n) :=
  rationalToDeRhamCohomology_injective_of_quasiIso structureMap d inferInstance n

/-- The rational-to-de Rham comparison is compatible with rational scalar multiplication. -/
lemma rationalToDeRhamCohomology_smul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (q : ℚ) (α : RationalCohomology structureMap n) :
    rationalToDeRhamCohomology structureMap d n (q • α) =
      q • rationalToDeRhamCohomology structureMap d n α := by
  rw [rational_smul_eq, deRham_rational_smul_eq]
  unfold rationalToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [rationalToHolomorphicDeRhamComplexInt_scalar]

/-- The rational-to-de Rham comparison as a rational-linear map. -/
def rationalToDeRhamCohomologyLinear
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    RationalCohomology structureMap n →ₗ[ℚ]
      DeRhamHypercohomology structureMap d n where
  toFun := rationalToDeRhamCohomology structureMap d n
  map_add' := (rationalToDeRhamCohomology structureMap d n).map_add
  map_smul' := rationalToDeRhamCohomology_smul structureMap d n

/-- The balanced map that extends rational-to-de Rham comparison after scalar extension from
`ℚ` to `ℂ`. -/
def rationalToDeRhamComplexificationBilinear
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    ℂ →ₗ[ℂ] RationalCohomology structureMap n →ₗ[ℚ]
      DeRhamHypercohomology structureMap d n where
  toFun c := c • (rationalToDeRhamCohomologyLinear structureMap d n)
  map_add' a b := by
    ext α
    simp [add_smul]
  map_smul' a b := by
    ext α
    simp [mul_smul]

/-- The canonical complex-linear comparison from the complexification of rational
constant-sheaf cohomology to holomorphic de Rham hypercohomology. -/
def rationalToDeRhamComplexification
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    TensorProduct ℚ ℂ (RationalCohomology structureMap n) →ₗ[ℂ]
      DeRhamHypercohomology structureMap d n :=
  TensorProduct.AlgebraTensorModule.lift
    (rationalToDeRhamComplexificationBilinear structureMap d n)

@[simp] lemma rationalToDeRhamComplexification_tmul
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (c : ℂ) (α : RationalCohomology structureMap n) :
    rationalToDeRhamComplexification structureMap d n (c ⊗ₜ[ℚ] α) =
      c • rationalToDeRhamCohomology structureMap d n α :=
  rfl

/-- On the rational lattice, the complexified comparison agrees with the original map. -/
@[simp] lemma rationalToDeRhamComplexification_ofRational
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : RationalCohomology structureMap n) :
    rationalToDeRhamComplexification structureMap d n (1 ⊗ₜ[ℚ] α) =
      rationalToDeRhamCohomology structureMap d n α := by
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
    (p : ℤ) (q : ℚ) :
    hodgeFilteredDeRhamComplex structureMap d p ⟶
      hodgeFilteredDeRhamComplex structureMap d p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ))
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
    [SmoothOfRelativeDimension d structureMap] (p : ℤ) (q : ℚ) :
    hodgeFilteredDeRhamScalar structureMap d p q ≫
      hodgeFilteredDeRhamInclusion structureMap d p =
    hodgeFilteredDeRhamInclusion structureMap d p ≫
      scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ) := by
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt structureMap d (q : ℂ))

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

set_option backward.isDefEq.respectTransparency false in
/-- The Hodge filtration decreases as the filtration index increases. -/
lemma hodgeFiltration_antitone [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    Antitone (fun p : ℤ => hodgeFiltration structureMap d p n) := by
  intro p q hpq
  let ep := ComplexShape.embeddingUpIntGE p
  let Kq := hodgeFilteredDeRhamComplex structureMap d q
  let _ : Kq.IsStrictlyGE q := by
    unfold Kq hodgeFilteredDeRhamComplex
    infer_instance
  let _ : Kq.IsStrictlyGE p := CochainComplex.isStrictlyGE_of_ge Kq p q hpq
  let i := HomologicalComplex.stupidTruncInclusion Kq ep
  let _ : IsIso i := by
    unfold i ep
    infer_instance
  let f : hodgeFilteredDeRhamComplex structureMap d q ⟶
      hodgeFilteredDeRhamComplex structureMap d p :=
    inv i ≫ HomologicalComplex.stupidTruncMap
      (hodgeFilteredDeRhamInclusion structureMap d q) ep
  have hf : f ≫ hodgeFilteredDeRhamInclusion structureMap d p =
      hodgeFilteredDeRhamInclusion structureMap d q := by
    change (inv i ≫ HomologicalComplex.stupidTruncMap
      (hodgeFilteredDeRhamInclusion structureMap d q) ep) ≫
      HomologicalComplex.stupidTruncInclusion
        (holomorphicDeRhamComplexInt structureMap d) ep = _
    rw [Category.assoc, HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion]
    change inv i ≫ i ≫ _ = _
    simp
  rintro α ⟨β, rfl⟩
  refine ⟨hypercohomologyMap structureMap f n β, ?_⟩
  change hypercohomologyMap structureMap
    (hodgeFilteredDeRhamInclusion structureMap d p) n
    (hypercohomologyMap structureMap f n β) = _
  exact (hypercohomologyMap_comp_apply structureMap f
    (hodgeFilteredDeRhamInclusion structureMap d p) n β).symm.trans
      (congrArg (fun g => hypercohomologyMap structureMap g n β) hf)

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
def complexifiedRationalHodgeFiltration [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) :
    Submodule ℂ (HodgeStructure.Complexification (RationalCohomology structureMap n)) :=
  (hodgeFiltrationComplexSubmodule structureMap d p n).comap
    (rationalToDeRhamComplexification structureMap d n)

/-- The Hodge filtration is stable under rational scalar multiplication. -/
lemma hodgeFiltration_smul_mem [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) (q : ℚ) {α : DeRhamHypercohomology structureMap d n}
    (hα : α ∈ hodgeFiltration structureMap d p n) :
    q • α ∈ hodgeFiltration structureMap d p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨hypercohomologyMap structureMap
    (hodgeFilteredDeRhamScalar structureMap d p q) n β, ?_⟩
  rw [deRham_rational_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamScalar_comp_inclusion]

/-- The Hodge filtration bundled as a rational subspace of de Rham hypercohomology. -/
def hodgeFiltrationSubmodule [SmoothOfRelativeDimension d structureMap]
    (p n : ℤ) : Submodule ℚ (DeRhamHypercohomology structureMap d n) where
  carrier := hodgeFiltration structureMap d p n
  zero_mem' := (hodgeFiltration structureMap d p n).zero_mem
  add_mem' := (hodgeFiltration structureMap d p n).add_mem
  smul_mem' := fun q _ h => hodgeFiltration_smul_mem structureMap d p n q h

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

/-- At every nonpositive index, the Hodge filtration is the whole de Rham hypercohomology group. -/
lemma hodgeFiltration_eq_top_of_nonpos [SmoothOfRelativeDimension d structureMap]
    {p : ℤ} (hp : p ≤ 0) (n : ℤ) :
    hodgeFiltration structureMap d p n = ⊤ := by
  apply top_unique
  rw [← hodgeFiltration_zero_eq_top structureMap d n]
  exact hodgeFiltration_antitone structureMap d n hp

/-- The rational submodule underlying `F⁰` is the whole de Rham hypercohomology group. -/
lemma hodgeFiltrationSubmodule_zero_eq_top
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    hodgeFiltrationSubmodule structureMap d 0 n = ⊤ := by
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration structureMap d 0 n ↔ α ∈ (⊤ :
    Submodule ℚ (DeRhamHypercohomology structureMap d n))
  rw [hodgeFiltration_zero_eq_top structureMap d n]
  simp

/-- Rational cohomology classes whose de Rham images lie in `F^p H^{2p}`, bundled as an additive
subgroup. -/
def rationalHodgeClasses [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    Submodule ℚ (RationalCohomology structureMap (2 * p)) :=
  (hodgeFiltrationSubmodule structureMap d p (2 * p)).comap
    (rationalToDeRhamCohomologyLinear structureMap d (2 * p))

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma rationalHodgeClasses_eq_ker_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    rationalHodgeClasses structureMap d p =
      LinearMap.ker (rationalToDeRhamCohomologyLinear structureMap d (2 * p)) := by
  rw [rationalHodgeClasses, ← Submodule.comap_bot]
  congr 1
  apply SetLike.ext
  intro α
  change α ∈ hodgeFiltration structureMap d (p : ℤ) (2 * (p : ℤ)) ↔ α ∈ (⊥ :
    Submodule ℂ (DeRhamHypercohomology structureMap d (2 * (p : ℤ))))
  rw [hodgeFiltration_eq_bot_of_lt structureMap d (by exact_mod_cast hp)]
  rfl

/-- If the analytic constant-to-holomorphic de Rham comparison is a quasi-isomorphism, rational
Hodge classes vanish above the complex dimension. -/
lemma rationalHodgeClasses_eq_bot_of_lt_of_quasiIso
    [SmoothOfRelativeDimension d structureMap]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d))
    {p : ℕ} (hp : d < p) :
    rationalHodgeClasses structureMap d p = ⊥ := by
  rw [rationalHodgeClasses_eq_ker_of_lt structureMap d hp]
  apply LinearMap.ker_eq_bot.mpr
  exact rationalToDeRhamCohomology_injective_of_quasiIso structureMap d h (2 * p)

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma rationalHodgeClasses_eq_bot_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    rationalHodgeClasses structureMap d p = ⊥ :=
  rationalHodgeClasses_eq_bot_of_lt_of_quasiIso structureMap d inferInstance hp

/-- Rational Hodge classes described through the rational lattice inside its actual
complexification. -/
def rationalHodgeClassesViaComplexification
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    Submodule ℚ (RationalCohomology structureMap (2 * p)) :=
  Submodule.comap
    (HodgeStructure.ofRational (RationalCohomology structureMap (2 * p)))
    ((complexifiedRationalHodgeFiltration structureMap d p (2 * p)).restrictScalars ℚ)

/-- The direct definition of rational Hodge classes agrees with the definition using the
complexified rational lattice. -/
lemma rationalHodgeClassesViaComplexification_eq
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    rationalHodgeClassesViaComplexification structureMap d p =
      rationalHodgeClasses structureMap d p := by
  ext α
  change rationalToDeRhamComplexification structureMap d (2 * (p : ℤ))
      (HodgeStructure.ofRational
        (RationalCohomology structureMap (2 * (p : ℤ))) α) ∈
        hodgeFiltration structureMap d p (2 * (p : ℤ)) ↔
    rationalToDeRhamCohomology structureMap d (2 * (p : ℤ)) α ∈
      hodgeFiltration structureMap d p (2 * (p : ℤ))
  rw [HodgeStructure.ofRational_apply,
    rationalToDeRhamComplexification_ofRational]

/-- A rational cohomology class is a Hodge class of codimension `p` when it belongs to the
canonical subgroup of rational Hodge classes. -/
def IsRationalHodgeClass [SmoothOfRelativeDimension d structureMap] (p : ℕ)
    (α : RationalCohomology structureMap (2 * p)) : Prop :=
  α ∈ rationalHodgeClasses structureMap d p

lemma mem_rationalHodgeClasses_iff [SmoothOfRelativeDimension d structureMap]
    (p : ℕ) (α : RationalCohomology structureMap (2 * p)) :
    α ∈ rationalHodgeClasses structureMap d p ↔
      IsRationalHodgeClass structureMap d p α :=
  Iff.rfl

/-- Every rational degree-zero cohomology class belongs to the rational Hodge subgroup. -/
lemma rationalHodgeClasses_zero_eq_top [SmoothOfRelativeDimension d structureMap] :
    rationalHodgeClasses structureMap d 0 = ⊤ := by
  apply SetLike.ext
  intro α
  change rationalToDeRhamCohomology structureMap d (2 * (0 : ℕ)) α ∈
      hodgeFiltration structureMap d (0 : ℕ) (2 * (0 : ℕ)) ↔ True
  simp only [Nat.cast_zero]
  rw [hodgeFiltration_zero_eq_top]
  trivial

/-- Every rational degree-zero class has Hodge type `(0,0)`. -/
lemma isRationalHodgeClass_zero [SmoothOfRelativeDimension d structureMap]
    (α : RationalCohomology structureMap 0) :
    IsRationalHodgeClass structureMap d 0 α := by
  change α ∈ rationalHodgeClasses structureMap d 0
  rw [rationalHodgeClasses_zero_eq_top]
  trivial

end AlgebraicGeometry.ComplexPoint
