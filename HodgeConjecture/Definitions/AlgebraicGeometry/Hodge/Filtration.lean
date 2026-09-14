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

public import HodgeConjecture.Lemmas.Algebra.FieldToComplex
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import HodgeConjecture.Lemmas.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Mathlib.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.Hypercohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Data.Int.Cast.Lemmas

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The Hodge filtration

This file defines rational sheaf cohomology and holomorphic de Rham hypercohomology on the
analytic complex-point space of a smooth complex scheme. Hypercohomology is obtained from the
bounded-below derived global-sections functor.

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

/-- Sheaves of additive groups on the analytic complex-point space. -/
abbrev AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))

local instance analyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance additiveGroupsHasDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- The inclusion of the rational constant sheaf into the complex constant sheaf. -/
abbrev fieldToComplexConstantSheaf :
    𝓒(↧(ComplexPoint X); K) ⟶ 𝓒(↧(ComplexPoint X); ℂ) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)

/-- The constant rational sheaf complex, extended by zero to integer degrees. -/
@[implicit_reducible]
def constantFieldSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
    𝓒(↧(ComplexPoint X); K)).extend ComplexShape.embeddingUpNat

instance : (constantFieldSheafComplexInt K X).IsStrictlyGE 0 := by
  unfold constantFieldSheafComplexInt
  infer_instance

/-- The rational constant sheaf complex as a bounded-below complex. -/
abbrev constantFieldSheafComplexIntPlus :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨constantFieldSheafComplexInt K X, ⟨0, inferInstance⟩⟩

/-- The complex constant sheaf complex as a bounded-below complex. -/
abbrev constantComplexSheafComplexIntPlus :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨constantComplexSheafComplexInt X, ⟨0, inferInstance⟩⟩

/-- The holomorphic de Rham complex as a bounded-below complex. -/
abbrev holomorphicDeRhamComplexIntPlus [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨holomorphicDeRhamComplexInt X, ⟨0, inferInstance⟩⟩

/-- Extension of rational constants to complex constants as a map of integer complexes. -/
def fieldToComplexConstantSheafComplexInt :
    constantFieldSheafComplexInt K X ⟶
      constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat

/-- Rational constants mapped canonically into the holomorphic de Rham complex. -/
def fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    constantFieldSheafComplexInt K X ⟶
      holomorphicDeRhamComplexInt X :=
  fieldToComplexConstantSheafComplexInt K X ≫
    constantsToHolomorphicDeRhamComplexInt X

/-- The constant integer sheaf complex, extended by zero to integer degrees. -/
@[implicit_reducible]
def constantIntegerSheafComplexInt :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
    𝓒(↧(ComplexPoint X); ℤ)).extend ComplexShape.embeddingUpNat

/-- Scalar multiplication on the rational constant sheaf. -/
abbrev fieldScalarSheaf (q : K) :
    𝓒(↧(ComplexPoint X); K) ⟶ 𝓒(↧(ComplexPoint X); K) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q))

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_one : fieldScalarSheaf K X 1 = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.id K) = 𝟙 (AddCommGrpCat.of K) := by
    apply AddCommGrpCat.hom_ext
    rfl
  change (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft 1)) =
    𝟙 𝓒(↧(ComplexPoint X); K)
  rw [AddMonoidHom.mulLeft_one, h]
  exact (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map_id (AddCommGrpCat.of K)

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_add (a b : K) :
    fieldScalarSheaf K X (a + b) =
      fieldScalarSheaf K X a + fieldScalarSheaf K X b := by
  have h : AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a + AddMonoidHom.mulLeft b) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) +
        AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) :=
    AddCommGrpCat.hom_ext rfl
  change (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (a + b))) = _
  rw [AddMonoidHom.mulLeft_add, h, Functor.map_add]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_mul (a b : K) :
    fieldScalarSheaf K X (a * b) =
      fieldScalarSheaf K X b ≫ fieldScalarSheaf K X a := by
  have h : AddCommGrpCat.ofHom
      ((AddMonoidHom.mulLeft a).comp (AddMonoidHom.mulLeft b)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) :=
    AddCommGrpCat.hom_ext rfl
  change (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (a * b))) = _
  rw [AddMonoidHom.mulLeft_mul, h, Functor.map_comp]
  rfl

/-- Multiplying by `q` in `K` before including into `ℂ` agrees with including first and then
multiplying by `algebraMap K ℂ q`. -/
private lemma ofHom_algebraMap_comp_complexScalarSMul (q : K) :
    AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ (algebraMap K ℂ q)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q) ≫
        AddCommGrpCat.ofHom (@AddMonoidHomClass.toAddMonoidHom K ℂ (K →+* ℂ) Field.toSemifield.toNonAssocSemiring.toAddCommMonoidWithOne.toAddZeroClass.toAddZero
                Complex.instSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddZeroClass.toAddZero RingHom.instFunLike _
        (algebraMap K ℂ)) := by
  ext r
  simp [map_mul]

/-- The constant-presheaf map induced by the inclusion `K → ℂ`, followed by scalar multiplication
by `algebraMap K ℂ q` on the constant complex presheaf, is the constant-presheaf map induced by the
composite additive map. -/
private lemma const_map_algebraMap_comp_complexScalarPresheaf (q : K) : (Functor.const (Opens (ComplexPoint X))ᵒᵖ).map (AddCommGrpCat.ofHom ↑(algebraMap K ℂ)) ≫
    complexScalarPresheaf X ((algebraMap K ℂ) q) =
  (Functor.const (Opens (ComplexPoint X))ᵒᵖ).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ : K →+ ℂ) ≫ AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ ((algebraMap K ℂ) q))) := rfl

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1 TopCat.instCategorySheaf._aux_3
  TopCat.instCategorySheaf._aux_5 constantComplexAddCommGrpPresheaf in
/-- The inclusion of rational constants into complex constants commutes with scalar
multiplication. -/
private lemma fieldToComplexConstantSheaf_scalar (q : K) :
    fieldToComplexConstantSheaf K X ≫
      complexScalarSheaf X (algebraMap K ℂ q) =
    fieldScalarSheaf K X q ≫
      fieldToComplexConstantSheaf K X := by
  simp [fieldToComplexConstantSheaf, fieldScalarSheaf, complexScalarSheaf, constantSheaf,
    TopCat.Sheaf.const, TopCat.Sheaf.constantFunctor, ← Functor.map_comp,
    ← ofHom_algebraMap_comp_complexScalarSMul,
    const_map_algebraMap_comp_complexScalarPresheaf]

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- Scalar multiplication on the rational constant sheaf complex. -/
def fieldScalarComplex (q : K) :
    constantFieldSheafComplexInt K X ⟶
      constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_one : fieldScalarComplex K X 1 = 𝟙 _ := by
  unfold fieldScalarComplex constantFieldSheafComplexInt
  rw [fieldScalarSheaf_one, (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_id,
    HomologicalComplex.extendMap_id]

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_add (a b : K) :
    fieldScalarComplex K X (a + b) =
      fieldScalarComplex K X a + fieldScalarComplex K X b := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_add, Functor.map_add, HomologicalComplex.extendMap_add]

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_mul (a b : K) :
    fieldScalarComplex K X (a * b) =
      fieldScalarComplex K X b ≫ fieldScalarComplex K X a := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_mul, Functor.map_comp, HomologicalComplex.extendMap_comp]

/-- The integer-indexed inclusion of rational constants into complex constants commutes with
scalar multiplication. -/
private lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexScalarComplexInt X (algebraMap K ℂ q) =
    fieldScalarComplex K X q ≫
      fieldToComplexConstantSheafComplexInt K X := by
  rw [fieldToComplexConstantSheafComplexInt, complexScalarComplexInt, fieldScalarComplex,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    complexScalarComplex, ← Functor.map_comp, fieldToComplexConstantSheaf_scalar]

/-- The rational-to-de Rham comparison of complexes commutes with rational scalar
multiplication. -/
private lemma fieldToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (q : K) :
    fieldToHolomorphicDeRhamComplexInt K X ≫
      scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q) =
    fieldScalarComplex K X q ≫
      fieldToHolomorphicDeRhamComplexInt K X := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar, ← Category.assoc,
    fieldToComplexConstantSheafComplexInt_scalar, Category.assoc]

/-- Hypercohomology of bounded-below analytic sheaf complexes in degree `n`. -/
abbrev analyticHypercohomologyFunctor (n : ℤ) :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) ⥤ AddCommGrpCat :=
  DerivedCategory.Plus.Q ⋙
    TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n

/-- `H^n(X; K)` is constant-sheaf cohomology of the analytic space `X(ℂ)` with coefficients in
the field `K`, in integer degree `n`: the hypercohomology of the constant sheaf `K` on `X(ℂ)`.

The literature writes `H^n(X; K)` for the variety `X.left` alone; here the variety is presented by
its structure morphism `X`. -/
scoped notation3:max "H^" n:max "(" X "; " K ")" =>
  ↥((analyticHypercohomologyFunctor X n).obj (constantFieldSheafComplexIntPlus K X))

/-- Hypercohomology of the holomorphic de Rham complex in integer degree `n`. -/
abbrev DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :=
  ↥((analyticHypercohomologyFunctor X n).obj (holomorphicDeRhamComplexIntPlus X))

/-- The constant-to-holomorphic-de Rham quasi-isomorphism induces the corresponding
equivalence on hypercohomology. -/
def complexConstantCohomologyDeRhamAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ↥((analyticHypercohomologyFunctor X n).obj
      (constantComplexSheafComplexIntPlus X)) ≃+ DeRhamHypercohomology X n :=
  let f : (constantComplexSheafComplexIntPlus X :
      CochainComplex.Plus (AnalyticAdditiveSheaf X)) ⟶
      holomorphicDeRhamComplexIntPlus X :=
    ⟨constantsToHolomorphicDeRhamComplexInt X⟩
  letI : QuasiIso f.hom := constantsToHolomorphicDeRhamComplexInt_quasiIso X
  letI : IsIso (DerivedCategory.Plus.Q.map f) := inferInstance
  letI : IsIso ((analyticHypercohomologyFunctor X n).map f) :=
    by
      dsimp only [analyticHypercohomologyFunctor, Functor.comp_map]
      infer_instance
  (asIso ((analyticHypercohomologyFunctor X n).map f)).addCommGroupIsoToAddEquiv

/-- Scalars acting on a coefficient complex by an additive, unital and antimultiplicative family
of endomorphisms act on its hypercohomology. -/
noncomputable abbrev hypercohomologyModule {R : Type*} [Semiring R]
    {C : CochainComplex.Plus (AnalyticAdditiveSheaf X)} (s : R → (C ⟶ C)) (n : ℤ)
    [SMul R ↥((analyticHypercohomologyFunctor X n).obj C)]
    (smul_eq : ∀ (r : R) (α : ↥((analyticHypercohomologyFunctor X n).obj C)),
      r • α = (analyticHypercohomologyFunctor X n).map (s r) α)
    (s_add : ∀ a b : R, s (a + b) = s a + s b)
    (s_one : s 1 = 𝟙 C)
    (s_mul : ∀ a b : R, s (a * b) = s b ≫ s a) :
    Module R ↥((analyticHypercohomologyFunctor X n).obj C) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [smul_eq, smul_eq, smul_eq]
      exact ((analyticHypercohomologyFunctor X n).map (s r)).hom.map_add α β)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_add]
      simp)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_mul]
      simp)
    (fun α => by
      rw [smul_eq, s_one]
      simp)

/-- The rational action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
noncomputable instance (n : ℤ) :
    SMul K (H^n(X; K)) :=
  ⟨fun q α ↦ (analyticHypercohomologyFunctor X n).map
    (⟨fieldScalarComplex K X q⟩ : constantFieldSheafComplexIntPlus K X ⟶
      constantFieldSheafComplexIntPlus K X) α⟩

omit [Algebra K ℂ] in
lemma field_smul_eq (n : ℤ) (q : K) (α : H^n(X; K)) :
    q • α = (analyticHypercohomologyFunctor X n).map
      (⟨fieldScalarComplex K X q⟩ : constantFieldSheafComplexIntPlus K X ⟶
        constantFieldSheafComplexIntPlus K X) α := rfl

/-- Rational constant-sheaf cohomology is canonically a rational vector space. -/
noncomputable instance fieldCohomologyModule (n : ℤ) :
    Module K (H^n(X; K)) :=
  hypercohomologyModule X (fun q ↦
    (⟨fieldScalarComplex K X q⟩ : constantFieldSheafComplexIntPlus K X ⟶
      constantFieldSheafComplexIntPlus K X)) n
    (field_smul_eq K X n)
    (fun a b ↦ by apply ObjectProperty.hom_ext; exact fieldScalarComplex_add K X a b)
    (by apply ObjectProperty.hom_ext; exact fieldScalarComplex_one K X)
    (fun a b ↦ by apply ObjectProperty.hom_ext; exact fieldScalarComplex_mul K X a b)

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
noncomputable instance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul ℂ (DeRhamHypercohomology X n) :=
  ⟨fun c α ↦ (analyticHypercohomologyFunctor X n).map
    (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
      holomorphicDeRhamComplexIntPlus X) α⟩

lemma deRham_complex_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    c • α = (analyticHypercohomologyFunctor X n).map
      (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
        holomorphicDeRhamComplexIntPlus X) α :=
  rfl

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance deRhamHypercohomologyComplexModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module ℂ (DeRhamHypercohomology X n) :=
  hypercohomologyModule X (fun c ↦
    (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
      holomorphicDeRhamComplexIntPlus X)) n
    (deRham_complex_smul_eq X n)
    (fun a b ↦ by
      apply ObjectProperty.hom_ext
      exact scalarHolomorphicDeRhamComplexInt_add X a b)
    (by apply ObjectProperty.hom_ext; exact scalarHolomorphicDeRhamComplexInt_one X)
    (fun a b ↦ by
      apply ObjectProperty.hom_ext
      exact scalarHolomorphicDeRhamComplexInt_mul X a b)

/-- De Rham hypercohomology as a vector space over `K`, by restriction of complex scalars. -/
noncomputable instance deRhamHypercohomologyModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module K (DeRhamHypercohomology X n) :=
  Module.restrictScalars K ℂ (DeRhamHypercohomology X n)

lemma deRham_field_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α : DeRhamHypercohomology X n) :
    q • α = (analyticHypercohomologyFunctor X n).map
      (⟨scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)⟩ :
        holomorphicDeRhamComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) α :=
  rfl

/-- Restriction of complex scalars gives the scalar tower on de Rham hypercohomology. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ (DeRhamHypercohomology X n) :=
  IsScalarTower.restrictScalars K ℂ (DeRhamHypercohomology X n)

/-- The derived comparison from rational cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; K) →+ DeRhamHypercohomology X n :=
  ((analyticHypercohomologyFunctor X n).map
    (⟨fieldToHolomorphicDeRhamComplexInt K X⟩ : constantFieldSheafComplexIntPlus K X ⟶
      holomorphicDeRhamComplexIntPlus X)).hom

/-- The rational-to-de Rham comparison is compatible with rational scalar multiplication. -/
lemma fieldToDeRhamCohomology_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (q : K) (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n (q • α) =
      q • fieldToDeRhamCohomology K X n α := by
  rw [field_smul_eq, deRham_field_smul_eq]
  unfold fieldToDeRhamCohomology
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1
  apply congrArg (fun f ↦ ((analyticHypercohomologyFunctor X n).map f).hom)
  apply ObjectProperty.hom_ext
  exact (fieldToHolomorphicDeRhamComplexInt_scalar K X q).symm

/-- The rational-to-de Rham comparison as a rational-linear map. -/
def fieldToDeRhamCohomologyLinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; K) →ₗ[K]
      DeRhamHypercohomology X n where
  toFun := fieldToDeRhamCohomology K X n
  map_add' := (fieldToDeRhamCohomology K X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K X n

/-- The de Rham complex with only form degrees at least `p` retained. -/
def hodgeFilteredDeRhamComplex [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (holomorphicDeRhamComplexInt X).stupidTrunc
    (ComplexShape.embeddingUpIntGE p)

instance [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    (hodgeFilteredDeRhamComplex X p).IsStrictlyGE p := by
  unfold hodgeFilteredDeRhamComplex
  infer_instance

/-- The filtered de Rham complex as a bounded-below complex. -/
abbrev hodgeFilteredDeRhamComplexPlus [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨hodgeFilteredDeRhamComplex X p, ⟨p, inferInstance⟩⟩

/-- Inclusion of the degree-at-least-`p` de Rham complex into the full complex. -/
def hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    hodgeFilteredDeRhamComplex X p ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamComplexInt X) (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamComplexScalar [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplex X p ⟶
      hodgeFilteredDeRhamComplex X p :=
  HomologicalComplex.stupidTruncMap
    (scalarHolomorphicDeRhamComplexInt X c)
    (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered complex commutes with inclusion into the full
de Rham complex. -/
private lemma hodgeFilteredDeRhamComplexScalar_comp_inclusion
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar X p c ≫
      hodgeFilteredDeRhamInclusion X p =
    hodgeFilteredDeRhamInclusion X p ≫
      scalarHolomorphicDeRhamComplexInt X c :=
  HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion
    (ComplexShape.embeddingUpIntGE p)
    (scalarHolomorphicDeRhamComplexInt X c)

/-- Hypercohomology of the degree-at-least-`p` part of the de Rham complex. -/
abbrev FilteredDeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) :=
  ↥((analyticHypercohomologyFunctor X n).obj (hodgeFilteredDeRhamComplexPlus X p))

/-- The map from filtered to full de Rham hypercohomology. -/
def filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    FilteredDeRhamHypercohomology X p n →+
      DeRhamHypercohomology X n :=
  ((analyticHypercohomologyFunctor X n).map
    (⟨hodgeFilteredDeRhamInclusion X p⟩ : hodgeFilteredDeRhamComplexPlus X p ⟶
      holomorphicDeRhamComplexIntPlus X)).hom

/-- The Hodge filtration `F^p` on de Rham hypercohomology. -/
def hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    AddSubgroup (DeRhamHypercohomology X n) :=
  (filteredToDeRhamCohomology X p n).range

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma hodgeFiltration_complex_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (c : ℂ) {α : DeRhamHypercohomology X n}
    (hα : α ∈ hodgeFiltration X p n) :
    c • α ∈ hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨(analyticHypercohomologyFunctor X n).map
    (⟨hodgeFilteredDeRhamComplexScalar X p c⟩ : hodgeFilteredDeRhamComplexPlus X p ⟶
      hodgeFilteredDeRhamComplexPlus X p) β, ?_⟩
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1
  apply congrArg (fun f ↦ ((analyticHypercohomologyFunctor X n).map f).hom)
  apply ObjectProperty.hom_ext
  exact hodgeFilteredDeRhamComplexScalar_comp_inclusion X p c

/-- The Hodge filtration bundled as a complex subspace of de Rham hypercohomology. -/
def hodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology X n) where
  carrier := hodgeFiltration X p n
  zero_mem' := (hodgeFiltration X p n).zero_mem
  add_mem' := (hodgeFiltration X p n).add_mem
  smul_mem' := fun c _ h => hodgeFiltration_complex_smul_mem X p n c h

/-! ### Complex conjugation and the `(p,p)` part

Conjugation is not `ℂ`-linear, so it acts on the constant sheaf `ℂ` rather than on the holomorphic
de Rham complex, and is transported across the constant-to-de Rham comparison. The `(p,q)` piece
is then *defined* as `F^p ⊓ conj F^q`, which needs no Hodge decomposition theorem. -/

private lemma complexConstantCohomologyDeRhamAddEquiv_apply [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (α : ↥((analyticHypercohomologyFunctor X n).obj
      (constantComplexSheafComplexIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n α =
      (analyticHypercohomologyFunctor X n).map
        (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) α :=
  by
    unfold complexConstantCohomologyDeRhamAddEquiv
    rfl

/-- The comparison equivalence carries the constant-sheaf scalar action to the de Rham one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (β : ↥((analyticHypercohomologyFunctor X n).obj
      (constantComplexSheafComplexIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n
        ((analyticHypercohomologyFunctor X n).map
          (⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
            constantComplexSheafComplexIntPlus X) β) =
      c • complexConstantCohomologyDeRhamAddEquiv X n β := by
  rw [complexConstantCohomologyDeRhamAddEquiv_apply,
    complexConstantCohomologyDeRhamAddEquiv_apply,
    ← Functor.map_comp_apply]
  have h :
    ((⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X) ≫
      (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
        constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) :
      constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) =
      ((⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
        constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) ≫
      (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
        holomorphicDeRhamComplexIntPlus X) :
      constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) := by
    apply ObjectProperty.hom_ext
    exact (constantsToHolomorphicDeRhamComplexInt_scalar X c).symm
  rw [congrArg (fun f ↦ (analyticHypercohomologyFunctor X n).map f) h]
  rw [Functor.map_comp_apply, deRham_complex_smul_eq]

/-- The inverse comparison carries the de Rham scalar action back to the constant-sheaf one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_symm_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    (complexConstantCohomologyDeRhamAddEquiv X n).symm (c • α) =
      (analyticHypercohomologyFunctor X n).map
        (⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
          constantComplexSheafComplexIntPlus X)
        ((complexConstantCohomologyDeRhamAddEquiv X n).symm α) := by
  apply (complexConstantCohomologyDeRhamAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, complexConstantCohomologyDeRhamAddEquiv_scalar,
    AddEquiv.apply_symm_apply]

/-- Complex conjugation on de Rham hypercohomology, transported from the constant sheaf `ℂ`. -/
def deRhamConj [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →+ DeRhamHypercohomology X n :=
  ((complexConstantCohomologyDeRhamAddEquiv X n).toAddMonoidHom).comp
    (((analyticHypercohomologyFunctor X n).map
      (⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X)).hom.comp
      (complexConstantCohomologyDeRhamAddEquiv X n).symm.toAddMonoidHom)

lemma deRhamConj_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : DeRhamHypercohomology X n) :
    deRhamConj X n α =
      complexConstantCohomologyDeRhamAddEquiv X n
        ((analyticHypercohomologyFunctor X n).map
          (⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
            constantComplexSheafComplexIntPlus X)
          ((complexConstantCohomologyDeRhamAddEquiv X n).symm α)) :=
  rfl

set_option maxHeartbeats 400000 in
/-- Conjugation on de Rham hypercohomology is conjugate-linear. -/
lemma deRhamConj_smul [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : ℂ)
    (α : DeRhamHypercohomology X n) :
    deRhamConj X n (c • α) = (starRingEnd ℂ) c • deRhamConj X n α := by
  rw [deRhamConj_apply, deRhamConj_apply,
    complexConstantCohomologyDeRhamAddEquiv_symm_scalar,
    ← Functor.map_comp_apply]
  have h :
    ((⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X) ≫
      (⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X) :
      constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) =
      ((⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X) ≫
      (⟨complexScalarComplexInt X (starRingEnd ℂ c)⟩ :
        constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) :
      constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) := by
    apply ObjectProperty.hom_ext
    exact complexScalarComplexInt_comp_conj X c
  rw [congrArg (fun f ↦ (analyticHypercohomologyFunctor X n).map f) h]
  rw [Functor.map_comp_apply, complexConstantCohomologyDeRhamAddEquiv_scalar]

/-- Conjugation on de Rham hypercohomology, bundled as a conjugate-linear map. -/
def deRhamConjSemilinear [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →ₛₗ[starRingEnd ℂ] DeRhamHypercohomology X n where
  toFun := deRhamConj X n
  map_add' := (deRhamConj X n).map_add
  map_smul' := deRhamConj_smul X n

/-- The conjugate Hodge filtration `conj F^p`. Conjugation is an involution, so the preimage of
`F^p` is also its image. -/
def conjHodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology X n) :=
  (hodgeFiltrationComplexSubmodule X p n).comap (deRhamConjSemilinear X n)

/-- The intersection `F^p ⊓ conj F^q` in degree `n`. For smooth projective varieties and
`p + q = n`, this is the usual `(p,q)` Hodge piece. -/
def hodgePiece [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    Submodule ℂ (DeRhamHypercohomology X n) :=
  hodgeFiltrationComplexSubmodule X p n ⊓ conjHodgeFiltrationComplexSubmodule X q n

/-- Cohomology classes with coefficients in `K` whose de Rham images lie in `F^p ⊓ conj F^p`
in degree `2p`. When conjugation fixes the image of `K` in `ℂ`, see
`hodgeClasses_eq_comap_hodgeFiltrationComplexSubmodule` for the equivalent `F^p` condition. -/
def hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (H^(2 * p)(X; K)) :=
  ((hodgePiece X p p (2 * p)).restrictScalars K).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))

/-- `Hdg^p(K; f)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is presented by its
structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" K "; " f ")" => hodgeClasses K f p

end AlgebraicGeometry.ComplexPoint
