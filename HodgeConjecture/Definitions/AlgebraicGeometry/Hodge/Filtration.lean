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
open scoped TensorProduct TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

/-- Let `X` be a scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This is the category of
sheaves of abelian groups on `X(ℂ)`. -/
abbrev AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))

local instance analyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance additiveGroupsHasDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- Let `K` be a field with a specified embedding into `ℂ`, and let `X` be a scheme over `ℂ`. This
morphism of constant sheaves on the analytic space `X(ℂ)` sends a locally constant `K`-valued
function to the same function with values in `ℂ`. -/
abbrev fieldToComplexConstantSheaf :
    𝓒(↧(ComplexPoint X); K) ⟶ 𝓒(↧(ComplexPoint X); ℂ) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)

/-- The rational constant sheaf complex as a bounded-below complex. -/
abbrev constantFieldSheafComplexIntPlus :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).obj
    𝓒(↧(ComplexPoint X); K)

/-- The constant sheaf complex is the constant sheaf placed in degree zero. -/
def constantFieldSheafComplexIntIsoSingle :
    (constantFieldSheafComplexIntPlus K X).obj ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        𝓒(↧(ComplexPoint X); K) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint X); K) 0 0 rfl

/-- The holomorphic de Rham complex as a bounded-below complex. -/
abbrev holomorphicDeRhamComplexIntPlus [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨holomorphicDeRhamComplexInt X, ⟨0, inferInstance⟩⟩

/-- Let `K` be a field with a specified embedding into `ℂ`, and let `X` be a scheme over `ℂ`. This
map of integer-indexed complexes applies `K → ℂ` to the constant sheaves in degree zero. Both
complexes are zero in every other degree. -/
def fieldToComplexConstantSheafComplexInt :
    constantFieldSheafComplexIntPlus K X ⟶ constantComplexSheafComplexIntPlus X :=
  (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
    (fieldToComplexConstantSheaf K X)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, this map `K[0] → Ω^•` sends locally constant `K`-valued functions to
holomorphic zero-forms via the embedding. Here `Ω^•` is the complex of sheaves of holomorphic
differential forms with exterior derivative. -/
def fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    constantFieldSheafComplexIntPlus K X ⟶ holomorphicDeRhamComplexIntPlus X :=
  fieldToComplexConstantSheafComplexInt K X ≫
    ⟨constantsToHolomorphicDeRhamComplexInt X⟩

/-- Let `K` be a field, `X` a scheme over `ℂ`, and `q ∈ K`. This endomorphism of the constant sheaf
`K` on the analytic space `X(ℂ)` multiplies each locally constant function by `q`. -/
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
  TopCat.instCategorySheaf._aux_5 in
/-- The inclusion of `K`-valued constants into complex constants commutes with scalar
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
/-- Let `K` be a field, `X` a scheme over `ℂ`, and `q ∈ K`. This endomorphism of the integer-indexed
complex `K[0]` on the analytic space `X(ℂ)` multiplies its degree-zero constant sheaf by `q`. -/
def fieldScalarComplex (q : K) :
    constantFieldSheafComplexIntPlus K X ⟶ constantFieldSheafComplexIntPlus K X :=
  (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map (fieldScalarSheaf K X q)

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_one : fieldScalarComplex K X 1 = 𝟙 _ := by
  simpa only [fieldScalarComplex, fieldScalarSheaf_one] using
    (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map_id
      𝓒(↧(ComplexPoint X); K)

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_add (a b : K) :
    fieldScalarComplex K X (a + b) =
      fieldScalarComplex K X a + fieldScalarComplex K X b := by
  simpa only [fieldScalarComplex, fieldScalarSheaf_add] using
    (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map_add

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_mul (a b : K) :
    fieldScalarComplex K X (a * b) =
      fieldScalarComplex K X b ≫ fieldScalarComplex K X a := by
  simpa only [fieldScalarComplex, fieldScalarSheaf_mul] using
    (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map_comp
      (fieldScalarSheaf K X b) (fieldScalarSheaf K X a)

/-- The integer-indexed inclusion of `K`-valued constants into complex constants commutes with
scalar multiplication. -/
private lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    fieldToComplexConstantSheafComplexInt K X ≫
      (⟨complexScalarComplexInt X (algebraMap K ℂ q)⟩ :
        constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) =
    fieldScalarComplex K X q ≫
      fieldToComplexConstantSheafComplexInt K X := by
  apply ObjectProperty.hom_ext
  change
    HomologicalComplex.extendMap
          ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
            (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (complexScalarComplex X (algebraMap K ℂ q))
          ComplexShape.embeddingUpNat =
      HomologicalComplex.extendMap
          ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
            (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap
          ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
            (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ← Functor.map_comp, complexScalarComplex, ← Functor.map_comp,
    fieldToComplexConstantSheaf_scalar]

/-- The `K`-coefficient to de Rham comparison of complexes commutes with `K`-scalar
multiplication. -/
private lemma fieldToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (q : K) :
    fieldToHolomorphicDeRhamComplexInt K X ≫
      (⟨scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)⟩ :
        holomorphicDeRhamComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) =
    fieldScalarComplex K X q ≫
      fieldToHolomorphicDeRhamComplexInt K X := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc]
  have h :
      ((⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) ≫
        (⟨scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)⟩ :
          holomorphicDeRhamComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) :
        constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) =
      ((⟨complexScalarComplexInt X (algebraMap K ℂ q)⟩ :
          constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) ≫
        (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) :
        constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) := by
    apply ObjectProperty.hom_ext
    exact constantsToHolomorphicDeRhamComplexInt_scalar X (algebraMap K ℂ q)
  rw [h, ← Category.assoc, fieldToComplexConstantSheafComplexInt_scalar, Category.assoc]

/-- `H^n(X; K)` is constant-sheaf cohomology of the analytic space `X(ℂ)` with coefficients in
the field `K`, in integer degree `n`: the hypercohomology of the constant sheaf `K` on `X(ℂ)`.

The literature writes `H^n(X; K)` for the variety `X.left` alone; here the variety is presented by
its structure morphism `X`. -/
scoped notation3:max "H^" n:max "(" X "; " K ")" =>
  letI : HasDerivedCategory AddCommGrpCat := additiveGroupsHasDerivedCategory
  letI : HasDerivedCategory (AnalyticAdditiveSheaf X) := analyticHasDerivedCategory X
  ↥((TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).obj (constantFieldSheafComplexIntPlus K X))

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Holomorphic
de Rham cohomology `H_dR^n(X)` is the degree-`n` hypercohomology of the sheaf complex `𝒪 → Ω¹ →
Ω² → ⋯`, whose differential is exterior differentiation. The complex is zero in negative
degrees. -/
abbrev DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :=
  ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
    (holomorphicDeRhamComplexIntPlus X))

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
inclusion of locally constant complex functions into holomorphic zero-forms gives this
equivalence between constant-sheaf cohomology and holomorphic de Rham cohomology. The holomorphic
Poincaré lemma makes the inclusion of complexes a quasi-isomorphism. -/
def complexConstantCohomologyDeRhamAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X)) ≃+
      DeRhamHypercohomology X n :=
  letI f : (constantComplexSheafComplexIntPlus X :
      CochainComplex.Plus (AnalyticAdditiveSheaf X)) ⟶
      holomorphicDeRhamComplexIntPlus X :=
    ⟨constantsToHolomorphicDeRhamComplexInt X⟩
  letI : QuasiIso f.hom := constantsToHolomorphicDeRhamComplexInt_quasiIso X
  (asIso
    ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f)).addCommGroupIsoToAddEquiv

/-- Scalars acting through an additive functor by an additive, unital and antimultiplicative
family of endomorphisms give a module structure on the functor's value. -/
abbrev moduleOfFunctorEndomorphisms {R D : Type*} [Semiring R]
    [Category D] [Preadditive D] (F : D ⥤ AddCommGrpCat) [F.Additive]
    {C : D} (s : R → (C ⟶ C))
    [SMul R ↥(F.obj C)]
    (smul_eq : ∀ (r : R)
      (α : ↥(F.obj C)), r • α = F.map (s r) α)
    (s_add : ∀ a b : R, s (a + b) = s a + s b)
    (s_one : s 1 = 𝟙 C)
    (s_mul : ∀ a b : R, s (a * b) = s b ≫ s a) :
    Module R ↥(F.obj C) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [smul_eq, smul_eq, smul_eq]
      exact (F.map (s r)).hom.map_add α β)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_add]
      simp)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_mul]
      simp)
    (fun α => by
      rw [smul_eq, s_one]
      simp)

/-- The `K`-action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
noncomputable instance (n : ℤ) :
    SMul K (H^n(X; K)) :=
  ⟨fun q α ↦ (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (fieldScalarComplex K X q) α⟩

omit [Algebra K ℂ] in
lemma field_smul_eq (n : ℤ) (q : K) (α : H^n(X; K)) :
    q • α = (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
      (fieldScalarComplex K X q) α := rfl

/-- For a scheme `X` over `ℂ` and a field `K`, constant-sheaf cohomology `H^n(X(ℂ); K)` is a `K`-
vector space, with scalars acting on coefficient functions. -/
noncomputable instance fieldCohomologyModule (n : ℤ) :
    Module K (H^n(X; K)) :=
  moduleOfFunctorEndomorphisms (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))) (fun q ↦
    fieldScalarComplex K X q)
    (field_smul_eq K X n)
    (fieldScalarComplex_add K X)
    (fieldScalarComplex_one K X)
    (fieldScalarComplex_mul K X)

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
noncomputable instance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul ℂ (DeRhamHypercohomology X n) :=
  ⟨fun c α ↦ (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
      holomorphicDeRhamComplexIntPlus X) α⟩

lemma deRham_complex_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    c • α = (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
      (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
        holomorphicDeRhamComplexIntPlus X) α :=
  rfl

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance deRhamHypercohomologyComplexModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module ℂ (DeRhamHypercohomology X n) :=
  moduleOfFunctorEndomorphisms (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))) (fun c ↦
    (⟨scalarHolomorphicDeRhamComplexInt X c⟩ : holomorphicDeRhamComplexIntPlus X ⟶
      holomorphicDeRhamComplexIntPlus X))
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
    q • α = (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
      (⟨scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)⟩ :
        holomorphicDeRhamComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) α :=
  rfl

/-- Restriction of complex scalars gives the scalar tower on de Rham hypercohomology. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ (DeRhamHypercohomology X n) :=
  IsScalarTower.restrictScalars K ℂ (DeRhamHypercohomology X n)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, this additive map `H^n(X(ℂ); K) → H_dR^n(X)` is induced by including
locally constant `K`-valued functions as holomorphic zero-forms. -/
def fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; K) →+ DeRhamHypercohomology X n :=
  ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (fieldToHolomorphicDeRhamComplexInt K X)).hom

/-- The `K`-coefficient to de Rham comparison is compatible with `K`-scalar multiplication. -/
lemma fieldToDeRhamCohomology_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (q : K) (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n (q • α) =
      q • fieldToDeRhamCohomology K X n α := by
  rw [field_smul_eq, deRham_field_smul_eq]
  unfold fieldToDeRhamCohomology
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1
  apply congrArg (fun f ↦ ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f).hom)
  exact (fieldToHolomorphicDeRhamComplexInt_scalar K X q).symm

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, the inclusion `K[0] → Ω^•` induces this `K`-linear map from constant-sheaf
cohomology `H^n(X(ℂ); K)` to holomorphic de Rham cohomology `H_dR^n(X)`. -/
def fieldToDeRhamCohomologyLinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; K) →ₗ[K]
      DeRhamHypercohomology X n where
  toFun := fieldToDeRhamCohomology K X n
  map_add' := (fieldToDeRhamCohomology K X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K X n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, the complex `F^p Ω^•` has the sheaf of holomorphic `q`-forms in degrees `q ≥ p` and
zero in degrees `q < p`. Its remaining differentials are exterior derivatives; this is the
truncation by form degree. -/
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

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, this map `F^p Ω^• → Ω^•` is the identity on holomorphic forms in degrees at least
`p` and the zero map below `p`, where the source is zero. -/
def hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    hodgeFilteredDeRhamComplex X p ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamComplexInt X) (ComplexShape.embeddingUpIntGE p)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p` and a scalar `c ∈ ℂ`, this endomorphism multiplies forms by `c` in the complex `F^p
Ω^•` of holomorphic forms in degrees at least `p`, which is zero in lower degrees. -/
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

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, this is `ℍ^n(X(ℂ); F^p Ω^•)`, the hypercohomology of the holomorphic de
Rham complex with terms below form degree `p` replaced by zero. -/
abbrev FilteredDeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) :=
  ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
    (hodgeFilteredDeRhamComplexPlus X p))

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, inclusion of holomorphic forms of degree at least `p` into the full de
Rham complex induces this map `ℍ^n(X(ℂ); F^p Ω^•) → H_dR^n(X)`. -/
def filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    FilteredDeRhamHypercohomology X p n →+
      DeRhamHypercohomology X n :=
  ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (⟨hodgeFilteredDeRhamInclusion X p⟩ : hodgeFilteredDeRhamComplexPlus X p ⟶
      holomorphicDeRhamComplexIntPlus X)).hom

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The `p`-th
Hodge filtration in degree `n` is the additive subgroup `F^p H_dR^n(X)` given by the image of
`ℍ^n(X(ℂ); F^p Ω^•) → ℍ^n(X(ℂ); Ω^•)`. The source complex keeps holomorphic forms of degree at
least `p` and is zero in lower degrees. -/
def hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    AddSubgroup (DeRhamHypercohomology X n) :=
  (filteredToDeRhamCohomology X p n).range

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma hodgeFiltration_complex_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (c : ℂ) {α : DeRhamHypercohomology X n}
    (hα : α ∈ hodgeFiltration X p n) :
    c • α ∈ hodgeFiltration X p n := by
  rcases hα with ⟨β, rfl⟩
  refine ⟨(ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (⟨hodgeFilteredDeRhamComplexScalar X p c⟩ : hodgeFilteredDeRhamComplexPlus X p ⟶
      hodgeFilteredDeRhamComplexPlus X p) β, ?_⟩
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1
  apply congrArg (fun f ↦ ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f).hom)
  apply ObjectProperty.hom_ext
  exact hodgeFilteredDeRhamComplexScalar_comp_inclusion X p c

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The complex
subspace `F^p H_dR^n(X)` is the image on degree-`n` hypercohomology of the inclusion of
holomorphic forms of degrees at least `p` into the full de Rham complex. -/
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
    (n : ℤ) (α : ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n α =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
        (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) α := by
  unfold complexConstantCohomologyDeRhamAddEquiv
  rfl

/-- The comparison equivalence carries the constant-sheaf scalar action to the de Rham one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (β : ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n
        ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
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
  let F := ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))
  rw [congrArg F.map h,
    Functor.map_comp_apply, deRham_complex_smul_eq]

/-- The inverse comparison carries the de Rham scalar action back to the constant-sheaf one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_symm_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    (complexConstantCohomologyDeRhamAddEquiv X n).symm (c • α) =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
        (⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
          constantComplexSheafComplexIntPlus X)
        ((complexConstantCohomologyDeRhamAddEquiv X n).symm α) := by
  apply (complexConstantCohomologyDeRhamAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, complexConstantCohomologyDeRhamAddEquiv_scalar,
    AddEquiv.apply_symm_apply]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
additive endomorphism of `H_dR^n(X)` is complex conjugation transported through the equivalence
between constant-sheaf cohomology and de Rham cohomology. On constant-sheaf cohomology,
conjugation is induced by conjugating the locally constant coefficient functions. -/
def deRhamConj [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →+ DeRhamHypercohomology X n :=
  ((complexConstantCohomologyDeRhamAddEquiv X n).toAddMonoidHom).comp
    (((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
      (⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
        constantComplexSheafComplexIntPlus X)).hom.comp
      (complexConstantCohomologyDeRhamAddEquiv X n).symm.toAddMonoidHom)

lemma deRhamConj_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : DeRhamHypercohomology X n) :
    deRhamConj X n α =
      complexConstantCohomologyDeRhamAddEquiv X n
        ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
          (⟨conjConstantComplexSheafComplexInt X⟩ : constantComplexSheafComplexIntPlus X ⟶
            constantComplexSheafComplexIntPlus X)
          ((complexConstantCohomologyDeRhamAddEquiv X n).symm α)) :=
  rfl

/-- Conjugation on de Rham hypercohomology is conjugate-linear. -/
lemma deRhamConj_smul [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : ℂ)
    (α : DeRhamHypercohomology X n) :
    deRhamConj X n (c • α) = (starRingEnd ℂ) c • deRhamConj X n α := by
  rw [deRhamConj_apply, deRhamConj_apply,
    complexConstantCohomologyDeRhamAddEquiv_symm_scalar]
  let F := ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))
  let s : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨complexScalarComplexInt X c⟩
  let j : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨conjConstantComplexSheafComplexInt X⟩
  let s' : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨complexScalarComplexInt X (starRingEnd ℂ c)⟩
  let β := (complexConstantCohomologyDeRhamAddEquiv X n).symm α
  have h : s ≫ j = j ≫ s' := by
    apply ObjectProperty.hom_ext
    exact complexScalarComplexInt_comp_conj X c
  change (complexConstantCohomologyDeRhamAddEquiv X n) (F.map j (F.map s β)) =
    starRingEnd ℂ c • (complexConstantCohomologyDeRhamAddEquiv X n) (F.map j β)
  calc
    _ = (complexConstantCohomologyDeRhamAddEquiv X n) (F.map (s ≫ j) β) :=
      congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
        (Functor.map_comp_apply F s j β).symm
    _ = (complexConstantCohomologyDeRhamAddEquiv X n) (F.map (j ≫ s') β) :=
      congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
        (congrArg (fun f ↦ F.map f β) h)
    _ = (complexConstantCohomologyDeRhamAddEquiv X n) (F.map s' (F.map j β)) :=
      congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
        (Functor.map_comp_apply F j s' β)
    _ = _ := complexConstantCohomologyDeRhamAddEquiv_scalar X n (starRingEnd ℂ c) _

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Conjugation
of constant complex coefficients, transported through the equivalence between constant-sheaf
cohomology and de Rham cohomology, gives this conjugate-linear endomorphism of de Rham cohomology.
It sends `c α` to `conj(c) conj(α)`. -/
def deRhamConjSemilinear [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →ₛₗ[starRingEnd ℂ] DeRhamHypercohomology X n where
  toFun := deRhamConj X n
  map_add' := (deRhamConj X n).map_add
  map_smul' := deRhamConj_smul X n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
conjugate Hodge filtration in degree `n` consists of classes whose complex conjugates lie in
`F^p H_dR^n(X)`. Here `F^p` is the image of the hypercohomology of holomorphic forms of degree
at least `p`, and conjugation is transported from constant complex coefficients. -/
def conjHodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology X n) :=
  (hodgeFiltrationComplexSubmodule X p n).comap (deRhamConjSemilinear X n)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
complex subspace of `H_dR^n(X)` is `F^p ∩ conjugate(F^q)`, where `F^r` is the image of the
hypercohomology of holomorphic forms in degrees at least `r`. Conjugation comes from constant
complex coefficients. When `X` is projective and `p + q = n`, this is the Hodge component of
type `(p,q)`. -/
def hodgePiece [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    Submodule ℂ (DeRhamHypercohomology X n) :=
  hodgeFiltrationComplexSubmodule X p n ⊓ conjHodgeFiltrationComplexSubmodule X q n

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ` and a natural number `p`, these are the classes in `H^{2p}(X(ℂ); K)` whose
de Rham images belong to `F^p ∩ conjugate(F^p)`. The filtration `F^p` is the image of the
hypercohomology of holomorphic forms of degrees at least `p`. Conjugation is induced by
conjugating constant complex coefficients; for projective `X`, the intersection is the Hodge
component of type `(p,p)`. -/
def hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (H^(2 * p)(X; K)) :=
  ((hodgePiece X p p (2 * p)).restrictScalars K).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))

/-- `Hdg^p(f; K)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is
presented by its structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" f "; " K ")" => hodgeClasses K f p

end AlgebraicGeometry.ComplexPoint
