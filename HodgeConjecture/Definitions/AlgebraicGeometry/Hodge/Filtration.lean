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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.ModuleHolomorphicDeRham
public import HodgeConjecture.Lemmas.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Mathlib.Algebra.Homology.StupidTruncation
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.Hypercohomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.HypercohomologyChangeOfRings
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Data.Int.Cast.Lemmas

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
import HodgeConjecture.Mathlib.Algebra.Ring.Basic
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

/-- Multiplying by `q` in `K` before including into `ℂ` agrees with including first and then
multiplying by `algebraMap K ℂ q`. -/
private lemma ofHom_algebraMap_comp_complexScalarSMul (q : K) :
    AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ (algebraMap K ℂ q)) =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft q) ≫
        AddCommGrpCat.ofHom (@AddMonoidHomClass.toAddMonoidHom K ℂ (K →+* ℂ)
          Field.toSemifield.toNonAssocSemiring.toAddCommMonoidWithOne.toAddZeroClass.toAddZero
          Complex.instSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddZeroClass.toAddZero
          RingHom.instFunLike _ (algebraMap K ℂ)) := by
  ext r
  simp [map_mul]

/-- The constant-presheaf map induced by the inclusion `K → ℂ`, followed by scalar multiplication
by `algebraMap K ℂ q` on the constant complex presheaf, is the constant-presheaf map induced by the
composite additive map. -/
private lemma const_map_algebraMap_comp_complexScalarPresheaf (q : K) :
    (Functor.const (Opens (ComplexPoint X))ᵒᵖ).map
        (AddCommGrpCat.ofHom ↑(algebraMap K ℂ)) ≫
    complexScalarPresheaf X ((algebraMap K ℂ) q) =
    (Functor.const (Opens (ComplexPoint X))ᵒᵖ).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ : K →+ ℂ) ≫
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ ((algebraMap K ℂ) q))) := rfl

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- The inclusion of `K`-valued constants into complex constants commutes with scalar
multiplication. -/
private lemma fieldToComplexConstantSheaf_scalar (q : K) :
    fieldToComplexConstantSheaf K X ≫
      complexScalarSheaf X (algebraMap K ℂ q) =
    fieldScalarSheaf K X q ≫ fieldToComplexConstantSheaf K X := by
  simp [fieldToComplexConstantSheaf, fieldScalarSheaf, complexScalarSheaf, constantSheaf,
    TopCat.Sheaf.const, TopCat.Sheaf.constantFunctor, ← Functor.map_comp,
    ← ofHom_algebraMap_comp_complexScalarSMul,
    const_map_algebraMap_comp_complexScalarPresheaf]

/-- The integer-indexed inclusion of `K`-valued constants into complex constants commutes with
scalar multiplication. -/
private lemma fieldToComplexConstantSheafComplexInt_scalar (q : K) :
    fieldToComplexConstantSheafComplexInt K X ≫
      (⟨complexScalarComplexInt X (algebraMap K ℂ q)⟩ :
        constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) =
    fieldScalarComplex K X q ≫ fieldToComplexConstantSheafComplexInt K X := by
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

local instance analyticModuleHasDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

local instance complexModuleHasDerivedCategory : HasDerivedCategory (ModuleCat ℂ) :=
  HasDerivedCategory.standard _

local instance fieldModuleHasDerivedCategory :
    HasDerivedCategory (ModuleCat K) :=
  HasDerivedCategory.standard _

local instance fieldModuleSheafHasDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

/-- The constant presheaf of `R`-modules on the analytic space `X(ℂ)`. -/
abbrev constantModulePresheaf (R : Type) [CommRing R] :
    TopCat.Presheaf (ModuleCat R) (TopCat.of (ComplexPoint X)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (ModuleCat.of R R)

/-- The constant sheaf of `R`-modules on the analytic space `X(ℂ)`. -/
def constantModuleSheaf (R : Type) [CommRing R] :
    TopCat.Sheaf (ModuleCat R) (TopCat.of (ComplexPoint X)) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (ModuleCat R)).obj (ModuleCat.of R R)

/-- The constant sheaf of `R`-modules placed in degree zero as a bounded-below complex on
`X(ℂ)`. -/
abbrev constantModuleSheafComplexIntPlus (R : Type) [CommRing R] :
    CochainComplex.Plus
      (TopCat.Sheaf (ModuleCat R) (TopCat.of (ComplexPoint X))) :=
  (CochainComplex.Plus.single₀ _).obj (constantModuleSheaf X R)

/-- The linear map between regular modules induced by a ring homomorphism. -/
def ringHomLinearMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat.of R R ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) :=
  ModuleCat.homMk (AddCommGrpCat.ofHom f.toAddMonoidHom) (by
    intro r
    ext x
    exact (f.map_mul r x).symm)

/-- The map of constant module sheaves induced by a ring homomorphism. -/
def constantModuleSheafMap {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) :
    constantModuleSheaf X R ⟶
      (CategoryTheory.Sheaf.restrictScalars
        (C := Opens (TopCat.of (ComplexPoint X))) (R := R) (S := S)
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) f).obj
        (constantModuleSheaf X S) :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  letI U := ModuleCat.restrictScalars f
  (constantSheaf J (ModuleCat R)).map (ringHomLinearMap f) ≫
    (CategoryTheory.constantCommuteCompose J U).inv.app (ModuleCat.of S S)

/-- The map between degree-zero constant module complexes induced by a ring homomorphism. -/
def constantModuleComplexMap {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) :
    constantModuleSheafComplexIntPlus X R ⟶
      (CategoryTheory.Sheaf.restrictScalars
        (C := Opens (TopCat.of (ComplexPoint X))) (R := R) (S := S)
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) f).mapCochainComplexPlus.obj
        (constantModuleSheafComplexIntPlus X S) :=
  (CochainComplex.Plus.single₀ _).map (constantModuleSheafMap X f) ≫
    (CochainComplex.Plus.mapSingle₀Iso
      (CategoryTheory.Sheaf.restrictScalars
        (C := Opens (TopCat.of (ComplexPoint X))) (R := R) (S := S)
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) f)
      (constantModuleSheaf X S)).inv

/-- Forgetting the module structure of the constant `R`-module sheaf gives the constant sheaf of
additive groups. -/
noncomputable def constantModuleSheafForgetIso (R : Type) [CommRing R] :
    (CategoryTheory.sheafCompose (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat R) AddCommGrpCat)).obj
        (constantModuleSheaf X R) ≅
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of R) :=
  (CategoryTheory.constantCommuteCompose
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ (ModuleCat R) AddCommGrpCat)).app (ModuleCat.of R R)

/-- Forgetting the module structure of the constant `R`-module complex gives the corresponding
constant complex of additive groups. -/
noncomputable def constantModuleSheafForgetComplexIso (R : Type) [CommRing R] :
    (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat R) AddCommGrpCat)).mapCochainComplexPlus.obj
      (constantModuleSheafComplexIntPlus X R) ≅
      (CochainComplex.Plus.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of R)) :=
  CochainComplex.Plus.mapSingle₀Iso
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat R) AddCommGrpCat))
      (constantModuleSheaf X R) ≪≫
    (CochainComplex.Plus.single₀ _).mapIso (constantModuleSheafForgetIso X R)

/-- Scalar multiplication on the constant `K`-module sheaf. -/
noncomputable def fieldScalarModuleSheaf (q : K) :
    constantModuleSheaf X K ⟶ constantModuleSheaf X K :=
  letI J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J (ModuleCat K)).map (ModuleCat.ofHom (LinearMap.lsmul K K q))

omit [Algebra K ℂ] in
private lemma fieldScalarModuleSheaf_eq_smul_id (q : K) :
    fieldScalarModuleSheaf K X q = q • 𝟙 _ := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let F := constantSheaf J (ModuleCat K)
  have hbase : ModuleCat.ofHom (LinearMap.lsmul K K q) =
      q • 𝟙 (ModuleCat.of K K) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  change F.map (ModuleCat.ofHom (LinearMap.lsmul K K q)) =
    q • 𝟙 (F.obj (ModuleCat.of K K))
  rw [hbase]
  exact (Functor.linear_iff K F).mp inferInstance _ q

/-- Scalar multiplication on the constant `K`-module complex. -/
noncomputable def fieldScalarModuleComplex (q : K) :
    constantModuleSheafComplexIntPlus X K ⟶ constantModuleSheafComplexIntPlus X K :=
  (CochainComplex.Plus.single₀ _).map (fieldScalarModuleSheaf K X q)

omit [Algebra K ℂ] in
private lemma fieldScalarModuleComplex_eq_smul_id (q : K) :
    fieldScalarModuleComplex K X q = q • 𝟙 _ := by
  unfold fieldScalarModuleComplex
  rw [fieldScalarModuleSheaf_eq_smul_id]
  exact (Functor.linear_iff K
    (CochainComplex.Plus.single₀
      (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))))).mp inferInstance _ q

/-- `H^n(X; K)` is constant-sheaf cohomology of the analytic space `X(ℂ)` with coefficients in
the field `K`, in integer degree `n`: the hypercohomology of the constant sheaf `K` on `X(ℂ)`.

The literature writes `H^n(X; K)` for the variety `X.left` alone; here the variety is presented by
its structure morphism `X`. -/
scoped notation3:max "H^" n:max "(" X "; " K ")" =>
  letI : HasDerivedCategory (ModuleCat K) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (TopCat.Sheaf (ModuleCat K)
      (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _
  ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
      (TopCat.of (ComplexPoint X)) n).obj (constantModuleSheafComplexIntPlus X K))

omit [Algebra K ℂ] in
/-- Scalar multiplication on `H^n(X; K)` is induced by the scalar endomorphism of the constant
`K`-module complex. -/
lemma field_smul_eq (n : ℤ) (q : K) (α : H^n(X; K)) :
    q • α =
      ((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
        (TopCat.of (ComplexPoint X)) n).map (fieldScalarModuleComplex K X q)).hom α := by
  rw [fieldScalarModuleComplex_eq_smul_id]
  have h := (Functor.linear_iff K
      (TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
        (TopCat.of (ComplexPoint X)) n)).mp inferInstance
    (constantModuleSheafComplexIntPlus X K) q
  exact (ConcreteCategory.congr_hom h α).symm

/-- The underlying additive group of module-valued constant-sheaf hypercohomology is canonically
equivalent to the additive-group-valued constant-sheaf hypercohomology. -/
noncomputable def constantModuleCohomologyToAdditiveEquiv
    (n : ℤ) :
    H^n(X; K) ≃+
      ↥((TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X)) n).obj (constantFieldSheafComplexIntPlus K X)) :=
  letI : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
  letI : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat K) AddCommGrpCat)) :=
    CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)
  letI :
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat K) AddCommGrpCat)).PreservesInjectiveObjects :=
    CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.Sheaf.intAlgebraMap_flat K)
  letI e := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := K)
    (TopCat.of (ComplexPoint X)) n
  (e.app (constantModuleSheafComplexIntPlus X K) ≪≫
    (TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).mapIso
      (constantModuleSheafForgetComplexIso X K)).addCommGroupIsoToAddEquiv

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
lemma constantModuleCohomologyToAdditiveEquiv_map_smul
    (n : ℤ) (q : K) (x : H^n(X; K)) :
    constantModuleCohomologyToAdditiveEquiv K X n (q • x) =
      (TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X)) n).map (fieldScalarComplex K X q)
        (constantModuleCohomologyToAdditiveEquiv K X n x) := by
  let : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
  let : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat K) AddCommGrpCat)) :=
    CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)
  let :
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat K) AddCommGrpCat)).PreservesInjectiveObjects :=
    CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.Sheaf.intAlgebraMap_flat K)
  let e := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := K)
    (TopCat.of (ComplexPoint X)) n
  let P : TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)) ⥤
      TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
    CategoryTheory.sheafCompose
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (forget₂ (ModuleCat K) AddCommGrpCat)
  let : P.Additive := by
    change (CategoryTheory.sheafCompose (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat K) AddCommGrpCat)).Additive
    infer_instance
  let : P.PreservesZeroMorphisms := P.preservesZeroMorphisms_of_additive
  let L := constantModuleSheafForgetComplexIso X K
  have hL :
      P.mapCochainComplexPlus.map (fieldScalarModuleComplex K X q) ≫ L.hom =
        L.hom ≫ fieldScalarComplex K X q := by
    dsimp only [L, constantModuleSheafForgetComplexIso, fieldScalarModuleComplex,
      fieldScalarComplex, Iso.trans_hom, Functor.mapIso_hom]
    rw [CochainComplex.Plus.mapSingle₀Iso_hom_naturality_assoc]
    simp only [Category.assoc]
    apply (cancel_epi (CochainComplex.Plus.mapSingle₀Iso P
      (constantModuleSheaf X K)).hom).2
    let STop := CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)
    let S := CochainComplex.Plus.single₀
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat)
    have hSheaf :
        P.map (fieldScalarModuleSheaf K X q) ≫
            (constantModuleSheafForgetIso X K).hom =
          (constantModuleSheafForgetIso X K).hom ≫ fieldScalarSheaf K X q := by
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
      let U := forget₂ (ModuleCat K) AddCommGrpCat
      let f := ModuleCat.ofHom (LinearMap.lsmul K K q)
      exact (CategoryTheory.constantCommuteCompose J U).hom.naturality f
    change STop.map (P.map (fieldScalarModuleSheaf K X q)) ≫
        S.map (constantModuleSheafForgetIso X K).hom =
      S.map (constantModuleSheafForgetIso X K).hom ≫
        STop.map (fieldScalarSheaf K X q)
    rw [show STop.map (P.map (fieldScalarModuleSheaf K X q)) =
      S.map (P.map (fieldScalarModuleSheaf K X q)) from rfl]
    rw [show STop.map (fieldScalarSheaf K X q) =
      S.map (fieldScalarSheaf K X q) from rfl]
    rw [← S.map_comp, hSheaf, S.map_comp]
  let E := constantModuleCohomologyToAdditiveEquiv K X n
  let F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  let A := constantModuleSheafComplexIntPlus X K
  have h := congrArg F.map hL
  rw [Functor.map_comp, Functor.map_comp] at h
  have he := e.hom.naturality (fieldScalarModuleComplex K X q)
  dsimp only [Functor.comp_map] at he
  have hm :
      ((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
        (TopCat.of (ComplexPoint X)) n).map
          (fieldScalarModuleComplex K X q)).hom x = q • x := by
    rw [fieldScalarModuleComplex_eq_smul_id]
    have h := (Functor.linear_iff K
      (TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
        (TopCat.of (ComplexPoint X)) n)).mp inferInstance A q
    exact ConcreteCategory.congr_hom h x
  have he_x := ConcreteCategory.congr_hom he x
  change (e.hom.app A)
      (((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat K)
        (TopCat.of (ComplexPoint X)) n).map
          (fieldScalarModuleComplex K X q)).hom x) =
    (F.map (P.mapCochainComplexPlus.map (fieldScalarModuleComplex K X q))).hom
      ((e.hom.app A) x) at he_x
  rw [hm] at he_x
  have h_x := ConcreteCategory.congr_hom h (e.hom.app A x)
  change (F.map L.hom).hom
      ((F.map (P.mapCochainComplexPlus.map (fieldScalarModuleComplex K X q))).hom
        ((e.hom.app A) x)) =
    (F.map (fieldScalarComplex K X q)).hom
      ((F.map L.hom).hom ((e.hom.app A) x)) at h_x
  change (F.map L.hom).hom (e.hom.app A (q • x)) =
    (F.map (fieldScalarComplex K X q)).hom
      ((F.map L.hom).hom (e.hom.app A x))
  rw [he_x, h_x]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Holomorphic
de Rham cohomology `H_dR^n(X)` is the degree-`n` hypercohomology of the sheaf complex `𝒪 → Ω¹ →
Ω² → ⋯`, whose differential is exterior differentiation. The complex is zero in negative
degrees. -/
abbrev DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :=
  ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (holomorphicDeRhamModuleComplexPlus X))

noncomputable instance constantComplexCohomologyModule (n : ℤ) :
    Module K (↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X))) :=
  Module.restrictScalars K ℂ _

noncomputable instance constantComplexCohomologyIsScalarTower (n : ℤ) :
    IsScalarTower K ℂ (↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X))) :=
  IsScalarTower.restrictScalars K ℂ _

/-- De Rham hypercohomology as a vector space over `K`, by restriction of complex scalars. -/
noncomputable instance deRhamHypercohomologyModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module K (DeRhamHypercohomology X n) :=
  Module.restrictScalars K ℂ _

/-- Restriction of complex scalars gives the scalar tower on de Rham hypercohomology. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ (DeRhamHypercohomology X n) :=
  IsScalarTower.restrictScalars K ℂ _

/-- The map from the constant `K`-module complex to the constant complex-module complex induced by
the embedding `K →+* ℂ`. -/
def fieldToComplexModuleComplex :
    constantModuleSheafComplexIntPlus X K ⟶
      (CategoryTheory.Sheaf.restrictScalars
        (C := Opens (TopCat.of (ComplexPoint X))) (R := K) (S := ℂ)
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (algebraMap K ℂ)).mapCochainComplexPlus.obj
        (constantComplexModuleSheafIntPlus X) :=
  constantModuleComplexMap X (algebraMap K ℂ)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
inclusion of locally constant complex functions into holomorphic zero-forms gives this
equivalence between constant-sheaf cohomology and holomorphic de Rham cohomology. The holomorphic
Poincaré lemma makes the inclusion of complexes a quasi-isomorphism. -/
noncomputable def complexConstantCohomologyDeRhamLinearEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) ≃ₗ[ℂ]
      DeRhamHypercohomology X n :=
  letI f : constantComplexModuleSheafIntPlus X ⟶ holomorphicDeRhamModuleComplexPlus X :=
    ⟨constantsToHolomorphicDeRhamModuleComplexInt X⟩
  letI : QuasiIso f.hom := constantsToHolomorphicDeRhamModuleComplexInt_quasiIso X
  (asIso
    ((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).map f)).toLinearEquiv

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
inclusion of locally constant complex functions into holomorphic zero-forms gives this
equivalence between constant-sheaf cohomology and holomorphic de Rham cohomology. The holomorphic
Poincaré lemma makes the inclusion of complexes a quasi-isomorphism. -/
noncomputable def complexConstantCohomologyDeRhamAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) ≃+
      DeRhamHypercohomology X n :=
  (complexConstantCohomologyDeRhamLinearEquiv X n).toAddEquiv

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, the complex `F^p Ω^•` has the sheaf of holomorphic `q`-forms in degrees `q ≥ p` and
zero in degrees `q < p`. Its remaining differentials are exterior derivatives; this is the
truncation by form degree. -/
def hodgeFilteredDeRhamComplex [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex
      (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) ℤ :=
  (holomorphicDeRhamModuleComplexInt X).stupidTrunc
    (ComplexShape.embeddingUpIntGE p)

instance [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    (hodgeFilteredDeRhamComplex X p).IsStrictlyGE p := by
  unfold hodgeFilteredDeRhamComplex
  infer_instance

/-- The filtered de Rham complex as a bounded-below complex. -/
abbrev hodgeFilteredDeRhamComplexPlus [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) :=
  ⟨hodgeFilteredDeRhamComplex X p, ⟨p, inferInstance⟩⟩

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For an
integer `p`, this map `F^p Ω^• → Ω^•` is the identity on holomorphic forms in degrees at least
`p` and the zero map below `p`, where the source is zero. -/
def hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    hodgeFilteredDeRhamComplex X p ⟶ holomorphicDeRhamModuleComplexInt X :=
  HomologicalComplex.stupidTruncInclusion
    (holomorphicDeRhamModuleComplexInt X) (ComplexShape.embeddingUpIntGE p)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, this is `ℍ^n(X(ℂ); F^p Ω^•)`, the hypercohomology of the holomorphic de
Rham complex with terms below form degree `p` replaced by zero. -/
abbrev FilteredDeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) :=
  ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
    (TopCat.of (ComplexPoint X)) n).obj (hodgeFilteredDeRhamComplexPlus X p))

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For
integers `p` and `n`, inclusion of holomorphic forms of degree at least `p` into the full de
Rham complex induces this map `ℍ^n(X(ℂ); F^p Ω^•) → H_dR^n(X)`. -/
def filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    FilteredDeRhamHypercohomology X p n →ₗ[ℂ] DeRhamHypercohomology X n :=
  ((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
    (TopCat.of (ComplexPoint X)) n).map
      (⟨hodgeFilteredDeRhamInclusion X p⟩ :
        hodgeFilteredDeRhamComplexPlus X p ⟶ holomorphicDeRhamModuleComplexPlus X)).hom

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The `p`-th
Hodge filtration in degree `n` is the additive subgroup `F^p H_dR^n(X)` given by the image of
`ℍ^n(X(ℂ); F^p Ω^•) → ℍ^n(X(ℂ); Ω^•)`. The source complex keeps holomorphic forms of degree at
least `p` and is zero in lower degrees. -/
def hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    Submodule ℂ (DeRhamHypercohomology X n) :=
  (filteredToDeRhamCohomology X p n).range

/-! ### Complex conjugation and the `(p,p)` part

Conjugation is not `ℂ`-linear, so it acts on the constant sheaf `ℂ` rather than on the holomorphic
de Rham complex, and is transported across the constant-to-de Rham comparison. The `(p,q)` piece
is then *defined* as `F^p ⊓ conj F^q`, which needs no Hodge decomposition theorem. -/

section ComplexConjugation

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

noncomputable def constantComplexModuleSheafForgetComplexIso :
    (analyticModuleSheafToAddCommGrp X).mapCochainComplexPlus.obj
        (constantComplexModuleSheafIntPlus X) ≅
      constantComplexSheafComplexIntPlus X :=
  CochainComplex.Plus.mapSingle₀Iso (analyticModuleSheafToAddCommGrp X)
      (constantComplexModuleSheaf X) ≪≫
    (CochainComplex.Plus.single₀ _).mapIso (constantComplexModuleSheaf_forgetIso X)

/-- The underlying additive group of complex constant-sheaf hypercohomology is canonically
equivalent to the additive-group-valued constant-sheaf hypercohomology. -/
noncomputable def constantComplexModuleCohomologyToAdditiveEquiv (n : ℤ) :
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) ≃+
      ↥((TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
        (TopCat.of (ComplexPoint X)) n).obj (constantComplexSheafComplexIntPlus X)) :=
  letI : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat ℂ) AddCommGrpCat)) :=
    CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)
  letI :
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat ℂ) AddCommGrpCat)).PreservesInjectiveObjects :=
    CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.Sheaf.intAlgebraMap_flat ℂ)
  letI e := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := ℂ)
    (TopCat.of (ComplexPoint X)) n
  (e.app (constantComplexModuleSheafIntPlus X) ≪≫
    (TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).mapIso
      (constantComplexModuleSheafForgetComplexIso X)).addCommGroupIsoToAddEquiv

set_option maxHeartbeats 2000000 in
lemma constantComplexModuleCohomologyToAdditiveEquiv_map_smul (n : ℤ) (c : ℂ)
    (x : ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X))) :
    constantComplexModuleCohomologyToAdditiveEquiv X n (c • x) =
      (TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).map
        (⟨complexScalarComplexInt X c⟩ : constantComplexSheafComplexIntPlus X ⟶
          constantComplexSheafComplexIntPlus X)
      (constantComplexModuleCohomologyToAdditiveEquiv X n x) := by
  let : PreservesFiniteColimits
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat ℂ) AddCommGrpCat)) :=
    CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)
  let :
      (CategoryTheory.sheafCompose (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) (forget₂ (ModuleCat ℂ) AddCommGrpCat)).PreservesInjectiveObjects :=
    CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (CategoryTheory.Sheaf.intAlgebraMap_flat ℂ)
  let e := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := ℂ)
    (TopCat.of (ComplexPoint X)) n
  let P := analyticModuleSheafToAddCommGrp X
  let L := constantComplexModuleSheafForgetComplexIso X
  let f : constantComplexModuleSheaf X ⟶ constantComplexModuleSheaf X :=
    fieldScalarModuleSheaf ℂ X c
  let g : constantComplexModuleSheafIntPlus X ⟶ constantComplexModuleSheafIntPlus X :=
    (CochainComplex.Plus.single₀ _).map f
  have hL :
      P.mapCochainComplexPlus.map g ≫ L.hom =
        L.hom ≫ (CochainComplex.Plus.single₀ _).map
          (complexScalarSheaf X c) := by
    dsimp only [L, constantComplexModuleSheafForgetComplexIso,
      Iso.trans_hom, Functor.mapIso_hom]
    change
      P.mapCochainComplexPlus.map ((CochainComplex.Plus.single₀ _).map f) ≫
          (CochainComplex.Plus.mapSingle₀Iso P (constantComplexModuleSheaf X)).hom ≫
        (CochainComplex.Plus.single₀ _).map (constantComplexModuleSheaf_forgetIso X).hom =
      ((CochainComplex.Plus.mapSingle₀Iso P (constantComplexModuleSheaf X)).hom ≫
          (CochainComplex.Plus.single₀ _).map (constantComplexModuleSheaf_forgetIso X).hom) ≫
        (CochainComplex.Plus.single₀ _).map (complexScalarSheaf X c)
    rw [CochainComplex.Plus.mapSingle₀Iso_hom_naturality_assoc]
    simp only [Category.assoc]
    let S := CochainComplex.Plus.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))
    have hSheaf :
        P.map f ≫
            (constantComplexModuleSheaf_forgetIso X).hom =
          (constantComplexModuleSheaf_forgetIso X).hom ≫ complexScalarSheaf X c := by
      let p : constantComplexModulePresheaf X ⟶ constantComplexModulePresheaf X :=
        (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map
          (ModuleCat.ofHom (LinearMap.lsmul ℂ ℂ c))
      have hf :
          Functor.whiskerRight p (forget₂ (ModuleCat ℂ) AddCommGrpCat) =
            complexScalarPresheaf X c := by
        ext U
        rfl
      rw [hf] at *
      change P.map ((presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (ModuleCat ℂ)).map p) ≫
          (analyticModuleSheafificationForgetIso X (constantComplexModulePresheaf X)).hom =
        (analyticModuleSheafificationForgetIso X (constantComplexModulePresheaf X)).hom ≫
          (presheafToSheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
            (complexScalarPresheaf X c)
      exact (analyticModuleSheafificationForgetIso_hom_naturality X p).symm
    slice_lhs 2 3 => rw [← S.map_comp, hSheaf, S.map_comp]
  let E := constantComplexModuleCohomologyToAdditiveEquiv X n
  let F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  let K := constantComplexModuleSheafIntPlus X
  let h := congrArg F.map hL
  simp only [Functor.map_comp] at h
  have he := e.hom.naturality g
  dsimp only [Functor.comp_map] at he
  have hm :
      ((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).map
          g).hom x = c • x := by
    rw [show g = c • 𝟙 _ by
      change fieldScalarModuleComplex ℂ X c = c • 𝟙 (constantModuleSheafComplexIntPlus X ℂ)
      exact fieldScalarModuleComplex_eq_smul_id ℂ X c]
    have h := (Functor.linear_iff ℂ
      (TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n)).mp inferInstance
        (constantComplexModuleSheafIntPlus X) c
    exact ConcreteCategory.congr_hom h x
  have he_x := ConcreteCategory.congr_hom he x
  change (e.hom.app K)
      (((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).map
          g).hom x) =
    (F.map (P.mapCochainComplexPlus.map g)).hom
      ((e.hom.app K) x) at he_x
  rw [hm] at he_x
  have h_x := ConcreteCategory.congr_hom h (e.hom.app K x)
  change (F.map L.hom).hom
      ((F.map (P.mapCochainComplexPlus.map g)).hom
        ((e.hom.app K) x)) =
    (F.map ((CochainComplex.Plus.single₀ _).map (complexScalarSheaf X c))).hom
      ((F.map L.hom).hom ((e.hom.app K) x)) at h_x
  change (F.map L.hom).hom (e.hom.app K (c • x)) =
    (F.map ((CochainComplex.Plus.single₀ _).map (complexScalarSheaf X c))).hom
      ((F.map L.hom).hom (e.hom.app K x))
  rw [he_x, h_x]

set_option maxHeartbeats 2000000 in
/-- Extension of coefficients from `K` to `ℂ` on constant-sheaf cohomology. -/
noncomputable def fieldToComplexCohomologyLinear (n : ℤ) :
    H^n(X; K) →ₗ[K]
      ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) :=
  letI eK := constantModuleCohomologyToAdditiveEquiv K X n
  letI eC := constantComplexModuleCohomologyToAdditiveEquiv X n
  letI F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  letI f := fieldToComplexConstantSheafComplexInt K X
  { toFun := fun x => eC.symm (F.map f (eK x))
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro q x
      apply eC.injective
      rw [AddEquiv.apply_symm_apply]
      change F.map f (eK (q • x)) =
        eC ((algebraMap K ℂ q) • eC.symm (F.map f (eK x)))
      rw [constantModuleCohomologyToAdditiveEquiv_map_smul,
        constantComplexModuleCohomologyToAdditiveEquiv_map_smul,
        AddEquiv.apply_symm_apply]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
        fieldToComplexConstantSheafComplexInt_scalar] }

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ`, the inclusion of locally constant `K`-valued functions as holomorphic zero-forms
induces this `K`-linear map from constant-sheaf cohomology to holomorphic de Rham cohomology. -/
noncomputable def fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; K) →ₗ[K] DeRhamHypercohomology X n :=
  (complexConstantCohomologyDeRhamLinearEquiv X n).toLinearMap.restrictScalars K |>.comp
    (fieldToComplexCohomologyLinear K X n)

set_option maxHeartbeats 2000000 in
/-- Complex conjugation on constant-sheaf hypercohomology. -/
def complexConjugationSemilinear (n : ℤ) :
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X))
      →ₛₗ[starRingEnd ℂ]
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) :=
  letI e := constantComplexModuleCohomologyToAdditiveEquiv X n
  letI F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  letI j : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨conjConstantComplexSheafComplexInt X⟩
  { toFun := fun x => e.symm (F.map j (e x))
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro c x
      let s : constantComplexSheafComplexIntPlus X ⟶
          constantComplexSheafComplexIntPlus X := ⟨complexScalarComplexInt X c⟩
      let s' : constantComplexSheafComplexIntPlus X ⟶
          constantComplexSheafComplexIntPlus X :=
        ⟨complexScalarComplexInt X (starRingEnd ℂ c)⟩
      have h : s ≫ j = j ≫ s' := by
        apply ObjectProperty.hom_ext
        exact complexScalarComplexInt_comp_conj X c
      apply e.injective
      rw [AddEquiv.apply_symm_apply]
      change F.map j (e (c • x)) =
        e ((starRingEnd ℂ) c • e.symm (F.map j (e x)))
      rw [constantComplexModuleCohomologyToAdditiveEquiv_map_smul,
        constantComplexModuleCohomologyToAdditiveEquiv_map_smul,
        AddEquiv.apply_symm_apply]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, h] }


/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. Conjugation
of constant complex coefficients, transported through the equivalence between constant-sheaf
cohomology and de Rham cohomology, gives this conjugate-linear endomorphism of de Rham cohomology.
It sends `c α` to `conj(c) conj(α)`. -/
def deRhamConjSemilinear [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    DeRhamHypercohomology X n →ₛₗ[starRingEnd ℂ] DeRhamHypercohomology X n :=
  letI e := complexConstantCohomologyDeRhamLinearEquiv X n
  letI g := complexConjugationSemilinear X n
  e.toLinearMap.comp (g.comp e.symm.toLinearMap)

/-- Conjugation on de Rham hypercohomology is conjugate-linear. -/
lemma deRhamConj_smul [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : ℂ)
    (α : DeRhamHypercohomology X n) :
    deRhamConjSemilinear X n (c • α) =
      (starRingEnd ℂ) c • deRhamConjSemilinear X n α :=
  by exact (deRhamConjSemilinear X n).map_smulₛₗ c α

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. The
conjugate Hodge filtration in degree `n` consists of classes whose complex conjugates lie in
`F^p H_dR^n(X)`. Here `F^p` is the image of the hypercohomology of holomorphic forms of degree
at least `p`, and conjugation is transported from constant complex coefficients. -/
def conjHodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ (DeRhamHypercohomology X n) :=
  (hodgeFiltration X p n).comap (deRhamConjSemilinear X n)

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. This
complex subspace of `H_dR^n(X)` is `F^p ∩ conjugate(F^q)`, where `F^r` is the image of the
hypercohomology of holomorphic forms in degrees at least `r`. Conjugation comes from constant
complex coefficients. When `X` is projective and `p + q = n`, this is the Hodge component of
type `(p,q)`. -/
def hodgePiece [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    Submodule ℂ (DeRhamHypercohomology X n) :=
  hodgeFiltration X p n ⊓ conjHodgeFiltrationComplexSubmodule X q n

end ComplexConjugation

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `X(ℂ)` its analytic topology. For a field
`K` embedded in `ℂ` and a natural number `p`, these are the classes in `H^{2p}(X(ℂ); K)` whose
de Rham images belong to `F^p ∩ conjugate(F^p)`. The filtration `F^p` is the image of the
hypercohomology of holomorphic forms of degrees at least `p`. Conjugation is induced by
conjugating constant complex coefficients; for projective `X`, the intersection is the Hodge
component of type `(p,p)`. -/
def hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (H^(2 * p)(X; K)) :=
  ((hodgePiece X p p (2 * p)).restrictScalars K).comap
    (fieldToDeRhamCohomology K X (2 * p))

/-- `Hdg^p(f; K)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is
presented by its structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" f "; " K ")" => hodgeClasses K f p

end AlgebraicGeometry.ComplexPoint
