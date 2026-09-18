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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.Algebra.FieldToComplex
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import HodgeConjecture.Lemmas.LinearAlgebra.HodgeStructure
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import HodgeConjecture.Mathlib.Algebra.Homology.StupidTruncation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Int.Cast.Lemmas

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The Hodge filtration

This file defines constant-sheaf cohomology and holomorphic de Rham hypercohomology on the
analytic complex-point space of a smooth complex scheme. Constant-sheaf cohomology is Mathlib's
sheaf cohomology. Hypercohomology is expressed with Mathlib's small shifted morphisms in the
localization at quasi-isomorphisms; for the constant sheaf complex it agrees with sheaf
cohomology. This avoids exposing a noncanonical choice of derived category in the public types.

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

set_option linter.auxLemma false
/- Sheaves on a space are sheaves on its site of opens; the category instance is looked up under
that spelling by Mathlib's sheaf cohomology. -/
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- Sheaves of additive groups on the analytic complex-point space. -/
abbrev AnalyticAdditiveSheaf :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))

local instance analyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

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

/-- Extension of rational constants to complex constants as a map of integer complexes. -/
def fieldToComplexConstantSheafComplexInt :
    constantFieldSheafComplexInt K X ⟶
      constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldToComplexConstantSheaf K X)) ComplexShape.embeddingUpNat

/-- Rational constants mapped canonically into the holomorphic de Rham complex. -/
def fieldToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    constantFieldSheafComplexInt K X ⟶ Ω•(X) :=
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

/-- Scalar multiplication on the rational constant sheaf complex. -/
def fieldScalarComplex (q : K) :
    constantFieldSheafComplexInt K X ⟶
      constantFieldSheafComplexInt K X :=
  HomologicalComplex.extendMap
    ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldScalarSheaf K X q)) ComplexShape.embeddingUpNat

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

/-- Quasi-isomorphisms of analytic sheaf complexes. -/
abbrev analyticQuasiIsomorphisms :=
  HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ

noncomputable instance analyticHasSmallLocalizedShiftedHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (analyticQuasiIsomorphisms X) ℤ K L := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization
    (analyticQuasiIsomorphisms X) DerivedCategory.Q

/-- Hypercohomology of an analytic sheaf complex in integer degree `n`. -/
@[implicit_reducible]
def Hypercohomology
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) : Type 1 :=
  Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
    (constantIntegerSheafComplexInt X) K n

/-- `ℍ^n(X; 𝒦)` is the hypercohomology in integer degree `n` of a complex `𝒦` of sheaves on the
analytic space `X(ℂ)`. The symbol `ℍ` follows page 51 of
[P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf). -/
scoped notation:max "ℍ^" n:max "(" X "; " 𝒦 ")" => Hypercohomology X 𝒦 n

/-- `Ext`-groups of analytic sheaves are computed in `Type 1`. The instance is stated on the site
category, which is how Mathlib's sheaf cohomology looks it up. -/
instance analyticHasExt :
    HasExt.{1} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  fun _ _ _ _ ↦ Localization.hasSmallLocalizedHom_of_isLocalization
    (analyticQuasiIsomorphisms X) DerivedCategory.Q

/-- `H^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with coefficients in the
constant sheaf `K`, in degree `n`, as defined in Mathlib.

The literature writes `H^n(X; K)` for the variety `X.left` alone; here the variety is presented by
its structure morphism `X`. -/
scoped notation3:max "H^" n:max "(" X "; " K ")" =>
  Sheaf.H ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).obj (AddCommGrpCat.of K)) n

/-- Complex constant-sheaf cohomology in integer degree `n`. -/
abbrev ComplexConstantCohomology (n : ℤ) : Type 1 :=
  ℍ^n(X; constantComplexSheafComplexInt X)

noncomputable instance hypercohomologyAddCommGroup
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    AddCommGroup ℍ^n(X; K) :=
  fast_instance% (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).addCommGroup

lemma hypercohomologyEquiv_zero
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (0 : ℍ^n(X; K)) = 0 := by
  rw [Equiv.zero_def, Equiv.apply_symm_apply]

lemma hypercohomologyEquiv_add
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (α β : ℍ^n(X; K)) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) (α + β) =
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) α +
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) β := by
  simp [Equiv.add_def]

/-- Hypercohomology of the holomorphic de Rham complex in integer degree `n`, that is
`ℍ^n(X; Ω•(X))`. -/
abbrev DeRhamHypercohomology [IsIntegral X.left] [Smooth X.hom] (n : ℤ) : Type 1 :=
  ℍ^n(X; Ω•(X))

@[inherit_doc DeRhamHypercohomology]
scoped notation:max "H_dR^" n:max "(" X ")" => DeRhamHypercohomology X n

/-- The constant-to-holomorphic-de Rham quasi-isomorphism induces the corresponding
equivalence on hypercohomology. -/
def complexConstantCohomologyDeRhamEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ComplexConstantCohomology X n ≃ H_dR^n(X) :=
  Localization.SmallShiftedHom.postcompEquiv
    (constantsToHolomorphicDeRhamComplexInt X)
    (by
      change QuasiIso (constantsToHolomorphicDeRhamComplexInt X)
      infer_instance)
/-- Postcomposition on hypercohomology by a map of complexes. -/
def hypercohomologyMap
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ) :
    ℍ^n(X; K) →+ ℍ^n(X; L) where
  toFun α := α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]

  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

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
    (α : ℍ^n(X; K)) :
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
  simpa only using
    (Localization.SmallShiftedHom.comp_assoc
      (analyticQuasiIsomorphisms X) α β γ
      (zero_add n) (zero_add (0 : ℤ)) (zero_add n)).symm

/-- Postcomposition on hypercohomology is additive in the map of complexes. -/
lemma hypercohomologyMap_add_apply
    {C D : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f g : C ⟶ D) (n : ℤ)
    (α : ℍ^n(X; C)) :
    hypercohomologyMap X (f + g) n α =
      hypercohomologyMap X f n α + hypercohomologyMap X g n α := by
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [hypercohomologyEquiv_add]
  simp [hypercohomologyMap, Localization.SmallShiftedHom.equiv_comp,
    Functor.map_add]

/-- The constant sheaf complex is the constant sheaf placed in degree zero. -/
def constantFieldSheafComplexIntIsoSingle :
    constantFieldSheafComplexInt K X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint X); K) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat 𝓒(↧(ComplexPoint X); K) 0 0 rfl

/-- The integer constant sheaf complex is the source object of Mathlib's sheaf cohomology placed
in degree zero. -/
def constantIntegerSheafComplexIntIsoSingleULift :
    constantIntegerSheafComplexInt X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      𝓒(↧(ComplexPoint X); ℤ) 0 0 rfl ≪≫
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).mapIso
      ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).mapIso
        (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso).symm

local instance analyticSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) :=
  analyticHasDerivedCategory X

/-- The source comparison, as a small shifted morphism from the source object of Mathlib's sheaf
cohomology to the integer constant sheaf complex. -/
private def constantIntegerComparison :=
  Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

/-- The target comparison, as a small shifted morphism from the constant sheaf complex to the
constant sheaf in degree zero. -/
private def constantFieldComparison :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantFieldSheafComplexIntIsoSingle K X).hom

/-- Precomposition with the source comparison commutes with postcomposition by a map of
complexes. -/
private lemma constantIntegerComparison_comp_comp_mk₀
    {L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ)
    (β : Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexInt X) L n) (h : L ⟶ M) :
    ((constantIntegerComparison X).comp β (add_zero n)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl h) (zero_add n) =
    (constantIntegerComparison X).comp
      (β.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl h)
        (zero_add n)) (add_zero n) :=
  Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) _ β _
    (add_zero n) (zero_add n) (by simp)

/-- Hypercohomology of the constant sheaf complex is Mathlib's sheaf cohomology of the constant
sheaf. -/
def hypercohomologyAddEquivConstantCohomology (n : ℕ) :
    Hypercohomology X (constantFieldSheafComplexInt K X) n ≃+ H^n(X; K) where
  toEquiv :=
    (Localization.SmallShiftedHom.precompEquiv.{1} (W := analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ))).symm.trans
    (Localization.SmallShiftedHom.postcompEquiv.{1} (W := analyticQuasiIsomorphisms X)
      (constantFieldSheafComplexIntIsoSingle K X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ)))
  map_add' α β := by
    apply Abelian.Ext.ext
    rw [Abelian.Ext.add_hom]
    show Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp (α + β) _).comp (constantFieldComparison K X) _) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp α _).comp (constantFieldComparison K X) _) +
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (((constantIntegerComparison X).comp β _).comp (constantFieldComparison K X) _)
    simp only [Localization.SmallShiftedHom.equiv_comp, hypercohomologyEquiv_add,
      ShiftedHom.add_comp, ShiftedHom.comp_add]
    rfl

omit [Algebra K ℂ] in
/-- The comparison with Mathlib's sheaf cohomology is natural in maps of constant sheaves. -/
lemma hypercohomologyAddEquivConstantCohomology_map {L : Type} [Field L]
    (f : 𝓒(↧(ComplexPoint X); K) ⟶ 𝓒(↧(ComplexPoint X); L)) (n : ℕ)
    (α : Hypercohomology X (constantFieldSheafComplexInt K X) n) :
    hypercohomologyAddEquivConstantCohomology L X n
      (hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n α) =
    Sheaf.H.map f n (hypercohomologyAddEquivConstantCohomology K X n α) := by
  show ((constantIntegerComparison X).comp (hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n α) (add_zero _)).comp
      (constantFieldComparison L X) (zero_add _) =
    (((constantIntegerComparison X).comp α (add_zero _)).comp (constantFieldComparison K X)
      (zero_add _)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f)) (zero_add _)
  refine (constantIntegerComparison_comp_comp_mk₀ X _ _ _).trans (Eq.trans ?_
    ((congrArg (fun γ => γ.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X)
      (0 : ℤ) rfl ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f))
      (zero_add _)) (constantIntegerComparison_comp_comp_mk₀ X _ α _)).trans
        (constantIntegerComparison_comp_comp_mk₀ X _ _ _)).symm)
  congr 1
  change hypercohomologyMap X _ n (hypercohomologyMap X _ n α) =
    hypercohomologyMap X _ n (hypercohomologyMap X _ n α)
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  exact congrArg (fun g => hypercohomologyMap X g n α)
    (HomologicalComplex.extendSingleIso_hom_naturality ComplexShape.embeddingUpNat f 0 0 rfl)

omit [Algebra K ℂ] in
/-- The inverse comparison is natural in maps of constant sheaves. -/
lemma hypercohomologyAddEquivConstantCohomology_symm_map {L : Type} [Field L]
    (f : 𝓒(↧(ComplexPoint X); K) ⟶ 𝓒(↧(ComplexPoint X); L)) (n : ℕ) (β : H^n(X; K)) :
    (hypercohomologyAddEquivConstantCohomology L X n).symm (Sheaf.H.map f n β) =
      hypercohomologyMap X (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map f)
          ComplexShape.embeddingUpNat) n
        ((hypercohomologyAddEquivConstantCohomology K X n).symm β) := by
  apply (hypercohomologyAddEquivConstantCohomology L X n).injective
  rw [AddEquiv.apply_symm_apply, hypercohomologyAddEquivConstantCohomology_map,
    AddEquiv.apply_symm_apply]

/-- Scalars acting on a coefficient complex by an additive, unital and antimultiplicative family
of endomorphisms act on its hypercohomology. -/
noncomputable abbrev hypercohomologyModule {R : Type*} [Semiring R]
    {C : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (s : R → (C ⟶ C)) (n : ℤ)
    [SMul R ℍ^n(X; C)]
    (smul_eq : ∀ (r : R) (α : ℍ^n(X; C)),
      r • α = hypercohomologyMap X (s r) n α)
    (s_add : ∀ a b : R, s (a + b) = s a + s b)
    (s_one : s 1 = 𝟙 C)
    (s_mul : ∀ a b : R, s (a * b) = s b ≫ s a) :
    Module R ℍ^n(X; C) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [smul_eq, smul_eq, smul_eq]
      exact (hypercohomologyMap X (s r) n).map_add α β)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_add]
      exact hypercohomologyMap_add_apply X (s a) (s b) n α)
    (fun a b α => by
      rw [smul_eq, smul_eq, smul_eq, s_mul]
      exact hypercohomologyMap_comp_apply X (s b) (s a) n α)
    (fun α => by
      rw [smul_eq, s_one]
      let e : ℍ^n(X; C) ≃
          ShiftedHom
            (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
            (DerivedCategory.Q.obj C) n :=
        Localization.SmallShiftedHom.equiv
          (analyticQuasiIsomorphisms X) DerivedCategory.Q
      apply e.injective
      simp [e, hypercohomologyMap])

/-- The rational action on constant-sheaf cohomology, induced by scalar multiplication on the
coefficient sheaf. -/
noncomputable instance (n : ℕ) :
    SMul K (H^n(X; K)) :=
  ⟨fun q α ↦ Sheaf.H.map (fieldScalarSheaf K X q) n α⟩

omit [Algebra K ℂ] in
lemma field_smul_eq (n : ℕ) (q : K) (α : H^n(X; K)) :
    q • α = Sheaf.H.map (fieldScalarSheaf K X q) n α := rfl

/-- Rational constant-sheaf cohomology is canonically a rational vector space. -/
noncomputable instance fieldCohomologyModule (n : ℕ) :
    Module K (H^n(X; K)) :=
  Module.ofMinimalAxioms
    (fun r α β => by
      rw [field_smul_eq, field_smul_eq, field_smul_eq]
      exact map_add _ α β)
    (fun a b α => by
      rw [field_smul_eq, field_smul_eq, field_smul_eq, fieldScalarSheaf_add]
      exact Sheaf.H.map_add_apply _ _ α)
    (fun a b α => by
      rw [field_smul_eq, field_smul_eq, field_smul_eq, fieldScalarSheaf_mul,
        Sheaf.H.map_comp_apply])
    (fun α => by
      rw [field_smul_eq, fieldScalarSheaf_one, Sheaf.H.map_id_apply])

omit [Algebra K ℂ] in
/-- The comparison with hypercohomology carries scalar multiplication to the action of the
scalar complex. -/
lemma hypercohomologyAddEquivConstantCohomology_symm_smul (n : ℕ) (q : K) (α : H^n(X; K)) :
    (hypercohomologyAddEquivConstantCohomology K X n).symm (q • α) =
      hypercohomologyMap X (fieldScalarComplex K X q) n
        ((hypercohomologyAddEquivConstantCohomology K X n).symm α) := by
  rw [field_smul_eq, hypercohomologyAddEquivConstantCohomology_symm_map]
  rfl

/-- The complex action on holomorphic de Rham hypercohomology, induced by scalar multiplication
on the holomorphic de Rham complex. -/
noncomputable instance
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    SMul ℂ H_dR^n(X) :=
  ⟨fun c α ↦ hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X c) n α⟩

lemma deRham_complex_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    c • α = hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X c) n α :=
  rfl

/-- Holomorphic de Rham hypercohomology is canonically a complex vector space. -/
noncomputable instance deRhamHypercohomologyComplexModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module ℂ H_dR^n(X) :=
  hypercohomologyModule X (scalarHolomorphicDeRhamComplexInt X) n
    (deRham_complex_smul_eq X n) (scalarHolomorphicDeRhamComplexInt_add X)
    (scalarHolomorphicDeRhamComplexInt_one X)
    (scalarHolomorphicDeRhamComplexInt_mul X)

/-- De Rham hypercohomology as a vector space over `K`, by restriction of complex scalars. -/
noncomputable instance deRhamHypercohomologyModule
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Module K H_dR^n(X) :=
  Module.restrictScalars K ℂ H_dR^n(X)

lemma deRham_field_smul_eq [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (q : K) (α : H_dR^n(X)) :
    q • α = hypercohomologyMap X
      (scalarHolomorphicDeRhamComplexInt X (algebraMap K ℂ q)) n α :=
  rfl

/-- Restriction of complex scalars gives the scalar tower on de Rham hypercohomology. -/
noncomputable instance deRhamHypercohomologyIsScalarTower
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    IsScalarTower K ℂ H_dR^n(X) :=
  IsScalarTower.restrictScalars K ℂ H_dR^n(X)

/-- The derived comparison from rational cohomology to holomorphic de Rham hypercohomology. -/
def fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; K) →+ H_dR^n(X) :=
  (hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt K X) n).comp
    (hypercohomologyAddEquivConstantCohomology K X n).symm.toAddMonoidHom

/-- The rational-to-de Rham comparison is compatible with rational scalar multiplication. -/
lemma fieldToDeRhamCohomology_smul
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (q : K) (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n (q • α) =
      q • fieldToDeRhamCohomology K X n α := by
  rw [deRham_field_smul_eq]
  unfold fieldToDeRhamCohomology
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rw [hypercohomologyAddEquivConstantCohomology_symm_smul, ← hypercohomologyMap_comp_apply,
    ← hypercohomologyMap_comp_apply, fieldToHolomorphicDeRhamComplexInt_scalar]

/-- The rational-to-de Rham comparison as a rational-linear map. -/
def fieldToDeRhamCohomologyLinear
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; K) →ₗ[K] H_dR^n(X) where
  toFun := fieldToDeRhamCohomology K X n
  map_add' := (fieldToDeRhamCohomology K X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul K X n

/-- `F^p Ω•(X)` is the holomorphic de Rham complex `Ω•(X)` with only the form degrees at least
`p` retained. -/
def hodgeFilteredDeRhamComplex [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  Ω•(X).stupidTrunc (ComplexShape.embeddingUpIntGE p)

@[inherit_doc hodgeFilteredDeRhamComplex]
scoped notation:max "F^" p:max " Ω•" "(" X ")" => hodgeFilteredDeRhamComplex X p

/-- Inclusion of the degree-at-least-`p` de Rham complex into the full complex. -/
def hodgeFilteredDeRhamInclusion [IsIntegral X.left] [Smooth X.hom] (p : ℤ) :
    F^p Ω•(X) ⟶ Ω•(X) :=
  HomologicalComplex.stupidTruncInclusion Ω•(X) (ComplexShape.embeddingUpIntGE p)

/-- Complex scalar multiplication on the filtered de Rham complex. -/
def hodgeFilteredDeRhamComplexScalar [IsIntegral X.left] [Smooth X.hom]
    (p : ℤ) (c : ℂ) :
    F^p Ω•(X) ⟶ F^p Ω•(X) :=
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
    (p n : ℤ) : Type 1 :=
  ℍ^n(X; F^p Ω•(X))

/-- The map from filtered to full de Rham hypercohomology. -/
def filteredToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    FilteredDeRhamHypercohomology X p n →+ H_dR^n(X) :=
  hypercohomologyMap X (hodgeFilteredDeRhamInclusion X p) n

/-- The Hodge filtration `F^p` on de Rham hypercohomology. -/
def hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p n : ℤ) :
    AddSubgroup H_dR^n(X) :=
  (filteredToDeRhamCohomology X p n).range

/-- The Hodge filtration is stable under arbitrary complex scalar multiplication. -/
lemma hodgeFiltration_complex_smul_mem [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (c : ℂ) {α : H_dR^n(X)}
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
    (p n : ℤ) : Submodule ℂ H_dR^n(X) where
  carrier := hodgeFiltration X p n
  zero_mem' := (hodgeFiltration X p n).zero_mem
  add_mem' := (hodgeFiltration X p n).add_mem
  smul_mem' := fun c _ h => hodgeFiltration_complex_smul_mem X p n c h

@[inherit_doc hodgeFiltrationComplexSubmodule]
scoped notation:max "F^" p:max " H_dR^" n:max "(" X ")" =>
  hodgeFiltrationComplexSubmodule X p n

/-! ### Complex conjugation and the `(p,p)` part

Conjugation is not `ℂ`-linear, so it acts on the constant sheaf `ℂ` rather than on the holomorphic
de Rham complex, and is transported across the constant-to-de Rham comparison. The `(p,q)` piece
is then *defined* as `F^p ⊓ conj F^q`, which needs no Hodge decomposition theorem. -/

/-- The constant-to-de Rham comparison equivalence, upgraded to an additive equivalence. -/
def complexConstantCohomologyDeRhamAddEquiv [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ComplexConstantCohomology X n ≃+ H_dR^n(X) :=
  { complexConstantCohomologyDeRhamEquiv X n with
    map_add' := fun α β ↦ by
      change hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n (α + β) =
        hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n α +
          hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n β
      exact map_add _ α β }

private lemma complexConstantCohomologyDeRhamAddEquiv_apply [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (α : ComplexConstantCohomology X n) :
    complexConstantCohomologyDeRhamAddEquiv X n α =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n α :=
  rfl

/-- The comparison equivalence carries the constant-sheaf scalar action to the de Rham one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (β : ComplexConstantCohomology X n) :
    complexConstantCohomologyDeRhamAddEquiv X n
        (hypercohomologyMap X (complexScalarComplexInt X c) n β) =
      c • complexConstantCohomologyDeRhamAddEquiv X n β := by
  rw [complexConstantCohomologyDeRhamAddEquiv_apply,
    complexConstantCohomologyDeRhamAddEquiv_apply,
    ← hypercohomologyMap_comp_apply, ← constantsToHolomorphicDeRhamComplexInt_scalar,
    hypercohomologyMap_comp_apply, deRham_complex_smul_eq]

/-- The inverse comparison carries the de Rham scalar action back to the constant-sheaf one. -/
private lemma complexConstantCohomologyDeRhamAddEquiv_symm_scalar [IsIntegral X.left] [Smooth X.hom]
    (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    (complexConstantCohomologyDeRhamAddEquiv X n).symm (c • α) =
      hypercohomologyMap X (complexScalarComplexInt X c) n
        ((complexConstantCohomologyDeRhamAddEquiv X n).symm α) := by
  apply (complexConstantCohomologyDeRhamAddEquiv X n).injective
  rw [AddEquiv.apply_symm_apply, complexConstantCohomologyDeRhamAddEquiv_scalar,
    AddEquiv.apply_symm_apply]

/-- Complex conjugation on de Rham hypercohomology, transported from the constant sheaf `ℂ`. -/
def deRhamConj [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H_dR^n(X) →+ H_dR^n(X) :=
  ((complexConstantCohomologyDeRhamAddEquiv X n).toAddMonoidHom).comp
    ((hypercohomologyMap X (conjConstantComplexSheafComplexInt X) n).comp
      (complexConstantCohomologyDeRhamAddEquiv X n).symm.toAddMonoidHom)

lemma deRhamConj_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (α : H_dR^n(X)) :
    deRhamConj X n α =
      complexConstantCohomologyDeRhamAddEquiv X n
        (hypercohomologyMap X (conjConstantComplexSheafComplexInt X) n
          ((complexConstantCohomologyDeRhamAddEquiv X n).symm α)) :=
  rfl

/-- Conjugation on de Rham hypercohomology is conjugate-linear. -/
lemma deRhamConj_smul [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : ℂ) (α : H_dR^n(X)) :
    deRhamConj X n (c • α) = (starRingEnd ℂ) c • deRhamConj X n α := by
  rw [deRhamConj_apply, deRhamConj_apply,
    complexConstantCohomologyDeRhamAddEquiv_symm_scalar,
    ← hypercohomologyMap_comp_apply, complexScalarComplexInt_comp_conj,
    hypercohomologyMap_comp_apply, complexConstantCohomologyDeRhamAddEquiv_scalar]

/-- Conjugation on de Rham hypercohomology, bundled as a conjugate-linear map. -/
def deRhamConjSemilinear [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H_dR^n(X) →ₛₗ[starRingEnd ℂ] H_dR^n(X) where
  toFun := deRhamConj X n
  map_add' := (deRhamConj X n).map_add
  map_smul' := deRhamConj_smul X n

/-- The conjugate Hodge filtration `conj F^p`. Conjugation is an involution, so the preimage of
`F^p` is also its image. -/
def conjHodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) : Submodule ℂ H_dR^n(X) :=
  (F^p H_dR^n(X)).comap (deRhamConjSemilinear X n)

/-- The intersection `F^p ⊓ conj F^q` in degree `n`. For smooth projective varieties and
`p + q = n`, this is the usual `(p,q)` Hodge piece. -/
def hodgePiece [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    Submodule ℂ H_dR^n(X) :=
  F^p H_dR^n(X) ⊓ conjHodgeFiltrationComplexSubmodule X q n

/-- Cohomology classes with coefficients in `K` whose de Rham images lie in `F^p ⊓ conj F^p`
in degree `2p`. When conjugation fixes the image of `K` in `ℂ`, see
`hodgeClasses_eq_comap_hodgeFiltrationComplexSubmodule` for the equivalent `F^p` condition. -/
def hodgeClasses [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Submodule K (H^(2 * p)(X; K)) :=
  ((hodgePiece X p p (2 * p : ℕ)).restrictScalars K).comap
    (fieldToDeRhamCohomologyLinear K X (2 * p))

/-- `Hdg^p(f; K)` is the space of Hodge classes of codimension `p` with coefficients in `K`.

The literature writes `Hdg^p(X.left)` for the variety `X.left` alone; here the variety is
presented by its structure morphism `f`, and the coefficient field is named. -/
scoped notation:max "Hdg^" p:max "(" f "; " K ")" => hodgeClasses K f p

end AlgebraicGeometry.ComplexPoint
