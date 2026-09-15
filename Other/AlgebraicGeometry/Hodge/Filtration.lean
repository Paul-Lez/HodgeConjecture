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
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Other.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import Other.LinearAlgebra.HodgeStructure

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Filtration, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct TopCat.Sheaf
namespace AlgebraicGeometry.ComplexPoint
open Point
variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))
attribute [local instance] analyticHasDerivedCategory
local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

/-- The chosen rational-linear retraction, applied to the complex constant sheaf. -/
def complexToFieldConstantSheaf :
    𝓒(↧(ComplexPoint X); ℂ) ⟶ 𝓒(↧(ComplexPoint X); K) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom)

/-- The chosen retraction from the complex constant sheaf complex to the rational one. -/
def complexToFieldConstantSheafComplexInt :
    constantComplexSheafComplexIntPlus X ⟶ constantFieldSheafComplexIntPlus K X :=
  (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
    (complexToFieldConstantSheaf K X)

/-- The unit in degree-zero field-valued cohomology, via the derived global-sections unit. -/
def fieldCohomologyUnit : H^0(X; K) :=
  let Y := TopCat.of (ComplexPoint X)
  let A := 𝓒(↧(ComplexPoint X); K)
  let s := TopCat.Sheaf.integerConstantHomAddEquivGlobalSections A
    ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
      (AddCommGrpCat.ofHom (zmultiplesAddHom K 1)))
  let t : ↥((CochainComplex.Plus.ι (AnalyticAdditiveSheaf X) ⋙
      (TopCat.Sheaf.globalSectionsFunctor AddCommGrpCat Y).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).obj
        (constantFieldSheafComplexIntPlus K X)) :=
    (TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y A).inv s
  ((TopCat.Sheaf.toHypercohomology AddCommGrpCat (TopCat.of (ComplexPoint X)) 0).app
    (constantFieldSheafComplexIntPlus K X)).hom t

/-- The degree-zero constant class associated to a field element. -/
def fieldCohomologyClass (q : K) : H^0(X; K) :=
  (ℍ[AddCommGrpCat]^0(TopCat.of (ComplexPoint X))).map
    (fieldScalarComplex K X q) (fieldCohomologyUnit K X)

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_zero :
    fieldCohomologyClass K X 0 = 0 := by
  simp [fieldCohomologyClass]

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_add (a b : K) :
    fieldCohomologyClass K X (a + b) =
      fieldCohomologyClass K X a + fieldCohomologyClass K X b := by
  simp [fieldCohomologyClass]

/-- Extension of coefficients from rational to complex constant-sheaf cohomology. -/
def fieldToComplexCohomology (n : ℤ) :
    H^n(X; K) →+ ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X)) :=
  ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (fieldToComplexConstantSheafComplexInt K X)).hom

/-- The cohomological retraction induced by the chosen rational-linear retraction `ℂ → K`. -/
def complexToFieldCohomology (n : ℤ) :
    ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X)) →+ H^n(X; K) :=
  ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (complexToFieldConstantSheafComplexInt K X)).hom

omit [Algebra K ℂ] in
/-- Constant degree-zero cohomology classes respect rational scalar multiplication. -/
lemma fieldCohomologyClass_mul (q r : K) :
    fieldCohomologyClass K X (q * r) =
      q • fieldCohomologyClass K X r := by
  rw [field_smul_eq]
  simp only [fieldCohomologyClass, fieldScalarComplex_mul, Functor.map_comp_apply]

/-- Rational constants map rational-linearly to degree-zero rational cohomology. -/
def fieldCohomologyClassLinear : K →ₗ[K] H^0(X; K) where
  toFun := fieldCohomologyClass K X
  map_add' := fieldCohomologyClass_add K X
  map_smul' q r := fieldCohomologyClass_mul K X q r

end AlgebraicGeometry.ComplexPoint
end

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct TopCat.Sheaf
namespace AlgebraicGeometry.ComplexPoint
open Point
variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))
attribute [local instance] analyticHasDerivedCategory
local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf :
    fieldToComplexConstantSheaf K X ≫
      complexToFieldConstantSheaf K X = 𝟙 _ := by
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  change F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    F.map (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom =
      𝟙 (AddCommGrpCat.of K) := by
    ext q
    exact complexToFieldLinear_algebraMap K q
  rw [h]
  exact F.map_id (AddCommGrpCat.of K)

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexToField :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexToFieldConstantSheafComplexInt K X = 𝟙 _ := by
  rw [fieldToComplexConstantSheafComplexInt, complexToFieldConstantSheafComplexInt,
    ← Functor.map_comp, fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf]
  exact (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map_id _

lemma complexConstantCohomologyDeRhamAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
      (constantComplexSheafComplexIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n α =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
        (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶
            holomorphicDeRhamComplexIntPlus X) α :=
  rfl

/-- The rational-to-complex cohomology map has the displayed cohomological left inverse. -/
lemma complexToFieldCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToFieldCohomology K X n)
      (fieldToComplexCohomology K X n) := by
  intro α
  unfold complexToFieldCohomology fieldToComplexCohomology
  let f : constantFieldSheafComplexIntPlus K X ⟶
      constantComplexSheafComplexIntPlus X :=
    fieldToComplexConstantSheafComplexInt K X
  let g : constantComplexSheafComplexIntPlus X ⟶
      constantFieldSheafComplexIntPlus K X :=
    complexToFieldConstantSheafComplexInt K X
  change (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map g
    ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f α) = α
  rw [← Functor.map_comp_apply]
  have h : f ≫ g = 𝟙 _ := by
    exact fieldToComplexConstantSheafComplexInt_comp_complexToField K X
  rw [h]
  simp

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma fieldToComplexCohomology_injective (n : ℤ) :
    Function.Injective (fieldToComplexCohomology K X n) :=
  (complexToFieldCohomology_leftInverse K X n).injective

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma fieldToDeRhamCohomology_factor
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n α =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
        (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶
            holomorphicDeRhamComplexIntPlus X)
        (fieldToComplexCohomology K X n α) := by
  exact Functor.map_comp_apply (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X)))
    (fieldToComplexConstantSheafComplexInt K X)
    (⟨constantsToHolomorphicDeRhamComplexInt X⟩ :
      constantComplexSheafComplexIntPlus X ⟶ holomorphicDeRhamComplexIntPlus X) α

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit splitting of `K → ℂ` proves that extending
scalars is injective; no finite-dimensionality assumption is needed. -/
lemma fieldToDeRhamCohomology_injective
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) := by
  intro α β hαβ
  apply fieldToComplexCohomology_injective K X n
  apply (complexConstantCohomologyDeRhamAddEquiv X n).injective
  simpa only [complexConstantCohomologyDeRhamAddEquiv_apply,
    fieldToDeRhamCohomology_factor K X n] using hαβ

/-- The part of the holomorphic de Rham complex in form degrees at least `p` is zero when `p`
is above the complex dimension. -/
lemma hodgeFilteredDeRhamComplex_isZero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    IsZero (hodgeFilteredDeRhamComplex X p) := by
  rw [hodgeFilteredDeRhamComplex,
    HomologicalComplex.isZero_stupidTrunc_iff]
  refine ⟨fun n => ?_⟩
  exact (holomorphicDeRhamComplexInt X).isZero_of_isStrictlyLE
    (dim X.left) (p + n) (by lia)

/-- Above the complex dimension the filtered-to-full inclusion has zero source and hence is the
zero morphism. -/
lemma hodgeFilteredDeRhamInclusion_eq_zero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    hodgeFilteredDeRhamInclusion X p = 0 :=
  (hodgeFilteredDeRhamComplex_isZero_of_lt X hp).eq_of_src _ _

/-- The Hodge filtration is zero above the complex dimension. -/
lemma hodgeFiltration_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    hodgeFiltration X p n = ⊥ := by
  change AddMonoidHom.range (((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
    (⟨hodgeFilteredDeRhamInclusion X p⟩ : hodgeFilteredDeRhamComplexPlus X p ⟶
      holomorphicDeRhamComplexIntPlus X)).hom) = ⊥
  have h : (⟨hodgeFilteredDeRhamInclusion X p⟩ :
      hodgeFilteredDeRhamComplexPlus X p ⟶ holomorphicDeRhamComplexIntPlus X) =
        (0 : hodgeFilteredDeRhamComplexPlus X p ⟶ holomorphicDeRhamComplexIntPlus X) := by
    apply ObjectProperty.hom_ext
    exact hodgeFilteredDeRhamInclusion_eq_zero_of_lt X hp
  rw [h, Functor.map_zero]
  simp

/-- Conjugation on de Rham hypercohomology is an involution. -/
lemma deRhamConj_involutive [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Involutive (deRhamConj X n) := by
  intro α
  rw [deRhamConj_apply, deRhamConj_apply, AddEquiv.symm_apply_apply]
  let F := ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))
  let f : constantComplexSheafComplexIntPlus X ⟶
      constantComplexSheafComplexIntPlus X := ⟨conjConstantComplexSheafComplexInt X⟩
  let β := (complexConstantCohomologyDeRhamAddEquiv X n).symm α
  have h : f ≫ f = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact conjConstantComplexSheafComplexInt_comp_self X
  change (complexConstantCohomologyDeRhamAddEquiv X n) (F.map f (F.map f β)) = α
  calc
    _ = (complexConstantCohomologyDeRhamAddEquiv X n) (F.map (f ≫ f) β) :=
      congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
        (Functor.map_comp_apply F f f β).symm
    _ = (complexConstantCohomologyDeRhamAddEquiv X n) (F.map (𝟙 _) β) :=
      congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
        (congrArg (fun g ↦ F.map g β) h)
    _ = α := by simp [β]

/-- If conjugation fixes the image of `K` in `ℂ`, it fixes the constant `K`-sheaf sitting inside
the constant `ℂ`-sheaf. -/
lemma fieldToComplexConstantSheaf_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheaf K X ≫ conjConstantComplexSheaf X =
      fieldToComplexConstantSheaf K X := by
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  change F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    F.map (AddCommGrpCat.ofHom (starRingEnd ℂ).toAddMonoidHom) =
    F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)
  rw [← Functor.map_comp]
  congr 1
  ext q
  exact hK q

/-- The same statement for the integer-indexed constant complexes. -/
lemma fieldToComplexConstantSheafComplexInt_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheafComplexInt K X ≫
        (⟨conjConstantComplexSheafComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) =
      fieldToComplexConstantSheafComplexInt K X := by
  change (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldToComplexConstantSheaf K X) ≫
      (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
        (conjConstantComplexSheaf X) =
    (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldToComplexConstantSheaf K X)
  rw [← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_conj K X hK]

/-- Such classes are their own conjugates in complex constant-sheaf cohomology. -/
lemma conj_fieldToComplexCohomology
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
      (⟨conjConstantComplexSheafComplexInt X⟩ :
        constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X)
        (fieldToComplexCohomology K X n α) =
      fieldToComplexCohomology K X n α := by
  unfold fieldToComplexCohomology
  let f : constantFieldSheafComplexIntPlus K X ⟶
      constantComplexSheafComplexIntPlus X :=
    fieldToComplexConstantSheafComplexInt K X
  let g : constantComplexSheafComplexIntPlus X ⟶
      constantComplexSheafComplexIntPlus X :=
    ⟨conjConstantComplexSheafComplexInt X⟩
  change (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map g
      ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f α) =
    (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f α
  rw [← Functor.map_comp_apply]
  have h : f ≫ g = f := by
    exact fieldToComplexConstantSheafComplexInt_comp_conj K X hK
  rw [h]

/-- Such classes are their own conjugates in de Rham hypercohomology. This is the step that
makes `F^p` alone the right condition over `ℚ`. -/
lemma deRhamConj_fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    deRhamConj X n (fieldToDeRhamCohomology K X n α) =
      fieldToDeRhamCohomology K X n α := by
  have he : fieldToDeRhamCohomology K X n α =
      complexConstantCohomologyDeRhamAddEquiv X n
        (fieldToComplexCohomology K X n α) :=
    fieldToDeRhamCohomology_factor K X n α
  rw [he, deRhamConj_apply, AddEquiv.symm_apply_apply]
  exact congrArg (complexConstantCohomologyDeRhamAddEquiv X n)
    (conj_fieldToComplexCohomology K X hK n α)

lemma mem_hodgePiece_iff [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ)
    (α : DeRhamHypercohomology X n) :
    α ∈ hodgePiece X p q n ↔
      α ∈ hodgeFiltration X p n ∧ deRhamConj X n α ∈ hodgeFiltration X q n :=
  Iff.rfl

/-- Above the complex dimension the Hodge pieces vanish, because `F^p` already does. -/
lemma hodgePiece_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (q n : ℤ) :
    hodgePiece X p q n = ⊥ := by
  refine le_antisymm (fun α hα ↦ ?_) bot_le
  have h : α ∈ hodgeFiltration X p n := hα.1
  rw [hodgeFiltration_eq_bot_of_lt X hp n, AddSubgroup.mem_bot] at h
  exact h

/-- When conjugation fixes `K`, a `K`-class is its own conjugate, so `F^p` already implies
`(p,p)` and the Hodge filtration alone cuts out the Hodge classes. -/
lemma hodgeClasses_eq_comap_hodgeFiltrationComplexSubmodule [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) (p : ℕ) :
    Hdg^p(K; X) =
      ((hodgeFiltrationComplexSubmodule X p (2 * p)).restrictScalars K).comap
        (fieldToDeRhamCohomologyLinear K X (2 * p)) := by
  refine SetLike.ext fun α ↦ ?_
  show fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgePiece X (p : ℤ) (p : ℤ) (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgeFiltration X (p : ℤ) (2 * (p : ℤ))
  rw [mem_hodgePiece_iff, deRhamConj_fieldToDeRhamCohomology K X hK]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h⟩⟩

/-- Over `ℚ`, the coefficient field the Hodge conjecture is stated for, the `(p,p)` and `F^p`
definitions agree. -/
lemma hodgeClasses_rat_eq_comap_hodgeFiltrationComplexSubmodule [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) :
    Hdg^p(ℚ; X) =
      ((hodgeFiltrationComplexSubmodule X p (2 * p)).restrictScalars ℚ).comap
        (fieldToDeRhamCohomologyLinear ℚ X (2 * p)) :=
  hodgeClasses_eq_comap_hodgeFiltrationComplexSubmodule ℚ X (fun q ↦ by simp) p

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma hodgeClasses_eq_ker_of_lt [IsIntegral X.left] [Smooth X.hom] {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) =
      LinearMap.ker (fieldToDeRhamCohomologyLinear K X (2 * p)) := by
  rw [hodgeClasses,
    hodgePiece_eq_bot_of_lt X (by exact_mod_cast hp : (dim X.left : ℤ) < (p : ℤ)),
    Submodule.restrictScalars_bot, Submodule.comap_bot]

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt
    [IsIntegral X.left] [Smooth X.hom]
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) = ⊥ := by
  rw [hodgeClasses_eq_ker_of_lt K X hp]
  exact LinearMap.ker_eq_bot.mpr (fieldToDeRhamCohomology_injective K X (2 * p))

end AlgebraicGeometry.ComplexPoint
end
