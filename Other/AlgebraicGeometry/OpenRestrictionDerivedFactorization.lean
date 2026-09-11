/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.OpenRestrictionLocalSheaf
public import Other.AlgebraicGeometry.BettiCohomologyWithSupportComparison
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Factoring derived morphisms into a pushed-forward resolution through the restriction morphism

Let `Ω` be an open subset of the analytic space, `j : Ω → X^an` its inclusion, and let `J` be a
bounded-below complex of injective sheaves each of which is a direct image `j_* S`. Such a
complex is K-injective, so a morphism `ℤ_X-free` sheaf-level source into `J` in the derived
category is represented by an actual cocycle; and since each term of `J` is *local on `Ω`*
(`TopCat.Sheaf.IsOpenRestrictionLocal`, proved in
[`OpenRestrictionLocalSheaf.lean`](OpenRestrictionLocalSheaf.lean)), that cocycle is the
composition of the canonical restriction morphism `η : F ⟶ j_*j^*F` with a cocycle on
`j_*j^*F`.

The outcome is `exists_smallShiftedHom_comp_eq`: **any derived morphism from `F` to a K-injective
complex whose terms are local on `Ω` factors through `η`.** Applied to the complex
`derivedPushforwardComplementConstantRationalComplexInt X Z` computing the rational cohomology of
`Ω = Zᶜ`, it is the missing derived-category input for the localisation of the first Chern class
(`ChernClassRestrictionVanishing.lean`).

No short exactness of `j_*` applied to the exponential sequence is used — and indeed none holds;
the point is precisely that the factorisation exists only after passing to the derived
(K-injective) model of `Rj_*ℚ_Ω`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory.Localization.SmallShiftedHom

universe w

variable {C : Type*} [Category* C] {M : Type*} [AddMonoid M] [HasShift C M]
  (W : MorphismProperty C) [W.IsCompatibleWithShift M]

/-- Composition of a degree-zero shifted morphism with a shifted morphism. -/
lemma mk₀_comp_mk {A B D : C} {n : M}
    [HasSmallLocalizedShiftedHom.{w} W M A B] [HasSmallLocalizedShiftedHom.{w} W M B D]
    [HasSmallLocalizedShiftedHom.{w} W M A D] [HasSmallLocalizedShiftedHom.{w} W M D D]
    (φ : A ⟶ B) (g : ShiftedHom B D n) :
    (SmallShiftedHom.mk₀.{w} W 0 rfl φ).comp (SmallShiftedHom.mk.{w} W g) (add_zero n) =
      SmallShiftedHom.mk.{w} W (φ ≫ g) := by
  apply (equiv W W.Q).injective
  rw [equiv_comp, equiv_mk₀, equiv_mk, equiv_mk, ShiftedHom.mk₀_comp]
  dsimp [ShiftedHom.map]
  rw [Functor.map_comp, Category.assoc]

/-- Composition of two degree-zero shifted morphisms. -/
lemma mk₀_comp_mk₀' {A B D : C}
    [HasSmallLocalizedShiftedHom.{w} W M A B] [HasSmallLocalizedShiftedHom.{w} W M B D]
    [HasSmallLocalizedShiftedHom.{w} W M A D] [HasSmallLocalizedShiftedHom.{w} W M D D]
    (f : A ⟶ B) (g : B ⟶ D) :
    (SmallShiftedHom.mk₀.{w} W 0 rfl f).comp (SmallShiftedHom.mk₀.{w} W 0 rfl g)
        (add_zero (0 : M)) = SmallShiftedHom.mk₀.{w} W 0 rfl (f ≫ g) := by
  apply (equiv W W.Q).injective
  rw [equiv_comp, equiv_mk₀, equiv_mk₀, equiv_mk₀, ShiftedHom.mk₀_comp_mk₀, Functor.map_comp]

end CategoryTheory.Localization.SmallShiftedHom

namespace AlgebraicGeometry.ComplexPoint

open CochainComplex.HomComplex

variable (X : Over (Spec ↧ℂ))

local instance openRestrictionFactorizationTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance openRestrictionFactorizationHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Precomposition with a morphism of complexes, read on cohomology classes of the `Hom`
complex. -/
lemma toSmallShiftedHom_mk_precomp
    {K L J : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (φ : K ⟶ L) {n : ℤ}
    (z : Cocycle L J n) :
    CohomologyClass.toSmallShiftedHom.{1} (CohomologyClass.mk (z.precomp φ)) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl φ).comp
        (CohomologyClass.toSmallShiftedHom.{1} (CohomologyClass.mk z)) (add_zero n) := by
  rw [CohomologyClass.toSmallShiftedHom_mk, CohomologyClass.toSmallShiftedHom_mk,
    Cocycle.equivHomShift_symm_precomp, Localization.SmallShiftedHom.mk₀_comp_mk]

/-- **Factorisation of derived morphisms into a K-injective complex.** If precomposition with
`η : A ⟶ B` is bijective on morphisms into every term of a K-injective complex `J`, then every
morphism from `A` to `J` in the derived category factors through `η`. -/
theorem exists_smallShiftedHom_comp_eq
    {A B : AnalyticAdditiveSheaf X} (η : A ⟶ B)
    (J : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [J.IsKInjective] (n : ℤ)
    (hbij : ∀ q : ℤ, Function.Bijective (fun b : B ⟶ J.X q => η ≫ b))
    (ζ' : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A) J n) :
    ∃ ζ : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj B) J n,
      ζ' = (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map η)).comp ζ
          (add_zero n) := by
  obtain ⟨x, rfl⟩ := (CohomologyClass.equivOfIsKInjective.{1}
    (K := (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A)
    (L := J) (n := n)).surjective ζ'
  obtain ⟨z, rfl⟩ := x.mk_surjective
  obtain ⟨a, ha, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  obtain ⟨b, hb⟩ := (hbij n).2 a
  replace hb : η ≫ b = a := hb
  subst hb
  have hb' : b ≫ J.d n (n + 1) = 0 := by
    apply (hbij (n + 1)).1
    show η ≫ b ≫ J.d n (n + 1) = η ≫ 0
    rw [← Category.assoc, ha, comp_zero]
  refine ⟨CohomologyClass.equivOfIsKInjective.{1}
    (K := (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj B) (L := J) (n := n)
    (CohomologyClass.mk (Cocycle.fromSingleMk b (zero_add n) (n + 1) rfl hb')), ?_⟩
  rw [Cocycle.fromSingleMk_precomp]
  exact toSmallShiftedHom_mk_precomp X _ _

section

variable (Ω : Opens (TopCat.of (ComplexPoint X))) (Z : Set (ComplexPoint X))

/-- The complement of `Z` mapped into an open set containing it. -/
def complementToOpen (hZΩ : (Ω : Set (ComplexPoint X)) = Zᶜ) :
    TopCat.of (AnalyticComplement X Z) ⟶ TopCat.of ↥Ω :=
  TopCat.ofHom ⟨fun x => ⟨x.1, hZΩ.ge x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- The inclusion of the complement of `Z` factors through an open set with complement `Z`. -/
lemma analyticComplementInclusion_eq (hZΩ : (Ω : Set (ComplexPoint X)) = Zᶜ) :
    analyticComplementInclusion X Z = complementToOpen X Ω Z hZΩ ≫ Ω.inclusion' := rfl

/-- Every term of the chosen derived-pushforward model from the complement of `Z` is local on an
open set with complement `Z`. -/
lemma isOpenRestrictionLocal_derivedPushforward
    (hZΩ : (Ω : Set (ComplexPoint X)) = Zᶜ) (q : ℤ) :
    TopCat.Sheaf.IsOpenRestrictionLocal (TopCat.of (ComplexPoint X)) Ω
      ((derivedPushforwardComplementConstantRationalComplexInt X Z).X q) := by
  by_cases hq : ∃ m : ℕ, (m : ℤ) = q
  · obtain ⟨m, rfl⟩ := hq
    refine (TopCat.Sheaf.isOpenRestrictionLocal_pushforward (TopCat.of (ComplexPoint X)) Ω
      ((TopCat.Sheaf.pushforward AddCommGrpCat (complementToOpen X Ω Z hZΩ)).obj
        ((complementConstantRationalInjectiveResolution X Z).cocomplex.X m))).of_iso ?_
    exact ((derivedPushforwardComplementConstantRationalComplexNat X Z).extendXIso
      ComplexShape.embeddingUpNat (i := m) rfl).symm
  · exact TopCat.Sheaf.isOpenRestrictionLocal_of_isZero
      ((derivedPushforwardComplementConstantRationalComplexNat X Z).isZero_extend_X
        ComplexShape.embeddingUpNat q (fun i hi ↦ hq ⟨i, hi⟩))

set_option linter.style.haveILetI false in
/-- The chosen derived-pushforward model from an open complement is K-injective: it is a
bounded-below complex of injective sheaves. -/
lemma derivedPushforwardComplementConstantRationalComplexInt_isKInjective
    (hZ : IsClosed Z) :
    (derivedPushforwardComplementConstantRationalComplexInt X Z).IsKInjective := by
  letI : ∀ q : ℤ, Injective ((derivedPushforwardComplementConstantRationalComplexInt X Z).X q) :=
    derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ
  letI : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE 0 := by
    dsimp only [derivedPushforwardComplementConstantRationalComplexInt]
    infer_instance
  exact CochainComplex.isKInjective_of_injective _ 0

set_option linter.style.haveILetI false in
/-- **The factorisation, for the complement of a closed set.** Every derived morphism from a
sheaf `F` to the derived pushforward of the rational constants on `Ω = Zᶜ` factors through the
canonical restriction morphism `F ⟶ j_* j^* F`. -/
theorem exists_comp_restrictionUnit_eq
    (hZ : IsClosed Z) (hZΩ : (Ω : Set (ComplexPoint X)) = Zᶜ)
    (F : AnalyticAdditiveSheaf X) (n : ℤ)
    (ζ' : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F)
      (derivedPushforwardComplementConstantRationalComplexInt X Z) n) :
    ∃ ζ : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          ((openRestrictionFunctor Ω).obj F))
        (derivedPushforwardComplementConstantRationalComplexInt X Z) n,
      ζ' = (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (restrictionUnit Ω F))).comp ζ (add_zero n) := by
  letI := derivedPushforwardComplementConstantRationalComplexInt_isKInjective X Z hZ
  exact exists_smallShiftedHom_comp_eq X (restrictionUnit Ω F) _ n
    (fun q => isOpenRestrictionLocal_derivedPushforward X Ω Z hZΩ q F) ζ'

end

end AlgebraicGeometry.ComplexPoint
