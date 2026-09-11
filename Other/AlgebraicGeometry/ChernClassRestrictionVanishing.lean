/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionOpenRestriction
public import Other.AlgebraicGeometry.CohomologyWithSupportExact
public import Other.AlgebraicGeometry.OpenRestrictionDerivedFactorization

/-!
# Localising the first Chern class on the complement of an open set

This file carries out step 3 of §4.3 of `docs/DIVISOR_HANDOFF.md`. Let `E` be an extension
`0 → 𝒪ˣ → E.middle → ℤ → 0` of analytic sheaves which *splits over an open set `Ω`*, in the sense
that there is a section `ℓ` of `E.middle` over `Ω` whose image under the projection is the
restriction of the constant integer section `1`. In the application `Ω` is the complement of the
support of the divisor, on which the rational section frames the line bundle.

The goal is that the rational first Chern class of `E` restricts to zero on `Ω`, hence lifts to
rational cohomology with support in `Z = Ωᶜ` through `forgetSupport`, by the exactness proved in
`Other/AlgebraicGeometry/CohomologyWithSupportExact.lean`.

What is **proved** unconditionally, in
[`UnitExtensionOpenRestriction.lean`](UnitExtensionOpenRestriction.lean), is the vanishing of the
*extension class* after restriction to `Ω`:

`E.cohomologyClass.comp (Ext.mk₀ (restrictionUnit Ω 𝒪ˣ)) = 0` in `Ext¹(ℤ, j_*(𝒪ˣ|_Ω))`.

The compatibility of the exponential connecting map with that restriction — that the restricted
rational Chern class depends only on the restricted extension class — is stated here as the two
propositions

* `HasRestrictedChernFactorization X d Ω` — the restricted rational Chern class factors through
  `Ext¹(ℤ, j_*(𝒪ˣ|_Ω))`;
* `RestrictedChernClassVanishes X d Ω` — the weaker form actually used: a class killed by the
  restriction of units has vanishing restricted rational Chern class.

The first implies the second (`restrictedChernClassVanishes_of_factorization`), and the second
gives the two theorems of step 3
(`restrictToComplement_integralToRational_firstChernClass_eq_zero` and
`exists_forgetSupport_eq_integralToRational_firstChernClass`).

**Both are now proved**, as `hasRestrictedChernFactorization` and
`restrictedChernClassVanishes`, so the hypothesis `hvan` of those two theorems is dischargeable.
The proof does *not* restrict the exponential sequence to `Ω`. Instead it observes that the whole
composite defining `restrictedRationalChernClass` is, after the identification of the source
complex, postcomposition of the extension class `e` with the single class

`ζ' := ε ∘ (ℤ → ℚ → j_* I^•) ∈ Hom_{D(X)}(𝒪ˣ, (j_* I^•)[1])`,

where `ε` is the exponential extension class, and that `ζ'` factors through
`η : 𝒪ˣ → j_*(𝒪ˣ|_Ω)`. That factorisation is
`AlgebraicGeometry.ComplexPoint.exists_comp_restrictionUnit_eq`
([`OpenRestrictionDerivedFactorization.lean`](OpenRestrictionDerivedFactorization.lean)): the
complex `j_* I^•` is a bounded-below complex of injectives, hence K-injective, so a derived
morphism into it is an honest cocycle; and each of its terms `j_* I^n` is *local on `Ω`*
(`TopCat.Sheaf.IsOpenRestrictionLocal`, from the adjunction `j^* ⊣ j_*` and the fact that `j^* η`
is an isomorphism), so that cocycle is `η` followed by a cocycle on `j_*(𝒪ˣ|_Ω)`.

Note that it would **not** suffice to factor the map through the underived group
`Ext²_X(ℤ_X, j_*ℚ_Ω)` and prove the vanishing there: that statement is strictly stronger than the
one needed, and there is no reason for it to hold. The derived model is used exactly to avoid it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance chernRestrictionTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance chernRestrictionHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

variable (Ω : Opens (TopCat.of (ComplexPoint X)))

/-- The rational first Chern class attached to a class in `Ext¹(ℤ, 𝒪ˣ)`, restricted to the
complement of `Ωᶜ`, that is to `Ω`. This is the composite appearing on both sides of the
obligations below. -/
def restrictedRationalChernClass
    (e : Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1) :
    Hypercohomology X
      (derivedPushforwardComplementConstantRationalComplexInt X
        ((Ω : Set (ComplexPoint X))ᶜ)) 2 :=
  restrictToComplement X ((Ω : Set (ComplexPoint X))ᶜ) 2
    (integralToRationalCohomology X 2
      ((analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
        (holomorphicFirstChernClass X d e)))

/-- **Obligation (step 3).** The restricted rational first Chern class factors through the
restriction of the extension class to `Ω`, that is through the map
`Ext¹(ℤ, 𝒪ˣ) → Ext¹(ℤ, j_*(𝒪ˣ|_Ω))` induced by the canonical restriction morphism.

Mathematically this is the naturality of the exponential connecting map under restriction to the
open set `Ω`, combined with the identification of the target of `restrictToComplement` — the
hypercohomology of the derived pushforward from `Ω` — with the cohomology of `Ω`. -/
def HasRestrictedChernFactorization : Prop :=
  ∃ Φ : Abelian.Ext.{1} (constantIntegerSheaf X)
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1 →+
      Hypercohomology X
        (derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ)) 2,
    ∀ e : Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1,
      restrictedRationalChernClass X d Ω e =
        Φ (e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1))

/-- **Obligation (step 3), weak form.** A class in `Ext¹(ℤ, 𝒪ˣ)` that dies under restriction of
units to `Ω` has vanishing restricted rational first Chern class. This is the only consequence of
`HasRestrictedChernFactorization` that the divisor comparison uses. -/
def RestrictedChernClassVanishes : Prop :=
  ∀ e : Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1,
    e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1) = 0 →
      restrictedRationalChernClass X d Ω e = 0

/-- The factorisation obligation implies the vanishing obligation. -/
theorem restrictedChernClassVanishes_of_factorization
    (h : HasRestrictedChernFactorization X d Ω) : RestrictedChernClassVanishes X d Ω := by
  obtain ⟨Φ, hΦ⟩ := h
  intro e he
  rw [hΦ e, he, map_zero]

section Factorization

open CategoryTheory.Localization

set_option maxHeartbeats 1000000 in
/-- The cohomology/Ext comparison is additive. -/
theorem analyticSheafCohomologyEquivExt_add (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α β : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X F n (α + β) =
      analyticSheafCohomologyEquivExt X F n α + analyticSheafCohomologyEquivExt X F n β := by
  apply (SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  change _ = (analyticSheafCohomologyEquivExt X F n α +
    analyticSheafCohomologyEquivExt X F n β).hom
  rw [Abelian.Ext.add_hom]
  change _ = (SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X)))
      (analyticSheafCohomologyEquivExt X F n α) +
    (SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X)))
      (analyticSheafCohomologyEquivExt X F n β)
  have hadd := hypercohomologyEquiv_add X (analyticSheafComplexInt X F) (n : ℤ) α β
  rw [analyticSheafCohomologyEquivExt_apply, analyticSheafCohomologyEquivExt_apply,
    analyticSheafCohomologyEquivExt_apply]
  simp only [SmallShiftedHom.equiv_comp]
  rw [hadd]
  simp

/-- The cohomology/Ext comparison, as an isomorphism of abelian groups. -/
def analyticSheafCohomologyAddEquivExt (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X (analyticSheafComplexInt X F) n ≃+
      Abelian.Ext.{1} (constantIntegerSheaf X) F n where
  toEquiv := analyticSheafCohomologyEquivExt X F n
  map_add' := analyticSheafCohomologyEquivExt_add X F n

/-- Composition with a fixed shifted morphism, as an additive map on hypercohomology. -/
def hypercohomologyCompHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {m p n : ℤ}
    (γ : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L p) (h : p + m = n) :
    Hypercohomology X K m →+ Hypercohomology X L n where
  toFun a := SmallShiftedHom.comp a γ h
  map_zero' := by
    apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [SmallShiftedHom.equiv_comp, hypercohomologyEquiv_zero, hypercohomologyEquiv_zero,
      ShiftedHom.zero_comp]
  map_add' a b := by
    apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [SmallShiftedHom.equiv_comp, hypercohomologyEquiv_add, hypercohomologyEquiv_add,
      SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_comp, ShiftedHom.add_comp]

/-- Composing an `Ext` class read as hypercohomology with a further class. -/
lemma analyticSheafCohomologyEquivExt_comp (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n)
    {L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {p q : ℤ}
    (γ : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F) L p)
    (h : p + (n : ℤ) = q) :
    SmallShiftedHom.comp (analyticSheafCohomologyEquivExt X F n α) γ h =
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv).comp
        (SmallShiftedHom.comp α
          (SmallShiftedHom.comp (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
            (analyticSheafComplexIntIsoSingle X F).hom) γ (add_zero p)) h) (add_zero q) := by
  rw [analyticSheafCohomologyEquivExt_apply]
  rw [SmallShiftedHom.comp_assoc _ _ _ _ (zero_add (n : ℤ)) (add_zero p)
    (show p + 0 + (n : ℤ) = q by lia)]
  rw [SmallShiftedHom.comp_assoc _ _ _ _ (add_zero (n : ℤ)) h
    (show p + (n : ℤ) + 0 = q by lia)]

/-- The composite from the integral constant complex to the model of the derived pushforward. -/
def chernRestrictionTargetMap :
    constantIntegerSheafComplexInt X ⟶
      derivedPushforwardComplementConstantRationalComplexInt X
        ((Ω : Set (ComplexPoint X))ᶜ) :=
  integerToFieldConstantSheafComplexInt ℚ X 1 ≫
    rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)

/-- The rational Chern class restricted to `Ω`, as a single composition. -/
lemma restrictedRationalChernClass_eq
    (e : Abelian.Ext.{1} (constantIntegerSheaf X) (holomorphicUnitSheaf X d) 1) :
    restrictedRationalChernClass X d Ω e =
      SmallShiftedHom.comp ((analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
        (holomorphicFirstChernClass X d e))
        (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (chernRestrictionTargetMap X Ω)) (zero_add 2) := by
  show SmallShiftedHom.comp (SmallShiftedHom.comp
        ((analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
        (holomorphicFirstChernClass X d e))
        (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (integerToFieldConstantSheafComplexInt ℚ X 1)) (zero_add 2))
        (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) (zero_add 2) = _
  rw [SmallShiftedHom.comp_assoc _ _ _ _ (zero_add (2 : ℤ)) (add_zero (0 : ℤ))
    (show (0 : ℤ) + 0 + 2 = 2 by lia)]
  congr 1
  exact SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ) (analyticQuasiIsomorphisms X)
    (integerToFieldConstantSheafComplexInt ℚ X 1)
    (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))

set_option maxHeartbeats 1000000 in
/-- **Step 3c.** The restricted rational first Chern class factors through the restriction of the
extension class to `Ω`.

The factorisation is composition with the class `ζ` obtained from
`exists_comp_restrictionUnit_eq`: the whole composite defining `restrictedRationalChernClass` is
composition of the extension class with the single derived morphism
`ε ∘ (ℤ → ℚ → j_* I^•)`, and that morphism factors through `restrictionUnit Ω 𝒪ˣ` because
`j_* I^•` is K-injective with terms local on `Ω`. -/
theorem hasRestrictedChernFactorization : HasRestrictedChernFactorization X d Ω := by
  obtain ⟨ζ, hζ⟩ := exists_comp_restrictionUnit_eq X Ω ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl (compl_compl _).symm (holomorphicUnitSheaf X d) ((1 : ℕ) : ℤ)
    (SmallShiftedHom.comp (holomorphicExponentialSequence_shortExact X d).extClass
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
          chernRestrictionTargetMap X Ω)) (zero_add 1))
  refine ⟨(hypercohomologyCompHom X
      (SmallShiftedHom.comp (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X ((openRestrictionFunctor Ω).obj
          (holomorphicUnitSheaf X d))).hom) ζ (add_zero 1))
      (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)).comp
    (analyticSheafCohomologyAddEquivExt X ((openRestrictionFunctor Ω).obj
      (holomorphicUnitSheaf X d)) 1).symm.toAddMonoidHom, ?_⟩
  intro e
  have hα : analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2
      ((analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
        (holomorphicFirstChernClass X d e)) = holomorphicFirstChernClass X d e :=
    (analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).apply_symm_apply _
  have h1 := analyticSheafCohomologyEquivExt_comp X (constantIntegerSheaf X) 2
    ((analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
      (holomorphicFirstChernClass X d e))
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        chernRestrictionTargetMap X Ω)) (zero_add 2)
  rw [hα, SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ),
    show (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom ≫
      (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        chernRestrictionTargetMap X Ω = chernRestrictionTargetMap X Ω by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]] at h1
  have hy : analyticSheafCohomologyEquivExt X
      ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1
      ((analyticSheafCohomologyAddEquivExt X
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1).symm
        (e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1))) =
      e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1) :=
    (analyticSheafCohomologyEquivExt X _ 1).apply_symm_apply _
  have h2 := analyticSheafCohomologyEquivExt_comp X
    ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1
    ((analyticSheafCohomologyAddEquivExt X
      ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1).symm
      (e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1)))
    ζ (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)
  rw [hy] at h2
  have h3 : SmallShiftedHom.comp (holomorphicFirstChernClass X d e)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
          chernRestrictionTargetMap X Ω)) (zero_add 2) =
      SmallShiftedHom.comp
        (e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1))
        ζ (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) := by
    show SmallShiftedHom.comp (SmallShiftedHom.comp e
        (holomorphicExponentialSequence_shortExact X d).extClass
        (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)) _ (zero_add 2) = _
    have e1 := SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) e
      (holomorphicExponentialSequence_shortExact X d).extClass
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
          chernRestrictionTargetMap X Ω))
      (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) (zero_add ((1 : ℕ) : ℤ))
      (show (0 : ℤ) + ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)
    have e3 := congrArg (fun t : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (holomorphicUnitSheaf X d))
        (derivedPushforwardComplementConstantRationalComplexInt X
          ((Ω : Set (ComplexPoint X))ᶜ)) ((1 : ℕ) : ℤ) =>
      SmallShiftedHom.comp e t
        (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)) hζ
    have e2 := SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) e
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (restrictionUnit Ω (holomorphicUnitSheaf X d)))) ζ
      (zero_add ((1 : ℕ) : ℤ)) (add_zero ((1 : ℕ) : ℤ))
      (show ((1 : ℕ) : ℤ) + 0 + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)
    exact e1.trans (e3.trans e2.symm)
  apply (SmallShiftedHom.precompEquiv
    (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv
    (by change QuasiIso _; infer_instance) (a := ((2 : ℕ) : ℤ))).injective
  rw [restrictedRationalChernClass_eq]
  exact h1.symm.trans (h3.trans h2)

/-- **Step 3c.** The vanishing obligation, unconditionally. -/
theorem restrictedChernClassVanishes : RestrictedChernClassVanishes X d Ω :=
  restrictedChernClassVanishes_of_factorization X d Ω
    (hasRestrictedChernFactorization X d Ω)

end Factorization

variable {X d Ω}

/-- The restricted rational Chern class of an extension is the restriction of the rational image
of its first Chern class. -/
lemma restrictedRationalChernClass_cohomologyClass (E : HolomorphicUnitExtension X d) :
    restrictedRationalChernClass X d Ω E.cohomologyClass =
      restrictToComplement X ((Ω : Set (ComplexPoint X))ᶜ) 2
        (integralToRationalCohomology X 2 E.firstChernClass) := rfl

/-- **Step 3, first half.** Granting the obligation, the rational first Chern class of an
extension splitting over `Ω` restricts to zero on `Ω`. -/
theorem restrictToComplement_integralToRational_firstChernClass_eq_zero
    (hvan : RestrictedChernClassVanishes X d Ω) (E : HolomorphicUnitExtension X d)
    (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    restrictToComplement X ((Ω : Set (ComplexPoint X))ᶜ) 2
      (integralToRationalCohomology X 2 E.firstChernClass) = 0 :=
  (restrictedRationalChernClass_cohomologyClass E).symm.trans
    (hvan E.cohomologyClass (E.cohomologyClass_comp_restrictionUnit_eq_zero Ω ℓ hℓ))

/-- **Step 3, second half.** Granting the obligation, the rational first Chern class of an
extension splitting over `Ω` lifts to rational cohomology with support in the closed set `Ωᶜ`. -/
theorem exists_forgetSupport_eq_integralToRational_firstChernClass
    (hvan : RestrictedChernClassVanishes X d Ω) (E : HolomorphicUnitExtension X d)
    (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    ∃ β : RationalCohomologyWithSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2,
      forgetSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2 β =
        integralToRationalCohomology X 2 E.firstChernClass :=
  exists_forgetSupport_eq_of_restrictToComplement_eq_zero X _ 2 _
    (restrictToComplement_integralToRational_firstChernClass_eq_zero hvan E ℓ hℓ)

end AlgebraicGeometry.ComplexPoint
