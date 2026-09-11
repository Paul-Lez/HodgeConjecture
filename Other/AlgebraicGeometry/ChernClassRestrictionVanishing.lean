/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionOpenRestriction
public import Other.AlgebraicGeometry.CohomologyWithSupportExact

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

What is **missing** is the compatibility of the exponential connecting map with that restriction,
i.e. that the restricted rational Chern class depends only on the restricted extension class. It
is stated here as the two propositions

* `HasRestrictedChernFactorization X d Ω` — the restricted rational Chern class factors through
  `Ext¹(ℤ, j_*(𝒪ˣ|_Ω))`;
* `RestrictedChernClassVanishes X d Ω` — the weaker form actually used: a class killed by the
  restriction of units has vanishing restricted rational Chern class.

The first implies the second (`restrictedChernClassVanishes_of_factorization`), and the second
gives the two theorems of step 3
(`restrictToComplement_integralToRational_firstChernClass_eq_zero` and
`exists_forgetSupport_eq_integralToRational_firstChernClass`).

Mathematically both hold because the whole exponential sequence restricts to `Ω`, where the
restricted extension splits; formalising that requires comparing
`Hypercohomology X (j_* I^•)` — the target of `restrictToComplement`, which is the *derived*
pushforward — with `Ext_Ω(ℤ_Ω, ℚ_Ω)`. Note that it would **not** suffice to factor the map through
the underived group `Ext²_X(ℤ_X, j_*ℚ_Ω)` and prove the vanishing there: that statement is
strictly stronger than the one needed, and there is no reason for it to hold.
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
