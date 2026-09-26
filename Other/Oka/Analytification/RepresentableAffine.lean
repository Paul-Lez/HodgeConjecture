/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.OverSpec
public import Other.Oka.Analytification.UniversalProperty
public import Other.Oka.Analytification.Functor

/-!
# The analytification of an affine scheme of finite type over `ℂ`

For a finitely generated `ℂ`-algebra `A`, the analytic space `X^an` of a presentation of `A`,
with the comparison morphism `X^an ⟶ Spec A`, is an analytification of `Spec A` over `Spec ℂ` in
the sense of `ComplexAnalytic.IsAnalytification`: by the Γ-Spec adjunction, a morphism
`Z ⟶ Spec A` over `Spec ℂ` is a `ℂ`-algebra map `A ⟶ Γ(Z, 𝒪_Z)`, and by the universal property of
`X^an` these are the morphisms `Z ⟶ X^an`.

## Main results

- `ComplexAnalytic.analytificationToSpecOver`: the comparison morphism `X^an ⟶ Spec (ℂ[x]/I)`
  as a morphism over `Spec ℂ`.
- `ComplexAnalytic.isAnalytification_analytificationToSpec`: it is an analytification.
- `ComplexAnalytic.rightAdjointObjIsDefined_specOver`: `Spec R` has an analytification for every
  `ℂ`-algebra `R` of finite type, by choosing a presentation of `R`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

/-- `Spec R` over `Spec ℂ`, for a ring map `ULift ℂ ⟶ R`. -/
noncomputable def specOver {R : CommRingCat.{u}} (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R) :
    Over specℂ.{u} :=
  Over.mk (Spec.locallyRingedSpaceMap φ)

/-- Composing the morphism `X ⟶ Spec S` of an algebra structure `α` with `Spec ψ` is the
morphism of the algebra structure `α ∘ ψ`. -/
theorem toSpecOfAlgMap_comp_locallyRingedSpaceMap {X : LocallyRingedSpace.{u}} {R S : Type u}
    [CommRing R] [CommRing S] (ψ : R →+* S) (α : S →+* X.presheaf.obj (op ⊤)) :
    X.toSpecOfAlgMap α ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ) =
      X.toSpecOfAlgMap (α.comp ψ) := by
  rw [LocallyRingedSpace.toSpecOfAlgMap, LocallyRingedSpace.toSpecOfAlgMap, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp]
  rfl

section Presented

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The constants of `ℂ[x]/I` act on `X^an` by the constants of `𝒪_{X^an}`. -/
theorem quotientToGlobal_comp_presentedAlgebraMap :
    (quotientToGlobal g).comp (presentedAlgebraMap g) =
      (AnalyticSpace.analytification g).algebraMap := by
  ext c
  change polyToGlobal g (MvPolynomial.C c) = _
  rw [polyToGlobal_eq_eval₂Hom, MvPolynomial.eval₂Hom_C]

/-- **The comparison morphism `X^an ⟶ Spec (ℂ[x]/I)`, as a morphism over `Spec ℂ`.** -/
noncomputable def analytificationToSpecOver :
    toOverSpec.obj (AnalyticSpace.analytification g) ⟶
      specOver (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap g))) :=
  Over.homMk (analytificationToSpec g) (by
    change LocallyRingedSpace.toSpecOfAlgMap _ (quotientToGlobal g) ≫ _ =
      LocallyRingedSpace.toSpecOfAlgMap _ (uliftAlgMap (AnalyticSpace.analytification g).algebraMap)
    refine (toSpecOfAlgMap_comp_locallyRingedSpaceMap _ _).trans ?_
    rw [← quotientToGlobal_comp_presentedAlgebraMap]
    rfl)

@[simp]
theorem analytificationToSpecOver_left :
    (analytificationToSpecOver g).left = analytificationToSpec g := rfl

/-- Composing with the comparison morphism is, under the Γ-Spec adjunction, pulling back
`ComplexAnalytic.quotientToGlobal`. -/
theorem map_comp_analytificationToSpecOver_left {Z : AnalyticSpace.{u}}
    (ψ : Z ⟶ AnalyticSpace.analytification g) :
    (toOverSpec.map ψ ≫ analytificationToSpecOver g).left =
      Z.toLocallyRingedSpace.toSpecOfAlgMap
        (LocallyRingedSpace.comapAlgMap ψ.toLRSHom (quotientToGlobal g)) :=
  LocallyRingedSpace.comp_toSpecOfAlgMap ψ.toLRSHom (quotientToGlobal g)

/-- **`X^an ⟶ Spec (ℂ[x]/I)` is an analytification over `Spec ℂ`.** -/
theorem isAnalytification_analytificationToSpec :
    IsAnalytification (analytificationToSpecOver g) := by
  intro Z
  constructor
  · intro ψ₁ ψ₂ h
    have h' := LocallyRingedSpace.toSpecOfAlgMap_injective _
      ((map_comp_analytificationToSpecOver_left g ψ₁).symm.trans
        ((congrArg CommaMorphism.left h).trans (map_comp_analytificationToSpecOver_left g ψ₂)))
    refine hom_ext_analytification g ψ₁ ψ₂ fun i ↦ ?_
    rw [coordPullback_comp, coordPullback_comp]
    have := RingHom.congr_fun h' (Ideal.Quotient.mk _ (MvPolynomial.X i))
    change (LocallyRingedSpace.Γ.map ψ₁.toLRSHom.op).hom (polyToGlobal g (MvPolynomial.X i)) =
      (LocallyRingedSpace.Γ.map ψ₂.toLRSHom.op).hom (polyToGlobal g (MvPolynomial.X i)) at this
    rwa [polyToGlobal_X] at this
  · intro f
    obtain ⟨β, hβ⟩ : ∃ β : PresentedAlgebra n k g →+* Z.presheaf.obj (op ⊤),
        Z.toLocallyRingedSpace.toSpecOfAlgMap β = f.left :=
      LocallyRingedSpace.exists_toSpecOfAlgMap_eq _ f.left
    have hβc' : β.comp (uliftAlgMap (presentedAlgebraMap g)) = uliftAlgMap Z.algebraMap :=
      LocallyRingedSpace.toSpecOfAlgMap_injective _
        ((toSpecOfAlgMap_comp_locallyRingedSpaceMap _ _).symm.trans
          ((congrArg (· ≫ Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap g)))) hβ).trans (Over.w f)))
    have hβc : β.comp (presentedAlgebraMap g) = Z.algebraMap :=
      RingHom.ext fun c ↦ RingHom.congr_fun hβc' (ULift.up c)
    let a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤) :=
      fun i ↦ β (Ideal.Quotient.mk _ (MvPolynomial.X i))
    have hβ' : β.comp (Ideal.Quotient.mk (presentationIdeal g)) =
        MvPolynomial.eval₂Hom Z.algebraMap a :=
      MvPolynomial.ringHom_ext
        (fun c ↦ (RingHom.congr_fun hβc c).trans (MvPolynomial.eval₂Hom_C _ _ c).symm)
        (fun i ↦ (MvPolynomial.eval₂Hom_X' Z.algebraMap a i).symm)
    have ha : ∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0 := fun j ↦
      (RingHom.congr_fun hβ' (g j)).symm.trans
        ((congrArg β (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩))).trans
          (map_zero β))
    refine ⟨liftHom g Z a ha, Over.OverMorphism.ext ?_⟩
    rw [map_comp_analytificationToSpecOver_left, ← hβ]
    congr 1
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
    · change (LocallyRingedSpace.Γ.map (liftHom g Z a ha).toLRSHom.op).hom
          (((quotientToGlobal g).comp (presentedAlgebraMap g)) c) =
        (β.comp (presentedAlgebraMap g)) c
      rw [quotientToGlobal_comp_presentedAlgebraMap, hβc]
      exact (liftHom g Z a ha).isCLinear c
    · change (LocallyRingedSpace.Γ.map (liftHom g Z a ha).toLRSHom.op).hom
          (polyToGlobal g (MvPolynomial.X i)) = a i
      rw [polyToGlobal_X, analytificationCoord, ← coordPullback_comp]
      exact coordPullback_liftHom_comp g Z a ha i

end Presented

/-- **`Spec R` has an analytification when `R` is of finite type over `ℂ`.** -/
theorem rightAdjointObjIsDefined_specOver {R : CommRingCat.{u}}
    (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R) (hφ : φ.hom.FiniteType) :
    AnalyticSpace.toOverSpec.rightAdjointObjIsDefined (specOver φ) := by
  letI := (φ.hom.comp ULift.ringEquiv.symm.toRingHom : ℂ →+* R).toAlgebra
  haveI : Algebra.FiniteType ℂ R :=
    hφ.comp (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective)
  obtain ⟨P, ⟨e⟩⟩ := exists_presentation R
  let E : R ≅ CommRingCat.of P.alg := e.symm.toRingEquiv.toCommRingCatIso
  refine rightAdjointObjIsDefined_of_iso
    (Over.isoMk (Spec.toLocallyRingedSpace.mapIso E.op) ?_)
    (isAnalytification_analytificationToSpec P.g).rightAdjointObjIsDefined
  change Spec.locallyRingedSpaceMap E.hom ≫ Spec.locallyRingedSpaceMap φ =
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap P.g)))
  rw [← Spec.locallyRingedSpaceMap_comp]
  congr 1
  ext c
  exact e.symm.commutes c.down

end ComplexAnalytic

end
