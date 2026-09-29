/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveSpace

/-!
# The analytification of affine space is `ℂⁿ`

`ComplexAnalytic.affineSpace n = Spec ℂ[Y₀, …, Yₙ₋₁]` is presented by the empty tuple of
polynomials in `ℂ[x₁, …, xₙ]` (the variables indexed by `ULift (Fin n)`), whose zero locus is all
of `ℂⁿ`. Hence `ℂⁿ = AnalyticSpace.complexAffineSpace n`, with the comparison morphism
`ComplexAnalytic.complexAffineSpaceπ n : ℂⁿ ⟶ 𝔸ⁿ` over `Spec ℂ`, is an analytification of `𝔸ⁿ`,
and the analytification functor sends `affineSpace n` to `ℂⁿ`
(`ComplexAnalytic.analytificationAffineSpaceIso`), compatibly with the maps to `𝔸ⁿ`.

On points, `complexAffineSpaceπ n` sends `z` to the maximal ideal of polynomials vanishing at `z`
(`ComplexAnalytic.complexAffineSpaceπ_base_asIdeal`); in particular it is injective.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable (n : ℕ)

/-- The ring `ℂ[Y₀, …, Yₙ₋₁]` of `affineSpace n` is the algebra presented by the empty tuple:
coefficients `ULift ℂ ≃ ℂ`, variables `Fin n ≃ ULift (Fin n)`, and the quotient by the zero
ideal. -/
def affineSpaceRingEquiv :
    MvPolynomial (Fin n) (ULift.{u} ℂ) ≃+* PresentedAlgebra.{u} n 0 Fin.elim0 :=
  ((MvPolynomial.mapEquiv (Fin n) ULift.ringEquiv).trans
      (MvPolynomial.renameEquiv ℂ Equiv.ulift.symm).toRingEquiv).trans
    ((RingEquiv.quotientBot _).symm.trans (Ideal.quotEquivOfEq (by simp [presentationIdeal])))

@[simp]
lemma affineSpaceRingEquiv_C (c : ULift.{u} ℂ) :
    affineSpaceRingEquiv n (MvPolynomial.C c) =
      Ideal.Quotient.mk _ (MvPolynomial.C c.down) := by
  simp [affineSpaceRingEquiv]
  rfl

@[simp]
lemma affineSpaceRingEquiv_X (m : Fin n) :
    affineSpaceRingEquiv.{u} n (MvPolynomial.X m) =
      Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up m)) := by
  simp [affineSpaceRingEquiv]

/-- The zero locus of the empty tuple is `ℂⁿ`. -/
def analytificationEmptyIso :
    AnalyticSpace.analytification.{u} (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ) ≅
      AnalyticSpace.complexAffineSpace.{u} n where
  hom := analytificationInclHom _
  inv := liftHom _ _ coord (fun j ↦ j.elim0)
  hom_inv_id := hom_ext_analytification _ _ _ fun i ↦ by
    rw [Category.id_comp, Category.assoc, coordPullback_comp, coordPullback_liftHom_comp]
    rfl
  inv_hom_id := hom_ext_complexAffineSpace _ _ fun j ↦ by
    change coordPullback _ j = coordPullback (𝟙 _) j
    rw [coordPullback_liftHom_comp]
    simp only [coordPullback_apply]
    rfl

/-- `Spec` of `affineSpaceRingEquiv`, as an isomorphism over `Spec ℂ` from the spectrum of the
presented algebra to `affineSpace n`. -/
def specPresentationOverIso :
    specOver (CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap
      (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)))) ≅
      schemeToOverSpec.obj (affineSpace.{u} n).obj :=
  Over.isoMk (Spec.toLocallyRingedSpace.mapIso
    (affineSpaceRingEquiv.{u} n).toCommRingCatIso.op) (by
      change Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _ =
        Spec.locallyRingedSpaceMap _
      rw [← Spec.locallyRingedSpaceMap_comp]
      congr 1
      ext c
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      exact affineSpaceRingEquiv_C n c)

/-- **The comparison morphism `ℂⁿ ⟶ 𝔸ⁿ`** over `Spec ℂ`. -/
def complexAffineSpaceπ :
    toOverSpec.obj (AnalyticSpace.complexAffineSpace.{u} n) ⟶
      schemeToOverSpec.obj (affineSpace.{u} n).obj :=
  toOverSpec.map (analytificationEmptyIso.{u} n).inv ≫ analytificationToSpecOver _ ≫
    (specPresentationOverIso.{u} n).hom

/-- **`ℂⁿ` is the analytification of `𝔸ⁿ`.** -/
theorem isAnalytification_complexAffineSpaceπ :
    IsAnalytification (complexAffineSpaceπ.{u} n) := by
  have h := ((isAnalytification_analytificationToSpec _).of_iso
    (specPresentationOverIso.{u} n)).of_iso_source (analytificationEmptyIso.{u} n).symm
  simpa [complexAffineSpaceπ] using h

/-- **The analytification of `affineSpace n` is `ℂⁿ`.** -/
def analytificationAffineSpaceIso :
    analytification.obj (affineSpace.{u} n) ≅ AnalyticSpace.complexAffineSpace.{u} n :=
  (isAnalytification_analytificationπ _).isoOfIsAnalytification
    (isAnalytification_complexAffineSpaceπ n)

@[reassoc (attr := simp)]
theorem analytificationAffineSpaceIso_hom_comp :
    toOverSpec.map (analytificationAffineSpaceIso.{u} n).hom ≫ complexAffineSpaceπ n =
      analytificationπ (affineSpace.{u} n) :=
  IsAnalytification.isoOfIsAnalytification_hom_comp _ _

@[reassoc (attr := simp)]
theorem analytificationAffineSpaceIso_inv_comp :
    toOverSpec.map (analytificationAffineSpaceIso.{u} n).inv ≫
        analytificationπ (affineSpace.{u} n) = complexAffineSpaceπ n :=
  IsAnalytification.isoOfIsAnalytification_inv_comp _ _

/-- Evaluation of `ℂ[Y₀, …, Yₙ₋₁]` at a point of `ℂⁿ`. -/
def affineEval (z : AnalyticSpace.complexAffineSpace.{u} n) :
    MvPolynomial (Fin n) (ULift.{u} ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom ULift.ringEquiv.toRingHom fun m ↦ (z : ULift.{u} (Fin n) → ℂ) ⟨m⟩

/-- **On points, `ℂⁿ ⟶ 𝔸ⁿ` sends `z` to the ideal of polynomials vanishing at `z`.** -/
theorem complexAffineSpaceπ_base_asIdeal (z : AnalyticSpace.complexAffineSpace.{u} n) :
    ((complexAffineSpaceπ.{u} n).left.base z).asIdeal = RingHom.ker (affineEval n z) := by
  set y := (analytificationEmptyIso.{u} n).inv.toLRSHom.base z
  have hy : (y.1.1 : ULift.{u} (Fin n) → ℂ) = z := by
    have := congrArg (fun f ↦ f.toLRSHom.base z) (analytificationEmptyIso.{u} n).inv_hom_id
    exact this
  have h1 : (complexAffineSpaceπ.{u} n).left.base z =
      PrimeSpectrum.comap (affineSpaceRingEquiv.{u} n).toRingHom
        ((analytificationToSpec _).base y) := rfl
  rw [h1, PrimeSpectrum.comap_asIdeal, analytificationToSpec_base_asIdeal, RingHom.comap_ker]
  congr 1
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun m ↦ ?_)
  · simp [affineEval, quotientEval_mk]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, affineSpaceRingEquiv_X, quotientEval_mk, affineEval,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
    rw [hy]

/-- **`ℂⁿ ⟶ 𝔸ⁿ` is injective on points.** -/
theorem complexAffineSpaceπ_base_injective :
    Function.Injective (complexAffineSpaceπ.{u} n).left.base := by
  intro z w h
  have key (p : MvPolynomial (Fin n) (ULift.{u} ℂ)) :
      affineEval n z p = 0 ↔ affineEval n w p = 0 := by
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, ← complexAffineSpaceπ_base_asIdeal,
      ← complexAffineSpaceπ_base_asIdeal, h]
  funext ⟨m⟩
  have := (key (MvPolynomial.X m - MvPolynomial.C ⟨(w : ULift.{u} (Fin n) → ℂ) ⟨m⟩⟩)).2
    (by
      simp only [affineEval, RingEquiv.toRingHom_eq_coe, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, RingHom.coe_coe]
      exact sub_self _)
  simp only [affineEval, RingEquiv.toRingHom_eq_coe, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, RingHom.coe_coe,
    sub_eq_zero] at this
  exact this

end

end ComplexAnalytic

end
