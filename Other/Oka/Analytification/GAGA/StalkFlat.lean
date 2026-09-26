/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.SchemeAffine
public import Other.Oka.Analytification.RepresentableOpen
public import Other.Oka.Analytification.PresentationFlatness
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.FaithfullyFlatStalkMap

/-!
# The comparison morphism `X^an ⟶ X` has faithfully flat stalk maps

For a scheme `X` locally of finite type over `ℂ`, the stalk map of the comparison morphism
`π : X^an ⟶ X` is faithfully flat at every point of `X^an`.

The affine case, for the zero locus of a presentation, is
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec`. In general, the preimage of an
open `U` of `X` is an analytification of `U` (`ComplexAnalytic.IsAnalytification.restrict`);
if `U` is affine it is therefore isomorphic, over `U`, to the zero locus of a presentation
(`ComplexAnalytic.IsAnalytification.isoOfIsAnalytification`), and stalk maps are invariant under
isomorphisms and open immersions.

## Main results

- `ComplexAnalytic.faithfullyFlat_stalkMap_of_isAnalytification`: an analytification of a
  locally ringed space over `Spec ℂ` which is locally isomorphic to spectra of finitely
  generated `ℂ`-algebras has faithfully flat stalk maps.
- `ComplexAnalytic.faithfullyFlat_stalkMap_analytificationπ`: the comparison morphism
  `X^an ⟶ X` has faithfully flat stalk maps.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- `Spec R`, for a `ℂ`-algebra `R` of finite type, is isomorphic over `Spec ℂ` to the spectrum
of a presented algebra `ℂ[x] ⧸ (g)`. -/
theorem exists_iso_specOver_presentation {R : CommRingCat.{u}}
    (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R) (hφ : φ.hom.FiniteType) :
    ∃ (n k : ℕ) (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ),
      Nonempty (specOver (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap g))) ≅
        specOver φ) := by
  letI := (φ.hom.comp ULift.ringEquiv.symm.toRingHom : ℂ →+* R).toAlgebra
  haveI : Algebra.FiniteType ℂ R :=
    hφ.comp (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective)
  obtain ⟨P, ⟨e⟩⟩ := exists_presentation R
  let E : R ≅ CommRingCat.of P.alg := e.symm.toRingEquiv.toCommRingCatIso
  refine ⟨P.n, P.k, P.g, ⟨Over.isoMk (Spec.toLocallyRingedSpace.mapIso E.op) ?_⟩⟩
  change Spec.locallyRingedSpaceMap E.hom ≫ Spec.locallyRingedSpaceMap φ =
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap P.g)))
  rw [← Spec.locallyRingedSpaceMap_comp]
  congr 1
  ext c
  exact e.symm.commutes c.down

/-- **An analytification of the spectrum of a presented algebra has faithfully flat stalk
maps**, whichever analytification it is. -/
theorem faithfullyFlat_stalkMap_of_isAnalytification_of_iso {Y : Over specℂ}
    {W : AnalyticSpace.{u}} {π : toOverSpec.obj W ⟶ Y} (h : IsAnalytification π) {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (e : specOver (CommRingCat.ofHom (uliftAlgMap (presentedAlgebraMap g))) ≅ Y) (w : W) :
    (π.left.stalkMap w).hom.FaithfullyFlat := by
  have h' := (isAnalytification_analytificationToSpec g).of_iso e
  let I := h.isoOfIsAnalytification h'
  have hπ : π.left = I.hom.toLRSHom ≫ analytificationToSpec g ≫ e.hom.left :=
    (congrArg CommaMorphism.left
      (IsAnalytification.isoOfIsAnalytification_hom_comp h h')).symm
  rw [hπ]
  refine LocallyRingedSpace.faithfullyFlat_stalkMap_comp _ _ _
    (LocallyRingedSpace.faithfullyFlat_stalkMap_iso_hom
      ((Over.forget _).mapIso (toOverSpec.mapIso I)) _) ?_
  exact LocallyRingedSpace.faithfullyFlat_stalkMap_comp _ _ _
    (faithfullyFlat_stalkMap_analytificationToSpec g _)
    (LocallyRingedSpace.faithfullyFlat_stalkMap_iso_hom ((Over.forget _).mapIso e) _)

/-- **An analytification has faithfully flat stalk maps** as soon as the analytified space is
covered by opens isomorphic over `Spec ℂ` to spectra of `ℂ`-algebras of finite type. -/
theorem faithfullyFlat_stalkMap_of_isAnalytification {Y : Over specℂ}
    {W : AnalyticSpace.{u}} {π : toOverSpec.obj W ⟶ Y} (h : IsAnalytification π)
    (hY : ∀ y : Y.left, ∃ (U : Opens Y.left) (_ : y ∈ U) (R : CommRingCat.{u})
      (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R) (_ : φ.hom.FiniteType),
      Nonempty (specOver φ ≅ overRestrict Y U)) (w : W) :
    (π.left.stalkMap w).hom.FaithfullyFlat := by
  obtain ⟨U, hU, R, φ, hφ, ⟨e⟩⟩ := hY (π.left.base w)
  obtain ⟨n, k, g, ⟨e'⟩⟩ := exists_iso_specOver_presentation φ hφ
  let V := preimageOpens π U
  let w' : W.restrict V := ⟨w, hU⟩
  have h1 := faithfullyFlat_stalkMap_of_isAnalytification_of_iso (h.restrict U) g (e' ≪≫ e) w'
  have h2 := LocallyRingedSpace.faithfullyFlat_stalkMap_comp _ (overRestrictι Y U).left w' h1
    (LocallyRingedSpace.faithfullyFlat_stalkMap_of_isOpenImmersion
      (Y.left.ofRestrict U.isOpenEmbedding) _)
  have e : (restrictπ π U).left ≫ (overRestrictι Y U).left =
      (W.ofRestrict V).toLRSHom ≫ π.left :=
    congrArg CommaMorphism.left (restrictπ_comp π U)
  exact LocallyRingedSpace.faithfullyFlat_stalkMap_of_comp_eq (W.ofRestrict V).toLRSHom π.left
    _ e.symm w' h2

/-- Every point of a scheme locally of finite type over `ℂ` has an open neighbourhood which is
isomorphic over `Spec ℂ` to the spectrum of a `ℂ`-algebra of finite type. -/
theorem exists_iso_specOver_overRestrict (X : SchemeLFTℂ.{u}) (x : X.obj.left) :
    ∃ (U : Opens (schemeToOverSpec.obj X.obj).left) (_ : x ∈ U) (R : CommRingCat.{u})
      (φ : CommRingCat.of (ULift.{u} ℂ) ⟶ R) (_ : φ.hom.FiniteType),
      Nonempty (specOver φ ≅ overRestrict (schemeToOverSpec.obj X.obj) U) := by
  let 𝒰 := X.obj.left.affineCover
  let Y := schemeToOverSpec.obj X.obj
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have : LocallyRingedSpace.IsOpenImmersion (𝒰.f i).toLRSHom :=
    (inferInstance : IsOpenImmersion (𝒰.f i))
  let j : Over.mk ((𝒰.f i).toLRSHom ≫ Y.hom) ⟶ Y := Over.homMk (𝒰.f i).toLRSHom
  have : LocallyRingedSpace.IsOpenImmersion j.left := this
  let g : Spec Γ(𝒰.X i, ⊤) ⟶ Specℂ.{u} := (𝒰.X i).isoSpec.inv ≫ 𝒰.f i ≫ X.obj.hom
  have hg : LocallyOfFiniteType g := by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    dsimp [g]; infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  have hφft : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    exact hg
  refine ⟨opensRangeOver j, ⟨y, rfl⟩, _, φ, hφft, ⟨?_ ≪≫ isoOverRestrictOfIsOpenImmersion j⟩⟩
  refine Over.isoMk (Scheme.forgetToLocallyRingedSpace.mapIso (𝒰.X i).isoSpec.symm) ?_
  change (𝒰.X i).isoSpec.inv.toLRSHom ≫ (𝒰.f i).toLRSHom ≫ X.obj.hom.toLRSHom =
    (Spec.map φ).toLRSHom
  rw [hφ]
  rfl

/-- **The comparison morphism `X^an ⟶ X` has faithfully flat stalk maps**, at every point of
`X^an`, for every scheme `X` locally of finite type over `ℂ`. -/
theorem faithfullyFlat_stalkMap_analytificationπ (X : SchemeLFTℂ.{u})
    (w : analytification.obj X) :
    ((analytificationπ X).left.stalkMap w).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_isAnalytification (isAnalytification_analytificationπ X)
    (exists_iso_specOver_overRestrict X) w

/-- **The comparison morphism `X^an ⟶ X` has flat stalk maps.** -/
theorem flat_stalkMap_analytificationπ (X : SchemeLFTℂ.{u}) (w : analytification.obj X) :
    ((analytificationπ X).left.stalkMap w).hom.Flat :=
  (faithfullyFlat_stalkMap_analytificationπ X w).flat

/-- **Restricting over an open preserves faithful flatness of stalk maps**: if `π : W ⟶ Y` has
faithfully flat stalk maps, so does its restriction `π⁻¹ U ⟶ U` over an open `U` of `Y`. -/
theorem faithfullyFlat_stalkMap_restrictπ {Y : Over specℂ} {W : AnalyticSpace.{u}}
    {π : toOverSpec.obj W ⟶ Y} (hπ : ∀ w : W, (π.left.stalkMap w).hom.FaithfullyFlat)
    (U : Opens Y.left) (w : W.restrict (preimageOpens π U)) :
    ((restrictπ π U).left.stalkMap w).hom.FaithfullyFlat := by
  have e : (restrictπ π U).left ≫ Y.left.ofRestrict U.isOpenEmbedding =
      (W.ofRestrict (preimageOpens π U)).toLRSHom ≫ π.left :=
    congrArg CommaMorphism.left (restrictπ_comp π U)
  have hI : IsIso ((Y.left.ofRestrict U.isOpenEmbedding).stalkMap ((restrictπ π U).left.base w)) :=
    LocallyRingedSpace.ofRestrict_stalkMap_isIso _ _ _
  exact @LocallyRingedSpace.faithfullyFlat_stalkMap_of_comp_eq_right _ _ _ _ _ _ e w hI
    (LocallyRingedSpace.faithfullyFlat_stalkMap_comp _ _ w
      (LocallyRingedSpace.faithfullyFlat_stalkMap_of_isIso _ w) (hπ _))

/-- **The restriction `π⁻¹ U ⟶ U` of the comparison morphism `X^an ⟶ X` over an open `U` of `X`
has faithfully flat stalk maps.** -/
theorem faithfullyFlat_stalkMap_restrictπ_analytificationπ (X : SchemeLFTℂ.{u})
    (U : Opens (schemeToOverSpec.obj X.obj).left)
    (w : (analytification.obj X).restrict (preimageOpens (analytificationπ X) U)) :
    ((restrictπ (analytificationπ X) U).left.stalkMap w).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_restrictπ (faithfullyFlat_stalkMap_analytificationπ X) U w

end ComplexAnalytic

end
