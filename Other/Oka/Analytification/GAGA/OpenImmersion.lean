/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.SchemeAffine

/-!
# The analytification of an open immersion

For an open immersion `f : X ⟶ Y` of schemes locally of finite type over `ℂ`, the analytification
`f^an : X^an ⟶ Y^an` is, up to a unique isomorphism, the inclusion of the open subspace
`π⁻¹(f(X)) ⊆ Y^an`, where `π : Y^an ⟶ Y` is the comparison morphism
(`ComplexAnalytic.analytificationOpenImmersionIso`). In particular `f^an` is an open embedding
on points with range `π⁻¹(f(X))`, and an open immersion of locally ringed spaces.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable {X Y : SchemeLFTℂ.{u}} (f : X ⟶ Y) [IsOpenImmersion f.hom.left]

instance : LocallyRingedSpace.IsOpenImmersion (schemeToOverSpec.map f.hom).left :=
  (inferInstance : IsOpenImmersion f.hom.left)

/-- The preimage in `Y^an` of the image of an open immersion `f : X ⟶ Y`. -/
abbrev analytificationOpenImmersionPreimage : (analytification.obj Y).Opens :=
  preimageOpens (analytificationπ Y) (opensRangeOver (schemeToOverSpec.map f.hom))

lemma mem_analytificationOpenImmersionPreimage_iff (y : analytification.obj Y) :
    y ∈ analytificationOpenImmersionPreimage f ↔
      (analytificationπ Y).left.base y ∈ Set.range f.hom.left.base :=
  Iff.rfl

@[reassoc (attr := simp)]
lemma isoOverRestrictOfIsOpenImmersion_hom_ι {U Y : Over specℂ} (j : U ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j.left] :
    (isoOverRestrictOfIsOpenImmersion j).hom ≫ overRestrictι Y (opensRangeOver j) = j := by
  ext1
  have hV := LocallyRingedSpace.isOpenImmersion_ofRestrict Y.left (opensRangeOver j)
  change (isoOverRestrictOfIsOpenImmersion j).hom.left ≫
    Y.left.ofRestrict (opensRangeOver j).isOpenEmbedding = j.left
  exact @LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ j.left
    (Y.left.ofRestrict (opensRangeOver j).isOpenEmbedding) _ hV
    (by rw [LocallyRingedSpace.range_ofRestrict]; rfl)

/-- **The analytification of an open immersion `f : X ⟶ Y` is the open subspace of `Y^an` over
the image of `f`.** -/
def analytificationOpenImmersionIso :
    analytification.obj X ≅
      (analytification.obj Y).restrict (analytificationOpenImmersionPreimage f) :=
  (isAnalytification_analytificationπ X).isoOfIsAnalytification
    (((isAnalytification_analytificationπ Y).restrict _).of_iso
      (isoOverRestrictOfIsOpenImmersion (schemeToOverSpec.map f.hom)).symm)

@[reassoc (attr := simp)]
theorem analytificationOpenImmersionIso_hom_ofRestrict :
    (analytificationOpenImmersionIso f).hom ≫ (analytification.obj Y).ofRestrict _ =
      analytification.map f := by
  refine (isAnalytification_analytificationπ Y).hom_ext ?_
  rw [analytificationπ_naturality, Functor.map_comp, Category.assoc, ← restrictπ_comp]
  have h := IsAnalytification.isoOfIsAnalytification_hom_comp
    (isAnalytification_analytificationπ X)
    (((isAnalytification_analytificationπ Y).restrict
      (opensRangeOver (schemeToOverSpec.map f.hom))).of_iso
      (isoOverRestrictOfIsOpenImmersion (schemeToOverSpec.map f.hom)).symm)
  refine Eq.trans ?_ (congrArg (· ≫ schemeToOverSpec.map f.hom) h)
  simp only [Iso.symm_hom, Category.assoc]
  congr 2
  exact (Iso.eq_inv_comp _).2 (isoOverRestrictOfIsOpenImmersion_hom_ι _)

instance isIso_forget_analytificationOpenImmersionIso_hom :
    IsIso (analytificationOpenImmersionIso f).hom.toLRSHom :=
  (forgetToLocallyRingedSpace.mapIso (analytificationOpenImmersionIso f)).isIso_hom

/-- **The analytification of an open immersion is an open immersion.** -/
instance isOpenImmersion_analytification_map :
    LocallyRingedSpace.IsOpenImmersion (analytification.map f).toLRSHom := by
  rw [← analytificationOpenImmersionIso_hom_ofRestrict]
  haveI : LocallyRingedSpace.IsOpenImmersion
      ((analytification.obj Y).ofRestrict (analytificationOpenImmersionPreimage f)).toLRSHom :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict (analytification.obj Y).toLocallyRingedSpace
      (analytificationOpenImmersionPreimage f)
  exact LocallyRingedSpace.IsOpenImmersion.comp
    (analytificationOpenImmersionIso f).hom.toLRSHom
    ((analytification.obj Y).ofRestrict (analytificationOpenImmersionPreimage f)).toLRSHom

/-- The analytification of an open immersion is an open embedding on points. -/
theorem isOpenEmbedding_analytification_map :
    Topology.IsOpenEmbedding (analytification.map f).toLRSHom.base :=
  PresheafedSpace.IsOpenImmersion.base_open (f := (analytification.map f).toLRSHom.toHom)

/-- **The image of the analytification of an open immersion `f` is the preimage of the image
of `f`.** -/
theorem range_analytification_map :
    Set.range (analytification.map f).toLRSHom.base = analytificationOpenImmersionPreimage f := by
  rw [← analytificationOpenImmersionIso_hom_ofRestrict]
  have hs := (AnalyticSpace.bijective_base_of_isIso
    (analytificationOpenImmersionIso f).hom).2.range_eq
  change Set.range (((analytification.obj Y).ofRestrict _).toLRSHom.base ∘
    (analytificationOpenImmersionIso f).hom.toLRSHom.base) = _
  rw [Set.range_comp, hs, Set.image_univ, range_base_ofRestrict]

end

end ComplexAnalytic

end
