/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Other.Oka.Analytification.GAGA.SheafAnalytification
public import Other.Oka.AnalyticSpace.ZeroLocus
public import Other.Oka.AnalyticSpace.Factorisation

/-!
# The analytification of a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over `ℂ`, and write
`π_X : X^an ⟶ X`, `π_Z : Z^an ⟶ Z` for the comparison morphisms.

**Affine target.** If `X` is affine and `h₁, …, h_p ∈ Γ(X, 𝒪_X)` generate the kernel of
`Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)`, then `i^an` cuts out `Z^an` inside `X^an` by the pulled-back sections
`π_X^♯ h_j` (`ComplexAnalytic.isCutOutBy_analytification_map`). The proof compares `Z^an` with the
zero locus `W` of the `π_X^♯ h_j` through the universal properties on both sides: `i^an` kills
the `π_X^♯ h_j`, so factors through `W`; conversely `W ⟶ X^an ⟶ X` kills the kernel of
`Γ(X) → Γ(Z)`, so factors through `Z`
(`AlgebraicGeometry.LocallyRingedSpace.closedImmersionLift`), hence through `Z^an`.

**General target.** Covering `X` by affine opens, the analytification of `i` is, over the preimage
of each of them, the analytification of the restricted closed immersion. Consequently:

- `ComplexAnalytic.range_analytification_map_of_isClosedImmersion`: the image of `i^an` is
  `π_X⁻¹(i(Z))`;
- `ComplexAnalytic.isClosedEmbedding_analytification_map`: `i^an` is a closed embedding;
- `ComplexAnalytic.surjective_stalkMap_analytification_map`: the stalk maps of `i^an` are
  surjective.

So `i^an` is a closed immersion of locally ringed spaces, and `Z^an` is in bijection with
`π_X⁻¹(i(Z))`: the square formed by `i`, `i^an` and the comparison morphisms is cartesian on
points (`ComplexAnalytic.existsUnique_analytification_map_eq`,
`ComplexAnalytic.analytificationHomeomorphPreimage`).

Finally, `ComplexAnalytic.analytificationPushforwardBaseChange` is the base change morphism
`(i_* G)^an ⟶ (i^an)_* (G^an)` for sheaves of modules, defined for any morphism `i`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-- A morphism of locally ringed spaces between complex analytic spaces which lifts a morphism of
analytic spaces along a morphism of analytic spaces is itself a morphism of analytic spaces. -/
def AnalyticSpace.homOfFac {A B C : AnalyticSpace.{u}} (f : A.toLocallyRingedSpace ⟶
    B.toLocallyRingedSpace) (g : B ⟶ C) (h : A ⟶ C) (w : f ≫ g.toLRSHom = h.toLRSHom) :
    A ⟶ B :=
  ⟨f, IsCLinearHom.of_comp w h.isCLinear g.isCLinear⟩

@[simp]
lemma AnalyticSpace.toLRSHom_homOfFac {A B C : AnalyticSpace.{u}} (f : A.toLocallyRingedSpace ⟶
    B.toLocallyRingedSpace) (g : B ⟶ C) (h : A ⟶ C) (w : f ≫ g.toLRSHom = h.toLRSHom) :
    (homOfFac f g h w).toLRSHom = f :=
  rfl

variable {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X)

/-- The naturality square of the comparison morphisms, as morphisms of locally ringed spaces. -/
@[reassoc]
lemma analytificationπLRS_naturality :
    (analytification.map i).toLRSHom ≫ analytificationπLRS X =
      analytificationπLRS Z ≫ i.hom.left.toLRSHom :=
  congrArg CommaMorphism.left (analytificationπ_naturality i)

/-! ### Affine target -/

section Affine

variable [IsClosedImmersion i.hom.left] [IsAffine X.obj.left] {p : ℕ}
  (h : Fin p → Γ(X.obj.left, ⊤))

/-- The sections `π_X^♯ h_j` of `𝒪_{X^an}` pulled back from sections `h_j` of `𝒪_X`. -/
abbrev analytificationSections : Fin p → (analytification.obj X).presheaf.obj (op ⊤) :=
  fun j ↦ (LocallyRingedSpace.Γ.map (analytificationπLRS X).op).hom (h j)

variable (hh : Ideal.span (Set.range h) = RingHom.ker i.hom.left.appTop.hom)

include hh

omit [IsClosedImmersion i.hom.left] [IsAffine X.obj.left] in
/-- `i^an` kills the sections `π_X^♯ h_j`. -/
lemma analytification_map_kills :
    ∀ j, (analytification.map i).toLRSHom.c.app (op ⊤) (analytificationSections h j) = 0 := by
  intro j
  change (LocallyRingedSpace.Γ.map (analytification.map i).toLRSHom.op).hom
    ((LocallyRingedSpace.Γ.map (analytificationπLRS X).op).hom (h j)) = 0
  rw [← LocallyRingedSpace.Γ_map_comp_apply, analytificationπLRS_naturality,
    LocallyRingedSpace.Γ_map_comp_apply]
  have hj : h j ∈ RingHom.ker i.hom.left.appTop.hom := hh ▸ Ideal.subset_span ⟨j, rfl⟩
  have : (LocallyRingedSpace.Γ.map i.hom.left.toLRSHom.op).hom (h j) = 0 := hj
  rw [this, map_zero]

/-- The zero locus `W ⊆ X^an` of the sections `π_X^♯ h_j`. -/
abbrev analytificationZeroLocus : AnalyticSpace.{u} :=
  AnalyticSpace.zeroLocusSubspace (analytification.obj X) (analytificationSections h)

omit [IsClosedImmersion i.hom.left] [IsAffine X.obj.left] in
/-- `W ⟶ X^an ⟶ X` kills the kernel of `Γ(X) → Γ(Z)`. -/
lemma zeroLocusSubspaceι_comp_kills (a : Γ(X.obj.left, ⊤)) (ha : i.hom.left.appTop a = 0) :
    (LocallyRingedSpace.Γ.map ((zeroLocusSubspaceι (analytification.obj X)
      (analytificationSections h)).toLRSHom ≫ analytificationπLRS X).op) a = 0 := by
  have hmem : a ∈ Ideal.span (Set.range h) := hh ▸ ha
  refine (Ideal.span_le (I := RingHom.ker (LocallyRingedSpace.Γ.map
    ((zeroLocusSubspaceι (analytification.obj X) (analytificationSections h)).toLRSHom ≫
      analytificationπLRS X).op).hom)).2 ?_ hmem
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, LocallyRingedSpace.Γ_map_comp_apply]
  exact pullbackΓ_zeroLocusSubspaceι_eq_zero _ _ j

/-- The morphism `W ⟶ Z` of locally ringed spaces through which `W ⟶ X^an ⟶ X` factors. -/
def zeroLocusToScheme :
    (analytificationZeroLocus h).toLocallyRingedSpace ⟶ Z.obj.left.toLocallyRingedSpace :=
  LocallyRingedSpace.closedImmersionLift i.hom.left _ (zeroLocusSubspaceι_comp_kills i h hh)

@[reassoc]
lemma zeroLocusToScheme_comp :
    zeroLocusToScheme i h hh ≫ i.hom.left.toLRSHom =
      (zeroLocusSubspaceι (analytification.obj X) (analytificationSections h)).toLRSHom ≫
        analytificationπLRS X :=
  LocallyRingedSpace.closedImmersionLift_comp _ _ _

/-- The morphism `W ⟶ Z` over `Spec ℂ`. -/
def zeroLocusToSchemeOver :
    toOverSpec.obj (analytificationZeroLocus h) ⟶ schemeToOverSpec.obj Z.obj :=
  Over.homMk (zeroLocusToScheme i h hh) (by
    have hZ : i.hom.left.toLRSHom ≫ X.obj.hom.toLRSHom = Z.obj.hom.toLRSHom :=
      congrArg Scheme.Hom.toLRSHom (Over.w i.hom)
    have hπ := Over.w (analytificationπ X)
    have hι := Over.w (toOverSpec.map
      (zeroLocusSubspaceι (analytification.obj X) (analytificationSections h)))
    change zeroLocusToScheme i h hh ≫ Z.obj.hom.toLRSHom = _
    rw [← hZ, zeroLocusToScheme_comp_assoc]
    change _ ≫ (analytificationπ X).left ≫ (schemeToOverSpec.obj X.obj).hom = _
    rw [hπ]
    exact hι)

/-- The morphism `W ⟶ Z^an` of analytic spaces. -/
def zeroLocusToAnalytification : analytificationZeroLocus h ⟶ analytification.obj Z :=
  (isAnalytification_analytificationπ Z).lift (zeroLocusToSchemeOver i h hh)

/-- The morphism `Z^an ⟶ W` of analytic spaces through which `i^an` factors. -/
def analytificationToZeroLocus : analytification.obj Z ⟶ analytificationZeroLocus h :=
  homOfFac ((isCutOutBy_zeroLocusSubspaceι (analytification.obj X)
      (analytificationSections h)).lift _ (analytification_map_kills i h hh))
    (zeroLocusSubspaceι _ _) (analytification.map i)
    ((isCutOutBy_zeroLocusSubspaceι _ _).lift_comp _ _)

omit [IsClosedImmersion i.hom.left] [IsAffine X.obj.left] in
@[reassoc (attr := simp)]
lemma analytificationToZeroLocus_ι :
    analytificationToZeroLocus i h hh ≫ zeroLocusSubspaceι _ _ = analytification.map i :=
  forgetToLocallyRingedSpace.map_injective
    ((isCutOutBy_zeroLocusSubspaceι _ _).lift_comp _ (analytification_map_kills i h hh))

@[reassoc]
lemma zeroLocusToAnalytification_π :
    (zeroLocusToAnalytification i h hh).toLRSHom ≫ analytificationπLRS Z =
      zeroLocusToScheme i h hh :=
  congrArg CommaMorphism.left ((isAnalytification_analytificationπ Z).lift_fac _)

@[reassoc (attr := simp)]
lemma zeroLocusToAnalytification_map :
    zeroLocusToAnalytification i h hh ≫ analytification.map i = zeroLocusSubspaceι _ _ := by
  refine (isAnalytification_analytificationπ X).hom_ext ?_
  ext1
  change (zeroLocusToAnalytification i h hh).toLRSHom ≫ (analytification.map i).toLRSHom ≫
    analytificationπLRS X = _
  rw [analytificationπLRS_naturality, zeroLocusToAnalytification_π_assoc,
    zeroLocusToScheme_comp]
  rfl

/-- **For an affine target, `Z^an` is the zero locus in `X^an` of the pulled-back generators of
the ideal of `Z`.** -/
def analytificationIsoZeroLocus : analytification.obj Z ≅ analytificationZeroLocus h where
  hom := analytificationToZeroLocus i h hh
  inv := zeroLocusToAnalytification i h hh
  hom_inv_id := by
    refine (isAnalytification_analytificationπ Z).hom_ext ?_
    ext1
    refine LocallyRingedSpace.closedImmersion_hom_ext i.hom.left ?_
    change (analytificationToZeroLocus i h hh).toLRSHom ≫
      ((zeroLocusToAnalytification i h hh).toLRSHom ≫ analytificationπLRS Z) ≫
        i.hom.left.toLRSHom = analytificationπLRS Z ≫ i.hom.left.toLRSHom
    rw [zeroLocusToAnalytification_π, zeroLocusToScheme_comp, ← Category.assoc,
      ← analytificationπLRS_naturality]
    exact congrArg (· ≫ analytificationπLRS X)
      (congrArg AnalyticSpace.Hom.toLRSHom (analytificationToZeroLocus_ι i h hh))
  inv_hom_id := by
    haveI := mono_zeroLocusSubspaceι (analytification.obj X) (analytificationSections h)
    rw [← cancel_mono (zeroLocusSubspaceι _ _), Category.assoc, analytificationToZeroLocus_ι,
      zeroLocusToAnalytification_map, Category.id_comp]

@[reassoc (attr := simp)]
lemma analytificationIsoZeroLocus_hom_ι :
    (analytificationIsoZeroLocus i h hh).hom ≫ zeroLocusSubspaceι _ _ = analytification.map i :=
  analytificationToZeroLocus_ι i h hh

/-- **The analytification of a closed immersion into an affine scheme cuts out `Z^an` by the
pulled-back generators of the ideal of `Z`.** -/
theorem isCutOutBy_analytification_map :
    IsCutOutBy (analytification.map i).toLRSHom (analytificationSections h) := by
  have := (isCutOutBy_zeroLocusSubspaceι (analytification.obj X)
    (analytificationSections h)).comp_iso
      (forgetToLocallyRingedSpace.mapIso (analytificationIsoZeroLocus i h hh))
  have e : (analytification.map i).toLRSHom =
      (forgetToLocallyRingedSpace.mapIso (analytificationIsoZeroLocus i h hh)).hom ≫
        (zeroLocusSubspaceι (analytification.obj X) (analytificationSections h)).toLRSHom :=
    (congrArg AnalyticSpace.Hom.toLRSHom (analytificationIsoZeroLocus_hom_ι i h hh)).symm
  rw [e]
  exact this

omit hh [IsAffine X.obj.left] in
/-- A point of `X^an` lies in the zero locus of the `π_X^♯ h_j` if and only if its image in `X`
lies in the zero locus of the `h_j`. -/
lemma mem_zeroLocus_analytificationSections_iff (x : analytification.obj X) :
    (∀ j, (analytification.obj X).presheaf.Γgerm x (analytificationSections h j) ∈
        IsLocalRing.maximalIdeal _) ↔
      ∀ j, ¬ IsUnit (X.obj.left.presheaf.Γgerm ((analytificationπLRS X).base x) (h j)) := by
  refine forall_congr' fun j ↦ ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine not_congr ?_
  have e : (analytification.obj X).presheaf.Γgerm x (analytificationSections h j) =
      (analytificationπLRS X).stalkMap x
        (X.obj.left.presheaf.Γgerm ((analytificationπLRS X).base x) (h j)) :=
    (LocallyRingedSpace.stalkMap_germ_apply (analytificationπLRS X) ⊤ x trivial (h j)).symm
  rw [e]
  exact isUnit_map_iff _ _

/-- **For an affine target, the image of `i^an` is `π_X⁻¹(i(Z))`.** -/
theorem range_analytification_map_of_isAffine :
    Set.range (analytification.map i).toLRSHom.base =
      (analytificationπLRS X).base ⁻¹' Set.range i.hom.left.base := by
  rw [(isCutOutBy_analytification_map i h hh).range_base]
  ext x
  rw [Set.mem_setOf_eq, mem_zeroLocus_analytificationSections_iff, Set.mem_preimage]
  rw [IsClosedImmersion.range_eq_of_isAffine i.hom.left h hh]
  rfl

end Affine

/-! ### Open subschemes -/

section Restrict

variable (X) (U : X.obj.left.Opens)

/-- The inclusion of an open subscheme, as a morphism of schemes locally of finite type over
`ℂ`. -/
def SchemeLFTℂ.restrictι : X.restrict U ⟶ X :=
  ObjectProperty.homMk (Over.homMk U.ι rfl)

@[simp]
lemma SchemeLFTℂ.restrictι_hom_left : (X.restrictι U).hom.left = U.ι := rfl

/-- **The analytification of the inclusion of an open subscheme `U ⊆ X` is the inclusion of the
open subspace `π_X⁻¹ U`**, through the identification `(X|_U)^an ≅ π_X⁻¹ U`. -/
theorem analytification_map_restrictι :
    analytification.map (X.restrictι U) =
      (analytificationRestrictIso X U).hom ≫
        (analytification.obj X).ofRestrict (analytificationPreimage X U) := by
  refine (isAnalytification_analytificationπ X).hom_ext ?_
  rw [analytificationπ_naturality]
  ext1
  change (analytificationπ (X.restrict U)).left ≫ U.ι.toLRSHom =
    (analytificationRestrictIso X U).hom.toLRSHom ≫
      ((analytification.obj X).ofRestrict (analytificationPreimage X U)).toLRSHom ≫
        (analytificationπ X).left
  rw [← analytificationRestrictIso_hom_comp]
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg _ (congrArg CommaMorphism.left (restrictπ_comp (analytificationπ X) U))

/-- The analytification of the inclusion of an open subscheme is an open embedding. -/
theorem isOpenEmbedding_analytification_map_restrictι :
    IsOpenEmbedding (analytification.map (X.restrictι U)).toLRSHom.base := by
  rw [analytification_map_restrictι]
  exact (TopologicalSpace.Opens.isOpenEmbedding _).comp
    (LocallyRingedSpace.homeoOfIso
      (forgetToLocallyRingedSpace.mapIso (analytificationRestrictIso X U))).isOpenEmbedding

/-- The image of the analytification of the inclusion of an open subscheme `U` is `π_X⁻¹ U`. -/
theorem range_analytification_map_restrictι :
    Set.range (analytification.map (X.restrictι U)).toLRSHom.base =
      (analytificationπLRS X).base ⁻¹' (U : Set X.obj.left) := by
  rw [analytification_map_restrictι]
  have hs := (AnalyticSpace.bijective_base_of_isIso
    (analytificationRestrictIso X U).hom).2.range_eq
  change Set.range (((analytification.obj X).ofRestrict _).toLRSHom.base ∘
    (analytificationRestrictIso X U).hom.toLRSHom.base) = _
  rw [Set.range_comp, hs, Set.image_univ, range_base_ofRestrict]
  rfl

instance isIso_stalkMap_analytification_map_restrictι (x) :
    IsIso ((analytification.map (X.restrictι U)).toLRSHom.stalkMap x) := by
  have key : ∀ {A B : LocallyRingedSpace.{u}} (f g : A ⟶ B) (a : A), f = g →
      IsIso (g.stalkMap a) → IsIso (f.stalkMap a) := by
    rintro A B f g a rfl h
    exact h
  refine key _ ((forgetToLocallyRingedSpace.mapIso (analytificationRestrictIso X U)).hom ≫
    ((analytification.obj X).ofRestrict (analytificationPreimage X U)).toLRSHom) x
    (congrArg AnalyticSpace.Hom.toLRSHom (analytification_map_restrictι X U)) ?_
  rw [LocallyRingedSpace.stalkMap_comp]
  haveI : LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.mapIso (analytificationRestrictIso X U)).hom :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (isIso_stalkMap_ofRestrict (analytification.obj X) (analytificationPreimage X U)
      ((forgetToLocallyRingedSpace.mapIso (analytificationRestrictIso X U)).hom.base x))
    (LocallyRingedSpace.IsOpenImmersion.stalk_iso
      (forgetToLocallyRingedSpace.mapIso (analytificationRestrictIso X U)).hom x)

end Restrict

/-! ### Restricting a closed immersion over an open of the target -/

section RestrictClosedImmersion

variable (U : X.obj.left.Opens)

/-- The restriction `i⁻¹ U ⟶ U` of `i : Z ⟶ X` over an open `U ⊆ X`. -/
def restrictHomLFT : Z.restrict (i.hom.left ⁻¹ᵁ U) ⟶ X.restrict U :=
  ObjectProperty.homMk (Over.homMk (i.hom.left ∣_ U) (by
    change (i.hom.left ∣_ U) ≫ U.ι ≫ X.obj.hom = (i.hom.left ⁻¹ᵁ U).ι ≫ Z.obj.hom
    rw [morphismRestrict_ι_assoc, Over.w i.hom]))

@[simp]
lemma restrictHomLFT_hom_left : (restrictHomLFT i U).hom.left = i.hom.left ∣_ U := rfl

@[reassoc]
lemma restrictHomLFT_restrictι :
    restrictHomLFT i U ≫ X.restrictι U = Z.restrictι (i.hom.left ⁻¹ᵁ U) ≫ i := by
  ext1
  exact Over.OverMorphism.ext (morphismRestrict_ι i.hom.left U)

instance [IsClosedImmersion i.hom.left] :
    IsClosedImmersion (restrictHomLFT i U).hom.left :=
  inferInstanceAs (IsClosedImmersion (i.hom.left ∣_ U))

/-- The analytification of the restricted morphism, composed with the inclusion of `π_X⁻¹ U`. -/
@[reassoc]
lemma analytification_map_restrictHomLFT_restrictι :
    analytification.map (restrictHomLFT i U) ≫ analytification.map (X.restrictι U) =
      analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U)) ≫ analytification.map i := by
  rw [← Functor.map_comp, ← Functor.map_comp, restrictHomLFT_restrictι]

end RestrictClosedImmersion

/-! ### General target -/

section Global

/-- The comparison morphisms intertwine `i^an` and `i` on points. -/
lemma analytificationπ_base_map (z : analytification.obj Z) :
    (analytificationπLRS X).base ((analytification.map i).toLRSHom.base z) =
      i.hom.left.base ((analytificationπLRS Z).base z) :=
  congrArg (fun f ↦ f.base z) (analytificationπLRS_naturality i)

/-- Every point of a scheme lies in an affine open. -/
lemma exists_affineOpens_mem (Y : Scheme.{u}) (y : Y) : ∃ U : Y.affineOpens, y ∈ (U : Y.Opens) :=
  Opens.mem_iSup.1 (by rw [iSup_affineOpens_eq_top]; trivial)

/-- The ring of global sections of an affine scheme locally of finite type over `ℂ` is
Noetherian. -/
lemma isNoetherianRing_of_isAffine (Y : SchemeLFTℂ.{u}) [IsAffine Y.obj.left] :
    IsNoetherianRing Γ(Y.obj.left, ⊤) := by
  haveI : LocallyOfFiniteType Y.obj.hom := Y.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  haveI : IsLocallyNoetherian Y.obj.left := LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The kernel of `Γ(X) → Γ(Z)` for a closed immersion into an affine scheme locally of finite type
over `ℂ` is finitely generated. -/
lemma exists_generators [IsAffine X.obj.left] :
    ∃ (p : ℕ) (h : Fin p → Γ(X.obj.left, ⊤)),
      Ideal.span (Set.range h) = RingHom.ker i.hom.left.appTop.hom := by
  haveI := isNoetherianRing_of_isAffine X
  exact Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (RingHom.ker i.hom.left.appTop.hom))

variable [IsClosedImmersion i.hom.left]

/-- The analytification of the restriction of `i` over an affine open is cut out by finitely many
sections. -/
lemma exists_isCutOutBy_restrict (U : X.obj.left.affineOpens) :
    ∃ (p : ℕ) (f : Fin p → (analytification.obj (X.restrict U.1)).presheaf.obj (op ⊤)),
      IsCutOutBy (analytification.map (restrictHomLFT i U.1)).toLRSHom f ∧
      Set.range (analytification.map (restrictHomLFT i U.1)).toLRSHom.base =
        (analytificationπLRS (X.restrict U.1)).base ⁻¹'
          Set.range (restrictHomLFT i U.1).hom.left.base := by
  haveI : IsAffine (X.restrict U.1).obj.left := inferInstanceAs (IsAffine U)
  obtain ⟨p, h, hh⟩ := exists_generators (restrictHomLFT i U.1)
  exact ⟨p, _, isCutOutBy_analytification_map _ h hh,
    range_analytification_map_of_isAffine _ h hh⟩

/-- **The image of the analytification of a closed immersion `i` is `π_X⁻¹(i(Z))`.** -/
theorem range_analytification_map_of_isClosedImmersion :
    Set.range (analytification.map i).toLRSHom.base =
      (analytificationπLRS X).base ⁻¹' Set.range i.hom.left.base := by
  ext x
  refine ⟨?_, fun ⟨z₀, hz₀⟩ ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, (analytificationπ_base_map i z).symm⟩
  obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left ((analytificationπLRS X).base x)
  have hx : x ∈ Set.range (analytification.map (X.restrictι U.1)).toLRSHom.base := by
    rw [range_analytification_map_restrictι]
    exact hU
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨p, f, -, hrange⟩ := exists_isCutOutBy_restrict i U
  have hy : y ∈ Set.range (analytification.map (restrictHomLFT i U.1)).toLRSHom.base := by
    rw [hrange]
    have h1 := analytificationπ_base_map (X.restrictι U.1) y
    have hmem : z₀ ∈ i.hom.left ⁻¹ᵁ U.1 := by
      change i.hom.left.base z₀ ∈ U.1
      rw [hz₀]
      exact hU
    refine ⟨⟨z₀, hmem⟩, Subtype.ext
      ((morphismRestrict_base_coe i.hom.left U.1 ⟨z₀, hmem⟩).trans ?_)⟩
    rw [hz₀, h1]
    rfl
  obtain ⟨w, rfl⟩ := hy
  refine ⟨(analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom.base w, ?_⟩
  exact (congrArg (fun φ ↦ φ.toLRSHom.base w)
    (analytification_map_restrictHomLFT_restrictι i U.1)).symm

/-- **The analytification of a closed immersion is a closed embedding.** -/
theorem isClosedEmbedding_analytification_map :
    IsClosedEmbedding (analytification.map i).toLRSHom.base := by
  have hemb : IsEmbedding (analytification.map i).toLRSHom.base := by
    refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _
      (analytification.map i).toLRSHom.base.hom.continuous
      (fun U : X.obj.left.affineOpens ↦ analytificationPreimage X U.1) ?_
      (fun U ↦ analytification.obj (Z.restrict (i.hom.left ⁻¹ᵁ U.1)))
      (fun U ↦ (analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom.base)
      (fun U ↦ (analytification.map _).toLRSHom.base.hom.continuous) (fun U ↦ ?_) (fun U ↦ ?_)
    · rintro _ ⟨z, rfl⟩
      obtain ⟨U, hU⟩ := exists_affineOpens_mem X.obj.left
        ((analytificationπLRS X).base ((analytification.map i).toLRSHom.base z))
      exact Opens.mem_iSup.2 ⟨U, hU⟩
    · intro z hz
      rw [range_analytification_map_restrictι]
      change i.hom.left.base ((analytificationπLRS Z).base z) ∈ U.1
      rw [← analytificationπ_base_map]
      exact hz
    · obtain ⟨p, f, hcut, -⟩ := exists_isCutOutBy_restrict i U
      have : (analytification.map i).toLRSHom.base ∘
          (analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom.base =
          (analytification.map (X.restrictι U.1)).toLRSHom.base ∘
            (analytification.map (restrictHomLFT i U.1)).toLRSHom.base :=
        funext fun w ↦ (congrArg (fun φ ↦ φ.toLRSHom.base w)
          (analytification_map_restrictHomLFT_restrictι i U.1)).symm
      rw [this]
      exact (isOpenEmbedding_analytification_map_restrictι X U.1).isEmbedding.comp
        hcut.isClosedEmbedding.isEmbedding
  refine ⟨hemb, ?_⟩
  rw [range_analytification_map_of_isClosedImmersion]
  exact i.hom.left.isClosedEmbedding.isClosed_range.preimage
    (analytificationπLRS X).base.hom.continuous

/-- **The stalk maps of the analytification of a closed immersion are surjective.** -/
theorem surjective_stalkMap_analytification_map (z : analytification.obj Z) :
    Function.Surjective ((analytification.map i).toLRSHom.stalkMap z) := by
  have key : ∀ {A B : LocallyRingedSpace.{u}} (f g : A ⟶ B) (a : A), f = g →
      Function.Surjective (g.stalkMap a) → Function.Surjective (f.stalkMap a) := by
    rintro A B f g a rfl h
    exact h
  obtain ⟨U, hU⟩ :=
    exists_affineOpens_mem X.obj.left (i.hom.left.base ((analytificationπLRS Z).base z))
  have hz : z ∈
      Set.range (analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom.base := by
    rw [range_analytification_map_restrictι]
    exact hU
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨p, f, hcut, -⟩ := exists_isCutOutBy_restrict i U
  have hsq := congrArg AnalyticSpace.Hom.toLRSHom
    (analytification_map_restrictHomLFT_restrictι i U.1)
  have h1 : Function.Surjective ((analytification.map (Z.restrictι (i.hom.left ⁻¹ᵁ U.1)) ≫
      analytification.map i).toLRSHom.stalkMap w) := by
    refine key _ ((analytification.map (restrictHomLFT i U.1)).toLRSHom ≫
      (analytification.map (X.restrictι U.1)).toLRSHom) w hsq.symm ?_
    rw [LocallyRingedSpace.stalkMap_comp]
    haveI := isIso_stalkMap_analytification_map_restrictι X U.1
      ((analytification.map (restrictHomLFT i U.1)).toLRSHom.base w)
    exact (hcut.surjective_stalkMap w).comp (ConcreteCategory.bijective_of_isIso
      ((analytification.map (X.restrictι U.1)).toLRSHom.stalkMap
        ((analytification.map (restrictHomLFT i U.1)).toLRSHom.base w))).2
  change Function.Surjective (((analytification.map
    (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom ≫ (analytification.map i).toLRSHom).stalkMap w)
    at h1
  rw [LocallyRingedSpace.stalkMap_comp] at h1
  haveI := isIso_stalkMap_analytification_map_restrictι Z (i.hom.left ⁻¹ᵁ U.1) w
  exact Function.Surjective.of_comp_left
    (f := (LocallyRingedSpace.Hom.stalkMap (analytification.map
      (Z.restrictι (i.hom.left ⁻¹ᵁ U.1))).toLRSHom w).hom) h1
    (ConcreteCategory.bijective_of_isIso _).1

/-- **`Z^an` is homeomorphic to `π_X⁻¹(i(Z)) ⊆ X^an`** via `i^an`. -/
def analytificationHomeomorphPreimage :
    analytification.obj Z ≃ₜ ((analytificationπLRS X).base ⁻¹' Set.range i.hom.left.base) :=
  (isClosedEmbedding_analytification_map i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_analytification_map_of_isClosedImmersion i))

@[simp]
lemma analytificationHomeomorphPreimage_apply_coe (z : analytification.obj Z) :
    (analytificationHomeomorphPreimage i z : analytification.obj X) =
      (analytification.map i).toLRSHom.base z :=
  rfl

/-- **The square formed by `i`, `i^an` and the comparison morphisms is cartesian on points**:
for `x ∈ X^an` and `z₀ ∈ Z` with `π_X(x) = i(z₀)` there is a unique `z ∈ Z^an` with
`i^an(z) = x`, and it satisfies `π_Z(z) = z₀`. -/
theorem existsUnique_analytification_map_eq (x : analytification.obj X) (z₀ : Z.obj.left)
    (hx : (analytificationπLRS X).base x = i.hom.left.base z₀) :
    ∃! z : analytification.obj Z, (analytification.map i).toLRSHom.base z = x ∧
      (analytificationπLRS Z).base z = z₀ := by
  have hmem : x ∈ Set.range (analytification.map i).toLRSHom.base := by
    rw [range_analytification_map_of_isClosedImmersion]
    exact ⟨z₀, hx.symm⟩
  obtain ⟨z, rfl⟩ := hmem
  refine ⟨z, ⟨rfl, i.hom.left.isClosedEmbedding.injective ?_⟩, fun z' hz' ↦
    (isClosedEmbedding_analytification_map i).injective hz'.1⟩
  rw [← analytificationπ_base_map, hx]

end Global

/-! ### The base change morphism for pushforward -/

section BaseChange

/-- **The base change morphism** `(i_* G)^an ⟶ (i^an)_* (G^an)` for a morphism `i : Z ⟶ X` of
schemes locally of finite type over `ℂ` and a sheaf of modules `G` on `Z`: the mate of the
isomorphism `(i^an)^* π_X^* ≅ π_Z^* i^*` of the commutative square
`i^an ≫ π_X = π_Z ≫ i`, i.e. the composite of the unit of `(i^an)^* ⊣ (i^an)_*` with
`(i^an)_*` of `(i^an)^* π_X^* i_* G ≅ π_Z^* i^* i_* G ⟶ π_Z^* G`. -/
def analytificationPushforwardBaseChange
    (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf) :
    (analytificationModules X).obj
        ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) ⟶
      (SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).obj
        ((analytificationModules Z).obj G) :=
  (analytification.map i).toLRSHom.pullbackModulesAdj.unit.app _ ≫
    (SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).map
      ((LocallyRingedSpace.Hom.pullbackModulesCommSqIso
          (analytificationπLRS_naturality i)).hom.app _ ≫
        (analytificationπLRS Z).pullbackModules.map
          (i.hom.left.toLRSHom.pullbackModulesAdj.counit.app G))

end BaseChange

end

end ComplexAnalytic

end
