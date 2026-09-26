/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.Geometry.RingedSpace.OpenImmersion
public import Other.Oka.Topology.Sheaves.Stalks

/-!
# Open covers of a locally ringed space, and gluing morphisms out of one

Mathlib glues locally ringed *spaces* ; `AlgebraicGeometry.LocallyRingedSpace.GlueData` in
`Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` ; but it does not glue *morphisms* out
of one. `AlgebraicGeometry.Scheme.Cover.glueMorphisms` exists and is one of the most-used
pieces of the scheme API; the analogue for a locally ringed space is absent, and this file
supplies it. Material for `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`; see
`README.md` on the mirror tree.

## The shape of the argument, and why it is a port

`CategoryTheory.GlueData.glued` is a `Multicoequalizer`, so mapping *out* of a glued space is
`Multicoequalizer.desc` and is free. All the content is therefore in identifying `X` with the
gluing of the members of a cover of it, i.e. in `IsIso fromGlued`, and that argument is the
scheme-side one with the `Scheme` layer removed:

* `fromGlued` is injective on points, by `GlueData.ι_eq_iff` and the fact that the topological
  pullback computes the intersection;
* it is an isomorphism on stalks, because `ι i ≫ fromGlued = 𝒰.map i` and both of the others are
  open immersions;
* it is an open map, by `GlueData.isOpen_iff`;
* hence it is an open immersion (`IsOpenImmersion.of_stalk_iso`), and it is surjective, so it is
  an isomorphism (`IsOpenImmersion.to_iso`).

**Only the last two steps existed for `LocallyRingedSpace`.** `IsOpenImmersion.of_stalk_iso` and
`IsOpenImmersion.to_iso` are in `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, as are the
pullbacks of open immersions and their preservation by every forgetful functor in sight. What was
missing, and is supplied here, is the carrier-level API of a `LocallyRingedSpace.GlueData`:
`isoCarrier`, `ι_isoCarrier_inv`, `Rel`, `ι_eq_iff` and `isOpen_iff`, each of which exists for
`Scheme.GlueData` and for no other level of the hierarchy. Their proofs are the scheme-side ones
with one `Iso.trans` removed.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.GlueData.isoCarrier`: the underlying space of a gluing is
  the gluing of the underlying spaces.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover`: an open cover of a locally ringed space.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.gluedCover`: the glue data of an open cover.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.fromGlued`: the canonical morphism from the
  gluing of a cover of `X` to `X`, an isomorphism.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`: the glued morphism.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`: the same, out of a gluing, with
  the compatibility asked for over the glue data's own overlaps.
- `AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens`: the open cover attached to a family of
  open subsets covering the space.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange`: the image of a member of a cover,
  as an open subset, with `…OpenCover.isoRestrict` identifying that member with the restriction
  to its image and `…OpenCover.restrictAlgMap` carrying an algebra structure across.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`: the members of a glue data are an
  open cover of the glued space.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData`: **the `LocallyRingedSpace`
  layer of a glue datum carries no data**, so two of them with the same underlying
  `CategoryTheory.GlueData` are equal. The only field the extension adds is `f_open`, a `Prop`;
  Mathlib states `AlgebraicGeometry.PresheafedSpace.GlueData` and
  `AlgebraicGeometry.SheafedSpace.GlueData` in the same shape and has the lemma for neither.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` and `…GlueData.isOpen_iff`: two points
  of a gluing are equal exactly when they are related in the evident way, and a subset of a
  gluing is open exactly when its preimage in every member is.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued`: **a locally ringed space is
  the gluing of the members of any open cover of it.**
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange`: the images of the members of
  a cover cover the space, which is `OpenCover.covers` in the form the cover-indexed API asks
  for.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms`: **morphisms out of
  the members of an open cover which agree on the overlaps glue to a unique morphism out of the
  whole space**, with `…OpenCover.ι_glueMorphisms` and `…OpenCover.hom_ext` as the two halves.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback`: the overlap `V (i, j)` of a glue
  data is the categorical pullback of the two inclusions into the gluing, and
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm` is what that buys: a
  family of morphisms out of the members which agrees over the *chosen* overlaps satisfies the
  *pullback* condition `OpenCover.glueMorphisms` asks for.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms` and
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext`: **the morphism glued out of a gluing
  restricts to the given one on each member, and it is the only one that does** ; the universal
  property in the two halves a caller uses.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext`: **an algebra structure on a
  space is determined by its pullbacks to the members of an open cover**, which is what lets a
  condition on global sections be checked member by member.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap`: **algebra
  structures on the members of a glue data which agree on the overlaps are compatible on the
  gluing** ; the hypothesis a caller can supply, in place of the sheaf-condition form, which for
  a glue data has nothing to be pulled back from.
- `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'`: the `f_open` field of a glue data
  built by `CategoryTheory.GlueData.ofGlueData'`, which is what makes that route to a
  `AlgebraicGeometry.LocallyRingedSpace.GlueData` cheaper than building one directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The transition maps of the associated glue data of presheafed spaces are open immersions.

This is `PresheafedSpace.GlueData.f_open` of the derived glue data. It has to be restated as an
instance because instance search does not unfold the `abbrev` chain
`toSheafedSpaceGlueData ≫ toPresheafedSpaceGlueData` to find the field; without it, the
`PreservesLimit (cospan _ _) (PresheafedSpace.forget _)` instances that `GlueData.gluedIso`
needs are not found. `Mathlib/AlgebraicGeometry/Gluing.lean` restates the same instances one
level up for the same reason. -/
instance isOpenImmersion_toPresheafedSpaceGlueData_f (i j : D.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f i j) :=
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f_open i j

local notation "D_" => TopCat.GlueData.toGlueData <|
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

set_option backward.isDefEq.respectTransparency false in
/-- **The underlying topological space of a gluing of locally ringed spaces is the gluing of the
underlying topological spaces.** -/
noncomputable def isoCarrier : 𝖣.glued.carrier ≅ (D_).glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    CategoryTheory.GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  exact D.isoSheafedSpace

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    (D_).ι i ≫ D.isoCarrier.inv = (𝖣.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv, CategoryTheory.GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv,
    Iso.trans_inv, Functor.mapIso_inv, SheafedSpace.forgetToPresheafedSpace_map,
    PresheafedSpace.forget_map, PresheafedSpace.forget_map, ← PresheafedSpace.comp_base,
    ← Category.assoc, D.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  dsimp
  rw [← PresheafedSpace.comp_base, ← InducedCategory.comp_hom, D.ι_isoSheafedSpace_inv i]
  rfl

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`. -/
def Rel (a b : Σ i, ((D.U i).carrier : Type u)) : Prop :=
  ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).base x = b.2

set_option backward.isDefEq.respectTransparency false in
theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    (𝖣.ι i).base x = (𝖣.ι j).base y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_ (TopCat.GlueData.ι_eq_iff_rel
    D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp ?_).eq_iff, ← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_isoCarrier_inv]
    rfl
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem isOpen_iff (U : Set 𝖣.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((𝖣.ι i).base ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage, TopCat.GlueData.isOpen_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← Set.preimage_comp, ← ι_isoCarrier_inv]
  rfl

end AlgebraicGeometry.LocallyRingedSpace.GlueData

namespace AlgebraicGeometry.LocallyRingedSpace

/-- An open cover of a locally ringed space. -/
structure OpenCover (X : LocallyRingedSpace.{u}) where
  /-- The index type of the cover. -/
  J : Type u
  /-- The locally ringed space covering `X` at the index `j`. -/
  obj : J → LocallyRingedSpace.{u}
  /-- The open immersion of the `j`-th member of the cover into `X`. -/
  map : ∀ j, obj j ⟶ X
  /-- For each point of `X`, an index whose member of the cover contains it. -/
  idx : X → J
  /-- The chosen member of the cover really does contain the point. -/
  covers : ∀ x, x ∈ Set.range (map (idx x)).base
  /-- Each member of the cover is an open immersion. -/
  [isOpen : ∀ j, IsOpenImmersion (map j)]

attribute [instance] OpenCover.isOpen

namespace OpenCover

variable {X : LocallyRingedSpace.{u}} (𝒰 : OpenCover X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
noncomputable def gluedCoverT' (x y z : 𝒰.J) :
    Limits.pullback (Limits.pullback.fst (𝒰.map x) (𝒰.map y))
        (Limits.pullback.fst (𝒰.map x) (𝒰.map z)) ⟶
      Limits.pullback (Limits.pullback.fst (𝒰.map y) (𝒰.map z))
        (Limits.pullback.fst (𝒰.map y) (𝒰.map x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp

theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

theorem glued_cover_cocycle (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

/-- The glue data associated with an open cover. -/
@[simps]
noncomputable def gluedCover : GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := 𝒰.gluedCoverT' x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  cocycle x y z := 𝒰.glued_cover_cocycle x y z
  f_open _ := inferInstance

/-- The canonical morphism from the gluing of an open cover of `X` into `X`. -/
noncomputable def fromGlued : 𝒰.gluedCover.toGlueData.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.map x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition

@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.J) : 𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued = 𝒰.map x :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem fromGlued_injective : Function.Injective 𝒰.fromGlued.base := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at h
  simp_rw [← LocallyRingedSpace.comp_base] at h
  rw [ι_fromGlued, ι_fromGlued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat)
        (𝒰.map i) (𝒰.map j))
  rw [𝒰.gluedCover.ι_eq_iff]
  refine ⟨e.hom ⟨⟨x, y⟩, h⟩, ?_, ?_⟩
  · erw [← ConcreteCategory.comp_apply e.hom,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  · erw [← ConcreteCategory.comp_apply e.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance isIso_stalkMap_fromGlued (x : 𝒰.gluedCover.toGlueData.glued) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) x
  rw [LocallyRingedSpace.stalkMap_comp, ← IsIso.eq_comp_inv] at h
  have heq : ((𝒰.gluedCover.toGlueData.ι i ≫ 𝒰.fromGlued).base) x = (𝒰.map i).base x := by
    rw [𝒰.ι_fromGlued i]
    rfl
  haveI := TopCat.Presheaf.isIso_stalkSpecializes_of_eq X.presheaf
    (specializes_of_eq heq.symm) heq
  rw [h]
  infer_instance

theorem base_map_eq (j : 𝒰.J) :
    ⇑(𝒰.map j).base = ⇑𝒰.fromGlued.base ∘ ⇑(𝒰.gluedCover.toGlueData.ι j).base := by
  rw [← 𝒰.ι_fromGlued j]
  rfl

theorem preimage_image_fromGlued (j : 𝒰.J) (U : Set 𝒰.gluedCover.toGlueData.glued) :
    ⇑(𝒰.map j).base ⁻¹' (⇑𝒰.fromGlued.base '' U) = ⇑(𝒰.gluedCover.toGlueData.ι j).base ⁻¹' U := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, 𝒰.base_map_eq j, Function.comp_apply]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [𝒰.fromGlued_injective hzy] at hz
  · exact fun hy ↦ ⟨_, hy, rfl⟩

theorem isOpenMap_fromGlued : IsOpenMap ⇑𝒰.fromGlued.base := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨⇑𝒰.fromGlued.base '' U ∩ Set.range ⇑(𝒰.map (𝒰.idx x)).base,
    Set.inter_subset_left, ?_, hx, 𝒰.covers x⟩
  rw [← Set.image_preimage_eq_inter_range, 𝒰.preimage_image_fromGlued]
  exact (𝒰.isOpen (𝒰.idx x)).base_open.isOpenMap _
    ((𝒰.gluedCover.isOpen_iff U).1 hU (𝒰.idx x))

theorem isOpenEmbedding_fromGlued : IsOpenEmbedding ⇑𝒰.fromGlued.base :=
  .of_continuous_injective_isOpenMap 𝒰.fromGlued.base.hom.continuous 𝒰.fromGlued_injective
    𝒰.isOpenMap_fromGlued

instance epi_base_fromGlued : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  exact ⟨(𝒰.gluedCover.toGlueData.ι (𝒰.idx x)).base y,
    (congrFun (𝒰.base_map_eq (𝒰.idx x)).symm y).trans hy⟩

instance isOpenImmersion_fromGlued : IsOpenImmersion 𝒰.fromGlued :=
  IsOpenImmersion.of_stalk_iso _ 𝒰.isOpenEmbedding_fromGlued

instance isIso_fromGlued : IsIso 𝒰.fromGlued :=
  IsOpenImmersion.to_iso _

/-- **Given an open cover of `X` and a morphism out of each member of the cover which agree on
the overlaps, they glue to a morphism out of `X`.** -/
noncomputable def glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) :
    X ⟶ Y := by
  refine inv 𝒰.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i ↦ f i
  rintro ⟨i, j⟩
  change pullback.fst _ _ ≫ f _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ f _
  rw [pullbackSymmetry_hom_comp_fst]
  exact hf i j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) (x : 𝒰.J) :
    𝒰.map x ≫ 𝒰.glueMorphisms f hf = f x := by
  rw [glueMorphisms, ← 𝒰.ι_fromGlued x, Category.assoc, IsIso.hom_inv_id_assoc]
  exact Multicoequalizer.π_desc _ _ _ _ _

theorem hom_ext {Y : LocallyRingedSpace.{u}} (f₁ f₂ : X ⟶ Y)
    (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi 𝒰.fromGlued]
  refine Multicoequalizer.hom_ext _ _ _ fun x ↦ ?_
  change 𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued ≫ f₁ =
    𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued ≫ f₂
  rw [𝒰.ι_fromGlued_assoc, 𝒰.ι_fromGlued_assoc]
  exact h x

/-- **The glued morphism is the unique one restricting to the given ones on the cover.** -/
theorem existsUnique_glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) :
    ∃! φ : X ⟶ Y, ∀ j, 𝒰.map j ≫ φ = f j :=
  ⟨𝒰.glueMorphisms f hf, 𝒰.ι_glueMorphisms f hf, fun _ hφ ↦
    𝒰.hom_ext _ _ fun j ↦ (hφ j).trans (𝒰.ι_glueMorphisms f hf j).symm⟩

/-! ### The members of a cover as open subspaces

An `OpenCover`'s members are arbitrary locally ringed spaces mapping into `X` by open immersions,
which is what a `GlueData` produces; the constructions that consume a cover ; notably
`ComplexAnalytic.AnalyticSpace.ofOpens` ; take a family of *opens* of `X` and restrict. The three
declarations below are the dictionary: the image of a member as an open subset, the fact that
those images cover, and the isomorphism between a member and the restriction to its image.

The isomorphism is `IsOpenImmersion.isoOfRangeEq` and the range equality is `range_ofRestrict`,
so nothing here is a computation; what it buys is that a property or a structure known on the
members can be transported to the restrictions, where the cover-indexed API lives.
-/

/-- **The image of the `j`-th member of an open cover, as an open subset of `X`.** -/
def opensRange (j : 𝒰.J) : Opens X :=
  ⟨Set.range (𝒰.map j).base, (𝒰.isOpen j).base_open.isOpen_range⟩

@[simp]
lemma coe_opensRange (j : 𝒰.J) : (𝒰.opensRange j : Set X) = Set.range (𝒰.map j).base :=
  rfl

/-- **The images of the members of an open cover cover `X`**, which is `OpenCover.covers` in the
form the cover-indexed API asks for. -/
lemma iSup_opensRange : ⨆ j, 𝒰.opensRange j = ⊤ :=
  Opens.ext <| Set.eq_univ_of_forall fun x ↦ by
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨𝒰.idx x, 𝒰.covers x⟩

/-- **A member of an open cover is the open subspace of `X` on its image.**

Both `𝒰.map j` and `X.ofRestrict (𝒰.opensRange j).isOpenEmbedding` are open immersions with the
same image ; by `range_ofRestrict`, and for the second one that is a definitional unfolding of
`opensRange` ; so `IsOpenImmersion.isoOfRangeEq` identifies their sources. -/
noncomputable def isoRestrict (j : 𝒰.J) :
    X.restrict (𝒰.opensRange j).isOpenEmbedding ≅ 𝒰.obj j :=
  IsOpenImmersion.isoOfRangeEq _ _ (X.range_ofRestrict (𝒰.opensRange j))

@[reassoc (attr := simp)]
lemma isoRestrict_hom_fac (j : 𝒰.J) :
    (𝒰.isoRestrict j).hom ≫ 𝒰.map j = X.ofRestrict (𝒰.opensRange j).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **An algebra structure on a member of the cover, carried to the open subspace of `X` on its
image.** This is `comapAlgMap` along `isoRestrict`, and it is what puts a family of structures
given on abstract members into the indexing `glueAlgMapRestrict` consumes. -/
noncomputable def restrictAlgMap {R : Type*} [NonAssocSemiring R] (j : 𝒰.J)
    (α : R →+* (𝒰.obj j).presheaf.obj (op ⊤)) :
    R →+* (X.restrict (𝒰.opensRange j).isOpenEmbedding).presheaf.obj (op ⊤) :=
  comapAlgMap (𝒰.isoRestrict j).hom α

/-- **If the structure on a member is pulled back from one on `X`, carrying it to the open
subspace gives the restriction of that structure.**

This is what makes the gluing of `ComplexAnalytic.AnalyticSpace.ofOpenCover` checkable: it turns
a family that came from an ambient structure back into the family of its restrictions, on which
compatibility is `isCompatible_map_le_top` and the gluing is `glueSection_map_le_top`. The proof
is `isoRestrict_hom_fac` read through `comapAlgMap_comp`; nothing is computed. -/
lemma restrictAlgMap_comapAlgMap {R : Type*} [NonAssocSemiring R] (j : 𝒰.J)
    (γ : R →+* X.presheaf.obj (op ⊤)) :
    𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) = X.resAlgMap γ (𝒰.opensRange j) := by
  rw [restrictAlgMap, ← comapAlgMap_comp, isoRestrict_hom_fac, comapAlgMap_ofRestrict]

/-- **A family of structures pulled back from one on `X` is compatible on the overlaps**, so it
satisfies the hypothesis of `glueAlgMapRestrict` with nothing to check.

Every member of the carried family is a restriction of the single global section `γ c`, by
`restrictAlgMap_comapAlgMap`, and `isCompatible_map_le_top` is exactly that case. This is the
hypothesis-discharging half of `glueAlgMapRestrict_comapAlgMap` below, and it is
stated separately because a caller of `ComplexAnalytic.AnalyticSpace.ofOpenCover` needs it before
it can name the space the theorem is about. -/
theorem isCompatible_restrictAlgMap_comapAlgMap {R : Type*} [NonAssocSemiring R]
    (γ : R →+* X.presheaf.obj (op ⊤)) (c : R) :
    TopCat.Presheaf.IsCompatible X.presheaf
      (fun j ↦ (𝒰.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) c := by
  have key : (fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) c) =
      fun j ↦ (X.presheaf.map (homOfLE (le_top :
        (𝒰.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op).hom (γ c) :=
    funext fun j ↦ congrArg (fun m : R →+* _ ↦ m c) (𝒰.restrictAlgMap_comapAlgMap j γ)
  rw [key]
  exact isCompatible_map_le_top _

/-- **Gluing the family a global structure induces on the members of a cover returns that
structure**: the round trip, in the `OpenCover` indexing.

`glueSection_map_le_top` is the same statement for a single section and is what this reduces to;
the content is `restrictAlgMap_comapAlgMap`, which says the carried family *is* the family of
restrictions. It is what identifies the output of `ComplexAnalytic.AnalyticSpace.ofOpenCover` on
a cover of a space that already carries a structure ; and note that it makes no reference to the
members being restrictions, which is the point of the whole section. -/
theorem glueAlgMapRestrict_comapAlgMap {R : Type*} [CommRing R]
    (γ : R →+* X.presheaf.obj (op ⊤)) :
    glueAlgMapRestrict 𝒰.iSup_opensRange
        (fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ))
        (𝒰.isCompatible_restrictAlgMap_comapAlgMap γ) = γ :=
  RingHom.ext fun c ↦
    glueSection_eq ((iSup_isOpenEmbedding_obj_top _).trans 𝒰.iSup_opensRange) _
      (𝒰.isCompatible_restrictAlgMap_comapAlgMap γ c) (γ c)
      fun j ↦ (congrArg (fun m : R →+* _ ↦ m c) (𝒰.restrictAlgMap_comapAlgMap j γ)).symm

/-- **An algebra structure on `X` is determined by its pullbacks to the members of an open cover
of `X`.**

The separatedness half of the sheaf condition, in the form the cover-indexed API states things
in, and the reason a condition on the *global* sections of `X` can be checked on the members: a
member of an `AlgebraicGeometry.LocallyRingedSpace.OpenCover` carries no map back to `X`, so
there is nothing to transport a structure forward along, and "agreeing on the cover" has to be
turned into "equal" by a gluing rather than by a computation.

There is no new argument here.
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap` says each side is
what gluing its own family of restrictions returns, and the two families are equal by hypothesis;
the compatibility proofs the two `glueAlgMapRestrict` calls carry are propositions and need no
comparison. -/
theorem comapAlgMap_ext {R : Type*} [CommRing R] {γ γ' : R →+* X.presheaf.obj (op ⊤)}
    (h : ∀ j, comapAlgMap (𝒰.map j) γ = comapAlgMap (𝒰.map j) γ') : γ = γ' := by
  rw [← 𝒰.glueAlgMapRestrict_comapAlgMap γ, ← 𝒰.glueAlgMapRestrict_comapAlgMap γ']
  congr 1
  exact funext fun j ↦ congrArg (𝒰.restrictAlgMap j) (h j)

end OpenCover

/-- **A family of open subsets covering `X` is an open cover of `X`** by the corresponding open
subspaces. This is the form in which an open cover of a locally ringed space usually arises: the
members are restrictions of `X` itself rather than abstract spaces mapping into it. -/
noncomputable def openCoverOfOpens {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) : OpenCover X where
  J := ι
  obj i := X.restrict (U i).isOpenEmbedding
  map _ := X.ofRestrict _
  idx x := (hU x).choose
  covers x := ⟨⟨x, (hU x).choose_spec⟩, rfl⟩
  isOpen _ := inferInstance

@[simp]
lemma openCoverOfOpens_obj {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (openCoverOfOpens U hU).obj i = X.restrict (U i).isOpenEmbedding :=
  rfl

@[simp]
lemma openCoverOfOpens_map {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (openCoverOfOpens U hU).map i = X.ofRestrict (U i).isOpenEmbedding :=
  rfl

/-- **The members of a glue data are an open cover of the glued space.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` and
`…GlueData.ι_jointly_surjective` are Mathlib's; this packages them, and it is the form in which
a gluing is fed to anything that consumes a cover. It is the converse direction to
`OpenCover.gluedCover`, and unlike `OpenCover.isIso_fromGlued` it costs nothing.

The index of a point is *chosen*, so this definition is noncomputable and non-canonical in the
same way `openCoverOfOpens` is; nothing downstream depends on which index is picked. -/
noncomputable def GlueData.openCover (D : GlueData.{u}) : OpenCover D.toGlueData.glued where
  J := D.J
  obj := D.U
  map := D.toGlueData.ι
  idx x := (D.ι_jointly_surjective x).choose
  covers x := (D.ι_jointly_surjective x).choose_spec

section GlueOverOpens

/-- **Morphisms out of the members of a cover of `X` by open subsets, agreeing on the pairwise
intersections, glue** ; and the glued morphism is unique.

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms` says the same thing
with the compatibility phrased on the *categorical pullback* of the two inclusions. That object
is opaque: to discharge the hypothesis one has to know what its points are, and the tools that
would discharge it ; anything of the form "two morphisms out of this space with the same
so-and-so are equal" ; are statements about spaces one can name. **So the hypothesis there is
not checkable by the machinery meant to check it**, and paying that cost once, here, is what this
spelling is for. `AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap` is
what paying it directly looks like: its members are the members of a glue data rather than opens
of one space, so the identification it uses is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback`, the chosen overlap `V (i, j)` as the
categorical pullback, and it builds the pullback equation out of that and hands it to
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms` itself.

Here the compatibility is an equation of morphisms out of `X.restrict (U i ⊓ U j)`, which is an
open subspace of `X` and therefore something the caller already understands ; for a complex
analytic space, `ComplexAnalytic.AnalyticSpace.restrict` makes it an analytic space and
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` applies to it.

The identification is
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`, which packages exactly that: the
pullback of two open immersions has as image the intersection of their images
(`…IsOpenImmersion.range_pullback_to_base_of_left`), so `…IsOpenImmersion.isoOfRangeEq` identifies
it with `X|(U ⊓ V)`. -/
theorem existsUnique_glueMorphisms_of_opens {X Y : LocallyRingedSpace.{u}} {ι : Type u}
    (U : ι → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
    (hf : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    ∃! φ : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ φ = f i := by
  refine (openCoverOfOpens U hU).existsUnique_glueMorphisms f fun i j ↦ ?_
  change pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
      (X.ofRestrict (U j).isOpenEmbedding) ≫ f i =
    pullback.snd (X.ofRestrict (U i).isOpenEmbedding)
      (X.ofRestrict (U j).isOpenEmbedding) ≫ f j
  rw [← cancel_epi (X.restrictInfIsoPullback (U i) (U j)).hom, ← Category.assoc, ← Category.assoc,
    restrictInfIsoPullback_hom_fst, restrictInfIsoPullback_hom_snd]
  exact hf i j

end GlueOverOpens

section GlueDataPrime

/-- **The morphisms of the glue data `CategoryTheory.GlueData.ofGlueData'` builds are open
immersions as soon as the ones it was given are.**

`CategoryTheory.GlueData'` asks for the overlaps only when `i ≠ j` and discharges `f_id`, `t_id`
and the degenerate branches of `t'`, which is a large part of the obligations of a glue data and
exactly the part that is bookkeeping. What it does not carry is
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `f_open` field, and the morphism that field is
checked against is `CategoryTheory.GlueData'.f'`, a `dif` on `i = j`. This says the `dif` costs
nothing: on the diagonal `f'` is an `eqToHom`, hence an isomorphism, hence an open immersion; off
it, it is an `eqToHom` followed by the given morphism.

**Worth stating because `CategoryTheory.GlueData.ofGlueData'` has no call sites in Mathlib at
all at `v4.32.0`** ; `grep -rn "ofGlueData'" Mathlib/` returns the definition and one
cross-reference in a docstring and nothing else, which `Other/Oka/CategoryTheory/GlueData.lean` records
with the rev and the control ; so Mathlib supplies no projection or `simp` lemma for any of its
fields, and a caller with only Mathlib to read has no way to know in advance which of them are
cheap to use. **This is not the sentence that file carries**: *no call sites* is about uses and
*no projection lemmas* is about statements, and here the first gives the second rather than
repeating it. **The version and the pointer were both absent until 2026-09-21**, when taxis #2118
swept the family; the claim is unchanged. This one is, and the route out of here does not ask about
the rest: `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` and hence
`ComplexAnalytic.AnalyticSpace.ofGlueData` read only `U`, `ι` and `glued`. A caller that does ask
about `t` has a dependent `dite` to unfold, and `CategoryTheory.GlueData.ofGlueData'_t_of_ne` is
that unfolding off the diagonal, `CategoryTheory.GlueData.ofGlueData'_t_self` on it. -/
theorem isOpenImmersion_f' (D : CategoryTheory.GlueData' LocallyRingedSpace.{u})
    (h : ∀ i j hij, IsOpenImmersion (D.f i j hij)) (i j : D.J) :
    IsOpenImmersion (D.f' i j) := by
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with hij
  · infer_instance
  · haveI := h i j hij
    infer_instance

end GlueDataPrime

namespace GlueData

variable (D : GlueData.{u})

/-- **The overlap `V (i, j)` of a glue data is the categorical pullback of the two inclusions
into the gluing.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.vPullbackConeIsLimit` says the square is
cartesian; this is the comparison isomorphism it produces, named because the two factorisations
below are what any computation with it uses, and because a bare `IsLimit` cannot be composed
with. -/
noncomputable def vIsoPullback (i j : D.J) :
    D.V (i, j) ≅ Limits.pullback (D.toGlueData.ι i) (D.toGlueData.ι j) :=
  Limits.IsLimit.conePointUniqueUpToIso (D.vPullbackConeIsLimit i j) (Limits.limit.isLimit _)

@[reassoc (attr := simp)]
theorem vIsoPullback_hom_fst (i j : D.J) :
    (D.vIsoPullback i j).hom ≫ Limits.pullback.fst _ _ = D.f i j :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _ Limits.WalkingCospan.left

@[reassoc (attr := simp)]
theorem vIsoPullback_hom_snd (i j : D.J) :
    (D.vIsoPullback i j).hom ≫ Limits.pullback.snd _ _ = D.t i j ≫ D.f j i :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _ Limits.WalkingCospan.right

/-! ### Gluing a morphism out of a gluing

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` asks for agreement over the
*categorical pullback* of two members' inclusions. **A glue datum contains no such object**: what
it carries is the chosen overlap `V (i, j)` with its inclusion `f i j` and its transition `t i j`,
and a caller who built the datum states compatibility in those terms and in no other. So the cover
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` produces cannot be fed a morphism
without this transport, and until it existed there was no morphism out of a gluing in this
repository ; not even the identity.

`…GlueData.vIsoPullback` is the whole of the argument, and it was already here: it identifies
`V (i, j)` with the pullback, and its two factorisation lemmas say the comparison carries the
pullback's projections to `f i j` and to `t i j ≫ f j i`. So cancelling the isomorphism turns the
pullback condition into the glue datum's own.

The four rewrites below are the ones `…GlueData.isCompatible_restrictAlgMap` already performs
inline, in its `have hpb`, for a family of morphisms to `Spec R`. **That `have` is left alone
deliberately**: it is stated at `toSpecOfAlgMap` of the members and its `h` hypothesis is an
equation between `comapAlgMap`s rather than between composites, so calling the lemma would need
the algebra hypothesis converted first and would replace four rewrites with a conversion of the
same length. The duplication is one line; the coupling would not be.
-/

/-- **A family of morphisms out of the members which agrees over the glue data's own overlaps
satisfies the pullback condition `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`
asks for.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback` and its two factorisations, with the
isomorphism cancelled.

**Stated with `D.toGlueData.ι`, not with `D.openCover.map`.** The two are the same term ;
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`'s `map` field *is* `ι` ; but an index
written `i : D.J` will not elaborate against `D.openCover.obj i`, which wants a `D.openCover.J`,
and the resulting error is an application type mismatch several layers in. The consumer applies
this at the cover anyway, where the two spellings are definitionally equal. -/
theorem pullback_condition_of_comm {Y : LocallyRingedSpace.{u}} (f : ∀ j, D.U j ⟶ Y)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) (i j : D.J) :
    Limits.pullback.fst (D.toGlueData.ι i) (D.toGlueData.ι j) ≫ f i =
      Limits.pullback.snd (D.toGlueData.ι i) (D.toGlueData.ι j) ≫ f j := by
  rw [← cancel_epi (D.vIsoPullback i j).hom, ← Category.assoc, ← Category.assoc,
    vIsoPullback_hom_fst, vIsoPullback_hom_snd, Category.assoc, h i j]

/-- **A morphism out of a gluing, glued from morphisms out of the members.**

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` at
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`, with its hypothesis supplied by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm`. The content is the
hypothesis and not the definition: this is the form in which a caller who built a glue datum can
actually map out of it. -/
noncomputable def glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, D.U j ⟶ Y)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) :
    D.toGlueData.glued ⟶ Y :=
  D.openCover.glueMorphisms f (pullback_condition_of_comm D f h)

/-- **It restricts to the given morphism on each member.** -/
@[reassoc (attr := simp)]
theorem ι_glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, D.U j ⟶ Y)
    (h : ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j) (j : D.J) :
    D.toGlueData.ι j ≫ glueMorphisms D f h = f j :=
  D.openCover.ι_glueMorphisms f _ j

/-- **And it is the only one that does**, which with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms` is the universal property in the
form a caller uses it. `AlgebraicGeometry.LocallyRingedSpace.OpenCover.hom_ext` at the glue data's
cover; the two together are `…OpenCover.existsUnique_glueMorphisms` unbundled. -/
theorem hom_ext {Y : LocallyRingedSpace.{u}} (f g : D.toGlueData.glued ⟶ Y)
    (h : ∀ j, D.toGlueData.ι j ≫ f = D.toGlueData.ι j ≫ g) : f = g :=
  D.openCover.hom_ext f g h

/-- **Algebra structures on the members of a glue data which agree on the overlaps are compatible
on the gluing.**

This is what `ComplexAnalytic.AnalyticSpace.ofGlueData` needs and what nothing supplied.
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap`
discharges the same conclusion, but its hypothesis is that the family is pulled back from a
structure on the ambient space ; which is exactly what a glue data does not have, since the
gluing is what is being built. The hypothesis here is instead the geometric one: on each overlap
the two structures it inherits, from the `i`-th member and from the `j`-th, agree.

**`R` is in the universe of the spaces, and that is forced**: the proof goes through `Spec R`,
and `Spec` of a ring in universe `v` is a locally ringed space in universe `v`. A caller whose
ring lives lower ; `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, at `R = ℂ` ; passes
`ULift.{u} R`, which changes nothing, since `α` composed with `ULift.ringEquiv` has the same
values and the two families of sections are equal on the nose.

**The proof is the `Γ`-`Spec` adjunction and the gluing of morphisms, and no section is ever
computed.** An algebra structure on a member is a morphism to `Spec R`
(`AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap`); the hypothesis says those morphisms
agree on the overlaps, which are the categorical pullbacks by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback`; so they glue, by
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms`, to a morphism out of
the gluing; and *that* is a structure on the gluing, whose restrictions are the given ones. The
family is therefore pulled back from an ambient structure after all ; one had to be built ; and
the lemma the glue data could not use applies. -/
theorem isCompatible_restrictAlgMap {R : Type u} [CommRing R]
    (α : ∀ j, R →+* (D.U j).presheaf.obj (op ⊤))
    (h : ∀ i j, comapAlgMap (D.f i j) (α i) = comapAlgMap (D.t i j ≫ D.f j i) (α j)) (c : R) :
    TopCat.Presheaf.IsCompatible D.toGlueData.glued.presheaf
      (fun j ↦ (D.openCover.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ D.openCover.restrictAlgMap j (α j) c := by
  have hpb : ∀ i j : D.J, Limits.pullback.fst (D.toGlueData.ι i) (D.toGlueData.ι j) ≫
      toSpecOfAlgMap (D.U i) (α i) =
      Limits.pullback.snd (D.toGlueData.ι i) (D.toGlueData.ι j) ≫ toSpecOfAlgMap (D.U j) (α j) := by
    intro i j
    rw [← cancel_epi (D.vIsoPullback i j).hom, ← Category.assoc, ← Category.assoc,
      vIsoPullback_hom_fst, vIsoPullback_hom_snd, comp_toSpecOfAlgMap, comp_toSpecOfAlgMap, h i j]
  obtain ⟨g, hg, -⟩ :=
    D.openCover.existsUnique_glueMorphisms (fun j ↦ toSpecOfAlgMap (D.U j) (α j)) hpb
  obtain ⟨γ, hγ⟩ := exists_toSpecOfAlgMap_eq D.toGlueData.glued g
  have hαγ : ∀ j : D.J, α j = comapAlgMap (D.toGlueData.ι j) γ := fun j ↦
    toSpecOfAlgMap_injective (D.U j) <| by
      rw [← comp_toSpecOfAlgMap (D.toGlueData.ι j) γ, hγ]
      exact (hg j).symm
  simp_rw [hαγ]
  exact D.openCover.isCompatible_restrictAlgMap_comapAlgMap γ c

/-! ### Extensionality -/

/-- **Two glue data of locally ringed spaces with the same underlying `CategoryTheory.GlueData`
are equal.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData` extends `CategoryTheory.GlueData` by `f_open`
alone, which is a `Prop`, so the extension carries no data and the two `cases` below leave a goal
that proof irrelevance closes.

What it is for is the step after a congruence: a caller who has proved two
`CategoryTheory.GlueData`s equal ; because the data they were built from agree ; still has to get
past a field whose type mentions the thing just proved equal, and `subst` cannot fire until the
structure is taken apart. Doing that once here is what keeps it out of every such proof. -/
theorem ext_of_toGlueData {D₁ D₂ : GlueData.{u}} (h : D₁.toGlueData = D₂.toGlueData) :
    D₁ = D₂ := by
  obtain ⟨d₁, o₁⟩ := D₁
  obtain ⟨d₂, o₂⟩ := D₂
  dsimp only at h
  subst h
  rfl

end GlueData

end AlgebraicGeometry.LocallyRingedSpace

end
