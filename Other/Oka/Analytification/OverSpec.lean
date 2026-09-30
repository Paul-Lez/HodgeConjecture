/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Other.Oka.AnalyticSpace.Basic
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Analytic spaces as locally ringed spaces over `Spec ℂ`

A `ℂ`-algebra structure on a locally ringed space is the same thing as a morphism to `Spec ℂ`
(`AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap`), and a morphism is `ℂ`-linear exactly when
it is a morphism over `Spec ℂ`. So complex analytic spaces map to the category
`Over ComplexAnalytic.specℂ` of locally ringed spaces over `Spec ℂ`, by
`ComplexAnalytic.AnalyticSpace.toOverSpec`.

Everything is universe polymorphic: in universe `u` the base is `Spec (ULift.{u} ℂ)`
(`ComplexAnalytic.specℂ`), and the `ℂ`-algebra structure of an analytic space is read as a
`ULift ℂ`-algebra structure by `ComplexAnalytic.uliftAlgMap`.

The **analytification** of an object `Y` of `Over specℂ` is a value of the partial right adjoint of
that functor: an analytic space `Y^an` together with a morphism `Y^an ⟶ Y` over `Spec ℂ` through
which every morphism from an analytic space factors uniquely. Mathlib's
`CategoryTheory.Functor.partialRightAdjoint` turns this pointwise statement into a functor on the
full subcategory where it holds, so the only thing to prove about a class of objects is that the
functor `Z ↦ (Z ⟶ Y)` is representable on analytic spaces.
`ComplexAnalytic.IsAnalytification` is that condition in the form a construction produces it.

## Main definitions

- `ComplexAnalytic.specℂ`: `Spec ℂ` as a locally ringed space.
- `ComplexAnalytic.AnalyticSpace.toOverSpec`: complex analytic spaces as locally ringed spaces over
  `Spec ℂ`.
- `ComplexAnalytic.IsAnalytification`: a morphism `π : W ⟶ Y` over `Spec ℂ` from an analytic space
  through which every morphism from an analytic space factors uniquely.

## Main results

- `ComplexAnalytic.isCLinearHom_iff_comp_toSpecOfAlgMap`: `ℂ`-linearity is being a morphism over
  `Spec ℂ`.
- `ComplexAnalytic.IsAnalytification.rightAdjointObjIsDefined` and
  `ComplexAnalytic.exists_isAnalytification`: an analytification exists exactly when the partial
  right adjoint of `toOverSpec` is defined.
- `ComplexAnalytic.IsAnalytification.of_iso`: the condition transports along isomorphisms.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- `Spec ℂ`, as a locally ringed space in universe `u`: the spectrum of `ULift.{u} ℂ`. -/
noncomputable abbrev specℂ : LocallyRingedSpace.{u} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of (ULift.{u} ℂ))

/-- A `ℂ`-algebra structure, read as a `ULift ℂ`-algebra structure. -/
abbrev uliftAlgMap {A : Type*} [Semiring A] (α : ℂ →+* A) : ULift.{u} ℂ →+* A :=
  α.comp ULift.ringEquiv.toRingHom

/-- `ℂ`-linearity for the structure maps `α` and `β` is the equation
`comapAlgMap f β = α`. -/
theorem isCLinearHom_iff_comapAlgMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (α : ℂ →+* X.presheaf.obj (op ⊤)) (β : ℂ →+* Y.presheaf.obj (op ⊤)) :
    IsCLinearHom f α β ↔ LocallyRingedSpace.comapAlgMap f β = α :=
  ⟨fun h ↦ RingHom.ext h, fun h c ↦ by rw [← h]; rfl⟩

/-- **`ℂ`-linearity is being a morphism over `Spec ℂ`.** -/
theorem isCLinearHom_iff_comp_toSpecOfAlgMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (α : ℂ →+* X.presheaf.obj (op ⊤)) (β : ℂ →+* Y.presheaf.obj (op ⊤)) :
    IsCLinearHom f α β ↔
      f ≫ Y.toSpecOfAlgMap (uliftAlgMap β) = X.toSpecOfAlgMap (uliftAlgMap α) := by
  rw [isCLinearHom_iff_comapAlgMap, LocallyRingedSpace.comp_toSpecOfAlgMap]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  have := LocallyRingedSpace.toSpecOfAlgMap_injective X h
  ext c
  exact congrArg (fun γ : ULift.{u} ℂ →+* _ ↦ γ (ULift.up c)) this

namespace AnalyticSpace

/-- The structure morphism `Z ⟶ Spec ℂ` of a complex analytic space. -/
noncomputable abbrev toSpecℂ (Z : AnalyticSpace.{u}) : Z.toLocallyRingedSpace ⟶ specℂ :=
  Z.toLocallyRingedSpace.toSpecOfAlgMap (uliftAlgMap Z.algebraMap)

/-- **Complex analytic spaces are locally ringed spaces over `Spec ℂ`**, by their `ℂ`-algebra
structure; a morphism of analytic spaces is a morphism over `Spec ℂ` by its `ℂ`-linearity. -/
noncomputable def toOverSpec : AnalyticSpace.{u} ⥤ Over specℂ where
  obj Z := Over.mk Z.toSpecℂ
  map {Z W} φ := Over.homMk φ.toLRSHom
    ((isCLinearHom_iff_comp_toSpecOfAlgMap _ _ _).1 φ.isCLinear)

@[simp]
lemma toOverSpec_obj_left (Z : AnalyticSpace.{u}) :
    (toOverSpec.obj Z).left = Z.toLocallyRingedSpace := rfl

@[simp]
lemma toOverSpec_obj_hom (Z : AnalyticSpace.{u}) : (toOverSpec.obj Z).hom = Z.toSpecℂ := rfl

@[simp]
lemma toOverSpec_map_left {Z W : AnalyticSpace.{u}} (φ : Z ⟶ W) :
    (toOverSpec.map φ).left = φ.toLRSHom := rfl

instance : toOverSpec.Faithful where
  map_injective {_ _ _ _} h :=
    forgetToLocallyRingedSpace.map_injective (congrArg CommaMorphism.left h)

/-- **`toOverSpec` is full**: a morphism over `Spec ℂ` between analytic spaces is `ℂ`-linear. -/
instance : toOverSpec.Full where
  map_surjective {Z W} f :=
    ⟨⟨f.left, (isCLinearHom_iff_comp_toSpecOfAlgMap _ _ _).2 (Over.w f)⟩, by ext1; rfl⟩

end AnalyticSpace

open AnalyticSpace

/-- **`π : W ⟶ Y` is an analytification of `Y`**: every morphism over `Spec ℂ` from an analytic
space `Z` to `Y` factors uniquely through `π` by a morphism of analytic spaces. -/
def IsAnalytification {Y : Over specℂ} {W : AnalyticSpace.{u}} (π : toOverSpec.obj W ⟶ Y) : Prop :=
  ∀ Z : AnalyticSpace.{u}, Function.Bijective fun φ : Z ⟶ W ↦ toOverSpec.map φ ≫ π

namespace IsAnalytification

variable {Y : Over specℂ} {W : AnalyticSpace.{u}} {π : toOverSpec.obj W ⟶ Y}

/-- The representation of `Z ↦ (Z ⟶ Y)` given by an analytification. -/
noncomputable def representableBy (h : IsAnalytification π) :
    (toOverSpec.op ⋙ yoneda.obj Y).RepresentableBy W where
  homEquiv {Z} := Equiv.ofBijective _ (h Z)
  homEquiv_comp {Z Z'} f φ := by
    simp only [Equiv.ofBijective_apply, Functor.map_comp, Category.assoc]
    rfl

theorem rightAdjointObjIsDefined (h : IsAnalytification π) :
    toOverSpec.rightAdjointObjIsDefined Y :=
  h.representableBy.isRepresentable

/-- The factorisation of a morphism through an analytification. -/
noncomputable def lift (h : IsAnalytification π) {Z : AnalyticSpace.{u}}
    (f : toOverSpec.obj Z ⟶ Y) : Z ⟶ W :=
  (Equiv.ofBijective _ (h Z)).symm f

@[reassoc (attr := simp)]
theorem lift_fac (h : IsAnalytification π) {Z : AnalyticSpace.{u}}
    (f : toOverSpec.obj Z ⟶ Y) : toOverSpec.map (h.lift f) ≫ π = f :=
  (Equiv.ofBijective _ (h Z)).apply_symm_apply f

theorem hom_ext (h : IsAnalytification π) {Z : AnalyticSpace.{u}} {φ ψ : Z ⟶ W}
    (e : toOverSpec.map φ ≫ π = toOverSpec.map ψ ≫ π) : φ = ψ :=
  (h Z).1 e

theorem lift_unique (h : IsAnalytification π) {Z : AnalyticSpace.{u}}
    (f : toOverSpec.obj Z ⟶ Y) (φ : Z ⟶ W) (e : toOverSpec.map φ ≫ π = f) : φ = h.lift f :=
  h.hom_ext (by rw [e, lift_fac])

/-- **Analytifications transport along isomorphisms of the target.** -/
theorem of_iso (h : IsAnalytification π) {Y' : Over specℂ} (e : Y ≅ Y') :
    IsAnalytification (π ≫ e.hom) := by
  intro Z
  have : (fun φ : Z ⟶ W ↦ toOverSpec.map φ ≫ π ≫ e.hom) =
      (fun f ↦ f ≫ e.hom) ∘ fun φ : Z ⟶ W ↦ toOverSpec.map φ ≫ π := rfl
  rw [this]
  exact ((Iso.homCongr (Iso.refl _) e).bijective).comp (h Z)

/-- **Analytifications transport along isomorphisms of the source.** -/
theorem of_iso_source (h : IsAnalytification π) {W' : AnalyticSpace.{u}} (e : W' ≅ W) :
    IsAnalytification (toOverSpec.map e.hom ≫ π) := by
  intro Z
  have : (fun φ : Z ⟶ W' ↦ toOverSpec.map φ ≫ toOverSpec.map e.hom ≫ π) =
      (fun φ : Z ⟶ W ↦ toOverSpec.map φ ≫ π) ∘ fun φ ↦ φ ≫ e.hom := by
    funext φ; simp [Functor.map_comp]
  rw [this]
  exact (h Z).comp ((Iso.homCongr (Iso.refl _) e).bijective)

end IsAnalytification

/-- **An analytification exists wherever the partial right adjoint of `toOverSpec` is defined**:
the representing object and the image of its identity. -/
theorem exists_isAnalytification {Y : Over specℂ} (h : toOverSpec.rightAdjointObjIsDefined Y) :
    ∃ (W : AnalyticSpace.{u}) (π : toOverSpec.obj W ⟶ Y), IsAnalytification π := by
  haveI : (toOverSpec.op ⋙ yoneda.obj Y).IsRepresentable := h
  let R := (toOverSpec.op ⋙ yoneda.obj Y).representableBy
  refine ⟨_, R.homEquiv (𝟙 _), fun Z ↦ ?_⟩
  have : (fun φ : Z ⟶ _ ↦ toOverSpec.map φ ≫ R.homEquiv (𝟙 _)) = R.homEquiv := by
    funext φ
    rw [R.homEquiv_eq φ]
    rfl
  rw [this]
  exact R.homEquiv.bijective

/-- `toOverSpec.rightAdjointObjIsDefined` is closed under isomorphisms. -/
theorem rightAdjointObjIsDefined_of_iso {Y Y' : Over specℂ} (e : Y ≅ Y')
    (h : toOverSpec.rightAdjointObjIsDefined Y) : toOverSpec.rightAdjointObjIsDefined Y' := by
  obtain ⟨W, π, hπ⟩ := exists_isAnalytification h
  exact (hπ.of_iso e).rightAdjointObjIsDefined

end ComplexAnalytic

end
