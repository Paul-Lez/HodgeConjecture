/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Other.Oka.Analytification.RepresentableAffine
public import Other.Oka.Analytification.RepresentableGlue
public import Other.Oka.Geometry.RingedSpace.OpenImmersion

/-!
# The analytification functor on schemes locally of finite type over `ℂ`

For a scheme `X` locally of finite type over `ℂ`, the functor on complex analytic spaces
`Z ↦ Hom_ℂ(Z, X)` ; morphisms of locally ringed spaces over `Spec ℂ` ; is representable. The
representing object is the **analytification** `X^an`, and the universal element is the
comparison morphism `X^an ⟶ X`.

The proof is a dévissage: affine schemes of finite type
(`ComplexAnalytic.rightAdjointObjIsDefined_specOver`, from the universal property of the zero
locus of a presentation), open subspaces (`ComplexAnalytic.IsAnalytification.restrict`), and
gluing along an open cover (`ComplexAnalytic.rightAdjointObjIsDefined_of_iSup_eq_top`). A scheme is
covered by the members of its affine cover, each of which is the spectrum of a `ℂ`-algebra of
finite type.

The functor itself is Mathlib's partial right adjoint of
`ComplexAnalytic.AnalyticSpace.toOverSpec`, restricted along the inclusion of the schemes
locally of finite type.

Everything is universe polymorphic: `ComplexAnalytic.SchemeLFTℂ.{u}` is the category of schemes
in universe `u` locally of finite type over `ComplexAnalytic.Specℂ.{u} = Spec (ULift.{u} ℂ)`, and
the analytification takes values in `AnalyticSpace.{u}`.

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ`: the category of schemes locally of finite type over `ℂ`.
- `ComplexAnalytic.schemePoints`: the functor `X ↦ (Z ↦ Hom_ℂ(Z, X))` from schemes to presheaves
  on complex analytic spaces.
- `ComplexAnalytic.analytification`: the analytification functor `SchemeLFTℂ ⥤ AnalyticSpace`.
- `ComplexAnalytic.analytificationπ`: the comparison morphism `X^an ⟶ X`.

## Main results

- `ComplexAnalytic.rightAdjointObjIsDefined_schemeToOverSpec`: every scheme locally of finite type
  over `ℂ` has an analytification.
- `ComplexAnalytic.isAnalytification_analytificationπ`: every morphism from a complex analytic
  space to `X` over `ℂ` factors uniquely through `X^an ⟶ X`.
- `ComplexAnalytic.analytificationRepresentableBy`: `X^an` represents `schemePoints.obj X`.
- `ComplexAnalytic.analytificationCompYonedaIso`: `analytification ⋙ yoneda ≅ schemePoints`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

/-- `Spec ℂ` as a scheme in universe `u`: the spectrum of `ULift.{u} ℂ`. -/
noncomputable abbrev Specℂ : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℂ))

/-- The property of a scheme over `ℂ` of being locally of finite type. -/
def locallyOfFiniteTypeℂ : ObjectProperty (Over (Specℂ.{u})) :=
  fun X ↦ LocallyOfFiniteType X.hom

/-- **The category of schemes locally of finite type over `ℂ`**, as a full subcategory of the
schemes over `Spec ℂ`. -/
abbrev SchemeLFTℂ : Type (u + 1) := locallyOfFiniteTypeℂ.FullSubcategory

/-- A scheme over `Spec ℂ`, as a locally ringed space over `Spec ℂ`. -/
noncomputable def schemeToOverSpec : Over (Specℂ.{u}) ⥤ Over specℂ :=
  Over.post Scheme.forgetToLocallyRingedSpace

@[simp]
lemma schemeToOverSpec_obj_left (X : Over (Specℂ.{u})) :
    (schemeToOverSpec.obj X).left = X.left.toLocallyRingedSpace := rfl

@[simp]
lemma schemeToOverSpec_obj_hom (X : Over (Specℂ.{u})) :
    (schemeToOverSpec.obj X).hom = X.hom.toLRSHom := rfl

@[simp]
lemma schemeToOverSpec_map_left {X Y : Over (Specℂ.{u})} (f : X ⟶ Y) :
    (schemeToOverSpec.map f).left = f.left.toLRSHom := rfl

/-- **A scheme locally of finite type over `ℂ` has an analytification.** -/
theorem rightAdjointObjIsDefined_schemeToOverSpec (X : Over (Specℂ.{u}))
    (hX : LocallyOfFiniteType X.hom) :
    toOverSpec.rightAdjointObjIsDefined (schemeToOverSpec.obj X) := by
  let 𝒰 := X.left.affineCover
  let Y := schemeToOverSpec.obj X
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion (𝒰.f i).toLRSHom := fun i ↦
    (inferInstance : IsOpenImmersion (𝒰.f i))
  let j : ∀ i, Over.mk ((𝒰.f i).toLRSHom ≫ Y.hom) ⟶ Y := fun i ↦ Over.homMk (𝒰.f i).toLRSHom
  have : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).left := fun i ↦ this i
  refine rightAdjointObjIsDefined_of_iSup_eq_top Y (fun i ↦ opensRangeOver (j i)) ?_ fun i ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact Opens.mem_iSup.2 ⟨i, y, rfl⟩
  · refine rightAdjointObjIsDefined_of_iso (isoOverRestrictOfIsOpenImmersion (j i)) ?_
    -- the member is affine, and its structure morphism is `Spec.map φ` up to `isoSpec`
    let g : Spec Γ(𝒰.X i, ⊤) ⟶ Specℂ.{u} := (𝒰.X i).isoSpec.inv ≫ 𝒰.f i ≫ X.hom
    have hg : LocallyOfFiniteType g := by
      haveI := hX
      dsimp [g]; infer_instance
    obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
    have hφft : φ.hom.FiniteType := by
      rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
      exact hg
    refine rightAdjointObjIsDefined_of_iso ?_ (rightAdjointObjIsDefined_specOver φ hφft)
    refine Over.isoMk (Scheme.forgetToLocallyRingedSpace.mapIso (𝒰.X i).isoSpec.symm) ?_
    change (𝒰.X i).isoSpec.inv.toLRSHom ≫ (𝒰.f i).toLRSHom ≫ X.hom.toLRSHom =
      (Spec.map φ).toLRSHom
    rw [hφ]
    rfl

/-- A scheme locally of finite type over `ℂ`, as an object of the domain of the partial right
adjoint of `toOverSpec`. -/
noncomputable def schemeToPartialRightAdjointSource :
    SchemeLFTℂ ⥤ toOverSpec.PartialRightAdjointSource :=
  ObjectProperty.lift _ (locallyOfFiniteTypeℂ.ι ⋙ schemeToOverSpec)
    fun X ↦ rightAdjointObjIsDefined_schemeToOverSpec X.obj X.property

/-- **The analytification functor** from schemes locally of finite type over `ℂ` to complex
analytic spaces. -/
noncomputable def analytification : SchemeLFTℂ ⥤ AnalyticSpace.{u} :=
  schemeToPartialRightAdjointSource ⋙ toOverSpec.partialRightAdjoint

/-- **The functor of points of a scheme on complex analytic spaces**: `X` goes to the presheaf
`Z ↦ Hom_ℂ(Z, X)` of morphisms of locally ringed spaces over `Spec ℂ`. -/
noncomputable def schemePoints : SchemeLFTℂ ⥤ AnalyticSpace.{u}ᵒᵖ ⥤ Type u :=
  locallyOfFiniteTypeℂ.ι ⋙ schemeToOverSpec ⋙ yoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj toOverSpec.op

@[simp]
lemma schemePoints_obj_obj (X : SchemeLFTℂ) (Z : AnalyticSpace.{u}ᵒᵖ) :
    (schemePoints.obj X).obj Z = (toOverSpec.obj Z.unop ⟶ schemeToOverSpec.obj X.obj) := rfl

/-- **The universal property of the analytification**: morphisms `Z ⟶ X^an` of complex analytic
spaces are morphisms `Z ⟶ X` of locally ringed spaces over `Spec ℂ`. -/
noncomputable def analytificationHomEquiv (Z : AnalyticSpace.{u}) (X : SchemeLFTℂ) :
    (Z ⟶ analytification.obj X) ≃ (toOverSpec.obj Z ⟶ schemeToOverSpec.obj X.obj) :=
  toOverSpec.partialRightAdjointHomEquiv (Y := schemeToPartialRightAdjointSource.obj X)

/-- **The comparison morphism `X^an ⟶ X`.** -/
noncomputable def analytificationπ (X : SchemeLFTℂ) :
    toOverSpec.obj (analytification.obj X) ⟶ schemeToOverSpec.obj X.obj :=
  analytificationHomEquiv _ X (𝟙 _)

lemma analytificationHomEquiv_apply {Z : AnalyticSpace.{u}} {X : SchemeLFTℂ}
    (φ : Z ⟶ analytification.obj X) :
    analytificationHomEquiv Z X φ = toOverSpec.map φ ≫ analytificationπ X := by
  have := toOverSpec.partialRightAdjointHomEquiv_comp
    (Y := schemeToPartialRightAdjointSource.obj X) (𝟙 _) φ
  rw [Category.comp_id] at this
  exact this

/-- **`X^an ⟶ X` is an analytification of `X`**: every morphism over `Spec ℂ` from a complex
analytic space to `X` factors uniquely through it. -/
theorem isAnalytification_analytificationπ (X : SchemeLFTℂ) :
    IsAnalytification (analytificationπ X) := fun Z ↦ by
  have : (fun φ : Z ⟶ analytification.obj X ↦ toOverSpec.map φ ≫ analytificationπ X) =
      analytificationHomEquiv Z X := funext fun φ ↦ (analytificationHomEquiv_apply φ).symm
  rw [this]
  exact (analytificationHomEquiv Z X).bijective

/-- **The comparison morphism is natural.** -/
@[reassoc]
theorem analytificationπ_naturality {X Y : SchemeLFTℂ} (f : X ⟶ Y) :
    toOverSpec.map (analytification.map f) ≫ analytificationπ Y =
      analytificationπ X ≫ schemeToOverSpec.map f.hom := by
  rw [← analytificationHomEquiv_apply]
  exact toOverSpec.partialRightAdjointHomEquiv_map (schemeToPartialRightAdjointSource.map f)

/-- **`X^an` represents the functor `Z ↦ Hom_ℂ(Z, X)`.** -/
noncomputable def analytificationRepresentableBy (X : SchemeLFTℂ) :
    (schemePoints.obj X).RepresentableBy (analytification.obj X) where
  homEquiv {Z} := analytificationHomEquiv Z X
  homEquiv_comp {Z Z'} f φ := by
    refine (analytificationHomEquiv_apply (f ≫ φ)).trans ?_
    change _ = toOverSpec.map f ≫ analytificationHomEquiv Z' X φ
    rw [analytificationHomEquiv_apply, Functor.map_comp, Category.assoc]

/-- **The analytification represents the functor of points**: `analytification ⋙ yoneda` is
isomorphic to `schemePoints`, naturally in the scheme. -/
noncomputable def analytificationCompYonedaIso :
    analytification ⋙ yoneda ≅ schemePoints :=
  NatIso.ofComponents (fun X ↦ (analytificationRepresentableBy X).toIso) fun {X Y} f ↦ by
    ext Z φ
    change analytificationHomEquiv Z.unop Y (φ ≫ analytification.map f) =
      analytificationHomEquiv Z.unop X φ ≫ schemeToOverSpec.map f.hom
    rw [analytificationHomEquiv_apply, analytificationHomEquiv_apply, Functor.map_comp,
      Category.assoc, analytificationπ_naturality, Category.assoc]

end ComplexAnalytic

end
