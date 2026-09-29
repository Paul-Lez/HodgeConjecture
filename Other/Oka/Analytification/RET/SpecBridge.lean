/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.Functor
public import Other.Oka.Analytification.SchemeAffine

/-!
# Affine schemes of finite type over `ℂ` and presented algebras

This file compares the analytification functor on schemes locally of finite type over `ℂ`
(`ComplexAnalytic.analytification`) on affine schemes with the analytification of presented
algebras (`ComplexAnalytic.analytificationMap`).

## Main definitions

- `ComplexAnalytic.SchemeLFTℂ.specHom`: `Spec` of a ring map compatible with the structure maps,
  as a morphism of schemes locally of finite type over `ℂ`.
- `ComplexAnalytic.specPresHom`: the morphism `Spec (ℂ[x] ⧸ (g)) ⟶ Spec (ℂ[y] ⧸ (g'))` of a
  `ComplexAnalytic.PresHom`.

## Main results

- `ComplexAnalytic.analytification_map_specPresHom`: up to the identifications
  `ComplexAnalytic.analytificationSpecIso`, the analytification of `Spec` of a `ℂ`-algebra map of
  presented algebras is `ComplexAnalytic.analytificationMap`.
- `ComplexAnalytic.SchemeLFTℂ.exists_iso_specPresentation`: every affine scheme of finite type
  over `ℂ` is isomorphic to `Spec (ℂ[x] ⧸ (g))` for a presentation `g`.
- `ComplexAnalytic.exists_specPresHom_eq`: every morphism `Spec (ℂ[x] ⧸ (g)) ⟶ Spec (ℂ[y] ⧸ (g'))`
  over `ℂ` is `Spec` of a `ℂ`-algebra map.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

/-! ### `Spec` of ring maps over `ℂ` -/

section SpecHom

variable {R S T : CommRingCat.{u}} {φR : CommRingCat.of (ULift.{u} ℂ) ⟶ R}
  {φS : CommRingCat.of (ULift.{u} ℂ) ⟶ S} {φT : CommRingCat.of (ULift.{u} ℂ) ⟶ T}
  (hR : φR.hom.FiniteType) (hS : φS.hom.FiniteType) (hT : φT.hom.FiniteType)

/-- `Spec ρ : Spec S ⟶ Spec R` for a ring map `ρ : R ⟶ S` compatible with the structure maps from
`ℂ`, as a morphism of schemes locally of finite type over `ℂ`. -/
def SchemeLFTℂ.specHom (ρ : R ⟶ S) (h : φR ≫ ρ = φS) :
    SchemeLFTℂ.spec φS hS ⟶ SchemeLFTℂ.spec φR hR :=
  ObjectProperty.homMk (Over.homMk (Spec.map ρ) (by
    change Spec.map ρ ≫ Spec.map φR = Spec.map φS
    rw [← Spec.map_comp, h]))

@[simp]
lemma SchemeLFTℂ.specHom_hom_left (ρ : R ⟶ S) (h : φR ≫ ρ = φS) :
    (SchemeLFTℂ.specHom hR hS ρ h).hom.left = Spec.map ρ :=
  rfl

/-- `Spec` of a composite is the composite of the `Spec`s, in the opposite order. -/
lemma SchemeLFTℂ.specHom_comp_specHom (ρ : R ⟶ S) (σ : S ⟶ T) (τ : R ⟶ T)
    (h : φR ≫ ρ = φS) (h' : φS ≫ σ = φT) (h'' : φR ≫ τ = φT) (hτ : ρ ≫ σ = τ) :
    SchemeLFTℂ.specHom hS hT σ h' ≫ SchemeLFTℂ.specHom hR hS ρ h =
      SchemeLFTℂ.specHom hR hT τ h'' := by
  ext1
  exact Over.OverMorphism.ext (by
    change Spec.map σ ≫ Spec.map ρ = Spec.map τ
    rw [← Spec.map_comp, hτ])

/-- `Spec` of a ring isomorphism is an isomorphism. -/
instance SchemeLFTℂ.isIso_specHom (ρ : R ⟶ S) [IsIso ρ] (h : φR ≫ ρ = φS) :
    IsIso (SchemeLFTℂ.specHom hR hS ρ h) := by
  haveI : IsIso ((locallyOfFiniteTypeℂ.ι ⋙ Over.forget _).map
      (SchemeLFTℂ.specHom hR hS ρ h)) :=
    (inferInstance : IsIso (Spec.map ρ))
  exact isIso_of_reflects_iso _ (locallyOfFiniteTypeℂ.ι ⋙ Over.forget _)

end SpecHom

/-! ### `Spec` of maps of presented algebras -/

section Presented

variable {n k n' k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}

/-- A `ℂ`-algebra map of presented algebras commutes with the structure maps from `ULift ℂ`. -/
lemma uliftAlgMap_comp_presHom (ψ : PresHom.{u} g g') :
    CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g')) ≫
        CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g)) := by
  ext1
  change ψ.toRingHom.comp ((presentedAlgebraMap.{u} g').comp _) =
    (presentedAlgebraMap.{u} g).comp _
  rw [← RingHom.comp_assoc, ψ.commutes]

/-- **`Spec` of a `ℂ`-algebra map of presented algebras**, as a morphism
`Spec (ℂ[x] ⧸ (g)) ⟶ Spec (ℂ[y] ⧸ (g'))` of schemes locally of finite type over `ℂ`. It runs in
the same direction as `ComplexAnalytic.analytificationMap`. -/
def specPresHom (ψ : PresHom.{u} g g') :
    SchemeLFTℂ.specPresentation g ⟶ SchemeLFTℂ.specPresentation g' :=
  SchemeLFTℂ.specHom _ _ (CommRingCat.ofHom ψ.toRingHom) (uliftAlgMap_comp_presHom ψ)

@[simp]
lemma specPresHom_hom_left (ψ : PresHom.{u} g g') :
    (specPresHom ψ).hom.left = Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
  rfl

/-- The comparison morphisms `X^an ⟶ Spec (ℂ[x] ⧸ (g))` intertwine
`ComplexAnalytic.analytificationMap` and `Spec`. -/
theorem analytificationToSpecOver_naturality (ψ : PresHom.{u} g g') :
    toOverSpec.map (analytificationMap.{u} ψ) ≫ analytificationToSpecOver g' =
      analytificationToSpecOver g ≫ schemeToOverSpec.map (specPresHom ψ).hom := by
  ext1
  rw [map_comp_analytificationToSpecOver_left]
  change _ = analytificationToSpec g ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψ.toRingHom)
  rw [analytificationToSpec, Category.assoc, ← Spec.locallyRingedSpaceMap_comp,
    LocallyRingedSpace.toSpecOfAlgMap]
  congr 2
  ext1
  exact Γ_map_analytificationMap_comp_quotientToGlobal ψ

/-- **The analytification of `Spec` of a `ℂ`-algebra map of presented algebras is
`ComplexAnalytic.analytificationMap`**, through the identifications
`ComplexAnalytic.analytificationSpecIso`. -/
theorem analytification_map_specPresHom (ψ : PresHom.{u} g g') :
    analytification.map (specPresHom ψ) ≫ (analytificationSpecIso g').hom =
      (analytificationSpecIso g).hom ≫ analytificationMap.{u} ψ := by
  refine (isAnalytification_analytificationToSpec g').hom_ext ?_
  rw [Functor.map_comp, Category.assoc, analytificationSpecIso_hom_comp]
  refine (analytificationπ_naturality _).trans ?_
  rw [Functor.map_comp, Category.assoc, analytificationToSpecOver_naturality]
  exact (congrArg (· ≫ _) (analytificationSpecIso_hom_comp g).symm).trans (Category.assoc _ _ _)

/-- The analytification of `Spec` of a `ℂ`-algebra map of presented algebras, conjugated to
`ComplexAnalytic.analytificationMap`. -/
theorem analytification_map_specPresHom_eq (ψ : PresHom.{u} g g') :
    analytification.map (specPresHom ψ) =
      (analytificationSpecIso g).hom ≫ analytificationMap.{u} ψ ≫
        (analytificationSpecIso g').inv := by
  rw [← Category.assoc, ← analytification_map_specPresHom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Every morphism `Spec (ℂ[x] ⧸ (g)) ⟶ Spec (ℂ[y] ⧸ (g'))` over `ℂ` is `Spec` of a `ℂ`-algebra
map**, since `Spec` is fully faithful. -/
theorem exists_specPresHom_eq
    (φ : SchemeLFTℂ.specPresentation g ⟶ SchemeLFTℂ.specPresentation g') :
    ∃ ψ : PresHom.{u} g g', specPresHom ψ = φ := by
  set ρ := Spec.preimage φ.hom.left with hρdef
  have hρ : Spec.map ρ = φ.hom.left := Spec.map_preimage _
  have hc : CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g')) ≫ ρ =
      CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} g)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ]
    exact Over.w φ.hom
  refine ⟨⟨ρ.hom, ?_⟩, ?_⟩
  · ext c
    exact congrArg (fun f ↦ f.hom (ULift.up c)) hc
  · ext1
    exact Over.OverMorphism.ext hρ

end Presented

/-! ### Affine schemes of finite type -/

/-- **Every affine scheme of finite type over `ℂ` is `Spec (ℂ[x] ⧸ (g))`** for some presentation
`g`, as a scheme over `ℂ`. -/
theorem SchemeLFTℂ.exists_iso_specPresentation (T : SchemeLFTℂ.{u}) [IsAffine T.obj.left] :
    ∃ (n k : ℕ) (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ),
      Nonempty (SchemeLFTℂ.specPresentation g ≅ T) := by
  set ψ : CommRingCat.of (ULift.{u} ℂ) ⟶ Γ(T.obj.left, ⊤) :=
    Spec.preimage (T.obj.left.isoSpec.inv ≫ T.obj.hom) with hψdef
  have hψ : Spec.map ψ = T.obj.left.isoSpec.inv ≫ T.obj.hom := Spec.map_preimage _
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    haveI : LocallyOfFiniteType T.obj.hom := T.property
    infer_instance
  letI : Algebra ℂ Γ(T.obj.left, ⊤) := (ψ.hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(T.obj.left, ⊤) := by
    change (ψ.hom.comp ULift.ringEquiv.symm.toRingHom).FiniteType
    exact hft.comp (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective)
  obtain ⟨P, ⟨e⟩⟩ := exists_presentation Γ(T.obj.left, ⊤)
  let E : Γ(T.obj.left, ⊤) ≅ CommRingCat.of P.alg := e.symm.toRingEquiv.toCommRingCatIso
  refine ⟨P.n, P.k, P.g, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
    (Over.isoMk (Scheme.Spec.mapIso E.op ≪≫ T.obj.left.isoSpec.symm) ?_)⟩⟩
  change Spec.map E.hom ≫ T.obj.left.isoSpec.inv ≫ T.obj.hom =
    Spec.map (CommRingCat.ofHom (uliftAlgMap.{u} (presentedAlgebraMap.{u} P.g)))
  rw [← hψ, ← Spec.map_comp]
  congr 1
  ext c
  change e.symm (algebraMap ℂ Γ(T.obj.left, ⊤) c.down) = algebraMap ℂ P.alg c.down
  exact e.symm.commutes c.down

end

end ComplexAnalytic

end
