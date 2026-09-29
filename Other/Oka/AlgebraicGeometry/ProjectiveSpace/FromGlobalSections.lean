/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Morphisms to `Proj` from global sections, in charts

For a ring map `f : A →+* Γ(X, ⊤)` from a graded ring such that the irrelevant ideal generates
the unit ideal, and a homogeneous `t` of positive degree, the morphism
`Proj.fromOfGlobalSections 𝒜 f : X ⟶ Proj 𝒜` restricted to `D(f t) ⟶ D₊(t) ≅ Spec A_(t)` is
`D(f t) ⟶ Spec Γ(X, ⊤)[1 / f t] ⟶ Spec A_(t)`, the second map being induced by
`a / tⁿ ↦ f a / (f t)ⁿ` (`AlgebraicGeometry.Proj.fromOfGlobalSections_resLE_basicOpenIsoSpec_hom`).
-/

@[expose] public section

open CategoryTheory Limits HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- The canonical morphism `D(s) ⟶ Spec Γ(X, ⊤)[1/s]` for a global section `s`. -/
noncomputable def Scheme.basicOpenToSpecAway (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    (X.basicOpen s).toScheme ⟶ Spec (.of (Localization.Away s)) :=
  (X.isoOfEq (X.toSpecΓ_preimage_basicOpen s)).inv ≫ X.toSpecΓ ∣_ _ ≫
    (basicOpenIsoSpecAway s).hom

/-- `D(s) ⟶ Spec Γ(X, ⊤)[1 / s] ⟶ Spec Γ(X, ⊤)` is the inclusion followed by `X.toSpecΓ`. -/
@[reassoc (attr := simp)]
lemma Scheme.basicOpenToSpecAway_SpecMap (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    X.basicOpenToSpecAway s ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) =
      (X.basicOpen s).ι ≫ X.toSpecΓ := by
  simp [basicOpenToSpecAway, Scheme.isoOfEq_inv]

namespace Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- The ring map `A_(t) → Γ(X, ⊤)[1 / f t]`, `a / tⁿ ↦ f a / (f t)ⁿ`. -/
noncomputable def awayToLocalization (t : A) : Away 𝒜 t →+* Localization.Away (f t) :=
  (IsLocalization.map (M := .powers t) (S := Localization.Away t) (T := .powers (f t)) _ f (by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- `awayToLocalization` sends `a / tⁿ` to `f a / (f t)ⁿ`. -/
lemma awayToLocalization_mk {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayToLocalization 𝒜 f t (Away.mk 𝒜 hd n a ha) =
      IsLocalization.mk' _ (f a) (⟨f t ^ n, n, rfl⟩ : Submonoid.powers (f t)) := by
  simp [awayToLocalization, Localization.mk_eq_mk', IsLocalization.map_mk']

variable (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

/-- On the chart `D₊(t)`, `Proj.fromOfGlobalSections` is induced by `awayToLocalization`. -/
lemma fromOfGlobalSections_resLE_basicOpenIsoSpec_hom {t : A} {d : ℕ} (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) :
    (fromOfGlobalSections 𝒜 f hf).resLE _ _
      (fromOfGlobalSections_preimage_basicOpen 𝒜 f hf h0d hd).ge ≫
        (basicOpenIsoSpec 𝒜 t hd h0d).hom =
      X.basicOpenToSpecAway (f t) ≫
        Spec.map (CommRingCat.ofHom (awayToLocalization 𝒜 f t)) := by
  rw [fromOfGlobalSections_resLE 𝒜 f hf h0d hd]
  simp [toBasicOpenOfGlobalSections, Scheme.basicOpenToSpecAway, awayToLocalization]

end Proj

end AlgebraicGeometry

end
