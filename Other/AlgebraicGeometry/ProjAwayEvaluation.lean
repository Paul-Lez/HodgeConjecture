/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.PointEvaluationApp
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Values of regular functions at points factoring through an affine open

A morphism `Spec ℂ ⟶ Y` that factors as `Spec χ` followed by `IsAffineOpen.fromSpec` of an affine
open `W` reads a regular function on `W` simply by applying `χ`
(`ΓSpecIso_appLE_top_of_fromSpec`).  On `Proj 𝒜` the relevant affine opens are the basic opens
`D₊(f)`, whose global sections are `HomogeneousLocalization.Away 𝒜 f` through
`Proj.awayToSection`; `Proj.awayι` factors through `fromSpec` in exactly this way
(`awayι_eq_SpecMap_fromSpec`), so a point given by a ring map out of `A⁰_f` evaluates a
homogeneous fraction by applying that ring map (`ΓSpecIso_appLE_top_awayToSection`).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Values through an affine open.**  If a `ℂ`-point of `Y` factors through the affine open `W`
as `Spec χ ≫ fromSpec`, then reading a regular function on `W` at that point is applying `χ`. -/
theorem ΓSpecIso_appLE_top_of_fromSpec {Y : Scheme} {W : Y.Opens} (hW : IsAffineOpen W)
    (χ : Γ(Y, W) ⟶ ↧ℂ) (p : Spec ↧ℂ ⟶ Y) (hp : p = Spec.map χ ≫ hW.fromSpec)
    (h : (⊤ : (Spec ↧ℂ).Opens) ≤ p ⁻¹ᵁ W) (u : Γ(Y, W)) :
    (Scheme.ΓSpecIso ↧ℂ).hom (p.appLE W ⊤ h u) = χ.hom u := by
  revert h
  rw [hp]
  intro h
  have key : (Spec.map χ ≫ hW.fromSpec).appLE W ⊤ h ≫ (Scheme.ΓSpecIso ↧ℂ).hom = χ := by
    rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      Scheme.Hom.map_appLE_assoc]
    show (Scheme.ΓSpecIso Γ(Y, W)).inv ≫
        (Spec.map χ).appLE ⊤ (Spec.map χ ⁻¹ᵁ ⊤) le_rfl ≫ (Scheme.ΓSpecIso ↧ℂ).hom = χ
    rw [Scheme.Hom.appLE_eq_app, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) u

/-- The preimage of `W` under a point factoring through `fromSpec W` is everything. -/
theorem top_le_preimage_of_fromSpec {Y : Scheme} {W : Y.Opens} (hW : IsAffineOpen W)
    (χ : Γ(Y, W) ⟶ ↧ℂ) (p : Spec ↧ℂ ⟶ Y) (hp : p = Spec.map χ ≫ hW.fromSpec) :
    (⊤ : (Spec ↧ℂ).Opens) ≤ p ⁻¹ᵁ W := by
  rw [hp]
  intro x _
  show hW.fromSpec.base ((Spec.map χ).base x) ∈ W
  have h2 : (Spec.map χ).base x ∈ hW.fromSpec ⁻¹ᵁ W := by
    rw [hW.fromSpec_preimage_self]; trivial
  exact h2

namespace Proj

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

include f_deg hm in
/-- On a basic open of a positive-degree homogeneous element, `awayToSection` is an
isomorphism. -/
theorem isIso_awayToSection : IsIso (Proj.awayToSection 𝒜 f) := by
  rw [← Proj.basicOpenIsoAway_hom 𝒜 f f_deg hm]
  infer_instance

set_option maxHeartbeats 800000 in
/-- **`awayι` factors through `fromSpec`.** -/
theorem awayι_eq_SpecMap_fromSpec :
    Proj.awayι 𝒜 f f_deg hm =
      Spec.map (haveI := isIso_awayToSection 𝒜 f f_deg hm; inv (Proj.awayToSection 𝒜 f)) ≫
        (Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm).fromSpec := by
  haveI := isIso_awayToSection 𝒜 f f_deg hm
  haveI : IsIso (Spec.map (Proj.awayToSection 𝒜 f)) := inferInstance
  rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm,
    ← IsAffineOpen.toSpecΓ_fromSpec (Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm),
    ← Category.assoc]
  congr 1
  rw [Spec.map_inv]
  refine (IsIso.inv_eq_of_inv_hom_id ?_).symm
  rw [Category.assoc, ← Proj.basicOpenToSpec, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm,
    Iso.inv_hom_id]

end Proj

namespace Proj

variable {A : Type} {σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

set_option maxHeartbeats 800000 in
include f_deg hm in
/-- **Values of homogeneous fractions at a chart point.**  If a `ℂ`-point of `Proj 𝒜` is given by
a ring map `ψ` out of `A⁰_f`, then the regular function on `D₊(f)` attached to `t : A⁰_f` takes
the value `ψ t` there. -/
theorem ΓSpecIso_appLE_top_awayToSection
    (ψ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 f) ⟶ ↧ℂ)
    (p : Spec ↧ℂ ⟶ Proj 𝒜) (hp : p = Spec.map ψ ≫ Proj.awayι 𝒜 f f_deg hm)
    (h : (⊤ : (Spec ↧ℂ).Opens) ≤ p ⁻¹ᵁ Proj.basicOpen 𝒜 f)
    (t : HomogeneousLocalization.Away 𝒜 f) :
    (Scheme.ΓSpecIso ↧ℂ).hom
        (p.appLE (Proj.basicOpen 𝒜 f) ⊤ h (Proj.awayToSection 𝒜 f t)) = ψ.hom t := by
  haveI := isIso_awayToSection 𝒜 f f_deg hm
  have hp' : p = Spec.map (inv (Proj.awayToSection 𝒜 f) ≫ ψ) ≫
      (Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm).fromSpec := by
    rw [hp, awayι_eq_SpecMap_fromSpec, Spec.map_comp, Category.assoc]
  rw [ΓSpecIso_appLE_top_of_fromSpec (Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm) _ p hp' h]
  rw [← CommRingCat.comp_apply, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

include f_deg hm in
/-- A point factoring through `awayι` lies over `D₊(f)`. -/
theorem top_le_preimage_basicOpen_of_awayι
    (ψ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 f) ⟶ ↧ℂ)
    (p : Spec ↧ℂ ⟶ Proj 𝒜) (hp : p = Spec.map ψ ≫ Proj.awayι 𝒜 f f_deg hm) :
    (⊤ : (Spec ↧ℂ).Opens) ≤ p ⁻¹ᵁ Proj.basicOpen 𝒜 f := by
  rw [hp]
  intro x _
  show (Proj.awayι 𝒜 f f_deg hm).base ((Spec.map ψ).base x) ∈ Proj.basicOpen 𝒜 f
  rw [← Proj.opensRange_awayι 𝒜 f f_deg hm]
  exact ⟨_, rfl⟩

end Proj

end AlgebraicGeometry
