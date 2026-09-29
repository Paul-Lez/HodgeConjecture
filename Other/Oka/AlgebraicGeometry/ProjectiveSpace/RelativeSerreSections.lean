/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreMorphism
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentLocalization

/-!
# Sections of direct images along projective morphisms

In the setting of `Other/Oka/AlgebraicGeometry/ProjectiveSpace/RelativeSerreMorphism.lean` (`π : Y' ⟶ Y`
and `j : Y' ⟶ ℙₒ(n; K)` with `(π, j) : Y' ⟶ Y ×_K ℙₒ(n; K)` a closed immersion), the preimage of an
affine open `V ⊆ Y` is covered by the `n + 1` affine opens `π⁻¹ V ∩ j⁻¹ Uᵢ`, whose pairwise
intersections are affine (`ProjectiveSpace.affineCoverPreimage`). Consequently, for every
quasi-coherent `G` on `Y'` and every `m`:

* `π_* G(m)` is quasi-coherent (`ProjectiveSpace.isQuasicoherent_pushforward_twistAlong`);
* over an affine open `V` with ring `A` and `g ∈ A`, the sections of `π_* G(m)` over `D(g)` are
  the localisation `M_g` of `M = Γ(π⁻¹ V, G(m))`, in elementwise form
  (`ProjectiveSpace.exists_restrictOpen_eq_pow_smul_pushforward_twistAlong`,
  `ProjectiveSpace.exists_pow_smul_eq_zero_pushforward_twistAlong`).
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable {n : ℕ} {K : Type u} [CommRing K] {Y Y' : Scheme.{u}}

/-- Twists of quasi-coherent sheaves by cocycles on open covers are quasi-coherent. -/
instance isQuasicoherent_twistAlong (j : Y' ⟶ ℙₒ(n; K)) (G : Y'.Modules) [G.IsQuasicoherent]
    (m : ℤ) : (twistAlong j G m).IsQuasicoherent :=
  isQuasicoherent_of_restrictIso (fun i : ULift.{u} (Fin (n + 1)) ↦ j ⁻¹ᵁ U n K i.down)
    (by
      rw [eq_top_iff]
      intro x _
      have hx : j x ∈ (⊤ : ℙₒ(n; K).Opens) := trivial
      rw [← iSup_U n K] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i⟩, hi⟩)
    _ (fun _ ↦ G) fun i ↦ Scheme.Modules.twistRestrictIso G _ i.down

variable (y : Y ⟶ Spec (.of K)) (π : Y' ⟶ Y) (j : Y' ⟶ ℙₒ(n; K)) (w : π ≫ y = j ≫ toSpec n K)
  [IsClosedImmersion (pullback.lift π j w)] {V : Y.Opens} (hV : IsAffineOpen V)

/-- The cover of `π⁻¹ V` by the preimages of the standard charts of `ℙₒ(n; Γ(Y, V))`. -/
noncomputable def affineCoverPreimage (i : ULift.{u} (Fin (n + 1))) : Y'.Opens :=
  pullback.lift π j w ⁻¹ᵁ (affineChart n y hV ''ᵁ U n Γ(Y, V) i.down)

omit [IsClosedImmersion (pullback.lift π j w)] in
lemma iSup_affineCoverPreimage : ⨆ i, affineCoverPreimage y π j w hV i = π ⁻¹ᵁ V := by
  have h : ⨆ i : ULift.{u} (Fin (n + 1)), U n Γ(Y, V) i.down = ⊤ :=
    le_antisymm le_top ((iSup_U n _).ge.trans (iSup_le fun i ↦ le_iSup_of_le ⟨i⟩ le_rfl))
  simp only [affineCoverPreimage, ← Scheme.Hom.preimage_iSup, ← Scheme.Hom.image_iSup, h,
    Scheme.Hom.image_top_eq_opensRange, opensRange_affineChart, ← Scheme.Hom.comp_preimage,
    pullback.lift_fst]

lemma isAffineOpen_affineCoverPreimage (i : ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (affineCoverPreimage y π j w hV i) :=
  ((isAffineOpen_U i.down).image_of_isOpenImmersion _).preimage _

lemma isAffineOpen_affineCoverPreimage_inf (i k : ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (affineCoverPreimage y π j w hV i ⊓ affineCoverPreimage y π j w hV k) := by
  have h : affineChart n y hV ''ᵁ (U n Γ(Y, V) i.down ⊓ U n Γ(Y, V) k.down) =
      affineChart n y hV ''ᵁ U n Γ(Y, V) i.down ⊓ affineChart n y hV ''ᵁ U n Γ(Y, V) k.down := by
    conv_lhs => rw [← Scheme.Hom.preimage_image_eq (affineChart n y hV) (U n Γ(Y, V) k.down)]
    exact Scheme.Hom.image_inf_preimage _ _ _
  simp only [affineCoverPreimage, ← Scheme.Hom.preimage_inf, ← h]
  exact ((isAffineOpen_U_inf _ _).image_of_isOpenImmersion _).preimage _

include y w in
/-- The pushforward `π_* G(m)` of the twist of a quasi-coherent sheaf is quasi-coherent. -/
theorem isQuasicoherent_pushforward_twistAlong (G : Y'.Modules) [G.IsQuasicoherent] (m : ℤ) :
    ((pushforward π).obj (twistAlong j G m)).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_cover π _ fun _ hV ↦ ⟨_, inferInstance,
    affineCoverPreimage y π j w hV, iSup_affineCoverPreimage y π j w hV,
    isAffineOpen_affineCoverPreimage y π j w hV,
    isAffineOpen_affineCoverPreimage_inf y π j w hV⟩

include y w hV in
/-- Sections of `π_* G(m)` over a basic open `D(g)` of an affine open `V` extend to `V` after
multiplication by a power of `g`. -/
theorem exists_restrictOpen_eq_pow_smul_pushforward_twistAlong (G : Y'.Modules)
    [G.IsQuasicoherent] (m : ℤ) (g : Γ(Y, V))
    (s : Γ((pushforward π).obj (twistAlong j G m), Y.basicOpen g)) :
    ∃ (k : ℕ) (t : Γ((pushforward π).obj (twistAlong j G m), V)),
      TopCat.Presheaf.restrictOpen t (Y.basicOpen g) (Y.basicOpen_le g) =
        TopCat.Presheaf.restrictOpen g (Y.basicOpen g) (Y.basicOpen_le g) ^ k • s :=
  exists_restrictOpen_eq_pow_smul_pushforward π _ _ (iSup_affineCoverPreimage y π j w hV)
    (isAffineOpen_affineCoverPreimage y π j w hV)
    (isAffineOpen_affineCoverPreimage_inf y π j w hV) g s

include y w hV in
/-- A section of `π_* G(m)` over an affine open `V` vanishing on `D(g)` is killed by a power
of `g`. -/
theorem exists_pow_smul_eq_zero_pushforward_twistAlong (G : Y'.Modules) [G.IsQuasicoherent]
    (m : ℤ) (g : Γ(Y, V)) (t : Γ((pushforward π).obj (twistAlong j G m), V))
    (ht : TopCat.Presheaf.restrictOpen t (Y.basicOpen g) (Y.basicOpen_le g) = 0) :
    ∃ k : ℕ, g ^ k • t = 0 :=
  exists_pow_smul_eq_zero_pushforward π _ _ (iSup_affineCoverPreimage y π j w hV)
    (isAffineOpen_affineCoverPreimage y π j w hV) g t ht

end AlgebraicGeometry.ProjectiveSpace

end
