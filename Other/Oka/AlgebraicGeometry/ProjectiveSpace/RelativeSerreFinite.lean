/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreSections
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.GlobalSectionsFinite

/-!
# Finiteness of direct images along projective morphisms

In the setting of `Other/Oka/AlgebraicGeometry/ProjectiveSpace/RelativeSerreMorphism.lean` (`π : Y' ⟶ Y`
and `j : Y' ⟶ ℙₒ(n; K)` with `(π, j) : Y' ⟶ Y ×_K ℙₒ(n; K)` a closed immersion, `Y` locally
noetherian), let `G` be coherent on `Y'` and `V ⊆ Y` an affine open with ring `A`. Then
`Γ(V, π_* G(m)) = Γ(π⁻¹ V, G(m))` is a finite `A`-module for `m ≫ 0`
(`ProjectiveSpace.exists_module_finite_pushforward_twistAlong`).

The sections of `G(m)` over `π⁻¹ V` are, `A`-linearly, the global sections of `F(m)` on
`ℙₒ(n; A)`, where `F` is the restriction to `ℙₒ(n; A)` of the pushforward of `G` to
`Y ×_K ℙₒ(n; K)` (`ProjectiveSpace.sectionsLinearEquiv`), and these are finite for `m ≫ 0` by
`ProjectiveSpace.exists_module_finite_twist`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable {n : ℕ} {K : Type u} [CommRing K] {Y Y' : Scheme.{u}} (y : Y ⟶ Spec (.of K))
  {V : Y.Opens} (hV : IsAffineOpen V)

/-- `appLE` along equal morphisms. -/
lemma appLE_eq_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g) {U : Z.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

lemma affineChart_image_top :
    affineChart n y hV ''ᵁ ⊤ = pullback.fst y (toSpec n K) ⁻¹ᵁ V := by
  rw [Scheme.Hom.image_top_eq_opensRange, opensRange_affineChart]

lemma appIso_inv_globalRingHom (a : Γ(Y, V)) :
    ((affineChart n y hV).appIso ⊤).inv (globalRingHom n Γ(Y, V) a) =
      (pullback.fst y (toSpec n K)).appLE V _ (affineChart_image_top y hV).le a := by
  apply (ConcreteCategory.bijective_of_isIso ((affineChart n y hV).appIso ⊤).hom).1
  rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (affineChart_fst y hV) _
      (by rw [Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self]; exact le_top),
    Scheme.Hom.comp_appLE, ConcreteCategory.comp_apply, hV.fromSpec_app_self_apply,
    globalRingHom_apply]
  erw [← ConcreteCategory.comp_apply ((Spec Γ(Y, V)).presheaf.map _), Scheme.Hom.map_appLE]
  rfl

variable (ι : Y' ⟶ pullback y (toSpec n K)) (G : Y'.Modules) (m : ℤ)

/-- The twist of the pushforward of `G` to `Y ×_K ℙₒ(n; K)`, restricted to `ℙₒ(n; Γ(Y, V))`. -/
noncomputable def restrictTwistIso :
    (Scheme.Modules.twist ((pushforward ι).obj G)
      ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K)))).restrict (affineChart n y hV) ≅
      Scheme.Modules.twist (((pushforward ι).obj G).restrict (affineChart n y hV))
        (cocycle n Γ(Y, V) ^ m) :=
  restrictTwistComapIso _ _ _ ≪≫ twistComapCompIso _ _ _ _ ≪≫
    twistComapIsoOfEq (affineChart_snd y hV) _ _ ≪≫
    twistIsoOfIsPullback (map (structureRingHom y hV)) (fun i ↦ (map_preimage_U _ i).symm)
      (cocycle n K ^ m) (cocycle n Γ(Y, V) ^ m) ((cocycle_isPullback _).zpow m) _

/-- Sections of isomorphic sheaves of modules. -/
noncomputable def isoAppAddEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃+ Γ(N, U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  left_inv x := by rw [← Hom.comp_app_apply, e.hom_inv_id, Hom.id_app_apply]
  right_inv x := by rw [← Hom.comp_app_apply, e.inv_hom_id, Hom.id_app_apply]
  map_add' := map_add _

/-- Restriction along an equality of opens. -/
noncomputable def resAddEquiv {X : Scheme.{u}} (M : X.Modules) {U U' : X.Opens} (h : U = U') :
    Γ(M, U) ≃+ Γ(M, U') where
  toFun x := TopCat.Presheaf.restrictOpen x U' h.ge
  invFun x := TopCat.Presheaf.restrictOpen x U h.le
  left_inv x := by simp only [mres_res, mres_self]
  right_inv x := by simp only [mres_res, mres_self]
  map_add' := mres_add M _

/-- The first step of `sectionsAddEquiv`. -/
noncomputable def sectionsAddEquiv₁ :
    Γ(twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m, ⊤) ≃+
      Γ(Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K))),
          pullback.fst y (toSpec n K) ⁻¹ᵁ V) :=
  (isoAppAddEquiv (restrictTwistIso y hV ι G m).symm ⊤).trans
    (resAddEquiv (Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K))))
      (affineChart_image_top y hV))

/-- The second step of `sectionsAddEquiv`. -/
noncomputable def sectionsAddEquiv₂ :
    Γ(Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K))),
          pullback.fst y (toSpec n K) ⁻¹ᵁ V) ≃+
      Γ((pushforward (ι ≫ pullback.fst y (toSpec n K))).obj
        (twistAlong (ι ≫ pullback.snd y (toSpec n K)) G m), V) :=
  (isoAppAddEquiv (pushforwardTwistComapIso ι _ G).symm _).trans
    (isoAppAddEquiv (twistComapCompIso ι _ _ G) (ι ⁻¹ᵁ (pullback.fst y (toSpec n K) ⁻¹ᵁ V)))

lemma sectionsAddEquiv₁_apply
    (x : Γ(twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m, ⊤)) :
    sectionsAddEquiv₁ y hV ι G m x = TopCat.Presheaf.restrictOpen
      (F := (Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K)))).presheaf)
      ((restrictTwistIso y hV ι G m).inv.app ⊤ x) _ (affineChart_image_top y hV).ge :=
  rfl

lemma sectionsAddEquiv₁_smul (b : Γ(ℙₒ(n; Γ(Y, V)), ⊤))
    (x : Γ(twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m, ⊤)) :
    sectionsAddEquiv₁ y hV ι G m (b • x) =
      TopCat.Presheaf.restrictOpen (((affineChart n y hV).appIso ⊤).inv b) _
        (affineChart_image_top y hV).ge • sectionsAddEquiv₁ y hV ι G m x := by
  rw [sectionsAddEquiv₁_apply, sectionsAddEquiv₁_apply, Hom.app_smul]
  exact mres_smul _ _ _ _

lemma sectionsAddEquiv₂_apply
    (x : Γ(Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K))),
          pullback.fst y (toSpec n K) ⁻¹ᵁ V)) :
    sectionsAddEquiv₂ y ι G m x = (twistComapCompIso ι _ _ G).hom.app
      (ι ⁻¹ᵁ (pullback.fst y (toSpec n K) ⁻¹ᵁ V))
      ((pushforwardTwistComapIso ι _ G).inv.app _ x) :=
  rfl

lemma sectionsAddEquiv₂_smul (a : Γ(Y, V))
    (x : Γ(Scheme.Modules.twist ((pushforward ι).obj G)
        ((cocycle n K ^ m).comap (pullback.snd y (toSpec n K))),
          pullback.fst y (toSpec n K) ⁻¹ᵁ V)) :
    sectionsAddEquiv₂ y ι G m ((pullback.fst y (toSpec n K)).app V a • x) =
      a • sectionsAddEquiv₂ y ι G m x := by
  rw [sectionsAddEquiv₂_apply, sectionsAddEquiv₂_apply, Hom.app_smul]
  exact Hom.app_smul _ _ _

lemma restrictOpen_appIso_inv_globalRingHom (a : Γ(Y, V)) :
    TopCat.Presheaf.restrictOpen (((affineChart n y hV).appIso ⊤).inv
      (globalRingHom n Γ(Y, V) a)) _ (affineChart_image_top y hV).ge =
      (pullback.fst y (toSpec n K)).app V a := by
  rw [appIso_inv_globalRingHom, ← Scheme.Hom.appLE_eq_app]
  exact congr($(Scheme.Hom.appLE_map _ _ (homOfLE (affineChart_image_top y hV).ge).op) a)

/-- The sections of `G(m)` over `π⁻¹ V`, as a `Γ(Y, V)`-module, are the global sections of the
twist of the restriction to `ℙₒ(n; Γ(Y, V))` of the pushforward of `G`. -/
noncomputable def sectionsLinearEquiv :
    letI := sectionsModule (twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m)
    Γ(twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m, ⊤) ≃ₗ[Γ(Y, V)]
      Γ((pushforward (ι ≫ pullback.fst y (toSpec n K))).obj
        (twistAlong (ι ≫ pullback.snd y (toSpec n K)) G m), V) :=
  letI := sectionsModule (twist (((pushforward ι).obj G).restrict (affineChart n y hV)) m)
  { (sectionsAddEquiv₁ y hV ι G m).trans (sectionsAddEquiv₂ y ι G m) with
    map_smul' a x := by
      change sectionsAddEquiv₂ y ι G m (sectionsAddEquiv₁ y hV ι G m
        (globalRingHom n Γ(Y, V) a • x)) = a • sectionsAddEquiv₂ y ι G m
          (sectionsAddEquiv₁ y hV ι G m x)
      rw [sectionsAddEquiv₁_smul, restrictOpen_appIso_inv_globalRingHom,
        sectionsAddEquiv₂_smul] }

variable (π : Y' ⟶ Y) (j : Y' ⟶ ℙₒ(n; K)) (w : π ≫ y = j ≫ toSpec n K)
  [IsClosedImmersion (pullback.lift π j w)]

include w hV in
/-- **Finiteness of direct images.** For a coherent `G` on `Y'` and an affine open `V ⊆ Y`, the
sections `Γ(V, π_* G(m)) = Γ(π⁻¹ V, G(m))` form a finite `Γ(Y, V)`-module for `m ≫ 0`. -/
theorem exists_module_finite_pushforward_twistAlong [IsLocallyNoetherian Y] (G : Y'.Modules)
    [G.IsCoherent] : ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      Module.Finite Γ(Y, V) Γ((pushforward π).obj (twistAlong j G m), V) := by
  haveI : IsLocallyNoetherian (pullback y (toSpec n K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y (toSpec n K))
  haveI := isCoherent_pushforward (pullback.lift π j w) G
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsLocallyNoetherian ℙₒ(n; Γ(Y, V)) :=
    LocallyOfFiniteType.isLocallyNoetherian (toSpec n _)
  haveI := isCoherent_restrict (affineChart n y hV) ((pushforward (pullback.lift π j w)).obj G)
  obtain ⟨m₀, h⟩ := exists_module_finite_twist
    (((pushforward (pullback.lift π j w)).obj G).restrict (affineChart n y hV))
  refine ⟨m₀, fun m hm ↦ ?_⟩
  letI := sectionsModule
    (twist (((pushforward (pullback.lift π j w)).obj G).restrict (affineChart n y hV)) m)
  haveI := h m hm
  have := Module.Finite.equiv (sectionsLinearEquiv y hV (pullback.lift π j w) G m)
  rwa [pullback.lift_fst, pullback.lift_snd] at this

end AlgebraicGeometry.ProjectiveSpace

end
