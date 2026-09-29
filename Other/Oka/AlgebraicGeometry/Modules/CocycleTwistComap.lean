/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwistPushforward

/-!
# Pulling back cocycles along morphisms of schemes

For a morphism of schemes `φ : Y ⟶ X` and a cocycle `c` on a family of opens `U : ι → X.Opens`,
the transition functions `φ^♯ cᵢⱼ` form a cocycle `φ^♯ c` on the family `φ⁻¹ Uᵢ`. We show that
twisting is compatible with this operation.

## Main definitions and results

- `Scheme.Modules.Cocycle.comap`: the pullback `φ^♯ c`; it is a group homomorphism
  (`Cocycle.comapHom`, `Cocycle.comap_zpow`), compatible with composition (`Cocycle.comap_comap`)
  and a pullback in the sense of `Cocycle.IsPullback` (`Cocycle.isPullback_comap`).
- `Scheme.Modules.twistIsoOfIsPullback`, `Scheme.Modules.twistComapIsoOfEq`,
  `Scheme.Modules.twistComapCompIso`: identifications of twists by pullback cocycles.
- `Scheme.Modules.pushforwardTwistComapIso`: `φ_* (N ⊗ L_{φ^♯ c}) ≅ (φ_* N) ⊗ L_c`, natural in `N`
  (`Scheme.Modules.twistFunctorComapPushforwardIso`).
- `Scheme.Modules.restrictTwistComapIso`: `(F ⊗ L_c)|_Y ≅ F|_Y ⊗ L_{e^♯ c}` for an open immersion
  `e : Y ⟶ X`, natural in `F` (`Scheme.Modules.twistFunctorComapRestrictIso`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} {ι : Type} {U : ι → X.Opens}

namespace Cocycle

/-- The **pullback** `φ^♯ c` of a cocycle `c` on `U` along `φ : Y ⟶ X`: the cocycle on the family
`φ⁻¹ Uᵢ` with transition functions `φ^♯ cᵢⱼ`. -/
noncomputable def comap (φ : Y ⟶ X) (c : Cocycle U) : Cocycle (fun i ↦ φ ⁻¹ᵁ U i) where
  g i j := φ.appLE (U i ⊓ U j) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) le_rfl (c.g i j)
  self i := by rw [c.self, map_one]
  mul i j k := by
    simp only [res_appLE]
    have h := congrArg (φ.appLE (U i ⊓ U j ⊓ U k) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j ⊓ φ ⁻¹ᵁ U k) le_rfl)
      (c.mul i j k)
    rwa [map_mul, appLE_res, appLE_res, appLE_res] at h

variable (φ : Y ⟶ X) (c : Cocycle U)

/-- The transition functions of `φ^♯ c` are `φ^♯ cᵢⱼ`. -/
lemma comap_g (i j : ι) :
    (c.comap φ).g i j = φ.appLE (U i ⊓ U j) (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) le_rfl (c.g i j) :=
  rfl

/-- Restrictions of the transition functions of `φ^♯ c`. -/
lemma comap_g_res (i j : ι) (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j) :
    TopCat.Presheaf.restrictOpen ((c.comap φ).g i j) W hW = φ.appLE (U i ⊓ U j) W hW (c.g i j) :=
  res_appLE φ _ _ _

/-- The pullback of the trivial cocycle is trivial. -/
@[simp]
lemma comap_one : (1 : Cocycle U).comap φ = 1 :=
  ext fun _ _ ↦ map_one _

/-- Pullback of cocycles is multiplicative. -/
lemma comap_mul (c d : Cocycle U) : (c * d).comap φ = c.comap φ * d.comap φ :=
  ext fun _ _ ↦ map_mul _ _ _

/-- Pullback of cocycles commutes with inverses. -/
lemma comap_inv : c⁻¹.comap φ = (c.comap φ)⁻¹ :=
  ext fun i j ↦ by
    simp only [comap_g, inv_g]
    exact (appLE_res φ _ _ _).trans (res_appLE φ _ _ _).symm

/-- Pulling back cocycles along `φ` as a group homomorphism. -/
noncomputable def comapHom : Cocycle U →* Cocycle (fun i ↦ φ ⁻¹ᵁ U i) :=
  MonoidHom.mk' (comap φ) (comap_mul φ)

/-- `comapHom φ` is `Cocycle.comap φ`. -/
@[simp]
lemma comapHom_apply : comapHom φ c = c.comap φ :=
  rfl

/-- Pullback of cocycles commutes with integer powers. -/
lemma comap_zpow (m : ℤ) : (c ^ m).comap φ = c.comap φ ^ m :=
  map_zpow (comapHom φ) c m

/-- Pullback of cocycles commutes with natural powers. -/
lemma comap_pow (m : ℕ) : (c ^ m).comap φ = c.comap φ ^ m :=
  map_pow (comapHom φ) c m

/-- `φ^♯ c` is the pullback of `c` along `φ` in the sense of `Cocycle.IsPullback`. -/
lemma isPullback_comap : IsPullback φ id (fun _ ↦ le_rfl) c (c.comap φ) :=
  fun i j W hW ↦ (comap_g_res φ c i j W hW).symm

/-- A cocycle on `φ⁻¹ Uᵢ` which is a pullback of `c` is `φ^♯ c`. -/
lemma IsPullback.eq_comap {d : Cocycle (fun i ↦ φ ⁻¹ᵁ U i)}
    (h : IsPullback φ id (fun _ ↦ le_rfl) c d) : d = c.comap φ :=
  ext fun i j ↦ by
    have := h i j _ le_rfl
    rw [ores_self] at this
    exact this.symm

/-- Pulling back along a composition. -/
lemma comap_comap (ψ : Z ⟶ Y) : (c.comap φ).comap ψ = c.comap (ψ ≫ φ) :=
  ext fun i j ↦ congr($(Scheme.Hom.appLE_comp_appLE ψ φ _ _ _ le_rfl le_rfl) (c.g i j))

end Cocycle

section Twist

/-- Transport of the twist by `φ^♯ c` to a cocycle `d` on a family `U'` with `U' i = φ⁻¹ Uᵢ`
which is a pullback of `c`. -/
noncomputable def twistIsoOfIsPullback (φ : Y ⟶ X) {U' : ι → Y.Opens}
    (hU : ∀ i, U' i = φ ⁻¹ᵁ U i) (c : Cocycle U) (d : Cocycle U')
    (h : Cocycle.IsPullback φ id (fun i ↦ (hU i).le) c d) (F : Y.Modules) :
    twist F (c.comap φ) ≅ twist F d := by
  obtain rfl : U' = fun i ↦ φ ⁻¹ᵁ U i := funext hU
  exact (twistFunctorCongr (Cocycle.IsPullback.eq_comap φ c h).symm).app F

/-- Twists by pullbacks of `c` along equal morphisms are isomorphic. -/
noncomputable def twistComapIsoOfEq {φ φ' : Y ⟶ X} (h : φ = φ') (c : Cocycle U)
    (F : Y.Modules) : twist F (c.comap φ) ≅ twist F (c.comap φ') := by
  subst h
  exact Iso.refl _

/-- The twist by `ψ^♯ φ^♯ c` is the twist by `(ψ ≫ φ)^♯ c`. -/
noncomputable def twistComapCompIso (ψ : Z ⟶ Y) (φ : Y ⟶ X) (c : Cocycle U) (F : Z.Modules) :
    twist F ((c.comap φ).comap ψ) ≅ twist F (c.comap (ψ ≫ φ)) :=
  (twistFunctorCongr (c.comap_comap φ ψ)).app F

end Twist

section Pushforward

variable (φ : Y ⟶ X)

/-- `φ^♯` commutes with restriction. -/
lemma app_ores {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) :
    φ.app W (r |ₒ W) = TopCat.Presheaf.restrictOpen (φ.app V r) (φ ⁻¹ᵁ W) (φ.preimage_mono h) := by
  rw [φ.app_eq_appLE]
  exact appLE_res φ _ _ _

/-- Scalar multiplication by equal sections. -/
lemma smul_congr {M : Y.Modules} {W : Y.Opens} {a b : Γ(Y, W)} (h : a = b)
    (x : Γ(M, W)) :
    a • x = b • x :=
  h ▸ rfl

variable (c : Cocycle U) (N : Y.Modules)

/-- `φ^♯` of a restricted transition function of `c` is the restricted transition function
of `φ^♯ c`. -/
lemma app_ores_g_eq_comap_g (V : X.Opens) (i j : ι) :
    φ.app (V ⊓ (U i ⊓ U j)) (c.g i j |ₒ (V ⊓ (U i ⊓ U j))) =
      ((c.comap φ).g i j |ₒ (φ ⁻¹ᵁ V ⊓ (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j))) := by
  rw [φ.app_eq_appLE, Cocycle.comap_g_res]
  exact appLE_res φ _ _ _

/-- The map `φ_* (N ⊗ L_{φ^♯ c}) ⟶ (φ_* N) ⊗ L_c`, the identity on components. -/
noncomputable def pushforwardTwistComapHom :
    (pushforward φ).obj (twist N (c.comap φ)) ⟶ twist ((pushforward φ).obj N) c :=
  homMk (fun V ↦
    { toFun s := twistMk (F := (pushforward φ).obj N) (V := V) (c := c)
        (fun i ↦ twistComp (V := φ ⁻¹ᵁ V) s i) fun i j ↦
          (twistComp_compat (V := φ ⁻¹ᵁ V) s i j).trans
            (smul_congr (M := N) (app_ores_g_eq_comap_g φ c V i j).symm _)
      map_zero' := rfl
      map_add' _ _ := rfl })
    (fun V r _ ↦ twist_ext fun i ↦
      smul_congr (M := N) (W := φ ⁻¹ᵁ V ⊓ φ ⁻¹ᵁ U i) (app_ores φ inf_le_left r).symm _)
    (fun _ _ _ _ ↦ rfl)

/-- The map `(φ_* N) ⊗ L_c ⟶ φ_* (N ⊗ L_{φ^♯ c})`, the identity on components. -/
noncomputable def pushforwardTwistComapInv :
    twist ((pushforward φ).obj N) c ⟶ (pushforward φ).obj (twist N (c.comap φ)) :=
  homMk (fun V ↦
    { toFun s := twistMk (F := N) (V := φ ⁻¹ᵁ V) (c := c.comap φ)
        (fun i ↦ twistComp s i) fun i j ↦
          (twistComp_compat s i j).trans
            (smul_congr (M := N) (app_ores_g_eq_comap_g φ c V i j) _)
      map_zero' := rfl
      map_add' _ _ := rfl })
    (fun V r _ ↦ twist_ext (V := φ ⁻¹ᵁ V) fun i ↦
      smul_congr (M := N) (W := φ ⁻¹ᵁ V ⊓ φ ⁻¹ᵁ U i) (app_ores φ inf_le_left r) _)
    (fun _ _ _ _ ↦ rfl)

/-- **Twisting commutes with pushforward**: `φ_* (N ⊗ L_{φ^♯ c}) ≅ (φ_* N) ⊗ L_c`, the identity
on components. -/
noncomputable def pushforwardTwistComapIso :
    (pushforward φ).obj (twist N (c.comap φ)) ≅ twist ((pushforward φ).obj N) c :=
  isoMk (pushforwardTwistComapHom φ c N) (pushforwardTwistComapInv φ c N)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- `φ_* (N ⊗ L_{φ^♯ c}) ≅ (φ_* N) ⊗ L_c`, naturally in `N`. -/
noncomputable def twistFunctorComapPushforwardIso :
    twistFunctor (c.comap φ) ⋙ pushforward φ ≅ pushforward φ ⋙ twistFunctor c :=
  NatIso.ofComponents (fun N ↦ pushforwardTwistComapIso φ c N) fun _ ↦
    Hom.ext_apply fun _ _ ↦ rfl

end Pushforward

section Restrict

variable (e : Y ⟶ X) [IsOpenImmersion e]

/-- For an open immersion `e`, `e(W ∩ e⁻¹ V) = e(W) ∩ V`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.image_inf_preimage (W : Y.Opens) (V : X.Opens) :
    e ''ᵁ (W ⊓ e ⁻¹ᵁ V) = e ''ᵁ W ⊓ V :=
  Opens.ext (Set.image_inter_preimage _ _ _)

/-- For an open immersion `e`, `W ≤ e⁻¹ V` implies `e(W) ≤ V`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.image_le_of_le_preimage {W : Y.Opens} {V : X.Opens}
    (h : W ≤ e ⁻¹ᵁ V) : e ''ᵁ W ≤ V :=
  (e.image_mono h).trans (e.image_preimage_le V)

variable (c : Cocycle U) (F : X.Modules)

/-- Transporting the transition functions of `e^♯ c` along `e.appIso` gives the transition
functions of `c`. -/
lemma appIso_inv_comap_g_res (W : Y.Opens) (i j : ι) (hW : W ≤ e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j) :
    (e.appIso W).inv (TopCat.Presheaf.restrictOpen ((c.comap e).g i j) W hW) =
      TopCat.Presheaf.restrictOpen (c.g i j) (e ''ᵁ W) (e.image_le_of_le_preimage hW) := by
  rw [Cocycle.comap_g_res]
  exact Scheme.Hom.appLE_appIso_inv_apply e hW (c.g i j)

/-- `e.appIso` commutes with restriction. -/
lemma appIso_inv_ores {W W' : Y.Opens} (h : W' ≤ W) (r : Γ(Y, W)) :
    (e.appIso W').inv (r |ₒ W') =
      TopCat.Presheaf.restrictOpen ((e.appIso W).inv r) (e ''ᵁ W') (e.image_mono h) :=
  congr($(e.appIso_inv_naturality (homOfLE h).op) r)

variable {c F}

/-- The components of the image of a section of `(F ⊗ L_c)|_Y` in `F|_Y ⊗ L_{e^♯ c}`. -/
noncomputable def restrictTwistComp {W : Y.Opens} (s : Γ(twist F c, e ''ᵁ W)) (i : ι) :
    Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U i)) :=
  TopCat.Presheaf.restrictOpen (twistComp s i) _ (e.image_inf_preimage W (U i)).le

/-- The components `restrictTwistComp` satisfy the cocycle condition for `e^♯ c`. -/
lemma restrictTwistComp_compat {W : Y.Opens} (s : Γ(twist F c, e ''ᵁ W)) (i j : ι) :
    TopCat.Presheaf.restrictOpen (restrictTwistComp e s i)
        (e ''ᵁ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) (e.image_mono (by order)) =
      (e.appIso _).inv ((c.comap e).g i j |ₒ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) •
        TopCat.Presheaf.restrictOpen (restrictTwistComp e s j)
          (e ''ᵁ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) (e.image_mono (by order)) := by
  rw [appIso_inv_comap_g_res]
  simp only [restrictTwistComp, mres_res]
  refine twistComp_compat_res s i j _ (le_inf (e.image_mono inf_le_left) ?_)
  exact e.image_le_of_le_preimage (inf_le_right : _ ≤ e ⁻¹ᵁ (U i ⊓ U j))

/-- `restrictTwistComp` is linear. -/
lemma restrictTwistComp_smul {W : Y.Opens} (r : Γ(Y, W)) (s : Γ(twist F c, e ''ᵁ W)) (i : ι) :
    restrictTwistComp e ((e.appIso W).inv r • s) i =
      (e.appIso _).inv (r |ₒ (W ⊓ e ⁻¹ᵁ U i)) • restrictTwistComp e s i := by
  simp only [restrictTwistComp, twistComp_smul, mres_smul, ores_res]
  rw [appIso_inv_ores e inf_le_left r]

/-- `restrictTwistComp` commutes with restriction. -/
lemma restrictTwistComp_res {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(twist F c, e ''ᵁ W))
    (i : ι) :
    restrictTwistComp e (TopCat.Presheaf.restrictOpen s (e ''ᵁ W') (e.image_mono h)) i =
      TopCat.Presheaf.restrictOpen (restrictTwistComp e s i) (e ''ᵁ (W' ⊓ e ⁻¹ᵁ U i))
        (e.image_mono (by order)) := by
  simp only [restrictTwistComp, twistComp_res, mres_res]

variable (c F) in
/-- The map `(F ⊗ L_c)|_Y ⟶ F|_Y ⊗ L_{e^♯ c}`, restricting components. -/
noncomputable def restrictTwistComapHom :
    (twist F c).restrict e ⟶ twist (F.restrict e) (c.comap e) :=
  homMk (fun W ↦
    { toFun s := twistMk (F := F.restrict e) (c := c.comap e) (V := W)
        (fun i ↦ restrictTwistComp e s i) fun i j ↦ restrictTwistComp_compat e s i j
      map_zero' := twist_ext fun _ ↦ mres_zero _ _
      map_add' _ _ := twist_ext fun _ ↦ mres_add _ _ _ _ })
    (fun _ r s ↦ twist_ext fun i ↦ restrictTwistComp_smul e r s i)
    (fun _ _ h s ↦ twist_ext fun i ↦ restrictTwistComp_res e h s i)

/-- The components of the image of a section of `F|_Y ⊗ L_{e^♯ c}` in `(F ⊗ L_c)|_Y`. -/
noncomputable def restrictTwistInvComp {W : Y.Opens}
    (t : Γ(twist (F.restrict e) (c.comap e), W)) (i : ι) : Γ(F, e ''ᵁ W ⊓ U i) :=
  TopCat.Presheaf.restrictOpen (@id Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U i)) (twistComp t i)) _
    (e.image_inf_preimage W (U i)).ge

/-- The components `restrictTwistInvComp` satisfy the cocycle condition for `c`. -/
lemma restrictTwistInvComp_compat {W : Y.Opens} (t : Γ(twist (F.restrict e) (c.comap e), W))
    (i j : ι) :
    (restrictTwistInvComp e t i |ₒ (e ''ᵁ W ⊓ (U i ⊓ U j))) =
      (c.g i j |ₒ (e ''ᵁ W ⊓ (U i ⊓ U j))) •
        (restrictTwistInvComp e t j |ₒ (e ''ᵁ W ⊓ (U i ⊓ U j))) := by
  have h : TopCat.Presheaf.restrictOpen (@id Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U i)) (twistComp t i))
        (e ''ᵁ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) (e.image_mono (by order)) =
      (e.appIso _).inv ((c.comap e).g i j |ₒ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) •
        TopCat.Presheaf.restrictOpen (@id Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U j)) (twistComp t j))
          (e ''ᵁ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j))) (e.image_mono (by order)) :=
    twistComp_compat t i j
  rw [appIso_inv_comap_g_res] at h
  have hS : e ''ᵁ W ⊓ (U i ⊓ U j) ≤ e ''ᵁ (W ⊓ (e ⁻¹ᵁ U i ⊓ e ⁻¹ᵁ U j)) :=
    (e.image_inf_preimage W (U i ⊓ U j)).ge
  simp only [restrictTwistInvComp, mres_res]
  rw [← mres_res F (e.image_mono (by order)) hS, h, mres_smul, ores_res, mres_res]

/-- `restrictTwistInvComp` is linear. -/
lemma restrictTwistInvComp_smul {W : Y.Opens} (r : Γ(Y, W))
    (t : Γ(twist (F.restrict e) (c.comap e), W)) (i : ι) :
    restrictTwistInvComp e (r • t) i =
      ((e.appIso W).inv r |ₒ (e ''ᵁ W ⊓ U i)) • restrictTwistInvComp e t i := by
  have h : (@id Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U i)) (twistComp (r • t) i)) =
      (e.appIso _).inv (r |ₒ (W ⊓ e ⁻¹ᵁ U i)) •
        (@id Γ(F, e ''ᵁ (W ⊓ e ⁻¹ᵁ U i)) (twistComp t i)) :=
    rfl
  simp only [restrictTwistInvComp]
  rw [h, appIso_inv_ores e inf_le_left, mres_smul, ores_res]

/-- `restrictTwistInvComp` commutes with restriction. -/
lemma restrictTwistInvComp_res {W W' : Y.Opens} (h : W' ≤ W)
    (t : Γ(twist (F.restrict e) (c.comap e), W)) (i : ι) :
    restrictTwistInvComp e (TopCat.Presheaf.restrictOpen t W' h) i =
      TopCat.Presheaf.restrictOpen (restrictTwistInvComp e t i) (e ''ᵁ W' ⊓ U i)
        (inf_le_inf_right _ (e.image_mono h)) := by
  simp only [restrictTwistInvComp, twistComp_res]
  exact (mres_res F _ _ _).trans (mres_res F _ _ _).symm

variable (c F) in
/-- The map `F|_Y ⊗ L_{e^♯ c} ⟶ (F ⊗ L_c)|_Y`, restricting components. -/
noncomputable def restrictTwistComapInv :
    twist (F.restrict e) (c.comap e) ⟶ (twist F c).restrict e :=
  homMk (fun W ↦
    { toFun t := twistMk (F := F) (c := c) (V := e ''ᵁ W)
        (fun i ↦ restrictTwistInvComp e t i) fun i j ↦ restrictTwistInvComp_compat e t i j
      map_zero' := twist_ext fun _ ↦ mres_zero _ _
      map_add' _ _ := twist_ext fun _ ↦ mres_add _ _ _ _ })
    (fun _ r t ↦ twist_ext fun i ↦ restrictTwistInvComp_smul e r t i)
    (fun _ _ h t ↦ twist_ext fun i ↦ restrictTwistInvComp_res e h t i)

variable (c F) in
/-- **Twisting commutes with restriction along open immersions**:
`(F ⊗ L_c)|_Y ≅ F|_Y ⊗ L_{e^♯ c}` for an open immersion `e : Y ⟶ X`. -/
noncomputable def restrictTwistComapIso :
    (twist F c).restrict e ≅ twist (F.restrict e) (c.comap e) :=
  isoMk (restrictTwistComapHom e c F) (restrictTwistComapInv e c F)
    (fun _ s ↦ twist_ext fun i ↦ by
      change TopCat.Presheaf.restrictOpen (restrictTwistComp e s i) _ _ = twistComp s i
      rw [restrictTwistComp, mres_res, mres_self])
    (fun _ t ↦ twist_ext fun i ↦ by
      change TopCat.Presheaf.restrictOpen (restrictTwistInvComp e t i) _ _ = twistComp t i
      rw [restrictTwistInvComp, mres_res, mres_self]
      rfl)

variable (c) in
/-- `(F ⊗ L_c)|_Y ≅ F|_Y ⊗ L_{e^♯ c}`, naturally in `F`. -/
noncomputable def twistFunctorComapRestrictIso :
    twistFunctor c ⋙ restrictFunctor e ≅ restrictFunctor e ⋙ twistFunctor (c.comap e) :=
  NatIso.ofComponents (fun F ↦ restrictTwistComapIso e c F) fun φ ↦
    Hom.ext_apply fun _ s ↦ twist_ext fun i ↦ (Hom.app_mres _ φ _ (twistComp s i)).symm

end Restrict

end AlgebraicGeometry.Scheme.Modules

end
