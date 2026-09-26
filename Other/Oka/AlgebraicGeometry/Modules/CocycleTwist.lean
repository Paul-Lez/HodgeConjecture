/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Twisting a sheaf of modules by a Čech 1-cocycle of units

Let `X` be a scheme, `U : ι → X.Opens` a family of opens and `g` a *cocycle* on it: sections
`gᵢⱼ ∈ Γ(X, Uᵢ ∩ Uⱼ)` with `gᵢᵢ = 1` and `gᵢⱼ gⱼₖ = gᵢₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ` (so every `gᵢⱼ` is a
unit, with inverse `gⱼᵢ`). For an `𝒪_X`-module `F`, the **twist** `F ⊗ L_g` is the sheaf whose
sections over `V` are the families

  `(sᵢ)ᵢ`, `sᵢ ∈ Γ(F, V ∩ Uᵢ)`, with `sᵢ = gᵢⱼ • sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`.

This is the tensor product of `F` with the line bundle glued from free rank-one modules along the
transition functions `gᵢⱼ`, written without tensor products.

## Main definitions and results

- `Scheme.Modules.Cocycle U`: cocycles on `U`; they form a commutative group.
- `Scheme.Modules.twist F c`: the twist of `F` by `c`, and `Scheme.Modules.twistFunctor c`.
- `Scheme.Modules.homMk`: morphisms of `𝒪_X`-modules from compatible linear maps on sections.
- `Scheme.Modules.twistSectionsEquiv`: for `V ≤ Uᵢ`, `Γ(F ⊗ L_c, V) ≃ Γ(F, V)` (`s ↦ sᵢ`).
- `Scheme.Modules.twistRestrictIso`: `(F ⊗ L_c)|_{Uᵢ} ≅ F|_{Uᵢ}`, natural in `F`
  (`Scheme.Modules.twistFunctorRestrictIso`).
- `Scheme.Modules.twistOneIso`: `F ⊗ L_1 ≅ F` if the `Uᵢ` cover `X`.
- `Scheme.Modules.twistTwistIso`: `(F ⊗ L_c) ⊗ L_d ≅ F ⊗ L_{cd}`.
- `Scheme.Modules.twistEquivalence`: if the `Uᵢ` cover `X`, twisting by `c` is an autoequivalence
  of `X.Modules`, with inverse the twist by `c⁻¹`; in particular it is exact.
- `Scheme.Modules.twistMulSection`: a family `hᵢ ∈ Γ(X, Uᵢ)` with `hᵢ = dᵢⱼ hⱼ` (a global section
  of `L_d`) gives `F ⊗ L_c ⟶ F ⊗ L_{cd}`, `(sᵢ) ↦ (hᵢ sᵢ)`.

Along the way: the scoped notation `x |ₒ W` for restriction (the inclusion proved by `order`),
`Scheme.Modules.isoMk`, `Scheme.Modules.mono_of_injective`, `Scheme.Modules.isIso_of_bijective`,
`Scheme.Modules.restrictIsoOfLinearEquiv` (an isomorphism `M|_U ≅ N|_U` from compatible linear
equivalences of sections over opens `V ≤ U`), and
`IsAffineOpen.restrictOpen_mem_nonZeroDivisors`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of a section to a smaller open, the inclusion being proved by `order`. -/
scoped macro:80 x:term:80 " |ₒ " W:term:81 : term =>
  `(TopCat.Presheaf.restrictOpen $x $W (by order))

variable {X : Scheme.{u}}

section Restriction

variable (M : X.Modules) {V W W' : X.Opens}

lemma mres_add (h : W ≤ V) (x y : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (x + y) W h =
      TopCat.Presheaf.restrictOpen x W h + TopCat.Presheaf.restrictOpen y W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma mres_zero (h : W ≤ V) : TopCat.Presheaf.restrictOpen (0 : Γ(M, V)) W h = 0 := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma mres_smul (h : W ≤ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (r • x) W h =
      TopCat.Presheaf.restrictOpen r W h • TopCat.Presheaf.restrictOpen x W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma mres_res (h : W ≤ V) (h' : W' ≤ W) (x : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen x W h) W' h' =
      TopCat.Presheaf.restrictOpen x W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma mres_self (x : Γ(M, V)) : TopCat.Presheaf.restrictOpen x V le_rfl = x :=
  TopCat.Presheaf.restrict_self _

lemma Hom.app_mres {N : X.Modules} (φ : M ⟶ N) (h : W ≤ V) (x : Γ(M, V)) :
    φ.app W (TopCat.Presheaf.restrictOpen x W h) =
      TopCat.Presheaf.restrictOpen (φ.app V x) W h :=
  TopCat.Presheaf.map_restrict φ.mapPresheaf h x

lemma mres_injective_of_le (h : W ≤ V) (h' : V ≤ W) :
    Function.Injective fun x : Γ(M, V) ↦ TopCat.Presheaf.restrictOpen x W h := by
  intro a b e
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x V h') e
  simpa only [mres_res, mres_self] using this

end Restriction

section RingRestriction

variable {V W W' : X.Opens}

lemma ores_mul (h : W ≤ V) (r s : Γ(X, V)) :
    TopCat.Presheaf.restrictOpen (r * s) W h =
      TopCat.Presheaf.restrictOpen r W h * TopCat.Presheaf.restrictOpen s W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma ores_zero (h : W ≤ V) : TopCat.Presheaf.restrictOpen (0 : Γ(X, V)) W h = 0 := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma ores_one (h : W ≤ V) : TopCat.Presheaf.restrictOpen (1 : Γ(X, V)) W h = 1 := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma ores_res (h : W ≤ V) (h' : W' ≤ W) (x : Γ(X, V)) :
    TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen x W h) W' h' =
      TopCat.Presheaf.restrictOpen x W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma ores_self (x : Γ(X, V)) : TopCat.Presheaf.restrictOpen x V le_rfl = x :=
  TopCat.Presheaf.restrict_self _

lemma ores_injective_of_le (h : W ≤ V) (h' : V ≤ W) :
    Function.Injective fun x : Γ(X, V) ↦ TopCat.Presheaf.restrictOpen x W h := by
  intro a b e
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x V h') e
  simpa only [ores_res, ores_self] using this

end RingRestriction

section NonZeroDivisors

/-- A non-zero-divisor on an affine open `U` restricts to a non-zero-divisor on every open
`W ≤ U`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.restrictOpen_mem_nonZeroDivisors {U : X.Opens}
    (hU : IsAffineOpen U) {f : Γ(X, U)} (hf : f ∈ nonZeroDivisors Γ(X, U)) {W : X.Opens}
    (hW : W ≤ U) :
    TopCat.Presheaf.restrictOpen f W hW ∈ nonZeroDivisors Γ(X, W) := by
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
  have hcov : W ≤ ⨆ g : {g : Γ(X, U) // X.basicOpen g ≤ W}, X.basicOpen g.1 := by
    intro x hxW
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ (hW hxW)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgW⟩, hxg⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf _ W (fun g ↦ homOfLE g.2) hcov x 0 fun g ↦ ?_
  have := hU.isLocalization_basicOpen g.1
  have hfg : TopCat.Presheaf.restrictOpen f (X.basicOpen g.1) (g.2.trans hW) ∈
      nonZeroDivisors Γ(X, X.basicOpen g.1) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers g.1) _ hf
  have hx' := congrArg (fun y ↦ TopCat.Presheaf.restrictOpen y (X.basicOpen g.1) g.2) hx
  simp only [ores_mul, ores_res, ores_zero] at hx'
  exact (mem_nonZeroDivisors_iff_right.mp hfg _ hx').trans (ores_zero _).symm

end NonZeroDivisors

section homMk

variable {M N : X.Modules}

/-- A morphism of `𝒪_X`-modules from additive maps on sections which are linear and commute with
restrictions. -/
noncomputable def homMk (app : ∀ V : X.Opens, Γ(M, V) →+ Γ(N, V))
    (map_smul : ∀ V (r : Γ(X, V)) (x : Γ(M, V)), app V (r • x) = r • app V x)
    (naturality : ∀ V W (h : W ≤ V) (x : Γ(M, V)),
      app W (TopCat.Presheaf.restrictOpen x W h) = TopCat.Presheaf.restrictOpen (app V x) W h) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (app V.unop)
      naturality V W f := by
        ext x
        exact naturality V.unop W.unop f.unop.le x }
    (fun V r x ↦ map_smul V.unop r x)⟩

@[simp]
lemma homMk_app (app : ∀ V : X.Opens, Γ(M, V) →+ Γ(N, V)) (map_smul) (naturality) (V : X.Opens)
    (x : Γ(M, V)) : (homMk app map_smul naturality).app V x = app V x :=
  rfl

lemma Hom.ext_apply {φ ψ : M ⟶ N} (h : ∀ V (x : Γ(M, V)), φ.app V x = ψ.app V x) : φ = ψ :=
  hom_ext _ _ fun V ↦ by ext x; exact h V x

@[simp]
lemma Hom.comp_app_apply {K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (V : X.Opens) (x : Γ(M, V)) :
    (φ ≫ ψ).app V x = ψ.app V (φ.app V x) :=
  rfl

@[simp]
lemma Hom.id_app_apply (V : X.Opens) (x : Γ(M, V)) : (𝟙 M : M ⟶ M).app V x = x :=
  rfl

/-- An isomorphism of `𝒪_X`-modules from mutually inverse morphisms, checked on sections. -/
@[simps]
noncomputable def isoMk (φ : M ⟶ N) (ψ : N ⟶ M) (h₁ : ∀ V (x : Γ(M, V)), ψ.app V (φ.app V x) = x)
    (h₂ : ∀ V (y : Γ(N, V)), φ.app V (ψ.app V y) = y) : M ≅ N where
  hom := φ
  inv := ψ
  hom_inv_id := Hom.ext_apply fun V x ↦ h₁ V x
  inv_hom_id := Hom.ext_apply fun V y ↦ h₂ V y

variable (X) in
/-- Sections of the unit `𝒪_X`-module are sections of the structure sheaf. -/
noncomputable def unitSectionsEquiv (V : X.Opens) :
    Γ(SheafOfModules.unit X.ringCatSheaf, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma unitSectionsEquiv_res (V W : X.Opens) (h : W ≤ V)
    (x : Γ(SheafOfModules.unit X.ringCatSheaf, V)) :
    unitSectionsEquiv X W (TopCat.Presheaf.restrictOpen x W h) =
      TopCat.Presheaf.restrictOpen (unitSectionsEquiv X V x) W h :=
  rfl

lemma mono_of_injective (φ : M ⟶ N) (h : ∀ V, Function.Injective (φ.app V)) : Mono φ where
  right_cancellation g g' e := Hom.ext_apply fun V x ↦ h V (by
    rw [← Hom.comp_app_apply, e, Hom.comp_app_apply])

lemma isIso_of_bijective (φ : M ⟶ N) (h : ∀ V, Function.Bijective (φ.app V)) : IsIso φ :=
  Hom.isIso_iff_isIso_app.mpr fun V ↦ (ConcreteCategory.isIso_iff_bijective _).mpr (h V)

end homMk

section Gluing

variable (M : X.Modules) {κ : Type*} (W : κ → X.Opens) {V : X.Opens}

lemma mres_eq_of_locally_eq (hV : V ≤ iSup W) (hW : ∀ a, W a ≤ V) (s t : Γ(M, V))
    (h : ∀ a, TopCat.Presheaf.restrictOpen s (W a) (hW a) =
      TopCat.Presheaf.restrictOpen t (W a) (hW a)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ W V (fun a ↦ homOfLE (hW a)) hV s t h

lemma mres_existsUnique_gluing (hV : V ≤ iSup W) (hW : ∀ a, W a ≤ V) (sf : ∀ a, Γ(M, W a))
    (hsf : ∀ a b, (sf a |ₒ (W a ⊓ W b)) = (sf b |ₒ (W a ⊓ W b))) :
    ∃! s : Γ(M, V), ∀ a, TopCat.Presheaf.restrictOpen s (W a) (hW a) = sf a :=
  TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ W V (fun a ↦ homOfLE (hW a)) hV sf
    hsf

end Gluing

section RestrictIso

variable {M N : X.Modules} (U : X.Opens)
  (e : ∀ V, V ≤ U → (Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V)))
  (he : ∀ V W (hV : V ≤ U) (hW : W ≤ V) (x : Γ(M, V)),
    e W (hW.trans hV) (TopCat.Presheaf.restrictOpen x W hW) =
      TopCat.Presheaf.restrictOpen (e V hV x) W hW)

/-- An isomorphism `M|_U ≅ N|_U` from linear equivalences `Γ(M, V) ≃ Γ(N, V)`, `V ≤ U`,
compatible with restrictions. -/
noncomputable def restrictIsoOfLinearEquiv : M.restrict U.ι ≅ N.restrict U.ι :=
  isoMk
    (homMk (fun W ↦ (e _ (U.ι_image_le W)).toAddMonoidHom)
      (fun W r x ↦ (e _ (U.ι_image_le W)).map_smul ((U.ι.appIso W).inv r) x)
      (fun W W' h x ↦ he _ _ (U.ι_image_le W) (Scheme.Hom.image_mono _ h) x))
    (homMk (fun W ↦ (e _ (U.ι_image_le W)).symm.toAddMonoidHom)
      (fun W r x ↦ (e _ (U.ι_image_le W)).symm.map_smul ((U.ι.appIso W).inv r) x)
      (fun W W' h x ↦ by
        apply (e _ (U.ι_image_le W')).injective
        refine (LinearEquiv.apply_symm_apply _ _).trans ?_
        refine Eq.trans ?_ (he _ _ (U.ι_image_le W) (Scheme.Hom.image_mono _ h) _).symm
        exact congrArg (fun y ↦ TopCat.Presheaf.restrictOpen y _ _)
          (LinearEquiv.apply_symm_apply _ _).symm))
    (fun W x ↦ (e _ (U.ι_image_le W)).symm_apply_apply x)
    (fun W y ↦ (e _ (U.ι_image_le W)).apply_symm_apply y)

lemma restrictIsoOfLinearEquiv_hom_app (W : U.toScheme.Opens) (x : Γ(M, U.ι ''ᵁ W)) :
    (restrictIsoOfLinearEquiv U e he).hom.app W x = e _ (U.ι_image_le W) x :=
  rfl

lemma restrictIsoOfLinearEquiv_inv_app (W : U.toScheme.Opens) (y : Γ(N, U.ι ''ᵁ W)) :
    (restrictIsoOfLinearEquiv U e he).inv.app W y = (e _ (U.ι_image_le W)).symm y :=
  rfl

end RestrictIso

variable {ι : Type}

/-- A **cocycle** on the family of opens `U`: sections `gᵢⱼ` over `Uᵢ ∩ Uⱼ` with `gᵢᵢ = 1` and
`gᵢⱼ gⱼₖ = gᵢₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
structure Cocycle (U : ι → X.Opens) where
  /-- the transition function over `Uᵢ ∩ Uⱼ` -/
  g (i j : ι) : Γ(X, U i ⊓ U j)
  self (i : ι) : g i i = 1
  mul (i j k : ι) : (g i j |ₒ (U i ⊓ U j ⊓ U k)) * (g j k |ₒ (U i ⊓ U j ⊓ U k)) =
    g i k |ₒ (U i ⊓ U j ⊓ U k)

namespace Cocycle

variable {U : ι → X.Opens}

@[ext]
lemma ext {c d : Cocycle U} (h : ∀ i j, c.g i j = d.g i j) : c = d := by
  cases c; cases d; congr; funext i j; exact h i j

variable (c : Cocycle U)

lemma mul_res (i j k : ι) (W : X.Opens) (hW : W ≤ U i ⊓ U j ⊓ U k) :
    (c.g i j |ₒ W) * (c.g j k |ₒ W) = c.g i k |ₒ W := by
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) (c.mul i j k)
  simpa only [ores_mul, ores_res] using this

lemma self_res (i : ι) (W : X.Opens) (hW : W ≤ U i ⊓ U i) : (c.g i i |ₒ W) = 1 := by
  rw [c.self, ores_one]

lemma mul_res_symm (i j : ι) (W : X.Opens) (hW : W ≤ U i ⊓ U j) :
    (c.g i j |ₒ W) * (c.g j i |ₒ W) = 1 := by
  rw [c.mul_res i j i W (by order), c.self_res i W (by order)]

instance : One (Cocycle U) where
  one :=
    { g _ _ := 1
      self _ := rfl
      mul _ _ _ := by simp only [ores_one, mul_one] }

instance : Mul (Cocycle U) where
  mul c d :=
    { g i j := c.g i j * d.g i j
      self i := by rw [c.self, d.self, mul_one]
      mul i j k := by
        simp only [ores_mul]
        rw [← c.mul, ← d.mul]
        ring }

instance : Inv (Cocycle U) where
  inv c :=
    { g i j := c.g j i |ₒ (U i ⊓ U j)
      self i := by rw [c.self, ores_one]
      mul i j k := by
        simp only [ores_res]
        rw [mul_comm, c.mul_res k j i _ (by order)] }

@[simp] lemma one_g (i j : ι) : (1 : Cocycle U).g i j = 1 := rfl
@[simp] lemma mul_g (c d : Cocycle U) (i j : ι) : (c * d).g i j = c.g i j * d.g i j := rfl
@[simp] lemma inv_g (i j : ι) : c⁻¹.g i j = c.g j i |ₒ (U i ⊓ U j) := rfl

instance : CommGroup (Cocycle U) where
  mul_assoc _ _ _ := ext fun _ _ ↦ mul_assoc _ _ _
  one_mul _ := ext fun _ _ ↦ one_mul _
  mul_one _ := ext fun _ _ ↦ mul_one _
  mul_comm _ _ := ext fun _ _ ↦ mul_comm _ _
  inv_mul_cancel c := ext fun i j ↦ by
    rw [mul_g, inv_g, one_g, ← ores_self (c.g i j)]
    exact c.mul_res_symm j i _ (by order)

@[simp]
lemma pow_g (n : ℕ) (i j : ι) : (c ^ n).g i j = c.g i j ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, mul_g, ih, pow_succ]

end Cocycle

section Twist

variable (F : X.Modules) (U : ι → X.Opens)

/-- The families `(sᵢ)ᵢ` with `sᵢ ∈ Γ(F, V ∩ Uᵢ)`, a `Γ(X, V)`-module. -/
def TwistAmb (V : X.Opens) : Type u := ∀ i, Γ(F, V ⊓ U i)

noncomputable instance (V : X.Opens) : AddCommGroup (TwistAmb F U V) :=
  inferInstanceAs (AddCommGroup (∀ i, Γ(F, V ⊓ U i)))

noncomputable instance (V : X.Opens) : Module Γ(X, V) (TwistAmb F U V) :=
  letI (i : ι) : Module Γ(X, V) Γ(F, V ⊓ U i) :=
    Module.compHom _ (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op).hom
  inferInstanceAs (Module Γ(X, V) (∀ i, Γ(F, V ⊓ U i)))

variable {F U} in
@[simp]
lemma TwistAmb.add_apply {V : X.Opens} (s t : TwistAmb F U V) (i : ι) : (s + t) i = s i + t i :=
  rfl

variable {F U} in
@[simp]
lemma TwistAmb.zero_apply {V : X.Opens} (i : ι) : (0 : TwistAmb F U V) i = 0 :=
  rfl

variable {F U} in
lemma TwistAmb.smul_apply {V : X.Opens} (r : Γ(X, V)) (s : TwistAmb F U V) (i : ι) :
    (r • s) i = (r |ₒ (V ⊓ U i)) • s i :=
  rfl

variable {U}

/-- Sections of the twist of `F` by `c` over `V`: the families `(sᵢ)ᵢ`, `sᵢ ∈ Γ(F, V ∩ Uᵢ)`, with
`sᵢ = cᵢⱼ • sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`. -/
noncomputable def twistSubmodule (c : Cocycle U) (V : X.Opens) :
    Submodule Γ(X, V) (TwistAmb F U V) where
  carrier := {s | ∀ i j, (s i |ₒ (V ⊓ (U i ⊓ U j))) =
    (c.g i j |ₒ (V ⊓ (U i ⊓ U j))) • (s j |ₒ (V ⊓ (U i ⊓ U j)))}
  add_mem' {s t} hs ht i j := by
    simp only [Set.mem_setOf_eq, TwistAmb.add_apply, mres_add, hs i j, ht i j, smul_add] at *
  zero_mem' i j := by simp only [TwistAmb.zero_apply, mres_zero, smul_zero]
  smul_mem' r s hs i j := by
    simp only [Set.mem_setOf_eq, TwistAmb.smul_apply, mres_smul, ores_res] at *
    rw [hs i j, smul_smul, smul_smul, mul_comm]

variable {F}

/-- Restriction of families of sections. -/
noncomputable def TwistAmb.res {V V' : X.Opens} (h : V' ≤ V) :
    TwistAmb F U V →+ TwistAmb F U V' where
  toFun s i := s i |ₒ (V' ⊓ U i)
  map_zero' := funext fun i ↦ mres_zero _ _
  map_add' s t := funext fun i ↦ mres_add _ _ _ _

lemma TwistAmb.res_apply {V V' : X.Opens} (h : V' ≤ V) (s : TwistAmb F U V) (i : ι) :
    TwistAmb.res h s i = s i |ₒ (V' ⊓ U i) :=
  rfl

lemma TwistAmb.res_smul {V V' : X.Opens} (h : V' ≤ V) (r : Γ(X, V)) (s : TwistAmb F U V) :
    TwistAmb.res h (r • s) = (r |ₒ V') • TwistAmb.res h s := by
  funext i
  simp only [TwistAmb.res_apply, TwistAmb.smul_apply]
  rw [mres_smul]
  simp only [ores_res]

lemma TwistAmb.res_mem (c : Cocycle U) {V V' : X.Opens} (h : V' ≤ V) (s : TwistAmb F U V)
    (hs : s ∈ twistSubmodule F c V) : TwistAmb.res h s ∈ twistSubmodule F c V' := by
  intro i j
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x (V' ⊓ (U i ⊓ U j)) (by order)) (hs i j)
  simp only [mres_smul, mres_res, ores_res] at this
  simpa only [TwistAmb.res_apply, mres_res] using this

variable (F)

/-- The underlying abelian presheaf of the twist. -/
noncomputable def twistPresheaf (c : Cocycle U) : (X.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj V := AddCommGrpCat.of (twistSubmodule F c V.unop)
  map {V V'} f := AddCommGrpCat.ofHom
    { toFun s := ⟨TwistAmb.res f.unop.le s.1, TwistAmb.res_mem c f.unop.le s.1 s.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' s t := Subtype.ext (map_add _ _ _) }
  map_id V := by
    ext s
    funext i
    exact mres_self F (s.1 i)
  map_comp f f' := by
    ext s
    funext i
    exact (mres_res F _ _ (s.1 i)).symm

noncomputable instance (c : Cocycle U) (V : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((twistPresheaf F c).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (twistSubmodule F c V.unop))

/-- The twist of `F` by `c`, as a presheaf of modules. -/
noncomputable def twistPresheafOfModules (c : Cocycle U) : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (twistPresheaf F c) fun _ _ f r s ↦
    Subtype.ext (TwistAmb.res_smul f.unop.le r s.1)

lemma isSheaf_twistPresheaf (c : Cocycle U) : TopCat.Presheaf.IsSheaf (twistPresheaf F c) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hsf' (a b : κ) (i : ι) :
      ((sf a).1 i |ₒ (W a ⊓ W b ⊓ U i)) = ((sf b).1 i |ₒ (W a ⊓ W b ⊓ U i)) :=
    congrArg (fun x : twistSubmodule F c (W a ⊓ W b) ↦ x.1 i) (hsf a b)
  have key (i : ι) : ∃! t : Γ(F, iSup W ⊓ U i), ∀ a,
      TopCat.Presheaf.restrictOpen t (W a ⊓ U i) (by have := le_iSup W a; order) = (sf a).1 i := by
    refine mres_existsUnique_gluing F (fun a ↦ W a ⊓ U i) (by rw [iSup_inf_eq]) _ _ ?_
    intro a b
    have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x (W a ⊓ U i ⊓ (W b ⊓ U i))
      (by order)) (hsf' a b i)
    simpa only [mres_res] using this
  choose t ht hu using key
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun a ↦ ?_, fun s hs ↦ ?_⟩
  · refine mres_eq_of_locally_eq F (fun a ↦ W a ⊓ (U i ⊓ U j)) (by rw [iSup_inf_eq])
      (fun a ↦ by have := le_iSup W a; order) _ _ fun a ↦ ?_
    simp only [mres_res, mres_smul, ores_res]
    have hi := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x (W a ⊓ (U i ⊓ U j))
      (by order)) (ht i a)
    have hj := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x (W a ⊓ (U i ⊓ U j))
      (by order)) (ht j a)
    simp only [mres_res] at hi hj
    rw [hi, hj]
    exact (sf a).2 i j
  · exact Subtype.ext (funext fun i ↦ ht i a)
  · refine Subtype.ext (funext fun i ↦ hu i _ fun a ↦ ?_)
    exact congrArg (fun x : twistSubmodule F c (W a) ↦ x.1 i) (hs a)

/-- The **twist** `F ⊗ L_c` of an `𝒪_X`-module `F` by a cocycle `c`: its sections over `V` are the
families `(sᵢ)ᵢ`, `sᵢ ∈ Γ(F, V ∩ Uᵢ)`, with `sᵢ = cᵢⱼ • sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`. -/
noncomputable def twist (c : Cocycle U) : X.Modules where
  val := twistPresheafOfModules F c
  isSheaf := isSheaf_twistPresheaf F c

variable {F} {c : Cocycle U} {V : X.Opens}

/-- The `i`-th component `sᵢ ∈ Γ(F, V ∩ Uᵢ)` of a section `s` of the twist `F ⊗ L_c`. -/
def twistComp (s : Γ(twist F c, V)) (i : ι) : Γ(F, V ⊓ U i) :=
  (show twistSubmodule F c V from s).1 i

lemma twistComp_compat (s : Γ(twist F c, V)) (i j : ι) :
    (twistComp s i |ₒ (V ⊓ (U i ⊓ U j))) =
      (c.g i j |ₒ (V ⊓ (U i ⊓ U j))) • (twistComp s j |ₒ (V ⊓ (U i ⊓ U j))) :=
  (show twistSubmodule F c V from s).2 i j

/-- The section of `F ⊗ L_c` over `V` with components `sᵢ`. -/
def twistMk (s : ∀ i, Γ(F, V ⊓ U i))
    (hs : ∀ i j, (s i |ₒ (V ⊓ (U i ⊓ U j))) =
      (c.g i j |ₒ (V ⊓ (U i ⊓ U j))) • (s j |ₒ (V ⊓ (U i ⊓ U j)))) : Γ(twist F c, V) :=
  show twistSubmodule F c V from ⟨s, hs⟩

@[simp]
lemma twistComp_twistMk (s : ∀ i, Γ(F, V ⊓ U i)) (hs) (i : ι) :
    twistComp (twistMk (c := c) s hs) i = s i :=
  rfl

@[ext]
lemma twist_ext {s t : Γ(twist F c, V)} (h : ∀ i, twistComp s i = twistComp t i) : s = t :=
  Subtype.ext (funext h)

@[simp]
lemma twistComp_add (s t : Γ(twist F c, V)) (i : ι) :
    twistComp (s + t) i = twistComp s i + twistComp t i :=
  rfl

@[simp]
lemma twistComp_zero (i : ι) : twistComp (0 : Γ(twist F c, V)) i = 0 :=
  rfl

@[simp]
lemma twistComp_neg (s : Γ(twist F c, V)) (i : ι) : twistComp (-s) i = -twistComp s i :=
  rfl

@[simp]
lemma twistComp_sub (s t : Γ(twist F c, V)) (i : ι) :
    twistComp (s - t) i = twistComp s i - twistComp t i :=
  rfl

lemma twistComp_smul (r : Γ(X, V)) (s : Γ(twist F c, V)) (i : ι) :
    twistComp (r • s) i = (r |ₒ (V ⊓ U i)) • twistComp s i :=
  rfl

lemma twistComp_res {W : X.Opens} (h : W ≤ V) (s : Γ(twist F c, V)) (i : ι) :
    twistComp (TopCat.Presheaf.restrictOpen s W h) i = twistComp s i |ₒ (W ⊓ U i) :=
  rfl

/-- The components of a section of `F ⊗ L_c` restricted to a smaller open. -/
lemma twistComp_compat_res (s : Γ(twist F c, V)) (i j : ι) (W : X.Opens)
    (hW : W ≤ V ⊓ (U i ⊓ U j)) :
    TopCat.Presheaf.restrictOpen (twistComp s i) W (by order) =
      (c.g i j |ₒ W) • TopCat.Presheaf.restrictOpen (twistComp s j) W (by order) := by
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) (twistComp_compat s i j)
  simpa only [mres_res, mres_smul, ores_res] using this

variable (c) in
/-- The map on twists induced by a morphism of `𝒪_X`-modules. -/
noncomputable def twistMap {G : X.Modules} (φ : F ⟶ G) : twist F c ⟶ twist G c :=
  homMk (fun V ↦
    { toFun s := twistMk (fun i ↦ φ.app _ (twistComp s i)) fun i j ↦ by
        rw [← Hom.app_mres, ← Hom.app_mres, twistComp_compat, Hom.app_smul]
      map_zero' := by ext i; simp
      map_add' s t := by ext i; simp })
    (fun V r s ↦ by ext i; simp [twistComp_smul])
    (fun V W h s ↦ by ext i; simp [twistComp_res, Hom.app_mres])

@[simp]
lemma twistComp_twistMap_app {G : X.Modules} (φ : F ⟶ G) (s : Γ(twist F c, V)) (i : ι) :
    twistComp ((twistMap c φ).app V s) i = φ.app _ (twistComp s i) :=
  rfl

variable (c) in
/-- Twisting by `c` as a functor. -/
noncomputable def twistFunctor : X.Modules ⥤ X.Modules where
  obj F := twist F c
  map φ := twistMap c φ
  map_id F := Hom.ext_apply fun V s ↦ by ext i; simp
  map_comp φ ψ := Hom.ext_apply fun V s ↦ by ext i; simp

section Chart

variable (c) (i : ι) (hV : V ≤ U i)

/-- **Trivialisation on the chart `Uᵢ`**: for `V ≤ Uᵢ`, a section of `F ⊗ L_c` over `V` is
determined by its `i`-th component, `s ↦ sᵢ`, with inverse `t ↦ (cₖᵢ • t)ₖ`. -/
noncomputable def twistSectionsEquiv : Γ(twist F c, V) ≃ₗ[Γ(X, V)] Γ(F, V) where
  toFun s := twistComp s i |ₒ V
  invFun t := twistMk (fun k ↦ (c.g k i |ₒ (V ⊓ U k)) • (t |ₒ (V ⊓ U k))) fun k l ↦ by
    simp only [mres_smul, ores_res, mres_res, smul_smul]
    rw [c.mul_res k l i _ (by order)]
  map_add' s t := by simp [mres_add]
  map_smul' r s := by
    simp only [twistComp_smul, mres_smul, ores_res, ores_self, RingHom.id_apply]
  left_inv s := by
    ext k
    simp only [twistComp_twistMk, mres_res]
    rw [← twistComp_compat_res s k i _ (by order), mres_self]
  right_inv t := by
    simp only [twistComp_twistMk, mres_smul, ores_res, mres_res, mres_self]
    rw [c.self_res i V (by order), one_smul]

lemma twistSectionsEquiv_apply (s : Γ(twist F c, V)) :
    twistSectionsEquiv c i hV s = twistComp s i |ₒ V :=
  rfl

lemma twistComp_twistSectionsEquiv_symm (t : Γ(F, V)) (k : ι) :
    twistComp ((twistSectionsEquiv c i hV).symm t) k = (c.g k i |ₒ (V ⊓ U k)) • (t |ₒ (V ⊓ U k)) :=
  rfl

lemma twistSectionsEquiv_injective : Function.Injective (twistSectionsEquiv (F := F) c i hV) :=
  (twistSectionsEquiv c i hV).injective

lemma twistSectionsEquiv_res {W : X.Opens} (hW : W ≤ V) (s : Γ(twist F c, V)) :
    twistSectionsEquiv c i (hW.trans hV) (TopCat.Presheaf.restrictOpen s W hW) =
      TopCat.Presheaf.restrictOpen (twistSectionsEquiv c i hV s) W hW := by
  simp only [twistSectionsEquiv_apply, twistComp_res, mres_res]

lemma twistSectionsEquiv_symm_res {W : X.Opens} (hW : W ≤ V) (t : Γ(F, V)) :
    (twistSectionsEquiv c i (hW.trans hV)).symm (TopCat.Presheaf.restrictOpen t W hW) =
      TopCat.Presheaf.restrictOpen ((twistSectionsEquiv c i hV).symm t) W hW := by
  apply (twistSectionsEquiv c i (hW.trans hV)).injective
  rw [LinearEquiv.apply_symm_apply, twistSectionsEquiv_res c i hV hW,
    LinearEquiv.apply_symm_apply]

/-- Changing the chart used to trivialise `F ⊗ L_c` multiplies by the transition function. -/
lemma twistSectionsEquiv_change (j : ι) (hj : V ≤ U j) (s : Γ(twist F c, V)) :
    twistSectionsEquiv c i hV s = (c.g i j |ₒ V) • twistSectionsEquiv c j hj s := by
  simp only [twistSectionsEquiv_apply]
  exact twistComp_compat_res s i j V (by order)

end Chart

variable (F c) in
/-- **The twist `F ⊗ L_c` is trivial on the chart `Uᵢ`**: `(F ⊗ L_c)|_{Uᵢ} ≅ F|_{Uᵢ}`. -/
noncomputable def twistRestrictIso (i : ι) : (twist F c).restrict (U i).ι ≅ F.restrict (U i).ι :=
  restrictIsoOfLinearEquiv (U i) (fun _ hV ↦ twistSectionsEquiv c i hV)
    fun _ _ hV hW s ↦ twistSectionsEquiv_res c i hV hW s

lemma twistRestrictIso_hom_app (i : ι) (W : (U i).toScheme.Opens)
    (s : Γ(twist F c, (U i).ι ''ᵁ W)) :
    (twistRestrictIso F c i).hom.app W s = twistSectionsEquiv c i ((U i).ι_image_le W) s :=
  rfl

@[reassoc]
lemma twistRestrictIso_naturality {G : X.Modules} (φ : F ⟶ G) (i : ι) :
    (restrictFunctor (U i).ι).map (twistMap c φ) ≫ (twistRestrictIso G c i).hom =
      (twistRestrictIso F c i).hom ≫ (restrictFunctor (U i).ι).map φ :=
  Hom.ext_apply fun W s ↦ by
    change twistSectionsEquiv c i ((U i).ι_image_le W) ((twistMap c φ).app _ s) =
      φ.app _ (twistSectionsEquiv c i ((U i).ι_image_le W) s)
    rw [twistSectionsEquiv_apply, twistSectionsEquiv_apply, twistComp_twistMap_app, Hom.app_mres]

variable (c) in
/-- The trivialisation `(F ⊗ L_c)|_{Uᵢ} ≅ F|_{Uᵢ}`, natural in `F`. -/
noncomputable def twistFunctorRestrictIso (i : ι) :
    twistFunctor c ⋙ restrictFunctor (U i).ι ≅ restrictFunctor (U i).ι :=
  NatIso.ofComponents (fun F ↦ twistRestrictIso F c i) fun φ ↦ twistRestrictIso_naturality φ i

section One

variable (F)

/-- The map `F ⟶ F ⊗ L_1`, `t ↦ (t|_{Uᵢ})ᵢ`. -/
noncomputable def toTwistOne : F ⟶ twist F (1 : Cocycle U) :=
  homMk (fun V ↦
    { toFun t := twistMk (fun i ↦ t |ₒ (V ⊓ U i)) fun i j ↦ by
        simp only [mres_res, Cocycle.one_g, ores_one, one_smul]
      map_zero' := by ext i; simp [mres_zero]
      map_add' s t := by ext i; simp [mres_add] })
    (fun V r t ↦ by ext i; simp [twistComp_smul, mres_smul])
    (fun V W h t ↦ by ext i; simp [twistComp_res, mres_res])

@[simp]
lemma twistComp_toTwistOne_app (t : Γ(F, V)) (i : ι) :
    twistComp ((toTwistOne (U := U) F).app V t) i = t |ₒ (V ⊓ U i) :=
  rfl

variable {F}

lemma toTwistOne_bijective (hU : ⨆ i, U i = ⊤) (V : X.Opens) :
    Function.Bijective ((toTwistOne (U := U) F).app V) := by
  have hcov : V ≤ ⨆ i, V ⊓ U i := by rw [← inf_iSup_eq, hU, inf_top_eq]
  refine ⟨fun t t' h ↦ ?_, fun s ↦ ?_⟩
  · exact mres_eq_of_locally_eq F _ hcov (fun _ ↦ inf_le_left) t t' fun i ↦
      congrArg (fun x ↦ twistComp x i) h
  · obtain ⟨t, ht, -⟩ := mres_existsUnique_gluing F (fun i ↦ V ⊓ U i) hcov (fun _ ↦ inf_le_left)
      (twistComp s) fun i j ↦ by
        rw [twistComp_compat_res s i j _ (by order)]
        simp only [Cocycle.one_g, ores_one, one_smul]
    exact ⟨t, twist_ext fun i ↦ ht i⟩

variable (F) in
/-- **The twist by the trivial cocycle** is `F` itself, if the `Uᵢ` cover `X`. -/
noncomputable def twistOneIso (hU : ⨆ i, U i = ⊤) : twist F (1 : Cocycle U) ≅ F :=
  have := isIso_of_bijective _ (toTwistOne_bijective (F := F) hU)
  (asIso (toTwistOne F)).symm

lemma twistOneIso_inv (hU : ⨆ i, U i = ⊤) : (twistOneIso F hU).inv = toTwistOne F :=
  rfl

@[reassoc]
lemma toTwistOne_naturality {G : X.Modules} (φ : F ⟶ G) :
    φ ≫ toTwistOne (U := U) G = toTwistOne F ≫ twistMap 1 φ :=
  Hom.ext_apply fun V t ↦ by ext i; simp [Hom.app_mres]

variable (U) in
/-- Twisting by the trivial cocycle is isomorphic to the identity, if the `Uᵢ` cover `X`. -/
noncomputable def twistFunctorOneIso (hU : ⨆ i, U i = ⊤) : twistFunctor (1 : Cocycle U) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F ↦ twistOneIso F hU) fun {F G} φ ↦ by
    change twistMap 1 φ ≫ (twistOneIso G hU).hom = (twistOneIso F hU).hom ≫ φ
    rw [← cancel_epi (twistOneIso F hU).inv, Iso.inv_hom_id_assoc, twistOneIso_inv,
      ← toTwistOne_naturality_assoc, ← twistOneIso_inv (F := G) hU, Iso.inv_hom_id,
      Category.comp_id]

end One

section TwistTwist

variable (c d : Cocycle U)

/-- The map `(F ⊗ L_c) ⊗ L_d ⟶ F ⊗ L_{cd}`, `(tᵢ)ᵢ ↦ ((tᵢ)ᵢ)ᵢ`. -/
noncomputable def twistTwistHom : twist (twist F c) d ⟶ twist F (c * d) :=
  homMk (fun V ↦
    { toFun s := twistMk (fun i ↦ twistSectionsEquiv c i inf_le_right (twistComp s i))
        fun i j ↦ by
          rw [← twistSectionsEquiv_res c i inf_le_right, twistComp_compat s i j,
            LinearEquiv.map_smul, twistSectionsEquiv_change c i _ j (by order),
            twistSectionsEquiv_res c j inf_le_right, smul_smul, Cocycle.mul_g, ores_mul,
            mul_comm]
      map_zero' := by ext i; simp
      map_add' s t := by ext i; simp })
    (fun V r t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, twistComp_twistMk, twistComp_smul,
        LinearEquiv.map_smul])
    (fun V W h t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, twistComp_twistMk, twistComp_res]
      exact twistSectionsEquiv_res c i inf_le_right _ _)

@[simp]
lemma twistComp_twistTwistHom_app (s : Γ(twist (twist F c) d, V)) (i : ι) :
    twistComp ((twistTwistHom c d).app V s) i =
      twistSectionsEquiv c i inf_le_right (twistComp s i) :=
  rfl

lemma twistTwistHom_bijective (V : X.Opens) :
    Function.Bijective ((twistTwistHom (F := F) c d).app V) := by
  refine ⟨fun s s' h ↦ twist_ext fun i ↦ (twistSectionsEquiv c i inf_le_right).injective ?_,
    fun t ↦ ?_⟩
  · simpa using congrArg (fun x ↦ twistComp x i) h
  refine ⟨twistMk (fun i ↦ (twistSectionsEquiv c i inf_le_right).symm (twistComp t i))
    fun i j ↦ ?_, twist_ext fun i ↦ ?_⟩
  · apply (twistSectionsEquiv c i (by order : V ⊓ (U i ⊓ U j) ≤ U i)).injective
    rw [LinearEquiv.map_smul, twistSectionsEquiv_res c i inf_le_right,
      LinearEquiv.apply_symm_apply]
    conv_rhs => rw [twistSectionsEquiv_change c i _ j (by order),
      twistSectionsEquiv_res c j inf_le_right, LinearEquiv.apply_symm_apply]
    rw [smul_smul, ← ores_mul, mul_comm (d.g i j)]
    exact twistComp_compat t i j
  · simp

variable (F) in
/-- **Twisting twice**: `(F ⊗ L_c) ⊗ L_d ≅ F ⊗ L_{cd}`. -/
noncomputable def twistTwistIso : twist (twist F c) d ≅ twist F (c * d) :=
  have := isIso_of_bijective _ (twistTwistHom_bijective (F := F) c d)
  asIso (twistTwistHom c d)

lemma twistTwistIso_hom : (twistTwistIso F c d).hom = twistTwistHom c d :=
  rfl

@[reassoc]
lemma twistTwistHom_naturality {G : X.Modules} (φ : F ⟶ G) :
    twistMap d (twistMap c φ) ≫ twistTwistHom c d = twistTwistHom c d ≫ twistMap (c * d) φ :=
  Hom.ext_apply fun V t ↦ by
    ext i
    simp [twistSectionsEquiv_apply, Hom.app_mres]

/-- `(twistFunctor c ⋙ twistFunctor d) ≅ twistFunctor (c * d)`. -/
noncomputable def twistFunctorCompIso :
    twistFunctor c ⋙ twistFunctor d ≅ twistFunctor (X := X) (c * d) :=
  NatIso.ofComponents (fun F ↦ twistTwistIso F c d) fun φ ↦ twistTwistHom_naturality c d φ

end TwistTwist

variable (F) in
/-- The identification `F ⊗ L_c ⟶ F ⊗ L_d` for equal cocycles `c = d` (the identity on
components). -/
noncomputable def twistCongrHom {c d : Cocycle U} (h : c = d) : twist F c ⟶ twist F d :=
  homMk (fun V ↦
    { toFun s := twistMk (twistComp s) fun i j ↦ by rw [← h]; exact twistComp_compat s i j
      map_zero' := rfl
      map_add' _ _ := rfl })
    (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

@[simp]
lemma twistComp_twistCongrHom_app {c d : Cocycle U} (h : c = d) (s : Γ(twist F c, V)) (i : ι) :
    twistComp ((twistCongrHom F h).app V s) i = twistComp s i :=
  rfl

/-- Twisting by equal cocycles gives isomorphic functors (the identity on components). -/
noncomputable def twistFunctorCongr {c d : Cocycle U} (h : c = d) :
    twistFunctor c ≅ twistFunctor (X := X) d :=
  NatIso.ofComponents
    (fun F ↦ isoMk (twistCongrHom F h) (twistCongrHom F h.symm) (fun _ _ ↦ rfl) fun _ _ ↦ rfl)
    fun _ ↦ Hom.ext_apply fun _ _ ↦ rfl

@[simp]
lemma twistFunctorCongr_hom_app {c d : Cocycle U} (h : c = d) :
    (twistFunctorCongr h).hom.app F = twistCongrHom F h :=
  rfl

instance (c : Cocycle U) : (twistFunctor (X := X) c).Additive where
  map_add := Hom.ext_apply fun _ _ ↦ twist_ext fun _ ↦ rfl

section Equivalence

variable (c) (hU : ⨆ i, U i = ⊤)

/-- **Twisting is an autoequivalence**: if the `Uᵢ` cover `X`, twisting by `c` is an equivalence
of categories `X.Modules ≌ X.Modules`, with inverse the twist by `c⁻¹`. -/
noncomputable def twistEquivalence : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (twistFunctor c) (twistFunctor c⁻¹)
    ((twistFunctorOneIso U hU).symm ≪≫ twistFunctorCongr (mul_inv_cancel c).symm ≪≫
      (twistFunctorCompIso c c⁻¹).symm)
    (twistFunctorCompIso c⁻¹ c ≪≫ twistFunctorCongr (inv_mul_cancel c) ≪≫
      twistFunctorOneIso U hU)

@[simp]
lemma twistEquivalence_functor : (twistEquivalence c hU).functor = twistFunctor c :=
  rfl

include hU in
lemma isEquivalence_twistFunctor : (twistFunctor (X := X) c).IsEquivalence :=
  (twistEquivalence c hU).isEquivalence_functor

include hU in
/-- Twisting preserves all limits (in particular it is left exact). -/
lemma preservesLimits_twistFunctor : PreservesLimits (twistFunctor (X := X) c) :=
  have := isEquivalence_twistFunctor c hU
  inferInstance

include hU in
/-- Twisting preserves all colimits (in particular it is right exact). -/
lemma preservesColimits_twistFunctor : PreservesColimits (twistFunctor (X := X) c) :=
  have := isEquivalence_twistFunctor c hU
  inferInstance

end Equivalence

section MulSection

lemma mulSection_inf_le_left (i j : ι) : U i ⊓ U j ≤ U i := inf_le_left

lemma mulSection_inf_le_right (i j : ι) : U i ⊓ U j ≤ U j := inf_le_right

variable (d : Cocycle U) (h : ∀ i, Γ(X, U i))
  (hh : ∀ i j,
    TopCat.Presheaf.restrictOpen (h i) (U i ⊓ U j)
        (mulSection_inf_le_left (U := U) i j) =
      d.g i j * TopCat.Presheaf.restrictOpen (h j) (U i ⊓ U j)
        (mulSection_inf_le_right (U := U) i j))

include hh in
lemma mulSection_compat (i j : ι) (W : X.Opens) (hW : W ≤ U i ⊓ U j) :
    (h i |ₒ W) = (d.g i j |ₒ W) * (h j |ₒ W) := by
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) (hh i j)
  simpa only [ores_mul, ores_res] using this

variable (F c) in
/-- **Multiplication by a global section of `L_d`**: a family `hᵢ ∈ Γ(X, Uᵢ)` with
`hᵢ = dᵢⱼ hⱼ` on `Uᵢ ∩ Uⱼ` gives `F ⊗ L_c ⟶ F ⊗ L_{cd}`, `(sᵢ) ↦ (hᵢ sᵢ)`. -/
noncomputable def twistMulSection : twist F c ⟶ twist F (c * d) :=
  homMk (fun V ↦
    { toFun s := twistMk (fun i ↦ (h i |ₒ (V ⊓ U i)) • twistComp s i) fun i j ↦ by
        rw [mres_smul, mres_smul, twistComp_compat, ores_res, ores_res,
          mulSection_compat d h hh i j _ (by order), smul_smul, smul_smul, Cocycle.mul_g,
          ores_mul]
        congr 1
        ring
      map_zero' := by ext i; simp
      map_add' s t := by ext i; simp [smul_add] })
    (fun V r t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, twistComp_twistMk, twistComp_smul]
      exact smul_comm _ _ _)
    (fun V W hVW t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, twistComp_twistMk, twistComp_res,
        mres_smul, ores_res])

@[simp]
lemma twistComp_twistMulSection_app (s : Γ(twist F c, V)) (i : ι) :
    twistComp ((twistMulSection F c d h hh).app V s) i = (h i |ₒ (V ⊓ U i)) • twistComp s i :=
  rfl

@[reassoc]
lemma twistMulSection_naturality {G : X.Modules} (φ : F ⟶ G) :
    twistMap c φ ≫ twistMulSection G c d h hh = twistMulSection F c d h hh ≫ twistMap (c * d) φ :=
  Hom.ext_apply fun V t ↦ by
    ext i
    simp

end MulSection

end Twist

end AlgebraicGeometry.Scheme.Modules

end
