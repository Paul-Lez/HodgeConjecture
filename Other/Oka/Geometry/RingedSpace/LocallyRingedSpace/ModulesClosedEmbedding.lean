/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.PullbackModulesStalk
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbedding

/-!
# Pullback and pushforward of modules along closed embeddings of locally ringed spaces

Let `f : X ⟶ Y` be a morphism of locally ringed spaces whose underlying map is a closed embedding
and whose stalk maps `𝒪_{Y,f x} → 𝒪_{X,x}` are surjective (e.g. a closed immersion of schemes,
or the analytification of one). We study the adjunction `f^* ⊣ f_*` on sheaves of modules.

- `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesStalkIso_hom_app_germ_unit`: for any
  morphism `f`, under `(f^* A)_x ≅ 𝒪_{X,x} ⊗ A_{f x}` the stalk of the unit `A ⟶ f_* f^* A` is
  `a ↦ 1 ⊗ a`.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.isIso_pullbackModulesAdj_unit_app`: the unit
  `A ⟶ f_* f^* A` is an isomorphism as soon as `A` has zero stalks off `f(X)` and each stalk
  `A_{f x}` is killed by the kernel of `𝒪_{Y,f x} → 𝒪_{X,x}`.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.isIso_pullbackModulesAdj_counit_app`: the counit
  `f^* f_* G ⟶ G` is an isomorphism for every sheaf of modules `G` on `X`.

The ideal `f.pushforwardStalkIdeal y ⊆ 𝒪_{Y,y}` (the kernel of `𝒪_{Y,y} → (f_* 𝒪_X)_y`) kills the
stalk at `y` of the pushforward of any sheaf of `𝒪_X`-modules
(`AlgebraicGeometry.LocallyRingedSpace.Hom.smul_eq_zero_of_mem_pushforwardStalkIdeal`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ModuleCat

/-- For a surjective ring map `f : R → S`, the map `M → S ⊗_R M`, `m ↦ 1 ⊗ m` is surjective. -/
lemma surjective_extendRestrictScalarsAdj_unit_app_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) : Function.Surjective ((extendRestrictScalarsAdj f).unit.app M) := by
  let g : S → R := Function.surjInv hf
  have hg : ∀ s, f (g s) = s := Function.surjInv_eq hf
  intro t
  change TensorProduct R ((restrictScalars f).obj (of S S)) M at t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s m =>
    refine ⟨g s • m, ?_⟩
    change (show (restrictScalars f).obj (of S S) from (1 : S)) ⊗ₜ[R] (g s • m) = _
    rw [← TensorProduct.smul_tmul]
    congr 1
    change f (g s) * 1 = s
    rw [hg, mul_one]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    exact ⟨a + b, by rw [map_add, ha, hb]; exact rfl⟩

/-- For a surjective ring map `f : R → S` and an `R`-module `M` killed by `ker f`, the map
`M → S ⊗_R M`, `m ↦ 1 ⊗ m` is bijective. -/
lemma bijective_extendRestrictScalarsAdj_unit_app_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (hM : ∀ r ∈ RingHom.ker f, ∀ m : M, r • m = 0) :
    Function.Bijective ((extendRestrictScalarsAdj f).unit.app M) := by
  have key : ∀ a b : R, f a = f b → ∀ m : M, a • m = b • m := fun a b h m ↦ by
    rw [← sub_eq_zero, ← sub_smul]
    exact hM _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) m
  let g : S → R := Function.surjInv hf
  have hg : ∀ s, f (g s) = s := Function.surjInv_eq hf
  let B : (restrictScalars f).obj (of S S) →ₗ[R] M →ₗ[R] M :=
    LinearMap.mk₂ R (fun s m ↦ g s • m)
      (fun s₁ s₂ m ↦ by
        rw [← add_smul]
        exact key _ _ (by rw [map_add, hg, hg, hg]; rfl) m)
      (fun r s m ↦ by
        rw [smul_smul]
        exact key _ _ (by rw [map_mul, hg, hg]; rfl) m)
      (fun s m₁ m₂ ↦ smul_add _ _ _)
      (fun r s m ↦ by rw [smul_comm])
  let Φ := TensorProduct.lift B
  have hΦ : ∀ m : M, Φ ((extendRestrictScalarsAdj f).unit.app M m) = m := fun m ↦ by
    change g 1 • m = m
    rw [key (g 1) 1 (by rw [hg, map_one]), one_smul]
  refine ⟨fun a b h ↦ ?_, surjective_extendRestrictScalarsAdj_unit_app_of_surjective f hf M⟩
  rw [← hΦ a, ← hΦ b, h]

/-- If an ideal `I ⊆ R` kills `M`, then `f(I) S` kills `S ⊗_R M`. -/
lemma smul_extendScalars_eq_zero_of_mem_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (I : Ideal R) (hI : ∀ k ∈ I, ∀ m : M, k • m = 0)
    (r : S) (hr : r ∈ Ideal.map f I) (t : (extendScalars f).obj M) : r • t = 0 := by
  let J : Ideal S := Module.annihilator S ((extendScalars f).obj M)
  suffices h : Ideal.map f I ≤ J from Module.mem_annihilator.1 (h hr) t
  refine Ideal.map_le_iff_le_comap.2 fun k hk ↦ ?_
  refine Module.mem_annihilator.2 fun t ↦ ?_
  induction t using TensorProduct.induction_on with
  | zero => exact (smul_zero (f k) : f k • (0 : (extendScalars f).obj M) = 0)
  | tmul s m =>
    change (show (restrictScalars f).obj (of S S) from f k * (show S from s)) ⊗ₜ[R] m = 0
    have : (show (restrictScalars f).obj (of S S) from f k * (show S from s)) = k • s := rfl
    rw [this, TensorProduct.smul_tmul, hI k hk m, TensorProduct.tmul_zero]
  | add t₁ t₂ h₁ h₂ => exact (smul_add _ _ _).trans (by rw [h₁, h₂, add_zero])

/-- The base change of the zero module is zero. -/
lemma subsingleton_extendScalars {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (hM : Subsingleton M) : Subsingleton ((extendScalars f).obj M) := by
  refine ⟨fun a b ↦ ?_⟩
  suffices h : ∀ t : (extendScalars f).obj M, t = 0 by rw [h a, h b]
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]; rfl
  | add t₁ t₂ h₁ h₂ => rw [h₁, h₂]; exact add_zero (0 : (extendScalars f).obj M)

end ModuleCat

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- **The stalk of the unit of `f^* ⊣ f_*`**: under `(f^* A)_x ≅ 𝒪_{X,x} ⊗ A_{f x}`, the germ at
`x` of the image of a section `a` under the unit `A ⟶ f_* f^* A` is `1 ⊗ a_{f x}`. -/
lemma Hom.pullbackModulesStalkIso_hom_app_germ_unit (A : SheafOfModules.{u} Y.ringSheaf)
    (U : Opens Y) (x : X) (hx : f.base x ∈ U) (a : A.val.obj (op U)) :
    (f.pullbackModulesStalkIso x).hom.app A
      (TopCat.Presheaf.germ (f.pullbackModules.obj A).val.presheaf ((Opens.map f.base).obj U) x hx
        ((f.pullbackModulesAdj.unit.app A).val.app (op U) a)) =
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
      ((Y.stalkFunctor (f.base x)).obj A)
        (TopCat.Presheaf.germ A.val.presheaf U (f.base x) hx a) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((SheafOfModules.pullbackPushforwardAdjunction f.toRingSheafHom).comp
      (SheafOfModules.stalkSkyscraperAdj (hR := X.isSheaf_ringSheaf) x)).ofNatIsoRight
        (SheafOfModules.skyscraperFunctorPushforwardIso
          (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c x))
    ((SheafOfModules.stalkSkyscraperAdj (hR := Y.isSheaf_ringSheaf) (f.base x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)) A
  exact congrArg (fun φ ↦ φ.val.app (op U) a ⟨hx⟩) h

/-- The kernel of `𝒪_{Y,y} → (f_* 𝒪_X)_y`, the stalk map of `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`. -/
def Hom.pushforwardStalkIdeal (y : Y) : Ideal (Y.presheaf.stalk y) :=
  RingHom.ker ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.c).hom

/-- **`f.pushforwardStalkIdeal y` kills the stalk at `y` of every pushforward `f_* H`.** -/
lemma Hom.smul_eq_zero_of_mem_pushforwardStalkIdeal (H : SheafOfModules.{u} X.ringSheaf)
    (y : Y) (r : Y.presheaf.stalk y) (hr : r ∈ f.pushforwardStalkIdeal y)
    (m : (Y.stalkFunctor y).obj ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H)) :
    r • m = 0 := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H).val.presheaf m
  have hr' : TopCat.Presheaf.germ (f.base _* X.presheaf) U y hU (f.c.app (op U) s) =
      TopCat.Presheaf.germ (f.base _* X.presheaf) U y hU 0 := by
    refine Eq.trans ?_ (map_zero _).symm
    have := hr
    rw [Hom.pushforwardStalkIdeal, RingHom.mem_ker] at this
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at this
    exact this
  obtain ⟨W, hW, iU, iU', hWe⟩ := TopCat.Presheaf.germ_eq _ y hU hU _ _ hr'
  have hW0 : f.c.app (op W) (Y.presheaf.map iU.op s) = 0 := by
    have hnat := congrArg (fun φ ↦ φ s) (congrArg CommRingCat.Hom.hom (f.c.naturality iU.op))
    exact hnat.trans (hWe.trans (map_zero _))
  have hle : W ⊓ V ≤ W := inf_le_left
  have h0 : f.c.app (op (W ⊓ V)) (Y.presheaf.map (homOfLE (hle.trans iU.le)).op s) = 0 := by
    have hnat := congrArg (fun φ ↦ φ (Y.presheaf.map iU.op s))
      (congrArg CommRingCat.Hom.hom (f.c.naturality (homOfLE hle).op))
    have e : Y.presheaf.map (homOfLE (hle.trans iU.le)).op s =
        Y.presheaf.map (homOfLE hle).op (Y.presheaf.map iU.op s) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [e]
    refine hnat.trans ?_
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [hW0]
    exact map_zero _
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (hle.trans iU.le)) y ⟨hW, hV⟩ s]
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_right : W ⊓ V ≤ V)) y ⟨hW, hV⟩ t]
  erw [← PresheafOfModules.germ_smul]
  refine (congrArg _ ?_).trans (map_zero _)
  let r' : X.ringSheaf.obj.obj (op ((Opens.map f.base).obj (W ⊓ V))) :=
    f.c.app (op (W ⊓ V)) (Y.presheaf.map (homOfLE (hle.trans iU.le)).op s)
  let m' : H.val.obj (op ((Opens.map f.base).obj (W ⊓ V))) :=
    H.val.presheaf.map ((Opens.map f.base).map (homOfLE (inf_le_right : W ⊓ V ≤ V))).op t
  change r' • m' = 0
  have hr0 : r' = 0 := h0
  rw [hr0, zero_smul]

/-- A morphism of sheaves of modules on a locally ringed space which is bijective on all stalks
is an isomorphism. -/
theorem isIso_of_bijective_stalkFunctor_map {M N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N)
    (h : ∀ y : Y, Function.Bijective ((Y.stalkFunctor y).map φ)) : IsIso φ := by
  haveI : ∀ y : (Y.toPresheafedSpace : TopCat.{u}),
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((SheafOfModules.toSheaf _).map φ).hom) := fun y ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (h y)
  haveI : IsIso ((SheafOfModules.toSheaf _).map φ) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (C := AddCommGrpCat.{u}) _
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf _)

/-- The map `(f_* H)_{f x} → H_x` on stalks of a sheaf of modules, as a function. -/
abbrev Hom.stalkPushforwardModules (H : SheafOfModules.{u} X.ringSheaf) (x : X) :
    (Y.stalkFunctor (f.base x)).obj ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H) →
      (X.stalkFunctor x).obj H :=
  TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base H.val.presheaf x

/-- `(f_* H)_{f x} → H_x` sends germs to germs. -/
lemma Hom.stalkPushforwardModules_germ (H : SheafOfModules.{u} X.ringSheaf) (x : X)
    (U : Opens Y) (hx : f.base x ∈ U)
    (t : ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H).val.obj (op U)) :
    f.stalkPushforwardModules H x
      (TopCat.Presheaf.germ ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H).val.presheaf
        U (f.base x) hx t) =
      TopCat.Presheaf.germ H.val.presheaf ((Opens.map f.base).obj U) x hx t :=
  ConcreteCategory.congr_hom (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.base
    H.val.presheaf U x hx) t

/-- For `f` inducing, `(f_* H)_{f x} → H_x` is bijective. -/
lemma Hom.bijective_stalkPushforwardModules (hf : IsInducing f.base)
    (H : SheafOfModules.{u} X.ringSheaf) (x : X) :
    Function.Bijective (f.stalkPushforwardModules H x) := by
  haveI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
    hf H.val.presheaf x
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- `(f_* H)_{f x} → H_x` is natural in `H`. -/
lemma Hom.stalkPushforwardModules_naturality {H H' : SheafOfModules.{u} X.ringSheaf}
    (φ : H ⟶ H') (x : X)
    (m : (Y.stalkFunctor (f.base x)).obj
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H)) :
    f.stalkPushforwardModules H' x ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) m) =
      (X.stalkFunctor x).map φ (f.stalkPushforwardModules H x m) := by
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H).val.presheaf m
  erw [PresheafOfModules.stalkFunctor_map_germ, f.stalkPushforwardModules_germ,
    f.stalkPushforwardModules_germ, PresheafOfModules.stalkFunctor_map_germ]
  rfl

/-- For `f` inducing, the kernel of the stalk map `𝒪_{Y,f x} → 𝒪_{X,x}` is contained in
`f.pushforwardStalkIdeal (f x)`. -/
lemma Hom.mem_pushforwardStalkIdeal_of_mem_ker (hf : IsInducing f.base) (x : X)
    (r : Y.presheaf.stalk (f.base x)) (hr : r ∈ RingHom.ker (f.stalkMap x).hom) :
    r ∈ RingHom.ker ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f.base x)).map f.c).hom := by
  haveI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat.{u}
    hf X.presheaf x
  have hinj := ((ConcreteCategory.isIso_iff_bijective
    (TopCat.Presheaf.stalkPushforward CommRingCat.{u} f.base X.presheaf x)).1 inferInstance).1
  rw [RingHom.mem_ker] at hr
  exact hinj (hr.trans (map_zero _).symm)

/-- Off the closed image of `f`, the stalks of a pushforward `f_* H` vanish. -/
lemma Hom.subsingleton_stalk_pushforward (hcl : IsClosed (Set.range f.base)) (y : Y)
    (hy : y ∉ Set.range f.base) (H : SheafOfModules.{u} X.ringSheaf) :
    Subsingleton ((Y.stalkFunctor y).obj
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H)) :=
  AddCommGrpCat.isZero_iff_subsingleton.1
    (TopCat.Sheaf.isZero_stalk_pushforwardAb f.base hcl hy ((SheafOfModules.toSheaf _).obj H))

/-- **The unit `A ⟶ f_* f^* A` is an isomorphism** if `f` is a closed embedding with surjective
stalk maps, `A` has zero stalks off `f(X)`, and each `A_{f x}` is killed by the kernel of
`𝒪_{Y,f x} → 𝒪_{X,x}`. -/
theorem Hom.isIso_pullbackModulesAdj_unit_app (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (A : SheafOfModules.{u} Y.ringSheaf)
    (h0 : ∀ y ∉ Set.range f.base, Subsingleton ((Y.stalkFunctor y).obj A))
    (hI : ∀ x, ∀ r ∈ RingHom.ker (f.stalkMap x).hom,
      ∀ m : (Y.stalkFunctor (f.base x)).obj A, r • m = 0) :
    IsIso (f.pullbackModulesAdj.unit.app A) := by
  refine isIso_of_bijective_stalkFunctor_map _ fun y ↦ ?_
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    let s := f.stalkPushforwardModules (f.pullbackModules.obj A) x
    let e := (f.pullbackModulesStalkIso x).hom.app A
    have hcomp : ∀ a,
        e (s ((Y.stalkFunctor (f.base x)).map (f.pullbackModulesAdj.unit.app A) a)) =
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app _ a := by
      intro a
      obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.val.presheaf a
      erw [PresheafOfModules.stalkFunctor_map_germ]
      have h1 := f.stalkPushforwardModules_germ (f.pullbackModules.obj A) x U hU
        ((f.pullbackModulesAdj.unit.app A).val.app (op U) t)
      exact (congrArg e h1).trans (f.pullbackModulesStalkIso_hom_app_germ_unit A U x hU t)
    have hb :=
      ModuleCat.bijective_extendRestrictScalarsAdj_unit_app_of_surjective _ (hs x) _ (hI x)
    have he : Function.Bijective e :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have hes : Function.Bijective (e ∘ s) :=
      he.comp (f.bijective_stalkPushforwardModules hf.isInducing _ x)
    refine ⟨fun a b hab ↦ hb.1 ?_, fun t ↦ ?_⟩
    · exact (hcomp a).symm.trans ((congrArg (fun m ↦ e (s m)) hab).trans (hcomp b))
    · obtain ⟨a, ha⟩ := hb.2 (e (s t))
      exact ⟨a, hes.1 ((hcomp a).trans ha)⟩
  · have h1 := h0 y hy
    have h2 := f.subsingleton_stalk_pushforward hf.isClosed_range y hy (f.pullbackModules.obj A)
    exact ⟨fun a b _ ↦ @Subsingleton.elim _ h1 a b, fun t ↦ ⟨0, @Subsingleton.elim _ h2 _ _⟩⟩

/-- **The counit `f^* f_* G ⟶ G` is an isomorphism** for `f` a closed embedding with surjective
stalk maps and `G` any sheaf of modules on `X`. -/
theorem Hom.isIso_pullbackModulesAdj_counit_app (hf : IsClosedEmbedding f.base)
    (hs : ∀ x, Function.Surjective (f.stalkMap x)) (G : SheafOfModules.{u} X.ringSheaf) :
    IsIso (f.pullbackModulesAdj.counit.app G) := by
  have hη : IsIso (f.pullbackModulesAdj.unit.app
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G)) :=
    f.isIso_pullbackModulesAdj_unit_app hf hs _
      (fun y hy ↦ f.subsingleton_stalk_pushforward hf.isClosed_range y hy G)
      (fun x r hr m ↦ f.smul_eq_zero_of_mem_pushforwardStalkIdeal G _ r
        (f.mem_pushforwardStalkIdeal_of_mem_ker hf.isInducing x r hr) m)
  have htri := f.pullbackModulesAdj.right_triangle_components G
  haveI : IsIso ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map
      (f.pullbackModulesAdj.counit.app G)) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hη (IsIso.id _) htri
  refine isIso_of_bijective_stalkFunctor_map _ fun x ↦ ?_
  have h1 : Function.Bijective ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map
        (f.pullbackModulesAdj.counit.app G))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hs1 := f.bijective_stalkPushforwardModules hf.isInducing
    (f.pullbackModules.obj ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G)) x
  have hs2 := f.bijective_stalkPushforwardModules hf.isInducing G x
  have key : (X.stalkFunctor x).map (f.pullbackModulesAdj.counit.app G) ∘
      f.stalkPushforwardModules _ x =
      f.stalkPushforwardModules G x ∘ (Y.stalkFunctor (f.base x)).map
        ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map
          (f.pullbackModulesAdj.counit.app G)) :=
    funext fun m ↦ (f.stalkPushforwardModules_naturality _ x m).symm
  have := hs2.comp h1
  rw [← key] at this
  exact (Function.Bijective.of_comp_iff _ hs1).1 this

end AlgebraicGeometry.LocallyRingedSpace

end
