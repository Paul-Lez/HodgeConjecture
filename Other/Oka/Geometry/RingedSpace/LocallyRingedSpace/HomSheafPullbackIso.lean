/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafPullback
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafStalk

/-!
# Pullback of the sheaf of homomorphisms along a flat morphism

Let `f : X ⟶ Y` be a morphism of locally ringed spaces whose stalk maps are flat, `F` a coherent
sheaf of `𝒪_Y`-modules whose pullback `f^* F` is of finite type, and `G` any sheaf of
`𝒪_Y`-modules. Then the comparison morphism `f^* 𝓗om(F, G) ⟶ 𝓗om(f^* F, f^* G)` is an
isomorphism (`AlgebraicGeometry.LocallyRingedSpace.isIso_homSheafPullbackComp`).

The proof is on stalks. Near `y = f x`, a local presentation of `F` by generators `sᵢ` and
relations `gₗ` identifies `𝓗om(F, G)_y` with the solutions of the relations in `((G_W)_y)ⁿ`; this
is an exact sequence, which stays exact after the flat base change `𝒪_{Y,y} ⟶ 𝒪_{X,x}`. On
the other side, the pulled back sections `f^* sᵢ` generate `f^* F` near `x`, so evaluation at them
embeds `𝓗om(f^* F, f^* G)_x` into `((f^* G)_{f⁻¹ W})_x)ⁿ`, and the comparison morphism is
compatible with the two evaluations
(`AlgebraicGeometry.LocallyRingedSpace.homSheafPullbackComp_comp_homSheafEval`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

section Algebra

/-- A diagram chase: `a` is bijective if it is compatible with an injective map `ι` into the kernel
of `γ`, a bijection `b`, an injective `c` and a map `ι'` which is injective with image in the
kernel of `γ'`. -/
lemma bijective_of_exact_square {M Q R M' Q' R' : Type*} [Zero R] [Zero R']
    (ι : M → Q) (γ : Q → R) (a : M → M') (b : Q → Q') (c : R → R') (ι' : M' → Q')
    (γ' : Q' → R') (hι : Function.Injective ι) (hex : ∀ q, γ q = 0 → ∃ m, ι m = q)
    (hb : Function.Bijective b) (hc : Function.Injective c) (hc0 : c 0 = 0)
    (hι' : Function.Injective ι') (hγ' : ∀ m', γ' (ι' m') = 0)
    (h1 : ∀ m, ι' (a m) = b (ι m)) (h2 : ∀ q, γ' (b q) = c (γ q)) : Function.Bijective a := by
  refine ⟨fun m₁ m₂ h ↦ hι (hb.1 ?_), fun m' ↦ ?_⟩
  · rw [← h1, ← h1, h]
  · obtain ⟨q, hq⟩ := hb.2 (ι' m')
    obtain ⟨m, hm⟩ := hex q (hc (by rw [← h2, hq, hγ', hc0]))
    exact ⟨m, hι' (by rw [h1, hm, hq])⟩

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The element `1 ⊗ m` of the extension of scalars. -/
abbrev extendScalarsOne {N : ModuleCat.{u} R} (m : N) : (ModuleCat.extendScalars φ).obj N :=
  (1 : S) ⊗ₜ[R, φ] m

/-- Two morphisms out of an extension of scalars agree if they agree on the elements `1 ⊗ m`. -/
lemma extendScalars_hom_ext {N : ModuleCat.{u} R} {Q : ModuleCat.{u} S}
    {g₁ g₂ : (ModuleCat.extendScalars φ).obj N ⟶ Q}
    (h : ∀ m : N, g₁ (extendScalarsOne φ m) = g₂ (extendScalarsOne φ m)) : g₁ = g₂ := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  ext m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h m

lemma extendScalarsOne_sum_smul {N : ModuleCat.{u} R} {n : ℕ} (c : Fin n → R) (v : Fin n → N) :
    extendScalarsOne φ (∑ i, c i • v i) = ∑ i, φ (c i) • extendScalarsOne φ (v i) := by
  refine (map_sum ((ModuleCat.extendRestrictScalarsAdj φ).unit.app N).hom _ _).trans
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact ((ModuleCat.extendRestrictScalarsAdj φ).unit.app N).hom.map_smul (c i) (v i)

/-- Two linear maps out of an extension of scalars agree if they agree on the elements
`1 ⊗ m`. -/
lemma extendScalars_linearMap_ext {N : ModuleCat.{u} R} {Q : Type*} [AddCommGroup Q] [Module S Q]
    {g₁ g₂ : (ModuleCat.extendScalars φ).obj N →ₗ[S] Q}
    (h : ∀ m : N, g₁ (extendScalarsOne φ m) = g₂ (extendScalarsOne φ m)) : g₁ = g₂ := by
  ext w
  induction w using TensorProduct.induction_on with
  | zero => exact g₁.map_zero.trans g₂.map_zero.symm
  | tmul s m =>
    have e : (show (ModuleCat.extendScalars φ).obj N from s ⊗ₜ[R, φ] m) =
        (show S from s) • extendScalarsOne φ m :=
      ((ModuleCat.ExtendScalars.smul_tmul φ (show S from s) 1 m).trans (by rw [mul_one]; rfl)).symm
    change g₁ (show (ModuleCat.extendScalars φ).obj N from s ⊗ₜ[R, φ] m) =
      g₂ (show (ModuleCat.extendScalars φ).obj N from s ⊗ₜ[R, φ] m)
    rw [e, _root_.map_smul, _root_.map_smul, h]
  | add w₁ w₂ h₁ h₂ => exact (g₁.map_add w₁ w₂).trans ((congrArg₂ (· + ·) h₁ h₂).trans
      (g₂.map_add w₁ w₂).symm)

/-- If the `vᵢ` generate `N`, then the `1 ⊗ vᵢ` generate the extension of scalars of `N`. -/
lemma exists_eq_sum_smul_unit {N : ModuleCat.{u} R} {n : ℕ} (v : Fin n → N)
    (hv : ∀ m : N, ∃ c : Fin n → R, m = ∑ i, c i • v i)
    (w : (ModuleCat.extendScalars φ).obj N) :
    ∃ c : Fin n → S, w = ∑ i, c i • extendScalarsOne φ (v i) := by
  let u : Fin n → (ModuleCat.extendScalars φ).obj N := fun i ↦ extendScalarsOne φ (v i)
  have hsmul : ∀ (c : R) (m : N), extendScalarsOne φ (c • m) =
      φ c • extendScalarsOne φ m := fun c m ↦
    ((ModuleCat.extendRestrictScalarsAdj φ).unit.app N).hom.map_smul c m
  have hunit : ∀ m : N, extendScalarsOne φ m ∈
      Submodule.span S (Set.range u) := fun m ↦ by
    obtain ⟨c, rfl⟩ := hv m
    rw [show extendScalarsOne φ (∑ i, c i • v i) = ∑ i, extendScalarsOne φ (c i • v i) from
      map_sum ((ModuleCat.extendRestrictScalarsAdj φ).unit.app N).hom _ _]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  suffices w ∈ Submodule.span S (Set.range u) from
    (Submodule.mem_span_range_iff_exists_fun S).1 this |>.imp fun c hc ↦ hc.symm
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul s m =>
    have h := Submodule.smul_mem (Submodule.span S (Set.range u)) (s : S) (hunit m)
    convert h using 1
    exact ((ModuleCat.ExtendScalars.smul_tmul φ (s : S) 1 m).trans (by rw [mul_one]; rfl)).symm
  | add w₁ w₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

/-- An additive functor between categories of modules commutes with finite products: the
projections `T(Nⁿ) ⟶ T(N)` are jointly bijective. -/
lemma bijective_map_proj (T : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [T.Additive]
    (N : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective (fun z : T.obj (ModuleCat.of R (Fin n → N)) ↦
      fun i ↦ T.map (ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin n ↦ N) i)) z) := by
  let pr : Fin n → (ModuleCat.of R (Fin n → N) ⟶ N) := fun i ↦
    ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun _ : Fin n ↦ N) i)
  let sg : Fin n → (N ⟶ ModuleCat.of R (Fin n → N)) := fun i ↦
    ModuleCat.ofHom (LinearMap.single R (fun _ : Fin n ↦ N) i)
  have hsum : ∑ i, pr i ≫ sg i = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_)
    simp only [pr, sg, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_proj, Function.eval, LinearMap.coe_single, ModuleCat.hom_id,
      LinearMap.id_coe, id_eq]
    exact Finset.univ_sum_single v
  have hps : ∀ i j, sg i ≫ pr j = if i = j then 𝟙 N else 0 := by
    intro i j
    ext v
    by_cases hij : i = j
    · subst hij
      simp [pr, sg]
    · simp [pr, sg, hij, Ne.symm hij]
  have hT : ∀ z : T.obj (ModuleCat.of R (Fin n → N)), z = ∑ i, T.map (sg i) (T.map (pr i) z) := by
    intro z
    conv_lhs => rw [← ConcreteCategory.id_apply (X := T.obj (ModuleCat.of R (Fin n → N))) z,
      ← T.map_id, ← hsum, Functor.map_sum]
    simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply, Functor.map_comp,
      ConcreteCategory.comp_apply]
  refine ⟨fun z z' h ↦ ?_, fun w ↦ ⟨∑ i, T.map (sg i) (w i), funext fun j ↦ ?_⟩⟩
  · rw [hT z, hT z']
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (T.map (sg i)) (congrFun h i)
  · change T.map (pr j) _ = _
    rw [map_sum]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hps]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp

end Algebra

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (F G : SheafOfModules.{u} Y.ringSheaf)

lemma homEquiv_homSheafPullbackComp :
    f.pullbackModulesAdj.homEquiv _ _ (homSheafPullbackComp f F G) = homSheafPullback f F G :=
  Equiv.apply_symm_apply _ _

/-- The section `f^* t` of `f^* F` over `f⁻¹ W` of a section `t` of `F` over `W`. -/
def pullbackSec {W : Opens Y.toPresheafedSpace} (t : F.val.obj (op W)) :
    (f.pullbackModules.obj F).val.obj (op ((Opens.map f.base).obj W)) :=
  (f.pullbackModulesAdj.unit.app F).val.app (op W) t

/-- **The comparison morphism is compatible with evaluation**: evaluating the pullback of a
morphism at `f^* t` is pulling back its value at `t`. -/
lemma homSheafPullbackComp_comp_homSheafEval {W : Opens Y.toPresheafedSpace}
    (t : F.val.obj (op W)) :
    homSheafPullbackComp f F G ≫ homSheafEval (f.pullbackModules.obj G) (pullbackSec f F t) =
      f.pullbackModules.map (homSheafEval G t) ≫ pullbackRestrictExtend f G W := by
  apply (f.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    homEquiv_pullbackRestrictExtend, homEquiv_homSheafPullbackComp]
  refine modHom_ext fun U h ↦ restrictExtend_ext ?_
  change restrictExtendSec ((homSheafEval (f.pullbackModules.obj G) (pullbackSec f F t)).val.app
      (op ((Opens.map f.base).obj U)) ((homSheafPullback f F G).val.app (op U) h)) =
    restrictExtendSec ((restrictExtendPush (G' := f.pullbackModules.obj G)
      (f.pullbackModulesAdj.unit.app G) W).val.app (op U) ((homSheafEval G t).val.app (op U) h))
  let h' : F ⟶ restrictExtend G U := h
  have key : (homSheafPullback f F G).val.app (op U) h = f.pullbackModules.map h' ≫
      pullbackRestrictExtend f G U := rfl
  have s2 : (f.pullbackModules.map h').val.app (op ((Opens.map f.base).obj W))
      (pullbackSec f F t) = (f.pullbackModulesAdj.unit.app (restrictExtend G U)).val.app (op W)
        (h'.val.app (op W) t) :=
    (congrArg (fun φ ↦ φ.val.app (op W) t) (f.pullbackModulesAdj.unit.naturality h')).symm
  have s3 : (pullbackRestrictExtend f G U).val.app (op ((Opens.map f.base).obj W))
      ((f.pullbackModulesAdj.unit.app (restrictExtend G U)).val.app (op W)
        (h'.val.app (op W) t)) =
      (restrictExtendPush (G' := f.pullbackModules.obj G) (f.pullbackModulesAdj.unit.app G)
        U).val.app (op W) (h'.val.app (op W) t) := by
    rw [← homEquiv_pullbackRestrictExtend, Adjunction.homEquiv_unit]
    rfl
  rw [restrictExtendSec_homSheafEval, restrictExtendPush_app]
  change modRes (restrictExtendSec ((pullbackRestrictExtend f G U).val.app _
    ((f.pullbackModules.map h').val.app _ (pullbackSec f F t)))) _ _ =
    (f.pullbackModulesAdj.unit.app G).val.app (op (U ⊓ W))
      (modRes (restrictExtendSec (h'.val.app (op W) t)) (U ⊓ W) (by order))
  rw [s2, s3, restrictExtendPush_app]
  have := modHom_modRes (f.pullbackModulesAdj.unit.app G) (show U ⊓ W ≤ W ⊓ U by order)
    (restrictExtendSec (h'.val.app (op W) t))
  exact this.symm

section Generation

variable {f F}

lemma pullbackSec_sum_smul {W : Opens Y.toPresheafedSpace} {n : ℕ}
    (a : Fin n → Y.presheaf.obj (op W)) (t : Fin n → F.val.obj (op W)) :
    pullbackSec f F (∑ i, a i • t i) = ∑ i, (show X.presheaf.obj (op ((Opens.map f.base).obj W))
      from f.c.app (op W) (a i)) • pullbackSec f F (t i) := by
  refine (map_sum ((f.pullbackModulesAdj.unit.app F).val.app (op W)).hom _ _).trans
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact modHom_smul (f.pullbackModulesAdj.unit.app F) (a i) (t i)

lemma pullbackSec_zero {W : Opens Y.toPresheafedSpace} :
    pullbackSec f F (0 : F.val.obj (op W)) = 0 :=
  map_zero _

/-- The germs of generators of `F` near `f x` generate the stalk of `f^* F` at `x`. -/
lemma exists_eq_sum_smul_mgerm_pullbackSec {W : Opens Y.toPresheafedSpace}
    (P : LocalGenerators F W) (x : X) (hx : f.base x ∈ W)
    (z : (X.stalkFunctor x).obj (f.pullbackModules.obj F)) :
    ∃ a : Fin P.n → X.presheaf.stalk x, z = ∑ i, a i •
      mgerm (f.pullbackModules.obj F) ((Opens.map f.base).obj W) x hx
        (pullbackSec f F (P.s i)) := by
  have hv : ∀ m : (Y.stalkFunctor (f.base x)).obj F, ∃ c : Fin P.n → Y.presheaf.stalk (f.base x),
      m = ∑ i, c i • mgerm F W (f.base x) hx (P.s i) := by
    intro m
    obtain ⟨U, hU, t, rfl⟩ := exists_mgerm_eq (f.base x) m
    obtain ⟨W'', hW'', hy'', c, hc⟩ :=
      P.gen (U ⊓ W) inf_le_right (modRes t (U ⊓ W) inf_le_left) (f.base x) ⟨hU, hx⟩
    refine ⟨fun i ↦ Y.presheaf.germ W'' (f.base x) hy'' (c i), ?_⟩
    rw [← mgerm_modRes (hW''.trans inf_le_left) (f.base x) hy'',
      show modRes t W'' (hW''.trans inf_le_left) =
        modRes (modRes t (U ⊓ W) inf_le_left) W'' hW'' from (modRes_res _ _ _).symm, hc,
      mgerm_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mgerm_smul, mgerm_modRes]
  let Ψ := f.pullbackModulesStalkIso x
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_unit (f.stalkMap x).hom
    (fun i ↦ mgerm F W (f.base x) hx (P.s i)) hv (Ψ.hom.app F z)
  refine ⟨a, ?_⟩
  have hz : z = Ψ.inv.app F (Ψ.hom.app F z) := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app]
    rfl
  rw [hz, ha]
  refine (map_sum (Ψ.inv.app F).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  refine ((Ψ.inv.app F).hom.map_smul _ _).trans ?_
  congr 1
  have e : extendScalarsOne (f.stalkMap x).hom (mgerm F W (f.base x) hx (P.s i)) =
      Ψ.hom.app F (mgerm (f.pullbackModules.obj F) ((Opens.map f.base).obj W) x hx
        (pullbackSec f F (P.s i))) :=
    (f.pullbackModulesStalkIso_hom_app_germ_unit F W x hx (P.s i)).symm
  refine (congrArg (Ψ.inv.app F).hom e).trans ?_
  exact (Ψ.app F).hom_inv_id_apply _

end Generation

section LocalGeneration

variable {Z : LocallyRingedSpace.{u}}

lemma modRes_sum_smul_of {N : SheafOfModules.{u} Z.ringSheaf} {V V' : Opens Z.toPresheafedSpace}
    (h : V' ≤ V) {n : ℕ} (c : Fin n → Z.presheaf.obj (op V)) (t : Fin n → N.val.obj (op V)) :
    modRes (∑ i, c i • t i) V' h =
      ∑ i, TopCat.Presheaf.restrictOpen (c i) V' h • modRes (t i) V' h := by
  rw [modRes_sum]
  exact Finset.sum_congr rfl fun i _ ↦ modRes_smul h (c i) (t i)

/-- If the germs at `x` of sections `tᵢ` of a sheaf of finite type generate its stalk, then the
`tᵢ` locally generate the sheaf near `x`. -/
lemma exists_isLocallyGenerated_of_span (N : SheafOfModules.{u} Z.ringSheaf) [N.IsFiniteType]
    {W : Opens Z.toPresheafedSpace} {n : ℕ} (t : Fin n → N.val.obj (op W)) (x : Z) (hx : x ∈ W)
    (hspan : ∀ z : (Z.stalkFunctor x).obj N, ∃ a : Fin n → Z.presheaf.stalk x,
      z = ∑ i, a i • mgerm N W x hx (t i)) :
    ∃ (V₀ : Opens Z.toPresheafedSpace) (hV₀ : V₀ ≤ W), x ∈ V₀ ∧
      ∀ (W' : Opens Z.toPresheafedSpace) (hW' : W' ≤ V₀) (t' : N.val.obj (op W')) (y : Z),
        y ∈ W' → ∃ (W'' : Opens Z.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin n → Z.presheaf.obj (op W''),
            modRes t' W'' hW'' = ∑ i, c i • modRes (t i) W'' (hW''.trans (hW'.trans hV₀)) := by
  obtain ⟨W₀, k, u, hxW₀, hgenu⟩ : ∃ (W₀ : Opens Z.toPresheafedSpace) (k : ℕ)
      (u : Fin k → N.val.obj (op W₀)), x ∈ W₀ ∧ ∀ (W' : Opens Z.toPresheafedSpace)
      (hW' : W' ≤ W₀) (t : N.val.obj (op W')), ∀ y ∈ W',
        ∃ (W'' : Opens Z.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin k → Z.presheaf.obj (op W''),
            modRes t W'' hW'' = ∑ l, c l • modRes (u l) W'' (hW''.trans hW') :=
    isLocallyFinitelyGeneratedModule_of_isFiniteType N x
  let Q : Fin k → Opens Z.toPresheafedSpace → Prop := fun j V ↦ ∃ hV : V ≤ W₀ ⊓ W,
    ∃ A : Fin n → Z.presheaf.obj (op V), modRes (u j) V (hV.trans inf_le_left) =
      ∑ i, A i • modRes (t i) V (hV.trans inf_le_right)
  have hQ : ∀ j V V', V' ≤ V → Q j V → Q j V' := by
    rintro j V V' hle ⟨hV, A, hA⟩
    refine ⟨hle.trans hV, fun i ↦ TopCat.Presheaf.restrictOpen (A i) V' hle, ?_⟩
    have := congrArg (fun z ↦ modRes (N := N) z V' hle) hA
    simp only [modRes_res, modRes_sum_smul_of] at this
    exact this
  have hj : ∀ j, ∃ V : Opens Z, x ∈ V ∧ Q j V := by
    intro j
    obtain ⟨a, ha⟩ := hspan (mgerm N W₀ x hxW₀ (u j))
    choose V hV A hA using fun i ↦ TopCat.Presheaf.exists_germ_eq Z.presheaf (a i)
    obtain ⟨V', hxV', hV'⟩ : ∃ V' : Opens Z.toPresheafedSpace, x ∈ V' ∧ ∀ i, V' ≤ V i :=
      exists_open_forall Z x (fun i V'' ↦ V'' ≤ V i) (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂)
        (fun i ↦ ⟨V i, hV i, le_rfl⟩)
    have hle : V' ⊓ (W₀ ⊓ W) ≤ W₀ ⊓ W := inf_le_right
    have hx'' : x ∈ V' ⊓ (W₀ ⊓ W) := ⟨hxV', hxW₀, hx⟩
    have hgerm : mgerm N (V' ⊓ (W₀ ⊓ W)) x hx'' (modRes (u j) _ (hle.trans inf_le_left)) =
        mgerm N (V' ⊓ (W₀ ⊓ W)) x hx'' (∑ i, TopCat.Presheaf.restrictOpen (A i) (V' ⊓ (W₀ ⊓ W))
          (inf_le_left.trans (hV' i)) • modRes (t i) (V' ⊓ (W₀ ⊓ W)) (hle.trans inf_le_right)) := by
      rw [mgerm_modRes, ha, mgerm_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mgerm_smul, mgerm_modRes, ← hA i]
      congr 1
      exact (TopCat.Presheaf.germ_res_apply Z.presheaf _ x hx'' _).symm
    obtain ⟨V₃, h₃, h₃', hx₃, e⟩ := exists_modRes_eq_of_mgerm_eq x hx'' hx'' _ _ hgerm
    refine ⟨V₃, hx₃, h₃.trans hle, fun i ↦ TopCat.Presheaf.restrictOpen
      (TopCat.Presheaf.restrictOpen (A i) (V' ⊓ (W₀ ⊓ W)) (inf_le_left.trans (hV' i))) V₃ h₃, ?_⟩
    rw [modRes_sum_smul_of] at e
    simp only [modRes_res] at e
    exact e
  obtain ⟨V₀, hxV₀, hV₀⟩ : ∃ V₀ : Opens Z.toPresheafedSpace, x ∈ V₀ ∧ ∀ j, Q j V₀ :=
    exists_open_forall Z x Q hQ hj
  have hV₁ : ∀ j, Q j (V₀ ⊓ (W₀ ⊓ W)) := fun j ↦ hQ j _ _ inf_le_left (hV₀ j)
  choose hV A hA using hV₁
  refine ⟨V₀ ⊓ (W₀ ⊓ W), inf_le_right.trans inf_le_right, ⟨hxV₀, hxW₀, hx⟩,
    fun W' hW' t' y hy ↦ ?_⟩
  obtain ⟨W₃, h₃, hy₃, c, hc⟩ : ∃ (W₃ : Opens Z.toPresheafedSpace) (h₃ : W₃ ≤ W'), y ∈ W₃ ∧
      ∃ c : Fin k → Z.presheaf.obj (op W₃), modRes t' W₃ h₃ = ∑ l, c l •
        modRes (u l) W₃ (h₃.trans (hW'.trans (inf_le_right.trans inf_le_left))) :=
    hgenu W' (hW'.trans (inf_le_right.trans inf_le_left)) t' y hy
  refine ⟨W₃, h₃, hy₃, fun i ↦ ∑ j, c j * TopCat.Presheaf.restrictOpen (A j i) W₃
    (h₃.trans hW'), ?_⟩
  have hu : ∀ j, modRes (u j) W₃ (h₃.trans (hW'.trans (inf_le_right.trans inf_le_left))) =
      ∑ i, TopCat.Presheaf.restrictOpen (A j i) W₃ (h₃.trans hW') •
        modRes (t i) W₃ (h₃.trans (hW'.trans (inf_le_right.trans inf_le_right))) := by
    intro j
    have := congrArg (fun z ↦ modRes (N := N) z W₃ (h₃.trans hW')) (hA j)
    simp only [modRes_res, modRes_sum_smul_of] at this
    exact this
  refine hc.trans ?_
  simp_rw [hu,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end LocalGeneration

section Main

variable {f G}

lemma isIso_stalk_pullbackRestrictExtend {W : Opens Y.toPresheafedSpace} (x : X)
    (hx : f.base x ∈ W) : IsIso ((X.stalkFunctor x).map (pullbackRestrictExtend f G W)) := by
  have h1 : IsIso ((X.stalkFunctor x).map
      (toRestrictExtend (f.pullbackModules.obj G) ((Opens.map f.base).obj W))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalk_toRestrictExtend _ _ x hx)
  have h2 : IsIso ((X.stalkFunctor x).map (f.pullbackModules.map (toRestrictExtend G W))) := by
    have h3 : IsIso ((Y.stalkFunctor (f.base x)).map (toRestrictExtend G W)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalk_toRestrictExtend _ _ _ hx)
    exact (NatIso.isIso_map_iff (f.pullbackModulesStalkIso x) (toRestrictExtend G W)).2
      (Functor.map_isIso (ModuleCat.extendScalars (f.stalkMap x).hom) _)
  have e := congrArg (X.stalkFunctor x).map (pullbackModules_map_toRestrictExtend_comp f G W)
  rw [Functor.map_comp] at e
  have h4 : IsIso ((X.stalkFunctor x).map (f.pullbackModules.map (toRestrictExtend G W)) ≫
      (X.stalkFunctor x).map (pullbackRestrictExtend f G W)) := by
    rw [e]
    exact h1
  exact IsIso.of_isIso_comp_left ((X.stalkFunctor x).map (f.pullbackModules.map
    (toRestrictExtend G W))) _


variable (f G) in
/-- **The comparison morphism `f^* 𝓗om(F, G) ⟶ 𝓗om(f^* F, f^* G)` is bijective on the stalk at
`x`**, if `f` is flat at `x`, `F` has a local presentation near `f x` and `f^* F` is of finite
type. -/
theorem bijective_stalk_homSheafPullbackComp [(f.pullbackModules.obj F).IsFiniteType]
    {W : Opens Y.toPresheafedSpace} (P : LocalPresentation F W) (x : X) (hx : f.base x ∈ W)
    (hflat : (f.stalkMap x).hom.Flat) :
    Function.Bijective ((X.stalkFunctor x).map (homSheafPullbackComp f F G)) := by
  set y := f.base x
  let T := ModuleCat.extendScalars (f.stalkMap x).hom
  haveI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  haveI : PreservesFiniteLimits T := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let Ψ := f.pullbackModulesStalkIso x
  let H := homSheaf F G
  let K := restrictExtend G W
  let W' := (Opens.map f.base).obj W
  have hx' : x ∈ W' := hx
  let t' : Fin P.n → (f.pullbackModules.obj F).val.obj (op W') := fun i ↦ pullbackSec f F (P.s i)
  let g' : Fin P.m → Fin P.n → X.presheaf.obj (op W') := fun l i ↦ f.c.app (op W) (P.g l i)
  -- the exact sequence on `Y`
  let ι := evalStalk G P.s y
  let γ := relStalk G y P.g hx
  have hι : Function.Injective ι :=
    evalStalk_injective G P.s y le_rfl hx fun W₁ hW₁ t₁ y₁ hy₁ ↦ P.gen W₁ hW₁ t₁ y₁ hy₁
  have hγι : γ.comp ι = 0 := LinearMap.ext (relStalk_evalStalk G P.s y P.g hx P.rel)
  let S₀ := ShortComplex.moduleCatMk ι γ hγι
  have hS₀ : S₀.Exact :=
    (ShortComplex.moduleCat_exact_iff S₀).2 fun v hv ↦ P.exists_evalStalk_eq G y hx v hv
  haveI : Mono S₀.f := (ModuleCat.mono_iff_injective _).2 hι
  have hTι : Function.Injective (T.map S₀.f) := (ModuleCat.mono_iff_injective _).1 inferInstance
  have hTex : ∀ q, T.map S₀.g q = 0 → ∃ z, T.map S₀.f z = q :=
    (ShortComplex.moduleCat_exact_iff _).1 (hS₀.map T)
  -- the comparison of the targets
  let βc : T.obj ((Y.stalkFunctor y).obj K) ⟶
      (X.stalkFunctor x).obj (restrictExtend (f.pullbackModules.obj G) W') :=
    Ψ.inv.app K ≫ (X.stalkFunctor x).map (pullbackRestrictExtend f G W)
  have hβ : Function.Bijective βc := by
    have h₁ : IsIso (Ψ.inv.app K) := (Ψ.app K).isIso_inv
    have h₂ : IsIso ((X.stalkFunctor x).map (pullbackRestrictExtend f G W)) :=
      isIso_stalk_pullbackRestrictExtend x hx
    have h₃ : IsIso βc := @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
    exact ConcreteCategory.bijective_of_isIso βc
  let prc : ∀ (k : ℕ) (_ : Fin k), ModuleCat.of (Y.presheaf.stalk y)
      (Fin k → (Y.stalkFunctor y).obj K) ⟶ (Y.stalkFunctor y).obj K := fun k i ↦
    ModuleCat.ofHom (LinearMap.proj (R := Y.presheaf.stalk y)
      (φ := fun _ : Fin k ↦ (Y.stalkFunctor y).obj K) i)
  let b : ∀ k : ℕ, T.obj (ModuleCat.of (Y.presheaf.stalk y) (Fin k → (Y.stalkFunctor y).obj K)) →
      (Fin k → (X.stalkFunctor x).obj (restrictExtend (f.pullbackModules.obj G) W')) :=
    fun k q i ↦ βc (T.map (prc k i) q)
  have hb : ∀ k, Function.Bijective (b k) := fun k ↦
    (show Function.Bijective (fun v : Fin k → _ ↦ fun i ↦ βc (v i)) from
      ⟨hβ.1.comp_left, hβ.2.comp_left⟩).comp (bijective_map_proj T _ k)
  -- the evaluation on `X`
  let ι' := evalStalk (f.pullbackModules.obj G) t' x
  let γ' := relStalk (f.pullbackModules.obj G) x g' hx'
  have hι' : Function.Injective ι' := by
    obtain ⟨V₀, hV₀, hxV₀, hgen⟩ := exists_isLocallyGenerated_of_span (f.pullbackModules.obj F)
      t' x hx' (exists_eq_sum_smul_mgerm_pullbackSec P.toLocalGenerators x hx)
    exact evalStalk_injective (f.pullbackModules.obj G) t' x hV₀ hxV₀ hgen
  have hγ' : ∀ m', γ' (ι' m') = 0 := relStalk_evalStalk (f.pullbackModules.obj G) t' x g' hx'
    fun l ↦ by
      change ∑ i, _ • pullbackSec f F (P.s i) = 0
      rw [← pullbackSec_sum_smul, P.rel, pullbackSec_zero]
  let a := fun z ↦ (X.stalkFunctor x).map (homSheafPullbackComp f F G) (Ψ.inv.app H z)
  have h1 : ∀ z, ι' (a z) = b P.n (T.map S₀.f z) := by
    intro z
    funext i
    have eKI := congrArg (fun φ ↦ (X.stalkFunctor x).map φ (Ψ.inv.app H z))
      (homSheafPullbackComp_comp_homSheafEval f F G (P.s i))
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at eKI
    have eN := congrArg (fun φ ↦ φ z) (Ψ.inv.naturality (homSheafEval G (P.s i)))
    simp only [ConcreteCategory.comp_apply, Functor.comp_map] at eN
    change (X.stalkFunctor x).map (homSheafEval _ (t' i))
      ((X.stalkFunctor x).map (homSheafPullbackComp f F G) (Ψ.inv.app H z)) =
      βc (T.map (prc P.n i) (T.map S₀.f z))
    rw [eKI]
    have hpr : S₀.f ≫ prc P.n i = (Y.stalkFunctor y).map (homSheafEval G (P.s i)) :=
      ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
    have eT : T.map (prc P.n i) (T.map S₀.f z) =
        T.map ((Y.stalkFunctor y).map (homSheafEval G (P.s i))) z := by
      rw [← hpr]
      exact (ConcreteCategory.congr_hom (T.map_comp S₀.f (prc P.n i)) z).symm
    change _ = (X.stalkFunctor x).map (pullbackRestrictExtend f G W)
      (Ψ.inv.app K (T.map (prc P.n i) (T.map S₀.f z)))
    rw [eT]
    congr 1
    exact eN.symm
  have h2 : ∀ q, γ' (b P.n q) = b P.m (T.map S₀.g q) := by
    let L₁ : T.obj S₀.X₂ →ₗ[X.presheaf.stalk x]
        (Fin P.m → (X.stalkFunctor x).obj (restrictExtend (f.pullbackModules.obj G) W')) :=
      γ' ∘ₗ LinearMap.pi (fun i ↦ βc.hom ∘ₗ (T.map (prc P.n i)).hom)
    let L₂ : T.obj S₀.X₂ →ₗ[X.presheaf.stalk x]
        (Fin P.m → (X.stalkFunctor x).obj (restrictExtend (f.pullbackModules.obj G) W')) :=
      LinearMap.pi (fun l ↦ βc.hom ∘ₗ (T.map (prc P.m l)).hom) ∘ₗ (T.map S₀.g).hom
    have hL : L₁ = L₂ := by
      refine extendScalars_linearMap_ext _ fun v ↦ funext fun l ↦ ?_
      change relStalk (f.pullbackModules.obj G) x g' hx'
        (fun i ↦ βc (extendScalarsOne _ (v i))) l = βc (extendScalarsOne _ (γ v l))
      rw [relStalk_apply, relStalk_apply, extendScalarsOne_sum_smul, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [_root_.map_smul]
      congr 1
      exact (stalkMap_germ_apply f W x hx (P.g l i)).symm
    exact fun q ↦ LinearMap.congr_fun hL q
  have hc0 : b P.m 0 = 0 := funext fun l ↦ by simp [b]
  have ha := bijective_of_exact_square (T.map S₀.f) (T.map S₀.g) a (b P.n) (b P.m) ι' γ' hTι
    hTex (hb P.n) (hb P.m).1 hc0 hι' hγ' h1 h2
  have hcomp : ((X.stalkFunctor x).map (homSheafPullbackComp f F G) : _ → _) =
      a ∘ (Ψ.hom.app H) := by
    funext z
    simp only [a, Function.comp_apply]
    exact congrArg _ ((Ψ.app H).hom_inv_id_apply z).symm
  rw [hcomp]
  exact ha.comp (ConcreteCategory.bijective_of_isIso (Ψ.app H).hom)

variable (f G) in
/-- **Pullback along a flat morphism commutes with `𝓗om` out of a coherent sheaf**: if the stalk
maps of `f` are flat, `F` is coherent and `f^* F` is of finite type, the comparison morphism
`f^* 𝓗om(F, G) ⟶ 𝓗om(f^* F, f^* G)` is an isomorphism. -/
theorem isIso_homSheafPullbackComp (hflat : ∀ x : X, (f.stalkMap x).hom.Flat) [F.IsCoherent]
    [(f.pullbackModules.obj F).IsFiniteType] : IsIso (homSheafPullbackComp f F G) :=
  isIso_of_bijective_stalkFunctor_map _ fun x ↦ by
    obtain ⟨W, hW, ⟨P⟩⟩ := exists_localPresentation F (f.base x)
    exact bijective_stalk_homSheafPullbackComp f F G P x hW (hflat x)

end Main

end AlgebraicGeometry.LocallyRingedSpace

end
