/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafLocal
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentPushforwardClosedEmbedding

/-!
# Stalks of the sheaf of homomorphisms

Let `F` be a sheaf of `𝒪_Y`-modules and `t₁, …, tₙ` sections of `F` over `W`. Evaluating at the
`tᵢ` gives an `𝒪_{Y,y}`-linear map on stalks at `y ∈ W`
(`AlgebraicGeometry.LocallyRingedSpace.evalStalk`)

`𝓗om(F, G)_y ⟶ ((G_W)_y)ⁿ`.

It is injective if the `tᵢ` locally generate `F` near `y`
(`AlgebraicGeometry.LocallyRingedSpace.evalStalk_injective`), it lands in the solutions of any
relations between the `tᵢ` (`AlgebraicGeometry.LocallyRingedSpace.relStalk_evalStalk`), and if
the `tᵢ` are the generators of a local presentation, then every solution of the relations is in
its image (`AlgebraicGeometry.LocallyRingedSpace.LocalPresentation.exists_evalStalk_eq`).
We also show that `N ⟶ N_U` is bijective on stalks at points of `U`
(`AlgebraicGeometry.LocallyRingedSpace.bijective_stalk_toRestrictExtend`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

section Germ

variable (N : SheafOfModules.{u} Y.ringSheaf)

/-- The germ at `y` of a section of a sheaf of modules, as an element of the stalk. -/
abbrev mgerm (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U) (x : N.val.obj (op U)) :
    (Y.stalkFunctor y).obj N :=
  TopCat.Presheaf.germ N.val.presheaf U y hy x

variable {N}

lemma stalkFunctor_map_mgerm {N' : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ N')
    (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U) (x : N.val.obj (op U)) :
    (Y.stalkFunctor y).map φ (mgerm N U y hy x) = mgerm N' U y hy (φ.val.app (op U) x) :=
  PresheafOfModules.stalkFunctor_map_germ y N.val N'.val φ.val U hy x

lemma mgerm_modRes {U V : Opens Y.toPresheafedSpace} (h : V ≤ U) (y : Y) (hy : y ∈ V)
    (x : N.val.obj (op U)) : mgerm N V y hy (modRes x V h) = mgerm N U y (h hy) x :=
  TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE h) y hy x

lemma mgerm_add (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U)
    (x x' : N.val.obj (op U)) : mgerm N U y hy (x + x') = mgerm N U y hy x + mgerm N U y hy x' :=
  map_add _ _ _

lemma mgerm_zero (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U) :
    mgerm N U y hy 0 = 0 :=
  map_zero _

lemma mgerm_sum (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U) {ι : Type*}
    (s : Finset ι) (x : ι → N.val.obj (op U)) :
    mgerm N U y hy (∑ i ∈ s, x i) = ∑ i ∈ s, mgerm N U y hy (x i) :=
  map_sum (TopCat.Presheaf.germ N.val.presheaf U y hy).hom x s

lemma mgerm_smul (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U)
    (r : Y.presheaf.obj (op U)) (x : N.val.obj (op U)) :
    mgerm N U y hy (r • x) = Y.presheaf.germ U y hy r • mgerm N U y hy x :=
  PresheafOfModules.germ_smul N.val y U hy r x

lemma exists_mgerm_eq (y : Y) (z : (Y.stalkFunctor y).obj N) :
    ∃ (U : Opens Y.toPresheafedSpace) (hy : y ∈ U) (x : N.val.obj (op U)), mgerm N U y hy x = z :=
  TopCat.Presheaf.exists_germ_eq N.val.presheaf z

lemma exists_modRes_eq_of_mgerm_eq {U V : Opens Y.toPresheafedSpace} (y : Y) (hU : y ∈ U)
    (hV : y ∈ V) (x : N.val.obj (op U)) (x' : N.val.obj (op V))
    (h : mgerm N U y hU x = mgerm N V y hV x') :
    ∃ (W : Opens Y.toPresheafedSpace) (hWU : W ≤ U) (hWV : W ≤ V), y ∈ W ∧
      modRes x W hWU = modRes x' W hWV := by
  obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq N.val.presheaf y hU hV x x' h
  exact ⟨W, leOfHom iU, leOfHom iV, hW, e⟩

lemma exists_modRes_eq_zero_of_mgerm_eq_zero {U : Opens Y.toPresheafedSpace} (y : Y)
    (hU : y ∈ U) (x : N.val.obj (op U)) (h : mgerm N U y hU x = 0) :
    ∃ (W : Opens Y.toPresheafedSpace) (hWU : W ≤ U), y ∈ W ∧ modRes x W hWU = 0 := by
  obtain ⟨W, hWU, hWU', hW, he⟩ := exists_modRes_eq_of_mgerm_eq y hU hU x 0
    (h.trans (mgerm_zero U y hU).symm)
  exact ⟨W, hWU, hW, he.trans (modRes_zero _)⟩

end Germ

/-- **`N ⟶ N_U` is bijective on stalks at points of `U`.** -/
lemma bijective_stalk_toRestrictExtend (N : SheafOfModules.{u} Y.ringSheaf)
    (U : Opens Y.toPresheafedSpace) (y : Y) (hy : y ∈ U) :
    Function.Bijective ((Y.stalkFunctor y).map (toRestrictExtend N U)) := by
  constructor
  · intro a b hab
    obtain ⟨V, hV, x, rfl⟩ := exists_mgerm_eq y a
    obtain ⟨V', hV', x', rfl⟩ := exists_mgerm_eq y b
    rw [stalkFunctor_map_mgerm, stalkFunctor_map_mgerm] at hab
    obtain ⟨V₀, h₀, h₀', hy₀, e⟩ := exists_modRes_eq_of_mgerm_eq y hV hV' _ _ hab
    have e' := congrArg (fun z ↦ mgerm N (V₀ ⊓ U) y ⟨hy₀, hy⟩ (restrictExtendSec z)) e
    simp only [restrictExtendSec_modRes, restrictExtendSec_toRestrictExtend, modRes_res,
      mgerm_modRes] at e'
    exact e'
  · intro b
    obtain ⟨V, hV, x, rfl⟩ := exists_mgerm_eq y b
    refine ⟨mgerm N (V ⊓ U) y ⟨hV, hy⟩ (restrictExtendSec x), ?_⟩
    rw [stalkFunctor_map_mgerm, ← mgerm_modRes (inf_le_left : V ⊓ U ≤ V) y ⟨hV, hy⟩]
    congr 1

lemma stalkFunctor_map_zero_apply {N N' : SheafOfModules.{u} Y.ringSheaf} (y : Y)
    (z : (Y.stalkFunctor y).obj N) : (Y.stalkFunctor y).map (0 : N ⟶ N') z = 0 := by
  obtain ⟨V, hV, x, rfl⟩ := exists_mgerm_eq y z
  rw [stalkFunctor_map_mgerm]
  exact mgerm_zero V y hV

/-- `restrictExtendSec` as an additive map. -/
def restrictExtendSecHom (N : SheafOfModules.{u} Y.ringSheaf) (U W : Opens Y.toPresheafedSpace) :
    (restrictExtend N U).val.obj (op W) →+ N.val.obj (op (W ⊓ U)) where
  toFun := restrictExtendSec
  map_zero' := rfl
  map_add' _ _ := rfl

lemma restrictExtendSec_sum {N : SheafOfModules.{u} Y.ringSheaf} {U W : Opens Y.toPresheafedSpace}
    {ι : Type*} (s : Finset ι) (x : ι → (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec (∑ i ∈ s, x i) = ∑ i ∈ s, restrictExtendSec (x i) :=
  map_sum (restrictExtendSecHom N U W) x s

/-- On stalks at points of `W`, multiplication by `a` on `N_W` is multiplication by the germ
of `a`. -/
lemma stalkFunctor_map_restrictExtendSMul (N : SheafOfModules.{u} Y.ringSheaf)
    {W : Opens Y.toPresheafedSpace} (a : Y.presheaf.obj (op W)) (y : Y) (hy : y ∈ W)
    (z : (Y.stalkFunctor y).obj (restrictExtend N W)) :
    (Y.stalkFunctor y).map (restrictExtendSMul N W a) z = Y.presheaf.germ W y hy a • z := by
  obtain ⟨V, hV, x, rfl⟩ := exists_mgerm_eq y z
  rw [stalkFunctor_map_mgerm, ← mgerm_modRes (inf_le_left : V ⊓ W ≤ V) y ⟨hV, hy⟩,
    ← mgerm_modRes (inf_le_left : V ⊓ W ≤ V) y ⟨hV, hy⟩ x,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (inf_le_right : V ⊓ W ≤ W)) y ⟨hV, hy⟩ a,
    ← mgerm_smul]
  congr 1
  refine restrictExtend_ext ?_
  rw [restrictExtendSec_modRes, restrictExtendSec_restrictExtendSMul, restrictExtendSec_smul,
    restrictExtendSec_modRes, modRes_smul, yres_res]
  erw [yres_res]

variable {F : SheafOfModules.{u} Y.ringSheaf} (G : SheafOfModules.{u} Y.ringSheaf)
  {W : Opens Y.toPresheafedSpace}

lemma homSheafEval_zero : homSheafEval G (0 : F.val.obj (op W)) = 0 := by
  refine modHom_ext fun U h ↦ restrictExtend_ext ?_
  rw [restrictExtendSec_homSheafEval, map_zero]
  exact modRes_zero _

/-- Evaluation at a linear combination. -/
lemma homSheafEval_sum_smul_app {n : ℕ} (a : Fin n → Y.presheaf.obj (op W))
    (t : Fin n → F.val.obj (op W)) (U : Opens Y.toPresheafedSpace)
    (h : (homSheaf F G).val.obj (op U)) :
    (homSheafEval G (∑ i, a i • t i)).val.app (op U) h =
      ∑ i, (restrictExtendSMul G W (a i)).val.app (op U)
        ((homSheafEval G (t i)).val.app (op U) h) := by
  refine restrictExtend_ext ?_
  rw [restrictExtendSec_homSheafEval, map_sum, restrictExtendSec_sum, restrictExtendSec_sum,
    modRes_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [modHom_smul, restrictExtendSec_smul, modRes_smul, restrictExtendSec_restrictExtendSMul,
    restrictExtendSec_homSheafEval, yres_res]

lemma stalkFunctor_map_homSheafEval_sum_smul {n : ℕ} (a : Fin n → Y.presheaf.obj (op W))
    (t : Fin n → F.val.obj (op W)) (y : Y) (hy : y ∈ W)
    (z : (Y.stalkFunctor y).obj (homSheaf F G)) :
    (Y.stalkFunctor y).map (homSheafEval G (∑ i, a i • t i)) z =
      ∑ i, Y.presheaf.germ W y hy (a i) • (Y.stalkFunctor y).map (homSheafEval G (t i)) z := by
  obtain ⟨U, hU, h, rfl⟩ := exists_mgerm_eq y z
  rw [stalkFunctor_map_mgerm, homSheafEval_sum_smul_app, mgerm_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← stalkFunctor_map_mgerm, stalkFunctor_map_restrictExtendSMul _ _ _ hy,
    stalkFunctor_map_mgerm]

variable {n : ℕ} (t : Fin n → F.val.obj (op W)) (y : Y)

/-- **Evaluation at the `tᵢ` on stalks**: `𝓗om(F, G)_y ⟶ ((G_W)_y)ⁿ`. -/
def evalStalk :
    (Y.stalkFunctor y).obj (homSheaf F G) →ₗ[Y.presheaf.stalk y]
      (Fin n → (Y.stalkFunctor y).obj (restrictExtend G W)) :=
  LinearMap.pi fun i ↦ ((Y.stalkFunctor y).map (homSheafEval G (t i))).hom

lemma evalStalk_apply (z : (Y.stalkFunctor y).obj (homSheaf F G)) (i : Fin n) :
    evalStalk G t y z i = (Y.stalkFunctor y).map (homSheafEval G (t i)) z :=
  rfl

variable {m : ℕ} (g : Fin m → Fin n → Y.presheaf.obj (op W)) (hy : y ∈ W)

/-- The relations `v ↦ (∑ᵢ gₗᵢ vᵢ)ₗ` on `((G_W)_y)ⁿ`. -/
def relStalk :
    (Fin n → (Y.stalkFunctor y).obj (restrictExtend G W)) →ₗ[Y.presheaf.stalk y]
      (Fin m → (Y.stalkFunctor y).obj (restrictExtend G W)) :=
  LinearMap.pi fun l ↦ ∑ i, Y.presheaf.germ W y hy (g l i) • LinearMap.proj i

lemma relStalk_apply (v : Fin n → (Y.stalkFunctor y).obj (restrictExtend G W)) (l : Fin m) :
    relStalk G y g hy v l = ∑ i, Y.presheaf.germ W y hy (g l i) • v i := by
  simp [relStalk]

/-- **Evaluations satisfy the relations between the `tᵢ`.** -/
lemma relStalk_evalStalk (hrel : ∀ l, ∑ i, g l i • t i = 0)
    (z : (Y.stalkFunctor y).obj (homSheaf F G)) :
    relStalk G y g hy (evalStalk G t y z) = 0 := by
  funext l
  rw [relStalk_apply]
  simp only [evalStalk_apply]
  rw [← stalkFunctor_map_homSheafEval_sum_smul, hrel l, homSheafEval_zero,
    stalkFunctor_map_zero_apply]
  rfl

omit hy in
/-- **Evaluation at local generators is injective on stalks.** -/
lemma evalStalk_injective {V₀ : Opens Y.toPresheafedSpace} (hV₀ : V₀ ≤ W) (hy₀ : y ∈ V₀)
    (hgen : ∀ (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ V₀) (t' : F.val.obj (op W')) (y' : Y),
      y' ∈ W' → ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y' ∈ W'' ∧
        ∃ c : Fin n → Y.presheaf.obj (op W''),
          modRes t' W'' hW'' = ∑ i, c i • modRes (t i) W'' (hW''.trans (hW'.trans hV₀))) :
    Function.Injective (evalStalk G t y) := by
  let P : LocalGenerators F V₀ := ⟨n, fun i ↦ modRes (t i) V₀ hV₀, fun W' hW' t' y' hy' ↦ by
    obtain ⟨W'', hW'', hy'', c, hc⟩ := hgen W' hW' t' y' hy'
    exact ⟨W'', hW'', hy'', c, hc.trans (by simp only [modRes_res])⟩⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨U, hU, h, rfl⟩ := exists_mgerm_eq y z
  have hz' : ∀ i, mgerm _ U y hU ((homSheafEval G (t i)).val.app (op U) h) = 0 := fun i ↦ by
    rw [← stalkFunctor_map_mgerm]
    exact congrFun hz i
  choose V hVU hyV hV using fun i ↦ exists_modRes_eq_zero_of_mgerm_eq_zero y hU _ (hz' i)
  obtain ⟨V', hyV', hV'⟩ : ∃ V' : Opens Y.toPresheafedSpace, y ∈ V' ∧ ∀ i, V' ≤ V i :=
    exists_open_forall Y y (fun i V'' ↦ V'' ≤ V i)
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) (fun i ↦ ⟨V i, hyV i, le_rfl⟩)
  have hV₁U : V' ⊓ V₀ ⊓ U ≤ U := inf_le_right
  have key : modRes h (V' ⊓ V₀ ⊓ U) hV₁U = 0 := by
    change (show F ⟶ restrictExtend G U from h) ≫ restrictExtendRes G hV₁U = 0
    refine P.homSec_eq_zero G (inf_le_left.trans inf_le_right) _ fun i ↦ ?_
    have hle : V₀ ⊓ (V' ⊓ V₀ ⊓ U) ≤ V i ⊓ W :=
      le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (hV' i))))
        (inf_le_left.trans hV₀)
    have e := congrArg (fun z ↦ modRes (N := G) (restrictExtendSec z) (V₀ ⊓ (V' ⊓ V₀ ⊓ U))
      hle) (hV i)
    simp only [restrictExtendSec_modRes, restrictExtendSec_homSheafEval, modRes_res,
      restrictExtendSec_zero, modRes_zero] at e
    change restrictExtendSec ((restrictExtendRes G hV₁U).val.app (op V₀)
      ((show F ⟶ restrictExtend G U from h).val.app (op V₀) (modRes (t i) V₀ hV₀))) = 0
    rw [restrictExtendSec_restrictExtendRes, modHom_modRes, restrictExtendSec_modRes, modRes_res]
    exact e
  rw [← mgerm_modRes hV₁U y ⟨⟨hyV', hy₀⟩, hU⟩, key, mgerm_zero]

/-- **Solutions of the relations of a local presentation come from `𝓗om(F, G)_y`.** -/
lemma LocalPresentation.exists_evalStalk_eq (P : LocalPresentation F W)
    (v : Fin P.n → (Y.stalkFunctor y).obj (restrictExtend G W))
    (hv : relStalk G y P.g hy v = 0) : ∃ z, evalStalk G P.s y z = v := by
  choose V hV k hk using fun i ↦ exists_mgerm_eq y (v i)
  obtain ⟨V₀', hyV₀', hV₀'⟩ : ∃ V' : Opens Y.toPresheafedSpace, y ∈ V' ∧ ∀ i, V' ≤ V i :=
    exists_open_forall Y y (fun i V'' ↦ V'' ≤ V i)
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) (fun i ↦ ⟨V i, hV i, le_rfl⟩)
  have hV₀W : V₀' ⊓ W ≤ W := inf_le_right
  have hV₀V : ∀ i, V₀' ⊓ W ≤ V i := fun i ↦ inf_le_left.trans (hV₀' i)
  have hyV₀ : y ∈ V₀' ⊓ W := ⟨hyV₀', hy⟩
  have hk₀ : ∀ i, mgerm _ (V₀' ⊓ W) y hyV₀ (modRes (k i) (V₀' ⊓ W) (hV₀V i)) = v i := fun i ↦ by
    rw [mgerm_modRes, hk i]
  have hrel : ∀ l, mgerm _ (V₀' ⊓ W) y hyV₀
      (∑ i, TopCat.Presheaf.restrictOpen (P.g l i) (V₀' ⊓ W) hV₀W •
        modRes (k i) (V₀' ⊓ W) (hV₀V i)) = 0 := fun l ↦ by
    rw [mgerm_sum]
    have := congrFun hv l
    rw [relStalk_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) this
    rw [mgerm_smul, hk₀]
    congr 1
    exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV₀W) y hyV₀ _
  choose Vl hVl hyVl hVl0 using fun l ↦ exists_modRes_eq_zero_of_mgerm_eq_zero y hyV₀ _ (hrel l)
  obtain ⟨V₁', hyV₁', hV₁'⟩ : ∃ V' : Opens Y.toPresheafedSpace, y ∈ V' ∧ ∀ l, V' ≤ Vl l :=
    exists_open_forall Y y (fun l V'' ↦ V'' ≤ Vl l)
    (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) (fun l ↦ ⟨Vl l, hyVl l, le_rfl⟩)
  set V₁ := V₁' ⊓ (V₀' ⊓ W) with hV₁
  have hV₁V₀ : V₁ ≤ V₀' ⊓ W := inf_le_right
  have hV₁W : V₁ ≤ W := hV₁V₀.trans hV₀W
  have hyV₁ : y ∈ V₁ := ⟨hyV₁', hyV₀⟩
  let kG : Fin P.n → G.val.obj (op V₁) := fun i ↦
    modRes (restrictExtendSec (modRes (k i) (V₀' ⊓ W) (hV₀V i))) V₁ (le_inf hV₁V₀ hV₁W)
  have hkG : ∀ l, ∑ i, TopCat.Presheaf.restrictOpen (P.g l i) V₁ hV₁W • kG i = 0 := fun l ↦ by
    have e := congrArg (fun z ↦ modRes (N := G) (restrictExtendSec
      (modRes (N := restrictExtend G W) z V₁ (inf_le_left.trans (hV₁' l)))) V₁
      (le_inf le_rfl hV₁W)) (hVl0 l)
    simp only [modRes_res, restrictExtendSec_modRes, restrictExtendSec_zero, modRes_zero,
      restrictExtendSec_sum, modRes_sum, restrictExtendSec_smul, modRes_smul, yres_res] at e
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) e
    simp only [kG, restrictExtendSec_modRes, modRes_res]
  refine ⟨mgerm _ V₁ y hyV₁ (P.homSecOf G hV₁W kG hkG), funext fun i ↦ ?_⟩
  rw [evalStalk_apply, stalkFunctor_map_mgerm, ← hk₀ i, ← mgerm_modRes hV₁V₀ y hyV₁]
  congr 1
  refine restrictExtend_ext ?_
  rw [restrictExtendSec_homSheafEval]
  erw [P.homSecOf_s G hV₁W kG hkG i]
  simp only [kG, restrictExtendSec_modRes, modRes_res]

end AlgebraicGeometry.LocallyRingedSpace

end
