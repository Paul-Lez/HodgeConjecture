/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwist

/-!
# The sheaf of homomorphisms between sheaves of modules

Let `Y` be a locally ringed space and `F`, `K` sheaves of `𝒪_Y`-modules. For an open `U ⊆ Y` let
`K_U` (`AlgebraicGeometry.LocallyRingedSpace.restrictExtend K U`) be the sheaf `W ↦ K(W ∩ U)`, the
pushforward of `K|_U` along the inclusion of `U`. The **sheaf of homomorphisms** `𝓗om(F, K)`
(`AlgebraicGeometry.LocallyRingedSpace.homSheaf F K`) has sections `F ⟶ K_U` over `U`: a
morphism `F ⟶ K_U` is the same as a morphism `F|_U ⟶ K|_U`. The `Γ(Y, U)`-module structure is
given by multiplication on `K_U`, and restriction by `K_U ⟶ K_V` for `V ≤ U`.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.restrictExtend K U`: the sheaf `W ↦ K(W ∩ U)`, with the
  maps `toRestrictExtend K U : K ⟶ K_U` and `restrictExtendRes K h : K_U ⟶ K_V` for `V ≤ U`.
- `AlgebraicGeometry.LocallyRingedSpace.homSheaf F K`: the sheaf `𝓗om(F, K)`.
- `AlgebraicGeometry.LocallyRingedSpace.homSheafGlobalEquiv`: `Γ(Y, 𝓗om(F, K)) ≃ (F ⟶ K)`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

set_option hygiene false in
/-- Sections of the structure sheaf of `Y` over `W`. -/
local notation "Γᵧ(" W ")" => Y.presheaf.obj (op W)

/-- Restriction of a section of a sheaf of modules, the inclusion being proved by `order`. -/
local macro:80 x:term:80 " |ₘ " W:term:81 : term =>
  `(modRes $x $W (by order))

variable {Y : LocallyRingedSpace.{u}}

section RestrictExtend

variable (N : SheafOfModules.{u} Y.ringSheaf) (U : Opens Y.toPresheafedSpace)

/-- The sections `N(W ∩ U)` of `N_U` over `W`, a `Γ(Y, W)`-module by restriction of scalars. -/
def ExtSec (W : Opens Y.toPresheafedSpace) : Type u := N.val.obj (op (W ⊓ U))

instance (W : Opens Y.toPresheafedSpace) : AddCommGroup (ExtSec N U W) :=
  inferInstanceAs (AddCommGroup (N.val.obj (op (W ⊓ U))))

instance (W : Opens Y.toPresheafedSpace) : Module Γᵧ(W) (ExtSec N U W) :=
  Module.compHom (N.val.obj (op (W ⊓ U)))
    (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op).hom

variable {N U} in
lemma ExtSec.smul_def {W : Opens Y.toPresheafedSpace} (r : Γᵧ(W)) (x : ExtSec N U W) :
    r • x = (show N.val.obj (op (W ⊓ U)) from
      (r |ₒ (W ⊓ U)) • (show N.val.obj (op (W ⊓ U)) from x)) :=
  rfl

/-- The underlying abelian presheaf of `N_U`. -/
def restrictExtendPresheaf (N : SheafOfModules.{u} Y.ringSheaf) (U : Opens Y.toPresheafedSpace) :
    (Opens Y.toPresheafedSpace)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (ExtSec N U W.unop)
  map {W W'} f := AddCommGrpCat.ofHom
    { toFun x := modRes (N := N) x (W'.unop ⊓ U) (inf_le_inf_right U f.unop.le)
      map_zero' := modRes_zero _
      map_add' := modRes_add _ }
  map_id W := by
    ext x
    exact modRes_self (N := N) x
  map_comp f g := by
    ext x
    exact (modRes_res (N := N) _ _ x).symm

instance (W : (Opens Y.toPresheafedSpace)ᵒᵖ) :
    Module (Y.ringSheaf.obj.obj W) ((restrictExtendPresheaf N U).obj W) :=
  inferInstanceAs (Module Γᵧ(W.unop) (ExtSec N U W.unop))

/-- `N_U` as a presheaf of modules. -/
def restrictExtendPresheafOfModules (N : SheafOfModules.{u} Y.ringSheaf)
    (U : Opens Y.toPresheafedSpace) : PresheafOfModules.{u} Y.ringSheaf.obj :=
  PresheafOfModules.ofPresheaf (restrictExtendPresheaf N U)
      fun W W' f (r : Y.presheaf.obj W) (x : N.val.obj (op (W.unop ⊓ U))) ↦ by
    change modRes (N := N) (TopCat.Presheaf.restrictOpen r (W.unop ⊓ U) inf_le_left • x)
        (W'.unop ⊓ U) (inf_le_inf_right U f.unop.le) =
      TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen r W'.unop f.unop.le)
        (W'.unop ⊓ U) inf_le_left • modRes (N := N) x
          (W'.unop ⊓ U) (inf_le_inf_right U f.unop.le)
    rw [modRes_smul, yres_res, yres_res]

lemma isSheaf_restrictExtendPresheaf :
    TopCat.Presheaf.IsSheaf (restrictExtendPresheaf N U) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have key : ∃! t : N.val.obj (op (iSup W ⊓ U)), ∀ a,
      modRes t (W a ⊓ U) (inf_le_inf_right U (le_iSup W a)) = sf a := by
    refine modRes_existsUnique_gluing N (fun a ↦ W a ⊓ U) (by rw [iSup_inf_eq]) _ _ ?_
    intro a b
    have h1 : modRes (N := N) (sf a) ((W a ⊓ W b) ⊓ U) (by order) =
        modRes (N := N) (sf b) ((W a ⊓ W b) ⊓ U) (by order) := hsf a b
    have := congrArg (fun x : N.val.obj (op ((W a ⊓ W b) ⊓ U)) ↦
      modRes x (W a ⊓ U ⊓ (W b ⊓ U)) (by order)) h1
    simpa only [modRes_res] using this
  obtain ⟨t, ht, hu⟩ := key
  exact ⟨t, ht, fun s hs ↦ hu s hs⟩

/-- **The sheaf `N_U : W ↦ N(W ∩ U)`**, the pushforward of the restriction of `N` to `U` along
the inclusion of `U`. -/
def restrictExtend (N : SheafOfModules.{u} Y.ringSheaf) (U : Opens Y.toPresheafedSpace) :
    SheafOfModules.{u} Y.ringSheaf where
  val := restrictExtendPresheafOfModules N U
  isSheaf := isSheaf_restrictExtendPresheaf N U

variable {N U}

/-- A section of `N_U` over `W` is a section of `N` over `W ∩ U`. -/
def restrictExtendSec {W : Opens Y.toPresheafedSpace} (x : (restrictExtend N U).val.obj (op W)) :
    N.val.obj (op (W ⊓ U)) := x

/-- A section of `N` over `W ∩ U` is a section of `N_U` over `W`. -/
def restrictExtendMk {W : Opens Y.toPresheafedSpace} (x : N.val.obj (op (W ⊓ U))) :
    (restrictExtend N U).val.obj (op W) := x

@[simp]
lemma restrictExtendSec_mk {W : Opens Y.toPresheafedSpace} (x : N.val.obj (op (W ⊓ U))) :
    restrictExtendSec (restrictExtendMk (U := U) x) = x :=
  rfl

@[simp]
lemma restrictExtendMk_sec {W : Opens Y.toPresheafedSpace}
    (x : (restrictExtend N U).val.obj (op W)) : restrictExtendMk (restrictExtendSec x) = x :=
  rfl

lemma restrictExtendSec_add {W : Opens Y.toPresheafedSpace}
    (x y : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec (x + y) = restrictExtendSec x + restrictExtendSec y :=
  rfl

lemma restrictExtendSec_zero {W : Opens Y.toPresheafedSpace} :
    restrictExtendSec (0 : (restrictExtend N U).val.obj (op W)) = 0 :=
  rfl

lemma restrictExtendSec_smul {W : Opens Y.toPresheafedSpace} (r : Γᵧ(W))
    (x : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec (r • x) = (r |ₒ (W ⊓ U)) • restrictExtendSec x :=
  rfl

lemma restrictExtendSec_modRes {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (x : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec (modRes x W' h) = modRes (restrictExtendSec x) (W' ⊓ U) (by order) :=
  rfl

lemma restrictExtend_ext {W : Opens Y.toPresheafedSpace}
    {x y : (restrictExtend N U).val.obj (op W)} (h : restrictExtendSec x = restrictExtendSec y) :
    x = y :=
  h

variable (N U)

/-- The restriction `N ⟶ N_U`, `x ↦ x|_{W ∩ U}`. -/
def toRestrictExtend : N ⟶ restrictExtend N U :=
  modHomMk (fun W ↦
      { toFun x := restrictExtendMk (modRes x (W ⊓ U) inf_le_left)
        map_zero' := modRes_zero _
        map_add' := modRes_add _ })
    (fun W r x ↦ by
      change modRes (N := N) (r • x) (W ⊓ U) inf_le_left =
        (r |ₒ (W ⊓ U)) • modRes (N := N) x (W ⊓ U) inf_le_left
      rw [modRes_smul])
    (fun W W' h x ↦ by
      change modRes (N := N) (modRes x W' h) (W' ⊓ U) inf_le_left =
        modRes (N := N) (modRes x (W ⊓ U) inf_le_left) (W' ⊓ U) (inf_le_inf_right U h)
      rw [modRes_res, modRes_res])

@[simp]
lemma restrictExtendSec_toRestrictExtend {W : Opens Y.toPresheafedSpace}
    (x : N.val.obj (op W)) :
    restrictExtendSec ((toRestrictExtend N U).val.app (op W) x) =
      modRes x (W ⊓ U) inf_le_left :=
  rfl

variable {U} in
/-- The restriction `N_U ⟶ N_V` for `V ≤ U`. -/
def restrictExtendRes {V : Opens Y.toPresheafedSpace} (h : V ≤ U) :
    restrictExtend N U ⟶ restrictExtend N V :=
  modHomMk (fun W ↦
      { toFun x := restrictExtendMk (modRes (restrictExtendSec x) (W ⊓ V) (inf_le_inf_left W h))
        map_zero' := modRes_zero _
        map_add' x y := modRes_add (N := N) _ (restrictExtendSec x) (restrictExtendSec y) })
    (fun W r x ↦ by
      change modRes (N := N) ((r |ₒ (W ⊓ U)) • restrictExtendSec x) (W ⊓ V)
          (inf_le_inf_left W h) =
        (r |ₒ (W ⊓ V)) • modRes (N := N) (restrictExtendSec x) (W ⊓ V) (inf_le_inf_left W h)
      rw [modRes_smul, yres_res])
    (fun W W' h' x ↦ by
      change modRes (N := N) (modRes (N := N) (restrictExtendSec x) (W' ⊓ U)
          (inf_le_inf_right U h')) (W' ⊓ V) (inf_le_inf_left W' h) =
        modRes (N := N) (modRes (N := N) (restrictExtendSec x) (W ⊓ V) (inf_le_inf_left W h))
          (W' ⊓ V) (inf_le_inf_right V h')
      rw [modRes_res, modRes_res])

lemma restrictExtendSec_restrictExtendRes {V W : Opens Y.toPresheafedSpace} (h : V ≤ U)
    (x : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec ((restrictExtendRes N h).val.app (op W) x) =
      modRes (restrictExtendSec x) (W ⊓ V) (inf_le_inf_left W h) :=
  rfl

lemma restrictExtendRes_comp {V V' : Opens Y.toPresheafedSpace} (h : V ≤ U) (h' : V' ≤ V) :
    restrictExtendRes N h ≫ restrictExtendRes N h' = restrictExtendRes N (h'.trans h) := by
  refine modHom_ext fun W x ↦ ?_
  exact modRes_res (N := N) (inf_le_inf_left W h) (inf_le_inf_left W h') (restrictExtendSec x)

lemma restrictExtendRes_self : restrictExtendRes N (le_refl U) = 𝟙 _ := by
  refine modHom_ext fun W x ↦ ?_
  exact modRes_self (N := N) (restrictExtendSec x)

lemma toRestrictExtend_comp_res {V : Opens Y.toPresheafedSpace} (h : V ≤ U) :
    toRestrictExtend N U ≫ restrictExtendRes N h = toRestrictExtend N V := by
  refine modHom_ext fun W x ↦ ?_
  exact modRes_res (N := N) inf_le_left (inf_le_inf_left W h) x

/-- Multiplication by a section `a` of `𝒪_Y` over `U` on `N_U`. -/
def restrictExtendSMul (a : Γᵧ(U)) : restrictExtend N U ⟶ restrictExtend N U :=
  modHomMk (fun W ↦
      { toFun x := restrictExtendMk ((a |ₒ (W ⊓ U)) • restrictExtendSec x)
        map_zero' := smul_zero (A := N.val.obj (op (W ⊓ U))) _
        map_add' x y := smul_add (a |ₒ (W ⊓ U)) (restrictExtendSec x) (restrictExtendSec y) })
    (fun W r x ↦ by
      change (a |ₒ (W ⊓ U)) • (r |ₒ (W ⊓ U)) • restrictExtendSec x =
        (r |ₒ (W ⊓ U)) • (a |ₒ (W ⊓ U)) • restrictExtendSec x
      rw [smul_smul, smul_smul, mul_comm])
    (fun W W' h x ↦ by
      change (a |ₒ (W' ⊓ U)) •
          modRes (N := N) (restrictExtendSec x) (W' ⊓ U) (inf_le_inf_right U h) =
        modRes (N := N) ((a |ₒ (W ⊓ U)) • restrictExtendSec x) (W' ⊓ U) (inf_le_inf_right U h)
      rw [modRes_smul, yres_res])

lemma restrictExtendSec_restrictExtendSMul (a : Γᵧ(U)) {W : Opens Y.toPresheafedSpace}
    (x : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec ((restrictExtendSMul N U a).val.app (op W) x) =
      (a |ₒ (W ⊓ U)) • restrictExtendSec x :=
  rfl

lemma restrictExtendSMul_res {V : Opens Y.toPresheafedSpace} (h : V ≤ U) (a : Γᵧ(U)) :
    restrictExtendSMul N U a ≫ restrictExtendRes N h =
      restrictExtendRes N h ≫ restrictExtendSMul N V (a |ₒ V) := by
  refine modHom_ext fun W x ↦ ?_
  change modRes (N := N) ((a |ₒ (W ⊓ U)) • restrictExtendSec x) (W ⊓ V)
      (inf_le_inf_left W h) =
    ((a |ₒ V) |ₒ (W ⊓ V)) • modRes (N := N) (restrictExtendSec x) (W ⊓ V) (inf_le_inf_left W h)
  rw [modRes_smul, yres_res, yres_res]

/-- Multiplication on `N_U`, as a ring homomorphism `Γ(Y, U) →+* End(N_U)`. -/
def restrictExtendSMulHom : Γᵧ(U) →+* End (restrictExtend N U) where
  toFun := restrictExtendSMul N U
  map_one' := modHom_ext fun W x ↦ by
    change ((1 : Γᵧ(U)) |ₒ (W ⊓ U)) • restrictExtendSec x = restrictExtendSec x
    rw [yres_one, one_smul]
  map_mul' a b := modHom_ext fun W x ↦ by
    change ((a * b) |ₒ (W ⊓ U)) • restrictExtendSec x =
      (a |ₒ (W ⊓ U)) • (b |ₒ (W ⊓ U)) • restrictExtendSec x
    rw [yres_mul, mul_smul]
  map_zero' := modHom_ext fun W x ↦ by
    change ((0 : Γᵧ(U)) |ₒ (W ⊓ U)) • restrictExtendSec x = 0
    rw [yres_zero, zero_smul]
  map_add' a b := modHom_ext fun W x ↦ by
    change ((a + b) |ₒ (W ⊓ U)) • restrictExtendSec x =
      (a |ₒ (W ⊓ U)) • restrictExtendSec x + (b |ₒ (W ⊓ U)) • restrictExtendSec x
    rw [yres_add, add_smul]

variable {N} in
/-- The functoriality `N_U ⟶ N'_U` of `N ↦ N_U`. -/
def restrictExtendMap {N' : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ N') :
    restrictExtend N U ⟶ restrictExtend N' U :=
  modHomMk (fun W ↦
      { toFun x := restrictExtendMk (φ.val.app (op (W ⊓ U)) (restrictExtendSec x))
        map_zero' := map_zero (φ.val.app (op (W ⊓ U))).hom
        map_add' x y := map_add (φ.val.app (op (W ⊓ U))).hom (restrictExtendSec x)
          (restrictExtendSec y) })
    (fun W r x ↦ by
      change φ.val.app (op (W ⊓ U)) ((r |ₒ (W ⊓ U)) • restrictExtendSec x) =
        (r |ₒ (W ⊓ U)) • φ.val.app (op (W ⊓ U)) (restrictExtendSec x)
      rw [modHom_smul])
    (fun W W' h x ↦ by
      change φ.val.app (op (W' ⊓ U)) (modRes (N := N) (restrictExtendSec x) (W' ⊓ U)
          (inf_le_inf_right U h)) =
        modRes (φ.val.app (op (W ⊓ U)) (restrictExtendSec x)) (W' ⊓ U) (inf_le_inf_right U h)
      rw [modHom_modRes])

lemma restrictExtendSec_restrictExtendMap {N' : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ N')
    {W : Opens Y.toPresheafedSpace} (x : (restrictExtend N U).val.obj (op W)) :
    restrictExtendSec ((restrictExtendMap U φ).val.app (op W) x) =
      φ.val.app (op (W ⊓ U)) (restrictExtendSec x) :=
  rfl

/-- Restriction along `W ∩ ⊤ = W` is bijective. -/
lemma bijective_modRes_inf_top (W : Opens Y.toPresheafedSpace) :
    Function.Bijective (fun x : N.val.obj (op W) ↦ modRes x (W ⊓ ⊤) inf_le_left) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨modRes y W (by simp), ?_⟩⟩
  · have := congrArg (fun z ↦ modRes z W (by simp)) hxy
    simpa only [modRes_res, modRes_self] using this
  · simp only [modRes_res, modRes_self]

instance : IsIso (toRestrictExtend N ⊤) :=
  (modIsoOfBijective (toRestrictExtend N ⊤) fun W ↦ bijective_modRes_inf_top N W).isIso_hom

/-- `N ≅ N_⊤`. -/
def restrictExtendTopIso : N ≅ restrictExtend N ⊤ :=
  asIso (toRestrictExtend N ⊤)

lemma restrictExtendTopIso_hom : (restrictExtendTopIso N).hom = toRestrictExtend N ⊤ :=
  rfl

end RestrictExtend

section HomSheaf

variable (F K : SheafOfModules.{u} Y.ringSheaf)

/-- The sections `F ⟶ K_U` of `𝓗om(F, K)` over `U`. -/
def HomSec (U : Opens Y.toPresheafedSpace) : Type u := F ⟶ restrictExtend K U

instance (U : Opens Y.toPresheafedSpace) : AddCommGroup (HomSec F K U) :=
  inferInstanceAs (AddCommGroup (F ⟶ restrictExtend K U))

instance (U : Opens Y.toPresheafedSpace) : Module Γᵧ(U) (HomSec F K U) :=
  letI : Module (End (restrictExtend K U)) (HomSec F K U) :=
    inferInstanceAs (Module (End (restrictExtend K U)) (F ⟶ restrictExtend K U))
  Module.compHom (HomSec F K U) (restrictExtendSMulHom K U)

variable {F K} in
lemma HomSec.smul_def {U : Opens Y.toPresheafedSpace} (a : Γᵧ(U)) (h : HomSec F K U) :
    a • h = (show F ⟶ restrictExtend K U from h) ≫ restrictExtendSMul K U a :=
  rfl

/-- The underlying abelian presheaf of `𝓗om(F, K)`. -/
def homSheafPresheaf (F K : SheafOfModules.{u} Y.ringSheaf) :
    (Opens Y.toPresheafedSpace)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (HomSec F K U.unop)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun h := (show F ⟶ restrictExtend K U.unop from h) ≫ restrictExtendRes K f.unop.le
      map_zero' := zero_comp
      map_add' h h' := Preadditive.add_comp _ _ _ _ _ _ }
  map_id U := by
    ext h
    change h ≫ restrictExtendRes K (le_refl _) = h
    rw [restrictExtendRes_self, Category.comp_id]
  map_comp f g := by
    ext h
    change h ≫ restrictExtendRes K _ = (h ≫ restrictExtendRes K _) ≫ restrictExtendRes K _
    rw [Category.assoc, restrictExtendRes_comp]

instance (U : (Opens Y.toPresheafedSpace)ᵒᵖ) :
    Module (Y.ringSheaf.obj.obj U) ((homSheafPresheaf F K).obj U) :=
  inferInstanceAs (Module Γᵧ(U.unop) (HomSec F K U.unop))

/-- `𝓗om(F, K)` as a presheaf of modules. -/
def homSheafPresheafOfModules (F K : SheafOfModules.{u} Y.ringSheaf) :
    PresheafOfModules.{u} Y.ringSheaf.obj :=
  PresheafOfModules.ofPresheaf (homSheafPresheaf F K) fun U V f a h ↦ by
    change ((show F ⟶ restrictExtend K U.unop from h) ≫ restrictExtendSMul K U.unop a) ≫
        restrictExtendRes K f.unop.le =
      ((show F ⟶ restrictExtend K U.unop from h) ≫ restrictExtendRes K f.unop.le) ≫
        restrictExtendSMul K V.unop (TopCat.Presheaf.restrictOpen a V.unop f.unop.le)
    rw [Category.assoc, Category.assoc, restrictExtendSMul_res]
    rfl


section Glue

variable {F K} {κ : Type u} (U : κ → Opens Y.toPresheafedSpace) (hf : ∀ a, HomSec F K (U a))

/-- Gluing of the values of a compatible family of sections of `𝓗om(F, K)`. -/
lemma homSec_existsUnique_gluing
    (hc : ∀ a b, (show F ⟶ restrictExtend K (U a) from hf a) ≫
        restrictExtendRes K (inf_le_left : U a ⊓ U b ≤ U a) =
      (show F ⟶ restrictExtend K (U b) from hf b) ≫ restrictExtendRes K inf_le_right)
    (W : Opens Y.toPresheafedSpace) (x : F.val.obj (op W)) :
    ∃! t : K.val.obj (op (W ⊓ iSup U)), ∀ a,
      modRes t (W ⊓ U a) (inf_le_inf_left W (le_iSup U a)) =
        restrictExtendSec ((show F ⟶ restrictExtend K (U a) from hf a).val.app (op W) x) := by
  refine modRes_existsUnique_gluing K (fun a ↦ W ⊓ U a) (by rw [inf_iSup_eq]) _ _ ?_
  intro a b
  have h1 := congrArg (fun φ : F ⟶ restrictExtend K (U a ⊓ U b) ↦
    restrictExtendSec (φ.val.app (op W) x)) (hc a b)
  change modRes (N := K) (restrictExtendSec ((show F ⟶ restrictExtend K (U a) from hf a).val.app
      (op W) x)) (W ⊓ (U a ⊓ U b)) (inf_le_inf_left W inf_le_left) =
    modRes (N := K) (restrictExtendSec ((show F ⟶ restrictExtend K (U b) from hf b).val.app
      (op W) x)) (W ⊓ (U a ⊓ U b)) (inf_le_inf_left W inf_le_right) at h1
  have := congrArg (fun y : K.val.obj (op (W ⊓ (U a ⊓ U b))) ↦
    modRes y (W ⊓ U a ⊓ (W ⊓ U b)) (by order)) h1
  simpa only [modRes_res] using this

variable (hc : ∀ a b, (show F ⟶ restrictExtend K (U a) from hf a) ≫
    restrictExtendRes K (inf_le_left : U a ⊓ U b ≤ U a) =
  (show F ⟶ restrictExtend K (U b) from hf b) ≫ restrictExtendRes K inf_le_right)

/-- The glued value. -/
def homSecGlueApp (W : Opens Y.toPresheafedSpace) (x : F.val.obj (op W)) :
    K.val.obj (op (W ⊓ iSup U)) :=
  (homSec_existsUnique_gluing U hf hc W x).exists.choose

lemma homSecGlueApp_spec (W : Opens Y.toPresheafedSpace) (x : F.val.obj (op W)) (a : κ) :
    modRes (homSecGlueApp U hf hc W x) (W ⊓ U a) (inf_le_inf_left W (le_iSup U a)) =
      restrictExtendSec ((show F ⟶ restrictExtend K (U a) from hf a).val.app (op W) x) :=
  (homSec_existsUnique_gluing U hf hc W x).exists.choose_spec a

lemma homSecGlueApp_unique (W : Opens Y.toPresheafedSpace) (x : F.val.obj (op W))
    (t : K.val.obj (op (W ⊓ iSup U)))
    (ht : ∀ a, modRes t (W ⊓ U a) (inf_le_inf_left W (le_iSup U a)) =
      restrictExtendSec ((show F ⟶ restrictExtend K (U a) from hf a).val.app (op W) x)) :
    t = homSecGlueApp U hf hc W x :=
  (homSec_existsUnique_gluing U hf hc W x).unique ht (homSecGlueApp_spec U hf hc W x)

/-- The gluing of a compatible family of sections of `𝓗om(F, K)`. -/
def homSecGlue : F ⟶ restrictExtend K (iSup U) :=
  modHomMk (fun W ↦
      { toFun x := restrictExtendMk (homSecGlueApp U hf hc W x)
        map_zero' := (homSecGlueApp_unique U hf hc W 0 0 fun a ↦ by
          rw [modRes_zero, map_zero]; rfl).symm
        map_add' x y := (homSecGlueApp_unique U hf hc W (x + y)
          (homSecGlueApp U hf hc W x + homSecGlueApp U hf hc W y) fun a ↦ by
          rw [modRes_add, homSecGlueApp_spec, homSecGlueApp_spec, map_add]; rfl).symm })
    (fun W r x ↦ (homSecGlueApp_unique U hf hc W (r • x) _ fun a ↦ by
          change modRes (N := K) ((r |ₒ (W ⊓ iSup U)) • homSecGlueApp U hf hc W x) _ _ = _
          rw [modRes_smul, homSecGlueApp_spec, yres_res, modHom_smul]; rfl).symm)
    (fun W W' h x ↦ (homSecGlueApp_unique U hf hc W' (modRes x W' h) _ fun a ↦ by
          change modRes (N := K) (modRes (N := K) (homSecGlueApp U hf hc W x) (W' ⊓ iSup U)
            (inf_le_inf_right _ h)) _ _ = _
          rw [modRes_res, modHom_modRes, restrictExtendSec_modRes, ← homSecGlueApp_spec,
            modRes_res]).symm)

lemma homSecGlue_res (a : κ) :
    homSecGlue U hf hc ≫ restrictExtendRes K (le_iSup U a) = hf a :=
  modHom_ext fun W x ↦ homSecGlueApp_spec U hf hc W x a

lemma homSecGlue_unique (s : F ⟶ restrictExtend K (iSup U))
    (hs : ∀ a, s ≫ restrictExtendRes K (le_iSup U a) = hf a) : s = homSecGlue U hf hc :=
  modHom_ext fun W x ↦ homSecGlueApp_unique U hf hc W x _ fun a ↦
    congrArg (fun φ : F ⟶ restrictExtend K (U a) ↦ restrictExtendSec (φ.val.app (op W) x)) (hs a)

end Glue

lemma isSheaf_homSheafPresheaf : TopCat.Presheaf.IsSheaf (homSheafPresheaf F K) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U hf hc
  exact ⟨homSecGlue U hf hc, fun a ↦ homSecGlue_res U hf hc a,
    fun s hs ↦ homSecGlue_unique U hf hc s hs⟩

/-- **The sheaf of homomorphisms `𝓗om(F, K)`**: its sections over `U` are the morphisms
`F ⟶ K_U`, that is, the morphisms `F|_U ⟶ K|_U`. -/
def homSheaf : SheafOfModules.{u} Y.ringSheaf where
  val := homSheafPresheafOfModules F K
  isSheaf := isSheaf_homSheafPresheaf F K

/-- **Global sections of `𝓗om(F, K)` are the morphisms `F ⟶ K`.** -/
def homSheafGlobalEquiv : (homSheaf F K).val.obj (op ⊤) ≃ (F ⟶ K) where
  toFun h := (show F ⟶ restrictExtend K ⊤ from h) ≫ (restrictExtendTopIso K).inv
  invFun φ := (φ ≫ (restrictExtendTopIso K).hom : F ⟶ restrictExtend K ⊤)
  left_inv h := by
    change ((show F ⟶ restrictExtend K ⊤ from h) ≫ (restrictExtendTopIso K).inv) ≫
      (restrictExtendTopIso K).hom = h
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  right_inv φ := by
    change (φ ≫ (restrictExtendTopIso K).hom) ≫ (restrictExtendTopIso K).inv = φ
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end HomSheaf

end AlgebraicGeometry.LocallyRingedSpace

end
