/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwistPullback

/-!
# Twisting sheaves of modules on a locally ringed space by a cocycle

Let `Y` be a locally ringed space, `V : ι → Opens Y` a family of opens and `c` a cocycle on it:
sections `cᵢⱼ ∈ Γ(Y, Vᵢ ∩ Vⱼ)` with `cᵢᵢ = 1` and `cᵢⱼ cⱼₖ = cᵢₖ` on `Vᵢ ∩ Vⱼ ∩ Vₖ`
(`LocallyRingedSpace.ModCocycle`). For a sheaf of `𝒪_Y`-modules `N`, the **twist** `N ⊗ L_c`
(`LocallyRingedSpace.modTwist N c`) is the sheaf whose sections over `W` are the families

  `(sᵢ)ᵢ`, `sᵢ ∈ Γ(N, W ∩ Vᵢ)`, with `sᵢ = cᵢⱼ • sⱼ` on `W ∩ Vᵢ ∩ Vⱼ`.

This is the analogue for locally ringed spaces of `AlgebraicGeometry.Scheme.Modules.twist`, with
the same proofs. If the `Vᵢ` cover `Y`, twisting by `c` is an autoequivalence of the category of
sheaves of `𝒪_Y`-modules, with inverse the twist by `c⁻¹`.

## Main definitions and results

- `LocallyRingedSpace.ModCocycle V`: cocycles on `V`; they form a commutative group.
- `LocallyRingedSpace.modTwist N c`, `LocallyRingedSpace.modTwistFunctor c`, with components
  `modTwistComp`, constructor `modTwistMk` and extensionality `modTwist_ext`.
- `LocallyRingedSpace.modTwistSectionsEquiv`: for `W ≤ Vᵢ`, `Γ(N ⊗ L_c, W) ≃ Γ(N, W)`.
- `LocallyRingedSpace.modTwistFunctorOneIso`, `LocallyRingedSpace.modTwistFunctorCompIso`,
  `LocallyRingedSpace.modTwistFunctorCongr`.
- `LocallyRingedSpace.modTwistEquivalence c hV`: twisting by `c` is an autoequivalence.
- Auxiliary: `LocallyRingedSpace.modIsoMk`, `LocallyRingedSpace.modIsoOfBijective`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.LocallyRingedSpace

set_option hygiene false in
/-- Sections of the structure sheaf of `Y` over `W`. -/
local notation "Γᵧ(" W ")" => Y.presheaf.obj (op W)

/-- Restriction of a section of a sheaf of modules, the inclusion being proved by `order`. -/
local macro:80 x:term:80 " |ₘ " W:term:81 : term =>
  `(modRes $x $W (by order))

variable {Y : LocallyRingedSpace.{u}}

section Helpers

variable {P Q : SheafOfModules.{u} Y.ringSheaf}

/-- An isomorphism of sheaves of modules on `Y` from mutually inverse morphisms, checked on
sections. -/
@[simps]
noncomputable def modIsoMk (φ : P ⟶ Q) (ψ : Q ⟶ P)
    (h₁ : ∀ W (x : P.val.obj (op W)), ψ.val.app (op W) (φ.val.app (op W) x) = x)
    (h₂ : ∀ W (y : Q.val.obj (op W)), φ.val.app (op W) (ψ.val.app (op W) y) = y) : P ≅ Q where
  hom := φ
  inv := ψ
  hom_inv_id := modHom_ext fun W x ↦ h₁ W x
  inv_hom_id := modHom_ext fun W y ↦ h₂ W y

/-- A morphism of sheaves of modules on `Y` which is bijective on all sections is an
isomorphism. -/
noncomputable def modIsoOfBijective (φ : P ⟶ Q)
    (h : ∀ W, Function.Bijective (φ.val.app (op W))) : P ≅ Q :=
  let e (W : Opens Y.toPresheafedSpace) : P.val.obj (op W) ≃+ Q.val.obj (op W) :=
    AddEquiv.ofBijective (φ.val.app (op W)).hom.toAddMonoidHom (h W)
  modIsoMk φ
    (modHomMk (fun W ↦ (e W).symm.toAddMonoidHom)
      (fun W r y ↦ (h W).1 (by
        change φ.val.app (op W) ((e W).symm (r • y)) =
          φ.val.app (op W) (r • (e W).symm y)
        rw [modHom_smul]
        exact ((e W).apply_symm_apply _).trans
          (congrArg (r • ·) ((e W).apply_symm_apply y)).symm))
      (fun W W' hW y ↦ (h W').1 (by
        change φ.val.app (op W') ((e W').symm (modRes y W' hW)) =
          φ.val.app (op W') (modRes ((e W).symm y) W' hW)
        rw [modHom_modRes]
        exact ((e W').apply_symm_apply _).trans
          (congrArg (modRes · W' hW) ((e W).apply_symm_apply y)).symm)))
    (fun W x ↦ (e W).symm_apply_apply x) (fun W y ↦ (e W).apply_symm_apply y)

@[simp]
lemma modIsoOfBijective_hom (φ : P ⟶ Q) (h : ∀ W, Function.Bijective (φ.val.app (op W))) :
    (modIsoOfBijective φ h).hom = φ :=
  rfl

variable (N : SheafOfModules.{u} Y.ringSheaf) {κ : Type*} (O : κ → Opens Y.toPresheafedSpace)
  {W : Opens Y.toPresheafedSpace}

lemma modRes_eq_of_cover (hW : W ≤ iSup O) (hO : ∀ a, O a ≤ W) (s t : N.val.obj (op W))
    (h : ∀ a, modRes s (O a) (hO a) = modRes t (O a) (hO a)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (modAbSheaf N) O W (fun a ↦ homOfLE (hO a)) hW s t h

lemma modRes_existsUnique_gluing (hW : W ≤ iSup O) (hO : ∀ a, O a ≤ W)
    (sf : ∀ a, N.val.obj (op (O a)))
    (hsf : ∀ a b, (sf a |ₘ (O a ⊓ O b)) = (sf b |ₘ (O a ⊓ O b))) :
    ∃! s : N.val.obj (op W), ∀ a, modRes s (O a) (hO a) = sf a := by
  exact TopCat.Sheaf.existsUnique_gluing' (modAbSheaf N) O W (fun a ↦ homOfLE (hO a)) hW sf
    fun a b ↦ hsf a b

end Helpers

variable {ι : Type}

/-- A **cocycle** on a family of opens `V` of a locally ringed space: sections `gᵢⱼ` over
`Vᵢ ∩ Vⱼ` with `gᵢᵢ = 1` and `gᵢⱼ gⱼₖ = gᵢₖ` on `Vᵢ ∩ Vⱼ ∩ Vₖ`. -/
structure ModCocycle (V : ι → Opens Y.toPresheafedSpace) where
  /-- the transition function over `Vᵢ ∩ Vⱼ` -/
  g (i j : ι) : Γᵧ(V i ⊓ V j)
  self (i : ι) : g i i = 1
  mul (i j k : ι) : (g i j |ₒ (V i ⊓ V j ⊓ V k)) * (g j k |ₒ (V i ⊓ V j ⊓ V k)) =
    g i k |ₒ (V i ⊓ V j ⊓ V k)

namespace ModCocycle

variable {V : ι → Opens Y.toPresheafedSpace}

@[ext]
lemma ext {c d : ModCocycle V} (h : ∀ i j, c.g i j = d.g i j) : c = d := by
  cases c; cases d; congr; funext i j; exact h i j

variable (c : ModCocycle V)

lemma mul_res (i j k : ι) (W : Opens Y.toPresheafedSpace) (hW : W ≤ V i ⊓ V j ⊓ V k) :
    (c.g i j |ₒ W) * (c.g j k |ₒ W) = c.g i k |ₒ W := by
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) (c.mul i j k)
  simpa only [yres_mul, yres_res] using this

lemma self_res (i : ι) (W : Opens Y.toPresheafedSpace) (hW : W ≤ V i ⊓ V i) :
    (c.g i i |ₒ W) = 1 := by
  rw [c.self, yres_one]

lemma mul_res_symm (i j : ι) (W : Opens Y.toPresheafedSpace) (hW : W ≤ V i ⊓ V j) :
    (c.g i j |ₒ W) * (c.g j i |ₒ W) = 1 := by
  rw [c.mul_res i j i W (by order), c.self_res i W (by order)]

instance : One (ModCocycle V) where
  one :=
    { g _ _ := 1
      self _ := rfl
      mul _ _ _ := by simp only [yres_one, mul_one] }

instance : Mul (ModCocycle V) where
  mul c d :=
    { g i j := c.g i j * d.g i j
      self i := by rw [c.self, d.self, mul_one]
      mul i j k := by
        simp only [yres_mul]
        rw [← c.mul, ← d.mul]
        ring }

instance : Inv (ModCocycle V) where
  inv c :=
    { g i j := c.g j i |ₒ (V i ⊓ V j)
      self i := by rw [c.self, yres_one]
      mul i j k := by
        simp only [yres_res]
        rw [mul_comm, c.mul_res k j i _ (by order)] }

@[simp] lemma one_g (i j : ι) : (1 : ModCocycle V).g i j = 1 := rfl
@[simp] lemma mul_g (c d : ModCocycle V) (i j : ι) : (c * d).g i j = c.g i j * d.g i j := rfl
@[simp] lemma inv_g (i j : ι) : c⁻¹.g i j = c.g j i |ₒ (V i ⊓ V j) := rfl

instance : CommGroup (ModCocycle V) where
  mul_assoc _ _ _ := ext fun _ _ ↦ mul_assoc _ _ _
  one_mul _ := ext fun _ _ ↦ one_mul _
  mul_one _ := ext fun _ _ ↦ mul_one _
  mul_comm _ _ := ext fun _ _ ↦ mul_comm _ _
  inv_mul_cancel c := ext fun i j ↦ by
    rw [mul_g, inv_g, one_g, ← yres_self (c.g i j)]
    exact c.mul_res_symm j i _ (by order)

end ModCocycle

section Twist

variable (N : SheafOfModules.{u} Y.ringSheaf) (V : ι → Opens Y.toPresheafedSpace)

/-- The families `(sᵢ)ᵢ` with `sᵢ ∈ Γ(N, W ∩ Vᵢ)`, a `Γ(Y, W)`-module. -/
def ModTwistAmb (W : Opens Y.toPresheafedSpace) : Type u := ∀ i, N.val.obj (op (W ⊓ V i))

noncomputable instance (W : Opens Y.toPresheafedSpace) : AddCommGroup (ModTwistAmb N V W) :=
  inferInstanceAs (AddCommGroup (∀ i, N.val.obj (op (W ⊓ V i))))

noncomputable instance (W : Opens Y.toPresheafedSpace) : Module Γᵧ(W) (ModTwistAmb N V W) :=
  letI (i : ι) : Module Γᵧ(W) (N.val.obj (op (W ⊓ V i))) :=
    Module.compHom _ (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom
  inferInstanceAs (Module Γᵧ(W) (∀ i, N.val.obj (op (W ⊓ V i))))

variable {N V} in
@[simp]
lemma ModTwistAmb.add_apply {W : Opens Y.toPresheafedSpace} (s t : ModTwistAmb N V W) (i : ι) :
    (s + t) i = s i + t i :=
  rfl

variable {N V} in
@[simp]
lemma ModTwistAmb.zero_apply {W : Opens Y.toPresheafedSpace} (i : ι) :
    (0 : ModTwistAmb N V W) i = 0 :=
  rfl

variable {N V} in
lemma ModTwistAmb.smul_apply {W : Opens Y.toPresheafedSpace} (r : Γᵧ(W))
    (s : ModTwistAmb N V W) (i : ι) : (r • s) i = (r |ₒ (W ⊓ V i)) • s i :=
  rfl

variable {V}

/-- Sections of the twist of `N` by `c` over `W`: the families `(sᵢ)ᵢ`, `sᵢ ∈ Γ(N, W ∩ Vᵢ)`,
with `sᵢ = cᵢⱼ • sⱼ` on `W ∩ Vᵢ ∩ Vⱼ`. -/
noncomputable def modTwistSubmodule (c : ModCocycle V) (W : Opens Y.toPresheafedSpace) :
    Submodule Γᵧ(W) (ModTwistAmb N V W) where
  carrier := {s | ∀ i j, (s i |ₘ (W ⊓ (V i ⊓ V j))) =
    (c.g i j |ₒ (W ⊓ (V i ⊓ V j))) • (s j |ₘ (W ⊓ (V i ⊓ V j)))}
  add_mem' {s t} hs ht i j := by
    simp only [Set.mem_setOf_eq, ModTwistAmb.add_apply, modRes_add, hs i j, ht i j,
      smul_add] at *
  zero_mem' i j := by simp only [ModTwistAmb.zero_apply, modRes_zero, smul_zero]
  smul_mem' r s hs i j := by
    simp only [Set.mem_setOf_eq, ModTwistAmb.smul_apply, modRes_smul, yres_res] at *
    rw [hs i j, smul_smul, smul_smul, mul_comm]

variable {N}

/-- Restriction of families of sections. -/
noncomputable def ModTwistAmb.res {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) :
    ModTwistAmb N V W →+ ModTwistAmb N V W' where
  toFun s i := s i |ₘ (W' ⊓ V i)
  map_zero' := funext fun i ↦ modRes_zero _
  map_add' s t := funext fun i ↦ modRes_add _ _ _

lemma ModTwistAmb.res_apply {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (s : ModTwistAmb N V W) (i : ι) : ModTwistAmb.res h s i = s i |ₘ (W' ⊓ V i) :=
  rfl

lemma ModTwistAmb.res_smul {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (r : Γᵧ(W))
    (s : ModTwistAmb N V W) :
    ModTwistAmb.res h (r • s) = (r |ₒ W') • ModTwistAmb.res h s := by
  funext i
  simp only [ModTwistAmb.res_apply, ModTwistAmb.smul_apply]
  rw [modRes_smul]
  simp only [yres_res]

lemma ModTwistAmb.res_mem (c : ModCocycle V) {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (s : ModTwistAmb N V W) (hs : s ∈ modTwistSubmodule N c W) :
    ModTwistAmb.res h s ∈ modTwistSubmodule N c W' := by
  intro i j
  have := congrArg (fun x ↦ modRes x (W' ⊓ (V i ⊓ V j)) (by order)) (hs i j)
  simp only [modRes_smul, modRes_res, yres_res] at this
  simpa only [ModTwistAmb.res_apply, modRes_res] using this

variable (N)

/-- The underlying abelian presheaf of the twist. -/
noncomputable def modTwistPresheaf (c : ModCocycle V) :
    (Opens Y.toPresheafedSpace)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (modTwistSubmodule N c W.unop)
  map {W W'} f := AddCommGrpCat.ofHom
    { toFun s := ⟨ModTwistAmb.res f.unop.le s.1, ModTwistAmb.res_mem c f.unop.le s.1 s.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' s t := Subtype.ext (map_add _ _ _) }
  map_id W := by
    ext s
    funext i
    exact modRes_self (s.1 i)
  map_comp f f' := by
    ext s
    funext i
    exact (modRes_res _ _ (s.1 i)).symm

noncomputable instance (c : ModCocycle V) (W : (Opens Y.toPresheafedSpace)ᵒᵖ) :
    Module (Y.ringSheaf.obj.obj W) ((modTwistPresheaf N c).obj W) :=
  inferInstanceAs (Module (Y.presheaf.obj W) (modTwistSubmodule N c W.unop))

/-- The twist of `N` by `c`, as a presheaf of modules. -/
noncomputable def modTwistPresheafOfModules (c : ModCocycle V) :
    PresheafOfModules.{u} Y.ringSheaf.obj :=
  PresheafOfModules.ofPresheaf (modTwistPresheaf N c) fun _ _ f r s ↦
    Subtype.ext (ModTwistAmb.res_smul f.unop.le r s.1)

lemma isSheaf_modTwistPresheaf (c : ModCocycle V) :
    TopCat.Presheaf.IsSheaf (modTwistPresheaf N c) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hsf' (a b : κ) (i : ι) :
      ((sf a).1 i |ₘ (W a ⊓ W b ⊓ V i)) = ((sf b).1 i |ₘ (W a ⊓ W b ⊓ V i)) :=
    congrArg (fun x : modTwistSubmodule N c (W a ⊓ W b) ↦ x.1 i) (hsf a b)
  have key (i : ι) : ∃! t : N.val.obj (op (iSup W ⊓ V i)), ∀ a,
      modRes t (W a ⊓ V i) (by have := le_iSup W a; order) = (sf a).1 i := by
    refine modRes_existsUnique_gluing N (fun a ↦ W a ⊓ V i) (by rw [iSup_inf_eq]) _ _ ?_
    intro a b
    have := congrArg (fun x ↦ modRes x (W a ⊓ V i ⊓ (W b ⊓ V i)) (by order)) (hsf' a b i)
    simpa only [modRes_res] using this
  choose t ht hu using key
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun a ↦ ?_, fun s hs ↦ ?_⟩
  · refine modRes_eq_of_cover N (fun a ↦ W a ⊓ (V i ⊓ V j)) (by rw [iSup_inf_eq])
      (fun a ↦ by have := le_iSup W a; order) _ _ fun a ↦ ?_
    simp only [modRes_res, modRes_smul, yres_res]
    have hi := congrArg (fun x ↦ modRes x (W a ⊓ (V i ⊓ V j)) (by order)) (ht i a)
    have hj := congrArg (fun x ↦ modRes x (W a ⊓ (V i ⊓ V j)) (by order)) (ht j a)
    simp only [modRes_res] at hi hj
    rw [hi, hj]
    exact (sf a).2 i j
  · exact Subtype.ext (funext fun i ↦ ht i a)
  · refine Subtype.ext (funext fun i ↦ hu i _ fun a ↦ ?_)
    exact congrArg (fun x : modTwistSubmodule N c (W a) ↦ x.1 i) (hs a)

/-- The **twist** `N ⊗ L_c` of a sheaf of `𝒪_Y`-modules `N` by a cocycle `c`: its sections over
`W` are the families `(sᵢ)ᵢ`, `sᵢ ∈ Γ(N, W ∩ Vᵢ)`, with `sᵢ = cᵢⱼ • sⱼ` on `W ∩ Vᵢ ∩ Vⱼ`. -/
noncomputable def modTwist (c : ModCocycle V) : SheafOfModules.{u} Y.ringSheaf where
  val := modTwistPresheafOfModules N c
  isSheaf := isSheaf_modTwistPresheaf N c

variable {N} {c : ModCocycle V} {W : Opens Y.toPresheafedSpace}

/-- The `i`-th component `sᵢ ∈ Γ(N, W ∩ Vᵢ)` of a section `s` of the twist `N ⊗ L_c`. -/
def modTwistComp (s : (modTwist N c).val.obj (op W)) (i : ι) : N.val.obj (op (W ⊓ V i)) :=
  (show modTwistSubmodule N c W from s).1 i

lemma modTwistComp_compat (s : (modTwist N c).val.obj (op W)) (i j : ι) :
    (modTwistComp s i |ₘ (W ⊓ (V i ⊓ V j))) =
      (c.g i j |ₒ (W ⊓ (V i ⊓ V j))) • (modTwistComp s j |ₘ (W ⊓ (V i ⊓ V j))) :=
  (show modTwistSubmodule N c W from s).2 i j

/-- The section of `N ⊗ L_c` over `W` with components `sᵢ`. -/
def modTwistMk (s : ∀ i, N.val.obj (op (W ⊓ V i)))
    (hs : ∀ i j, (s i |ₘ (W ⊓ (V i ⊓ V j))) =
      (c.g i j |ₒ (W ⊓ (V i ⊓ V j))) • (s j |ₘ (W ⊓ (V i ⊓ V j)))) :
    (modTwist N c).val.obj (op W) :=
  show modTwistSubmodule N c W from ⟨s, hs⟩

@[simp]
lemma modTwistComp_modTwistMk (s : ∀ i, N.val.obj (op (W ⊓ V i))) (hs) (i : ι) :
    modTwistComp (modTwistMk (c := c) s hs) i = s i :=
  rfl

@[ext]
lemma modTwist_ext {s t : (modTwist N c).val.obj (op W)}
    (h : ∀ i, modTwistComp s i = modTwistComp t i) : s = t :=
  Subtype.ext (funext h)

@[simp]
lemma modTwistComp_add (s t : (modTwist N c).val.obj (op W)) (i : ι) :
    modTwistComp (s + t) i = modTwistComp s i + modTwistComp t i :=
  rfl

@[simp]
lemma modTwistComp_zero (i : ι) : modTwistComp (0 : (modTwist N c).val.obj (op W)) i = 0 :=
  rfl

lemma modTwistComp_smul (r : Γᵧ(W)) (s : (modTwist N c).val.obj (op W)) (i : ι) :
    modTwistComp (r • s) i = (r |ₒ (W ⊓ V i)) • modTwistComp s i :=
  rfl

lemma modTwistComp_res {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (s : (modTwist N c).val.obj (op W)) (i : ι) :
    modTwistComp (modRes s W' h) i = modTwistComp s i |ₘ (W' ⊓ V i) :=
  rfl

/-- The components of a section of `N ⊗ L_c` restricted to a smaller open. -/
lemma modTwistComp_compat_res (s : (modTwist N c).val.obj (op W)) (i j : ι)
    (W' : Opens Y.toPresheafedSpace) (hW : W' ≤ W ⊓ (V i ⊓ V j)) :
    modRes (modTwistComp s i) W' (by order) =
      (c.g i j |ₒ W') • modRes (modTwistComp s j) W' (by order) := by
  have := congrArg (fun x ↦ modRes x W' hW) (modTwistComp_compat s i j)
  simpa only [modRes_res, modRes_smul, yres_res] using this

variable (c) in
/-- The map on twists induced by a morphism of sheaves of modules. -/
noncomputable def modTwistMap {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M) :
    modTwist N c ⟶ modTwist M c :=
  modHomMk (fun W ↦
    { toFun s := modTwistMk (fun i ↦ φ.val.app _ (modTwistComp s i)) fun i j ↦ by
        rw [← modHom_modRes, ← modHom_modRes, modTwistComp_compat, modHom_smul]
      map_zero' := by ext i; simp
      map_add' s t := by ext i; simp })
    (fun W r s ↦ by ext i; simp [modTwistComp_smul])
    (fun W W' h s ↦ by ext i; simp [modTwistComp_res, modHom_modRes])

@[simp]
lemma modTwistComp_modTwistMap_app {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M)
    (s : (modTwist N c).val.obj (op W)) (i : ι) :
    modTwistComp ((modTwistMap c φ).val.app (op W) s) i = φ.val.app _ (modTwistComp s i) :=
  rfl

variable (c) in
/-- Twisting by `c` as a functor. -/
noncomputable def modTwistFunctor :
    SheafOfModules.{u} Y.ringSheaf ⥤ SheafOfModules.{u} Y.ringSheaf where
  obj N := modTwist N c
  map φ := modTwistMap c φ
  map_id N := modHom_ext fun W s ↦ by ext i; rfl
  map_comp φ ψ := modHom_ext fun W s ↦ by ext i; rfl

@[simp]
lemma modTwistFunctor_obj (N : SheafOfModules.{u} Y.ringSheaf) :
    (modTwistFunctor c).obj N = modTwist N c :=
  rfl

@[simp]
lemma modTwistFunctor_map {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M) :
    (modTwistFunctor c).map φ = modTwistMap c φ :=
  rfl

section Chart

variable (c) (i : ι) (hW : W ≤ V i)

/-- **Trivialisation on `Vᵢ`**: for `W ≤ Vᵢ`, a section of `N ⊗ L_c` over `W` is determined by
its `i`-th component, `s ↦ sᵢ`, with inverse `t ↦ (cₖᵢ • t)ₖ`. -/
noncomputable def modTwistSectionsEquiv :
    (modTwist N c).val.obj (op W) ≃ₗ[Γᵧ(W)] N.val.obj (op W) where
  toFun s := modTwistComp s i |ₘ W
  invFun t := modTwistMk (fun k ↦ (c.g k i |ₒ (W ⊓ V k)) • (t |ₘ (W ⊓ V k))) fun k l ↦ by
    simp only [modRes_smul, yres_res, modRes_res, smul_smul]
    rw [c.mul_res k l i _ (by order)]
  map_add' s t := by simp [modRes_add]
  map_smul' r s := by
    simp only [modTwistComp_smul, modRes_smul, yres_res, yres_self, RingHom.id_apply]
  left_inv s := by
    ext k
    simp only [modTwistComp_modTwistMk, modRes_res]
    rw [← modTwistComp_compat_res s k i _ (by order), modRes_self]
  right_inv t := by
    simp only [modTwistComp_modTwistMk, modRes_smul, yres_res, modRes_res, modRes_self]
    rw [c.self_res i W (by order), one_smul]

lemma modTwistSectionsEquiv_apply (s : (modTwist N c).val.obj (op W)) :
    modTwistSectionsEquiv c i hW s = modTwistComp s i |ₘ W :=
  rfl

lemma modTwistSectionsEquiv_res {W' : Opens Y.toPresheafedSpace} (hW' : W' ≤ W)
    (s : (modTwist N c).val.obj (op W)) :
    modTwistSectionsEquiv c i (hW'.trans hW) (modRes s W' hW') =
      modRes (modTwistSectionsEquiv c i hW s) W' hW' := by
  simp only [modTwistSectionsEquiv_apply, modTwistComp_res, modRes_res]

/-- Changing the chart used to trivialise `N ⊗ L_c` multiplies by the transition function. -/
lemma modTwistSectionsEquiv_change (j : ι) (hj : W ≤ V j) (s : (modTwist N c).val.obj (op W)) :
    modTwistSectionsEquiv c i hW s = (c.g i j |ₒ W) • modTwistSectionsEquiv c j hj s := by
  simp only [modTwistSectionsEquiv_apply]
  exact modTwistComp_compat_res s i j W (by order)

end Chart

section One

variable (N)

/-- The map `N ⟶ N ⊗ L_1`, `t ↦ (t|_{Vᵢ})ᵢ`. -/
noncomputable def toModTwistOne : N ⟶ modTwist N (1 : ModCocycle V) :=
  modHomMk (fun W ↦
    { toFun t := modTwistMk (fun i ↦ t |ₘ (W ⊓ V i)) fun i j ↦ by
        simp only [modRes_res, ModCocycle.one_g, yres_one, one_smul]
      map_zero' := by ext i; simp [modRes_zero]
      map_add' s t := by ext i; simp [modRes_add] })
    (fun W r t ↦ by ext i; simp [modTwistComp_smul, modRes_smul])
    (fun W W' h t ↦ by ext i; simp [modTwistComp_res, modRes_res])

@[simp]
lemma modTwistComp_toModTwistOne_app (t : N.val.obj (op W)) (i : ι) :
    modTwistComp ((toModTwistOne (V := V) N).val.app (op W) t) i = t |ₘ (W ⊓ V i) :=
  rfl

variable {N}

lemma toModTwistOne_bijective (hV : ⨆ i, V i = ⊤) (W : Opens Y.toPresheafedSpace) :
    Function.Bijective ((toModTwistOne (V := V) N).val.app (op W)) := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by rw [← inf_iSup_eq, hV, inf_top_eq]
  refine ⟨fun t t' h ↦ ?_, fun s ↦ ?_⟩
  · exact modRes_eq_of_cover N _ hcov (fun _ ↦ inf_le_left) t t' fun i ↦
      congrArg (fun x ↦ modTwistComp x i) h
  · obtain ⟨t, ht, -⟩ := modRes_existsUnique_gluing N (fun i ↦ W ⊓ V i) hcov
      (fun _ ↦ inf_le_left) (modTwistComp s) fun i j ↦ by
        rw [modTwistComp_compat_res s i j _ (by order)]
        simp only [ModCocycle.one_g, yres_one, one_smul]
    exact ⟨t, modTwist_ext fun i ↦ ht i⟩

variable (N) in
/-- **The twist by the trivial cocycle** is `N` itself, if the `Vᵢ` cover `Y`. -/
noncomputable def modTwistOneIso (hV : ⨆ i, V i = ⊤) : modTwist N (1 : ModCocycle V) ≅ N :=
  (modIsoOfBijective (toModTwistOne N) (toModTwistOne_bijective hV)).symm

@[reassoc]
lemma toModTwistOne_naturality {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M) :
    φ ≫ toModTwistOne (V := V) M = toModTwistOne N ≫ modTwistMap 1 φ :=
  modHom_ext fun W t ↦ by ext i; simp [modHom_modRes]

variable (V) in
/-- Twisting by the trivial cocycle is isomorphic to the identity, if the `Vᵢ` cover `Y`. -/
noncomputable def modTwistFunctorOneIso (hV : ⨆ i, V i = ⊤) :
    modTwistFunctor (1 : ModCocycle V) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦ modTwistOneIso N hV) fun {N M} φ ↦ by
    change modTwistMap 1 φ ≫ (modTwistOneIso M hV).hom = (modTwistOneIso N hV).hom ≫ φ
    rw [← cancel_epi (modTwistOneIso N hV).inv, Iso.inv_hom_id_assoc]
    change toModTwistOne N ≫ _ ≫ _ = _
    rw [← toModTwistOne_naturality_assoc]
    change φ ≫ (modTwistOneIso M hV).inv ≫ (modTwistOneIso M hV).hom = φ
    rw [Iso.inv_hom_id, Category.comp_id]

end One

section TwistTwist

variable (c d : ModCocycle V)

/-- The map `(N ⊗ L_c) ⊗ L_d ⟶ N ⊗ L_{cd}`. -/
noncomputable def modTwistTwistHom : modTwist (modTwist N c) d ⟶ modTwist N (c * d) :=
  modHomMk (fun W ↦
    { toFun s := modTwistMk (fun i ↦ modTwistSectionsEquiv c i inf_le_right (modTwistComp s i))
        fun i j ↦ by
          rw [← modTwistSectionsEquiv_res c i inf_le_right, modTwistComp_compat s i j,
            LinearEquiv.map_smul, modTwistSectionsEquiv_change c i _ j (by order),
            modTwistSectionsEquiv_res c j inf_le_right, smul_smul, ModCocycle.mul_g, yres_mul,
            mul_comm]
      map_zero' := by ext i; simp
      map_add' s t := by ext i; simp })
    (fun W r t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, modTwistComp_modTwistMk,
        modTwistComp_smul, LinearEquiv.map_smul])
    (fun W W' h t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, modTwistComp_modTwistMk,
        modTwistComp_res]
      exact modTwistSectionsEquiv_res c i inf_le_right _ _)

@[simp]
lemma modTwistComp_modTwistTwistHom_app (s : (modTwist (modTwist N c) d).val.obj (op W))
    (i : ι) :
    modTwistComp ((modTwistTwistHom c d).val.app (op W) s) i =
      modTwistSectionsEquiv c i inf_le_right (modTwistComp s i) :=
  rfl

lemma modTwistTwistHom_bijective (W : Opens Y.toPresheafedSpace) :
    Function.Bijective ((modTwistTwistHom (N := N) c d).val.app (op W)) := by
  refine ⟨fun s s' h ↦ modTwist_ext fun i ↦
    (modTwistSectionsEquiv c i inf_le_right).injective ?_, fun t ↦ ?_⟩
  · simpa using congrArg (fun x ↦ modTwistComp x i) h
  refine ⟨modTwistMk (fun i ↦ (modTwistSectionsEquiv c i inf_le_right).symm (modTwistComp t i))
    fun i j ↦ ?_, modTwist_ext fun i ↦ ?_⟩
  · apply (modTwistSectionsEquiv c i (by order : W ⊓ (V i ⊓ V j) ≤ V i)).injective
    rw [LinearEquiv.map_smul, modTwistSectionsEquiv_res c i inf_le_right,
      LinearEquiv.apply_symm_apply]
    conv_rhs => rw [modTwistSectionsEquiv_change c i _ j (by order),
      modTwistSectionsEquiv_res c j inf_le_right, LinearEquiv.apply_symm_apply]
    rw [smul_smul, ← yres_mul, mul_comm (d.g i j)]
    exact modTwistComp_compat t i j
  · simp

@[reassoc]
lemma modTwistTwistHom_naturality {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M) :
    modTwistMap d (modTwistMap c φ) ≫ modTwistTwistHom c d =
      modTwistTwistHom c d ≫ modTwistMap (c * d) φ :=
  modHom_ext fun W t ↦ by
    ext i
    simp [modTwistSectionsEquiv_apply, modHom_modRes]

/-- `(modTwistFunctor c ⋙ modTwistFunctor d) ≅ modTwistFunctor (c * d)`. -/
noncomputable def modTwistFunctorCompIso :
    modTwistFunctor c ⋙ modTwistFunctor d ≅ modTwistFunctor (c * d) :=
  NatIso.ofComponents
    (fun N ↦ modIsoOfBijective (modTwistTwistHom (N := N) c d) (modTwistTwistHom_bijective c d))
    fun φ ↦ modTwistTwistHom_naturality c d φ

end TwistTwist

variable (N) in
/-- The identification `N ⊗ L_c ⟶ N ⊗ L_d` for equal cocycles `c = d`. -/
noncomputable def modTwistCongrHom {c d : ModCocycle V} (h : c = d) :
    modTwist N c ⟶ modTwist N d :=
  modHomMk (fun W ↦
    { toFun s := modTwistMk (modTwistComp s) fun i j ↦ by
        rw [← h]; exact modTwistComp_compat s i j
      map_zero' := rfl
      map_add' _ _ := rfl })
    (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)

/-- Twisting by equal cocycles gives isomorphic functors (the identity on components). -/
noncomputable def modTwistFunctorCongr {c d : ModCocycle V} (h : c = d) :
    modTwistFunctor c ≅ modTwistFunctor d :=
  NatIso.ofComponents
    (fun N ↦ modIsoMk (modTwistCongrHom N h) (modTwistCongrHom N h.symm) (fun _ _ ↦ rfl)
      fun _ _ ↦ rfl)
    fun _ ↦ modHom_ext fun _ _ ↦ rfl

section Equivalence

variable (c) (hV : ⨆ i, V i = ⊤)

/-- **Twisting is an autoequivalence**: if the `Vᵢ` cover `Y`, twisting by `c` is an
equivalence of the category of sheaves of `𝒪_Y`-modules, with inverse the twist by `c⁻¹`. -/
noncomputable def modTwistEquivalence :
    SheafOfModules.{u} Y.ringSheaf ≌ SheafOfModules.{u} Y.ringSheaf :=
  CategoryTheory.Equivalence.mk (modTwistFunctor c) (modTwistFunctor c⁻¹)
    ((modTwistFunctorOneIso V hV).symm ≪≫ modTwistFunctorCongr (mul_inv_cancel c).symm ≪≫
      (modTwistFunctorCompIso c c⁻¹).symm)
    (modTwistFunctorCompIso c⁻¹ c ≪≫ modTwistFunctorCongr (inv_mul_cancel c) ≪≫
      modTwistFunctorOneIso V hV)

@[simp]
lemma modTwistEquivalence_functor : (modTwistEquivalence c hV).functor = modTwistFunctor c :=
  rfl

@[simp]
lemma modTwistEquivalence_inverse : (modTwistEquivalence c hV).inverse = modTwistFunctor c⁻¹ :=
  rfl

end Equivalence

end Twist

end AlgebraicGeometry.LocallyRingedSpace

end
