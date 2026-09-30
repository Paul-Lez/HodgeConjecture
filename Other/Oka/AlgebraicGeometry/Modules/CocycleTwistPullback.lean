/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwist
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules

/-!
# Pullback of a twisted structure sheaf along a morphism of locally ringed spaces

Let `X` be a scheme, `c` a cocycle on a family of opens `U : ι → X.Opens` covering `X`, and
`L_c = 𝒪_X ⊗ L_c` the twist of the structure sheaf by `c` (`Scheme.Modules.twist`). For a
morphism of locally ringed spaces `f : Y ⟶ X`, the transition functions pull back to
`f^♯ cᵢⱼ ∈ Γ(Y, f⁻¹ Uᵢ ∩ f⁻¹ Uⱼ)`, and the families `(tᵢ)ᵢ`, `tᵢ ∈ Γ(Y, W ∩ f⁻¹ Uᵢ)`, with
`tᵢ = f^♯ cᵢⱼ · tⱼ` form a sheaf of `𝒪_Y`-modules `pbTwist f c`. We show

  `f^* L_c ≅ pbTwist f c`  (`LocallyRingedSpace.pullbackTwistUnitIso`).

The map `f^* L_c ⟶ pbTwist f c` is adjoint to `L_c ⟶ f_* pbTwist f c`, `s ↦ (f^♯ sᵢ)ᵢ`; the
inverse glues the local sections `tᵢ • eᵢ`, where `eᵢ` is the image in `f^* L_c` of the frame of
`L_c` over `Uᵢ` (the section with `i`-th component `1`). Both composites are checked on sections,
the second one after transposing along the adjunction `f^* ⊣ f_*`.

In particular the sections of `f^* L_c` over any open are explicit families of sections of
`𝒪_Y`, compatibly with restriction. This is how the analytification of the twisting sheaves
`𝒪(k)` on `ℙⁿ` is described.

## Main definitions and results

- `LocallyRingedSpace.pbTwist f c`: the twisted structure sheaf on `Y`, with components
  `pbComp`, constructor `pbMk` and extensionality `pbTwist_ext`.
- `LocallyRingedSpace.twistUnit c`: the twist `L_c` of `𝒪_X`, and `pbTwistUnit f c = f^* L_c`.
- `LocallyRingedSpace.pullbackTwistUnitIso f c hU : f^* L_c ≅ pbTwist f c`.
- `LocallyRingedSpace.pbTwistSectionsEquiv c i hW`: over `W ≤ f⁻¹ Uᵢ`, sections of `pbTwist f c`
  are sections of `𝒪_Y` (`t ↦ tᵢ`), compatibly with restriction.
- Auxiliary: `modRes` (restriction of sections of a sheaf of `𝒪_Y`-modules), `modHomMk`
  (morphisms from compatible linear maps on sections).
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

section Res

variable {Y : LocallyRingedSpace.{u}} {V W W' : Opens Y.toPresheafedSpace}

lemma yres_mul (h : W ≤ V) (r s : Γᵧ(V)) :
    TopCat.Presheaf.restrictOpen (r * s) W h =
      TopCat.Presheaf.restrictOpen r W h * TopCat.Presheaf.restrictOpen s W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma yres_add (h : W ≤ V) (r s : Γᵧ(V)) :
    TopCat.Presheaf.restrictOpen (r + s) W h =
      TopCat.Presheaf.restrictOpen r W h + TopCat.Presheaf.restrictOpen s W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma yres_zero (h : W ≤ V) : TopCat.Presheaf.restrictOpen (0 : Γᵧ(V)) W h = 0 := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma yres_one (h : W ≤ V) : TopCat.Presheaf.restrictOpen (1 : Γᵧ(V)) W h = 1 := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma yres_res (h : W ≤ V) (h' : W' ≤ W) (x : Γᵧ(V)) :
    TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen x W h) W' h' =
      TopCat.Presheaf.restrictOpen x W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma yres_self (x : Γᵧ(V)) : TopCat.Presheaf.restrictOpen x V le_rfl = x :=
  TopCat.Presheaf.restrict_self _

end Res

variable {Y : LocallyRingedSpace.{u}} {X : Scheme.{u}} (f : Y ⟶ X.toLocallyRingedSpace)

/-- The preimage of an open under a morphism of locally ringed spaces, as an open of the site of
`ringSheaf`. -/
abbrev preimOpen (V : X.Opens) : Opens Y.toPresheafedSpace := (Opens.map f.base).obj V

lemma preimOpen_inf (V W : X.Opens) : preimOpen f (V ⊓ W) = preimOpen f V ⊓ preimOpen f W := rfl

/-- The pullback `f^♯ x ∈ Γ(Y, f⁻¹ V)` of a section `x ∈ Γ(X, V)`. -/
noncomputable abbrev pbSec {V : X.Opens} (x : Γ(X, V)) : Γᵧ(preimOpen f V) :=
  (f.c.app (op V)).hom x

variable {ι : Type} {U : ι → X.Opens} (c : Cocycle U)

/-- The pulled back transition functions `f^♯ cᵢⱼ ∈ Γ(Y, f⁻¹ Uᵢ ∩ f⁻¹ Uⱼ)`. -/
noncomputable def pbG (i j : ι) : Y.presheaf.obj (op (preimOpen f (U i) ⊓ preimOpen f (U j))) :=
  pbSec f (c.g i j)

/-- The families `(tᵢ)ᵢ` of sections `tᵢ ∈ Γ(Y, W ∩ f⁻¹ Uᵢ)`. -/
def PbAmb (W : Opens Y.toPresheafedSpace) : Type u := ∀ i, Γᵧ(W ⊓ preimOpen f (U i))

noncomputable instance (W : Opens Y.toPresheafedSpace) : CommRing (PbAmb f (U := U) W) :=
  inferInstanceAs (CommRing (∀ i, Γᵧ(W ⊓ preimOpen f (U i))))

noncomputable instance (W : Opens Y.toPresheafedSpace) :
    Module (Γᵧ(W)) (PbAmb f (U := U) W) :=
  letI (i : ι) : Module (Γᵧ(W)) (Γᵧ(W ⊓ preimOpen f (U i))) :=
    Module.compHom _ (Y.presheaf.map (homOfLE (inf_le_left : W ⊓ preimOpen f (U i) ≤ W)).op).hom
  inferInstanceAs (Module (Γᵧ(W)) (∀ i, Γᵧ(W ⊓ preimOpen f (U i))))

lemma PbAmb.smul_apply {W : Opens Y.toPresheafedSpace} (r : Γᵧ(W))
    (s : PbAmb f (U := U) W) (i : ι) : (r • s) i = (r |ₒ (W ⊓ preimOpen f (U i))) * s i :=
  rfl

/-- The compatible families: `tᵢ = f^♯ cᵢⱼ · tⱼ` on `W ∩ f⁻¹ Uᵢ ∩ f⁻¹ Uⱼ`. -/
noncomputable def pbTwistSubmodule (W : Opens Y.toPresheafedSpace) :
    Submodule (Γᵧ(W)) (PbAmb f (U := U) W) where
  carrier := {s | ∀ i j, (s i |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) =
    (pbG f c i j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) *
      (s j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))))}
  add_mem' {s t} hs ht i j := by
    simp only [Set.mem_setOf_eq] at *
    change ((s i + t i) |ₒ _) = _ * ((s j + t j) |ₒ _)
    rw [yres_add, yres_add, hs i j, ht i j, mul_add]
  zero_mem' i j := by
    change ((0 : Y.presheaf.obj _) |ₒ _) = _ * ((0 : Y.presheaf.obj _) |ₒ _)
    rw [yres_zero, yres_zero, mul_zero]
  smul_mem' r s hs i j := by
    simp only [Set.mem_setOf_eq] at *
    rw [PbAmb.smul_apply, PbAmb.smul_apply, yres_mul, yres_mul, hs i j, yres_res, yres_res]
    ring


variable {f c}

/-- Restriction of families of sections. -/
noncomputable def PbAmb.res {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) :
    PbAmb f (U := U) W →+* PbAmb f (U := U) W' where
  toFun s i := s i |ₒ (W' ⊓ preimOpen f (U i))
  map_zero' := funext fun i ↦ yres_zero _
  map_one' := funext fun i ↦ yres_one _
  map_add' s t := funext fun i ↦ yres_add _ _ _
  map_mul' s t := funext fun i ↦ yres_mul _ _ _

lemma PbAmb.res_apply {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (s : PbAmb f (U := U) W)
    (i : ι) : PbAmb.res h s i = s i |ₒ (W' ⊓ preimOpen f (U i)) :=
  rfl

lemma PbAmb.res_smul {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (r : Γᵧ(W))
    (s : PbAmb f (U := U) W) : PbAmb.res h (r • s) = (r |ₒ W') • PbAmb.res h s := by
  funext i
  simp only [PbAmb.res_apply, PbAmb.smul_apply, yres_mul, yres_res]

lemma PbAmb.res_mem {W W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (s : PbAmb f (U := U) W)
    (hs : s ∈ pbTwistSubmodule f c W) : PbAmb.res h s ∈ pbTwistSubmodule f c W' := by
  intro i j
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x
    (W' ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) (by order)) (hs i j)
  simp only [yres_mul, yres_res] at this
  simpa only [PbAmb.res_apply, yres_res] using this

variable (f c)

/-- The underlying abelian presheaf of `pbTwist f c`. -/
noncomputable def pbTwistPresheaf : (Opens Y.toPresheafedSpace)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (pbTwistSubmodule f c W.unop)
  map {W W'} h := AddCommGrpCat.ofHom
    { toFun s := ⟨PbAmb.res h.unop.le s.1, PbAmb.res_mem h.unop.le s.1 s.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' s t := Subtype.ext (map_add _ _ _) }
  map_id W := by
    ext s
    funext i
    exact yres_self (s.1 i)
  map_comp h h' := by
    ext s
    funext i
    exact (yres_res _ _ (s.1 i)).symm

noncomputable instance (W : (Opens Y.toPresheafedSpace)ᵒᵖ) :
    Module (Y.ringSheaf.obj.obj W) ((pbTwistPresheaf f c).obj W) :=
  inferInstanceAs (Module (Y.presheaf.obj W) (pbTwistSubmodule f c W.unop))

/-- `pbTwist f c` as a presheaf of modules. -/
noncomputable def pbTwistPresheafOfModules : PresheafOfModules.{u} Y.ringSheaf.obj :=
  PresheafOfModules.ofPresheaf (pbTwistPresheaf f c) fun _ _ h r s ↦
    Subtype.ext (PbAmb.res_smul h.unop.le r s.1)

lemma isSheaf_pbTwistPresheaf : TopCat.Presheaf.IsSheaf (pbTwistPresheaf f c) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hsf' (a b : κ) (i : ι) :
      ((sf a).1 i |ₒ (W a ⊓ W b ⊓ preimOpen f (U i))) =
        ((sf b).1 i |ₒ (W a ⊓ W b ⊓ preimOpen f (U i))) :=
    congrArg (fun x : pbTwistSubmodule f c (W a ⊓ W b) ↦ x.1 i) (hsf a b)
  have key (i : ι) : ∃! t : Γᵧ(iSup W ⊓ preimOpen f (U i)), ∀ a,
      TopCat.Presheaf.restrictOpen t (W a ⊓ preimOpen f (U i))
        (by have := le_iSup W a; order) = (sf a).1 i := by
    refine TopCat.Sheaf.existsUnique_gluing' Y.sheaf (fun a ↦ W a ⊓ preimOpen f (U i)) _
      (fun a ↦ homOfLE (by have := le_iSup W a; order)) (by rw [iSup_inf_eq]) _ ?_
    intro a b
    have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x
      (W a ⊓ preimOpen f (U i) ⊓ (W b ⊓ preimOpen f (U i))) (by order)) (hsf' a b i)
    simp only [yres_res] at this
    exact this
  choose t ht hu using key
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun a ↦ ?_, fun s hs ↦ ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf
      (fun a ↦ W a ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) _
      (fun a ↦ homOfLE (by have := le_iSup W a; order)) (by rw [iSup_inf_eq]) _ _ fun a ↦ ?_
    have hi := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x
      (W a ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) (by order)) (ht i a)
    have hj := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x
      (W a ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) (by order)) (ht j a)
    simp only [yres_res] at hi hj
    have key : TopCat.Presheaf.restrictOpen
        (t i |ₒ (iSup W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))))
        (W a ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) (by have := le_iSup W a; order) =
      TopCat.Presheaf.restrictOpen
        ((pbG f c i j |ₒ (iSup W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) *
        (t j |ₒ (iSup W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))))
        (W a ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) (by have := le_iSup W a; order) := by
      rw [yres_res, yres_mul, yres_res, yres_res, hi, hj]
      exact (sf a).2 i j
    exact key
  · exact Subtype.ext (funext fun i ↦ ht i a)
  · refine Subtype.ext (funext fun i ↦ hu i _ fun a ↦ ?_)
    exact congrArg (fun x : pbTwistSubmodule f c (W a) ↦ x.1 i) (hs a)

/-- The **twisted structure sheaf** `f^♯ L_c` on `Y`: its sections over `W` are the families
`(tᵢ)ᵢ`, `tᵢ ∈ Γ(Y, W ∩ f⁻¹ Uᵢ)`, with `tᵢ = f^♯ cᵢⱼ · tⱼ`. -/
noncomputable def pbTwist : SheafOfModules.{u} Y.ringSheaf where
  val := pbTwistPresheafOfModules f c
  isSheaf := isSheaf_pbTwistPresheaf f c


variable {f c} {W : Opens Y.toPresheafedSpace}

/-- The `i`-th component of a section of `pbTwist f c`. -/
def pbComp (s : (pbTwist f c).val.obj (op W)) (i : ι) : Γᵧ(W ⊓ preimOpen f (U i)) :=
  (show pbTwistSubmodule f c W from s).1 i

lemma pbComp_compat (s : (pbTwist f c).val.obj (op W)) (i j : ι) :
    (pbComp s i |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) =
      (pbG f c i j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) *
        (pbComp s j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) :=
  (show pbTwistSubmodule f c W from s).2 i j

/-- The section of `pbTwist f c` with given components. -/
def pbMk (s : ∀ i, Γᵧ(W ⊓ preimOpen f (U i)))
    (hs : ∀ i j, (s i |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) =
      (pbG f c i j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))) *
        (s j |ₒ (W ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))))) : (pbTwist f c).val.obj (op W) :=
  show pbTwistSubmodule f c W from ⟨s, hs⟩

@[simp]
lemma pbComp_pbMk (s : ∀ i, Γᵧ(W ⊓ preimOpen f (U i))) (hs) (i : ι) :
    pbComp (pbMk (c := c) s hs) i = s i :=
  rfl

@[ext]
lemma pbTwist_ext {s t : (pbTwist f c).val.obj (op W)} (h : ∀ i, pbComp s i = pbComp t i) :
    s = t :=
  Subtype.ext (funext h)

@[simp]
lemma pbComp_add (s t : (pbTwist f c).val.obj (op W)) (i : ι) :
    pbComp (s + t) i = pbComp s i + pbComp t i :=
  rfl

@[simp]
lemma pbComp_zero (i : ι) : pbComp (0 : (pbTwist f c).val.obj (op W)) i = 0 :=
  rfl

lemma pbComp_smul (r : Γᵧ(W)) (s : (pbTwist f c).val.obj (op W)) (i : ι) :
    pbComp (r • s) i = (r |ₒ (W ⊓ preimOpen f (U i))) * pbComp s i :=
  rfl

lemma pbComp_res {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (s : (pbTwist f c).val.obj (op W)) (i : ι) :
    pbComp (TopCat.Presheaf.restrictOpen (F := (pbTwist f c).val.presheaf) s W' h) i =
      pbComp s i |ₒ (W' ⊓ preimOpen f (U i)) :=
  rfl


section PbSec

variable (f)

lemma pbSec_res {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    pbSec f (TopCat.Presheaf.restrictOpen x W h) =
      TopCat.Presheaf.restrictOpen (pbSec f x) (preimOpen f W) ((Opens.map f.base).monotone h) := by
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, pbSec]
  exact congr($(f.c.naturality (homOfLE h).op).hom x)

lemma pbSec_mul {V : X.Opens} (x y : Γ(X, V)) : pbSec f (x * y) = pbSec f x * pbSec f y :=
  map_mul _ _ _

lemma pbSec_one {V : X.Opens} : pbSec f (1 : Γ(X, V)) = 1 :=
  map_one _

end PbSec

/-- The `i`-th component of a section of `L_c`, as a section of `𝒪_X`. -/
noncomputable abbrev unitComp {V : X.Opens} (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c,
    V)) (i : ι) :
    Γ(X, V ⊓ U i) :=
  twistComp s i

lemma unitComp_compat {V : X.Opens} (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V))
    (i j : ι) :
    (unitComp s i |ₒ (V ⊓ (U i ⊓ U j))) =
      (c.g i j |ₒ (V ⊓ (U i ⊓ U j))) * (unitComp s j |ₒ (V ⊓ (U i ⊓ U j))) :=
  twistComp_compat s i j

variable (f c) in
/-- The map `L_c ⟶ f_* (f^♯ L_c)`, `s ↦ (f^♯ sᵢ)ᵢ`. -/
noncomputable def toPushforwardPbTwist :
    twist (SheafOfModules.unit X.ringCatSheaf) c ⟶
      ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwist f c) : X.Modules) :=
  Scheme.Modules.homMk (fun V ↦
    { toFun s := pbMk (W := preimOpen f V) (fun i ↦ pbSec f (unitComp s i)) fun i j ↦ by
        have := congrArg (pbSec f) (unitComp_compat s i j)
        rw [pbSec_mul, pbSec_res, pbSec_res, pbSec_res] at this
        exact this
      map_zero' := pbTwist_ext (W := preimOpen f V) fun i ↦ map_zero (f.c.app _).hom
      map_add' s t := pbTwist_ext (W := preimOpen f V) fun i ↦ map_add (f.c.app _).hom _ _ })
    (fun V r s ↦ pbTwist_ext (W := preimOpen f V) fun i ↦ by
      change pbSec f ((r |ₒ (V ⊓ U i)) * unitComp s i) =
        TopCat.Presheaf.restrictOpen (pbSec f r) (preimOpen f (V ⊓ U i))
          ((Opens.map f.base).monotone inf_le_left) * pbSec f (unitComp s i)
      rw [pbSec_mul, pbSec_res])
    (fun V W h s ↦ pbTwist_ext (W := preimOpen f W) fun i ↦ by
      change pbSec f (TopCat.Presheaf.restrictOpen _ _ _) = _
      rw [pbSec_res]
      rfl)


section ModRes

variable {N : SheafOfModules.{u} Y.ringSheaf} {V W W' : Opens Y.toPresheafedSpace}

/-- Restriction of sections of a sheaf of modules on `Y`. -/
noncomputable def modRes (x : N.val.obj (op V)) (W : Opens Y.toPresheafedSpace) (h : W ≤ V) :
    N.val.obj (op W) :=
  (N.val.map (homOfLE h).op).hom x

lemma modRes_smul (h : W ≤ V) (r : Γᵧ(V)) (x : N.val.obj (op V)) :
    modRes (r • x) W h = (r |ₒ W) • modRes x W h :=
  N.val.map_smul (homOfLE h).op r x

lemma modRes_add (h : W ≤ V) (x y : N.val.obj (op V)) :
    modRes (x + y) W h = modRes x W h + modRes y W h :=
  map_add _ _ _

lemma modRes_zero (h : W ≤ V) : modRes (0 : N.val.obj (op V)) W h = 0 :=
  map_zero _

lemma modRes_res (h : W ≤ V) (h' : W' ≤ W) (x : N.val.obj (op V)) :
    modRes (modRes x W h) W' h' = modRes x W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict (F := N.val.presheaf) _ _ _

lemma modRes_self (x : N.val.obj (op V)) : modRes x V le_rfl = x :=
  TopCat.Presheaf.restrict_self (F := N.val.presheaf) _

end ModRes

section PfHom

variable {N : SheafOfModules.{u} Y.ringSheaf} {M : X.Modules}
  (α : M ⟶ ((SheafOfModules.pushforward f.toRingSheafHom).obj N : X.Modules))

/-- The value of a morphism into a pushforward, as a section over the preimage. -/
noncomputable def pfSec (V : X.Opens) (x : Γ(M, V)) : N.val.obj (op (preimOpen f V)) := α.app V x

lemma pfSec_res {V W : X.Opens} (h : W ≤ V) (x : Γ(M, V)) :
    pfSec α W (TopCat.Presheaf.restrictOpen x W h) =
      modRes (pfSec α V x) (preimOpen f W) ((Opens.map f.base).monotone h) :=
  Hom.app_mres M α h x

lemma pfSec_smul {V : X.Opens} (r : Γ(X, V)) (x : Γ(M, V)) :
    pfSec α V (r • x) = pbSec f r • pfSec α V x :=
  Hom.app_smul α r x

lemma pfSec_add {V : X.Opens} (x y : Γ(M, V)) :
    pfSec α V (x + y) = pfSec α V x + pfSec α V y :=
  map_add _ _ _

end PfHom


section HomMk

variable {P Q : SheafOfModules.{u} Y.ringSheaf}

/-- A morphism of sheaves of modules on `Y` from compatible linear maps on sections. -/
noncomputable def modHomMk (app : ∀ W : Opens Y.toPresheafedSpace, P.val.obj (op W) →+ Q.val.obj
    (op W))
    (map_smul : ∀ W (r : Γᵧ(W)) (x : P.val.obj (op W)), app W (r • x) = r • app W x)
    (naturality : ∀ W W' (h : W' ≤ W) (x : P.val.obj (op W)),
      app W' (modRes x W' h) = modRes (app W x) W' h) : P ⟶ Q :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (app W.unop)
      naturality W W' h := by
        ext x
        exact naturality W.unop W'.unop h.unop.le x }
    (fun W r x ↦ map_smul W.unop r x)⟩

@[simp]
lemma modHomMk_app (app : ∀ W : Opens Y.toPresheafedSpace, P.val.obj (op W) →+ Q.val.obj (op W))
    (map_smul) (naturality) (W : Opens Y.toPresheafedSpace) (x : P.val.obj (op W)) :
    (modHomMk app map_smul naturality).val.app (op W) x = app W x :=
  rfl

lemma modHom_ext {φ ψ : P ⟶ Q}
    (h : ∀ W (x : P.val.obj (op W)), φ.val.app (op W) x = ψ.val.app (op W) x) :
    φ = ψ := by
  apply SheafOfModules.hom_ext
  ext W x
  exact h W.unop x

end HomMk

variable (f c)

/-- The twisted structure sheaf `L_c` on `X`. -/
noncomputable abbrev twistUnit : X.Modules := twist (SheafOfModules.unit X.ringCatSheaf) c

/-- The frame of `L_c` over `Uᵢ`: the section with `i`-th component `1`. -/
noncomputable def twistFrame (i : ι) : Γ(twistUnit c, U i) :=
  (twistSectionsEquiv c i le_rfl).symm ((unitSectionsEquiv X (U i)).symm 1)

/-- The pullback `f^* L_c`. -/
noncomputable def pbTwistUnit : SheafOfModules.{u} Y.ringSheaf := f.pullbackModules.obj (twistUnit
    c)

/-- The unit `L_c ⟶ f_* f^* L_c`. -/
noncomputable def twistUnitη :
    twistUnit c ⟶ ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwistUnit f c) :
        X.Modules) :=
  f.pullbackModulesAdj.unit.app (twistUnit c)


variable {f c}

lemma pbG_mul_pbG (i j : ι) (O : Opens Y.toPresheafedSpace)
    (hO : O ≤ preimOpen f (U i) ⊓ preimOpen f (U j)) :
    TopCat.Presheaf.restrictOpen (pbG f c i j) O hO *
      TopCat.Presheaf.restrictOpen (pbG f c j i) O (hO.trans (inf_comm _ _).le) = 1 := by
  have h := congrArg (fun x : Γ(X, U i ⊓ U j) ↦ TopCat.Presheaf.restrictOpen (pbSec f x) O hO)
    (c.mul_res_symm i j (U i ⊓ U j) le_rfl)
  simp only [pbSec_mul, pbSec_one, yres_one, yres_mul, pbSec_res, yres_res] at h
  exact h

variable (c) in
lemma unitComp_twistFrame_self (i : ι) :
    unitComp (twistFrame c i) i = 1 := by
  change (c.g i i |ₒ (U i ⊓ U i)) * ((1 : Γ(X, U i)) |ₒ (U i ⊓ U i)) = 1
  rw [c.self_res i _ le_rfl, ores_one, one_mul]

/-- A section over `V ≤ Uᵢ` is its `i`-th coordinate times the frame. -/
lemma eq_smul_twistFrame (i : ι) {V : X.Opens} (hV : V ≤ U i) (x : Γ(twistUnit c, V)) :
    x = unitSectionsEquiv X V (twistSectionsEquiv c i hV x) •
      TopCat.Presheaf.restrictOpen (twistFrame c i) V hV := by
  apply (twistSectionsEquiv c i hV).injective
  rw [LinearEquiv.map_smul, twistSectionsEquiv_res c i le_rfl hV, twistFrame,
    LinearEquiv.apply_symm_apply]
  change _ = (_ : Γ(X, V)) * ((1 : Γ(X, U i)) |ₒ V)
  rw [ores_one, mul_one]
  rfl


variable (c) in
lemma twistFrame_change (i j : ι) :
    TopCat.Presheaf.restrictOpen (twistFrame c i) (U i ⊓ U j) inf_le_left =
      (c.g j i |ₒ (U i ⊓ U j)) • TopCat.Presheaf.restrictOpen (twistFrame c j) (U i ⊓ U j)
        inf_le_right := by
  rw [eq_smul_twistFrame j inf_le_right (TopCat.Presheaf.restrictOpen (twistFrame c i) (U i ⊓ U j)
    inf_le_left)]
  congr 1
  change (twistComp (twistFrame c i) j |ₒ (U i ⊓ U j ⊓ U j)) |ₒ (U i ⊓ U j) = _
  change (((c.g j i |ₒ (U i ⊓ U j)) * ((1 : Γ(X, U i)) |ₒ (U i ⊓ U j))) |ₒ (U i ⊓ U j ⊓ U j))
    |ₒ (U i ⊓ U j) = _
  rw [ores_one, mul_one, ores_res, ores_res]

variable (f c) in
/-- The image `eᵢ ∈ Γ(f^* L_c, f⁻¹ Uᵢ)` of the frame of `L_c` over `Uᵢ`. -/
noncomputable def twistFrameη (i : ι) : (pbTwistUnit f c).val.obj (op (preimOpen f (U i))) :=
  pfSec (twistUnitη f c) (U i) (twistFrame c i)

lemma twistFrameη_change (i j : ι) (O : Opens Y.toPresheafedSpace)
    (hO : O ≤ preimOpen f (U i) ⊓ preimOpen f (U j)) :
    modRes (twistFrameη f c i) O (hO.trans inf_le_left) =
      TopCat.Presheaf.restrictOpen (pbG f c j i) O (hO.trans (inf_comm _ _).le) •
        modRes (twistFrameη f c j) O (hO.trans inf_le_right) := by
  have h := congrArg (pfSec (twistUnitη f c) (U i ⊓ U j)) (twistFrame_change c i j)
  rw [pfSec_smul, pfSec_res, pfSec_res, pbSec_res] at h
  have hij : O ≤ preimOpen f (U i ⊓ U j) := hO
  calc modRes (twistFrameη f c i) O _
      = modRes (modRes (twistFrameη f c i) (preimOpen f (U i ⊓ U j))
          ((Opens.map f.base).monotone inf_le_left))
          O hij := (modRes_res _ _ _).symm
    _ = modRes (TopCat.Presheaf.restrictOpen (pbSec f (c.g j i)) (preimOpen f (U i ⊓ U j))
          ((Opens.map f.base).monotone (inf_comm _ _).le) •
          modRes (twistFrameη f c j) (preimOpen f (U i ⊓ U j))
            ((Opens.map f.base).monotone inf_le_right))
          O hij := congrArg (fun x ↦ modRes x O hij) h
    _ = TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen (pbSec f (c.g j i))
          (preimOpen f (U i ⊓ U j)) ((Opens.map f.base).monotone (inf_comm _ _).le)) O hij •
          modRes (modRes (twistFrameη f c j) (preimOpen f (U i ⊓ U j))
            ((Opens.map f.base).monotone inf_le_right))
          O hij := modRes_smul _ _ _
    _ = _ := congrArg₂ (· • ·) (yres_res _ _ _) (modRes_res _ _ _)


private lemma smul_smul_cancel {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a b c' : R}
    (h : a * c' = 1) (x : M) : (a * b) • c' • x = b • x := by
  rw [smul_smul, mul_right_comm, h, one_mul]

/-- The underlying abelian sheaf of a sheaf of modules on `Y`. -/
noncomputable abbrev modAbSheaf (N : SheafOfModules.{u} Y.ringSheaf) :
    TopCat.Sheaf Ab.{u} Y.toPresheafedSpace :=
  ⟨N.val.presheaf, N.isSheaf⟩

lemma modRes_eq_of_locally_eq {N : SheafOfModules.{u} Y.ringSheaf} {κ : Type u}
    (V : κ → Opens Y.toPresheafedSpace) {W : Opens Y.toPresheafedSpace} (hW : W ≤ iSup V)
    (hV : ∀ a, V a ≤ W) (s t : N.val.obj (op W)) (h : ∀ a, modRes s (V a) (hV a) = modRes t (V a)
        (hV a)) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (modAbSheaf N) V W (fun a ↦ homOfLE (hV a)) hW s t h

lemma preimOpen_iSup (hU : ⨆ i, U i = ⊤) (W : Opens Y.toPresheafedSpace) :
    W ≤ ⨆ i, W ⊓ preimOpen f (U i) := by
  intro y hy
  have : f.base y ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact Opens.mem_iSup.2 ⟨i, hy, hi⟩

variable {W : Opens Y.toPresheafedSpace}

variable (f c) in
/-- The local pieces `tᵢ • eᵢ` of the section of `f^* L_c` attached to `t`. -/
noncomputable def pbTwistLoc (t : (pbTwist f c).val.obj (op W)) (i : ι) :
    (pbTwistUnit f c).val.obj (op (W ⊓ preimOpen f (U i))) :=
  pbComp t i • modRes (twistFrameη f c i) (W ⊓ preimOpen f (U i)) inf_le_right

lemma pbTwistLoc_compat (t : (pbTwist f c).val.obj (op W)) (i j : ι) (O : Opens Y.toPresheafedSpace)
    (hO : O ≤ W ⊓ preimOpen f (U i) ⊓ (W ⊓ preimOpen f (U j))) :
    modRes (pbTwistLoc f c t i) O (hO.trans inf_le_left) = modRes (pbTwistLoc f c t j) O (hO.trans
        inf_le_right) := by
  have hO' : O ≤ preimOpen f (U i) ⊓ preimOpen f (U j) := by
    refine le_inf (hO.trans ?_) (hO.trans ?_) <;> order
  have hc : TopCat.Presheaf.restrictOpen (pbComp t i) O (hO.trans inf_le_left) =
      TopCat.Presheaf.restrictOpen (pbG f c i j) O hO' *
        TopCat.Presheaf.restrictOpen (pbComp t j) O (hO.trans inf_le_right) := by
    have h := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x O (by
      refine le_inf ((hO.trans inf_le_left).trans inf_le_left) hO')) (pbComp_compat t i j)
    simp only [yres_res, yres_mul] at h
    exact h
  calc modRes (pbTwistLoc f c t i) O (hO.trans inf_le_left)
      = TopCat.Presheaf.restrictOpen (pbComp t i) O (hO.trans inf_le_left) •
          modRes (modRes (twistFrameη f c i) (W ⊓ preimOpen f (U i)) inf_le_right) O (hO.trans
              inf_le_left) :=
        modRes_smul _ _ _
    _ = (TopCat.Presheaf.restrictOpen (pbG f c i j) O hO' *
          TopCat.Presheaf.restrictOpen (pbComp t j) O (hO.trans inf_le_right)) •
          (TopCat.Presheaf.restrictOpen (pbG f c j i) O (hO'.trans (inf_comm _ _).le) •
            modRes (twistFrameη f c j) O (hO'.trans inf_le_right)) := by
        rw [hc, modRes_res, twistFrameη_change i j O hO']
    _ = TopCat.Presheaf.restrictOpen (pbComp t j) O (hO.trans inf_le_right) •
          modRes (twistFrameη f c j) O (hO'.trans inf_le_right) :=
        smul_smul_cancel (pbG_mul_pbG i j O hO') _
    _ = modRes (pbTwistLoc f c t j) O (hO.trans inf_le_right) := by
        rw [pbTwistLoc, modRes_smul, modRes_res]


variable (hU : ⨆ i, U i = ⊤)

include hU in
lemma exists_pbTwistGlue (t : (pbTwist f c).val.obj (op W)) :
    ∃! s : (pbTwistUnit f c).val.obj (op W), ∀ i, modRes s (W ⊓ preimOpen f (U i)) inf_le_left =
        pbTwistLoc f c t i := by
  obtain ⟨s, hs, hu⟩ := TopCat.Sheaf.existsUnique_gluing' (modAbSheaf (pbTwistUnit f c))
    (fun i ↦ W ⊓ preimOpen f (U i)) W (fun i ↦ homOfLE inf_le_left) (preimOpen_iSup hU W)
        (pbTwistLoc f c t)
    fun i j ↦ pbTwistLoc_compat t i j _ le_rfl
  exact ⟨s, hs, hu⟩

variable (f c) in
/-- The section of `f^* L_c` glued from the `tᵢ • eᵢ`. -/
noncomputable def pbTwistGlue (t : (pbTwist f c).val.obj (op W)) :
    (pbTwistUnit f c).val.obj (op W) :=
  (exists_pbTwistGlue hU t).exists.choose

lemma modRes_pbTwistGlue (t : (pbTwist f c).val.obj (op W)) (i : ι) :
    modRes (pbTwistGlue f c hU t) (W ⊓ preimOpen f (U i)) inf_le_left = pbTwistLoc f c t i :=
  (exists_pbTwistGlue hU t).exists.choose_spec i

include hU in
lemma eq_pbTwistGlue (t : (pbTwist f c).val.obj (op W)) (s : (pbTwistUnit f c).val.obj (op W))
    (hs : ∀ i, modRes s (W ⊓ preimOpen f (U i)) inf_le_left = pbTwistLoc f c t i) : s = pbTwistGlue
        f c hU t :=
  (exists_pbTwistGlue hU t).unique hs (modRes_pbTwistGlue hU t)


lemma pbComp_modRes {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W)
    (s : (pbTwist f c).val.obj (op W)) (i : ι) :
    pbComp (modRes s W' h) i = pbComp s i |ₒ (W' ⊓ preimOpen f (U i)) :=
  rfl

lemma pbTwistGlue_add (t t' : (pbTwist f c).val.obj (op W)) :
    pbTwistGlue f c hU (t + t') = pbTwistGlue f c hU t + pbTwistGlue f c hU t' := by
  refine (eq_pbTwistGlue hU _ _ fun i ↦ ?_).symm
  rw [modRes_add, modRes_pbTwistGlue, modRes_pbTwistGlue, pbTwistLoc, pbTwistLoc, pbTwistLoc,
      pbComp_add, add_smul]

lemma pbTwistGlue_zero : pbTwistGlue f c hU (0 : (pbTwist f c).val.obj (op W)) = 0 := by
  refine (eq_pbTwistGlue hU _ _ fun i ↦ ?_).symm
  rw [modRes_zero, pbTwistLoc, pbComp_zero, zero_smul]

lemma pbTwistGlue_smul (r : Γᵧ(W)) (t : (pbTwist f c).val.obj (op W)) :
    pbTwistGlue f c hU (r • t) = r • pbTwistGlue f c hU t := by
  refine (eq_pbTwistGlue hU _ _ fun i ↦ ?_).symm
  rw [modRes_smul, modRes_pbTwistGlue, pbTwistLoc, pbTwistLoc, pbComp_smul, smul_smul]

lemma pbTwistGlue_modRes {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (t : (pbTwist f c).val.obj
    (op W)) :
    pbTwistGlue f c hU (modRes t W' h) = modRes (pbTwistGlue f c hU t) W' h := by
  refine (eq_pbTwistGlue hU _ _ fun i ↦ ?_).symm
  have e := congrArg (fun x ↦ modRes x (W' ⊓ preimOpen f (U i)) (inf_le_inf_right _ h))
      (modRes_pbTwistGlue hU t i)
  simp only [modRes_res] at e
  rw [modRes_res, e, pbTwistLoc, pbTwistLoc, modRes_smul, modRes_res, pbComp_modRes]

variable (f c) in
/-- The morphism `f^♯ L_c ⟶ f^* L_c`, `t ↦` the gluing of the `tᵢ • eᵢ`. -/
noncomputable def pbTwistToPullback : pbTwist f c ⟶ pbTwistUnit f c :=
  modHomMk (fun _ ↦
    { toFun := pbTwistGlue f c hU
      map_zero' := pbTwistGlue_zero hU
      map_add' := pbTwistGlue_add hU })
    (fun _ r t ↦ pbTwistGlue_smul hU r t)
    (fun _ _ h t ↦ pbTwistGlue_modRes hU h t)


variable (f c) in
/-- The adjoint `f^* L_c ⟶ f^♯ L_c` of `L_c ⟶ f_* f^♯ L_c`. -/
noncomputable def pullbackToPbTwist : pbTwistUnit f c ⟶ pbTwist f c :=
  (f.pullbackModulesAdj.homEquiv (twistUnit c) (pbTwist f c)).symm (toPushforwardPbTwist f c)

lemma twistUnitη_comp_pullbackToPbTwist :
    twistUnitη f c ≫ ((SheafOfModules.pushforward f.toRingSheafHom).map (pullbackToPbTwist f c) :
      ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwistUnit f c) : X.Modules) ⟶
        ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwist f c) : X.Modules)) =
      toPushforwardPbTwist f c := by
  exact (f.pullbackModulesAdj.homEquiv_unit (twistUnit c) (pbTwist f c) _).symm.trans
    (Equiv.apply_symm_apply _ _)

lemma pullbackToPbTwist_pfSec {V : X.Opens} (x : Γ(twistUnit c, V)) :
    (pullbackToPbTwist f c).val.app (op (preimOpen f V)) (pfSec (twistUnitη f c) V x) =
      pfSec (toPushforwardPbTwist f c) V x :=
  congrArg (fun g ↦ Scheme.Modules.Hom.app g V x) twistUnitη_comp_pullbackToPbTwist

lemma modHom_modRes {P Q : SheafOfModules.{u} Y.ringSheaf} (φ : P ⟶ Q)
    {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (x : P.val.obj (op W)) :
    φ.val.app (op W') (modRes x W' h) = modRes (φ.val.app (op W) x) W' h :=
  congr($(φ.val.naturality (homOfLE h).op).hom x)

lemma modHom_smul {P Q : SheafOfModules.{u} Y.ringSheaf} (φ : P ⟶ Q)
    (r : Γᵧ(W)) (x : P.val.obj (op W)) :
    φ.val.app (op W) (r • x) = r • φ.val.app (op W) x :=
  (φ.val.app (op W)).hom.map_smul r x


lemma yres_injective_of_le {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (h' : W ≤ W') :
    Function.Injective fun x : Γᵧ(W) ↦ TopCat.Presheaf.restrictOpen x W' h := by
  intro a b e
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W h') e
  simpa only [yres_res, yres_self] using this

lemma pbComp_twistFrame_self (i : ι) :
    pbComp (pfSec (toPushforwardPbTwist f c) (U i) (twistFrame c i)) i = 1 := by
  change pbSec f (unitComp (twistFrame c i) i) = 1
  rw [unitComp_twistFrame_self, pbSec_one]

lemma pbTwistToPullback_comp :
    pbTwistToPullback f c hU ≫ pullbackToPbTwist f c = 𝟙 _ := by
  refine modHom_ext fun W t ↦ pbTwist_ext fun i ↦ ?_
  change pbComp ((pullbackToPbTwist f c).val.app (op W) (pbTwistGlue f c hU t)) i = pbComp t i
  apply yres_injective_of_le (W' := W ⊓ preimOpen f (U i) ⊓ preimOpen f (U i)) (by order) (by order)
  change pbComp (modRes ((pullbackToPbTwist f c).val.app (op W) (pbTwistGlue f c hU t)) (W ⊓
      preimOpen f (U i))
    inf_le_left) i = pbComp (modRes t (W ⊓ preimOpen f (U i)) inf_le_left) i
  rw [← modHom_modRes, modRes_pbTwistGlue, pbTwistLoc, modHom_smul, pbComp_smul, modHom_modRes,
      twistFrameη,
    pullbackToPbTwist_pfSec, pbComp_modRes, pbComp_twistFrame_self, yres_one, mul_one,
        pbComp_modRes]


lemma twistSectionsEquiv_res_inf (i : ι) {V : X.Opens} (x : Γ(twistUnit c, V)) :
    unitSectionsEquiv X (V ⊓ U i) (twistSectionsEquiv c i inf_le_right
      (TopCat.Presheaf.restrictOpen x (V ⊓ U i) inf_le_left)) = unitComp x i := by
  change (twistComp x i |ₒ (V ⊓ U i ⊓ U i)) |ₒ (V ⊓ U i) = twistComp x i
  rw [mres_res, mres_self]

lemma pfSec_twistUnitη_res (i : ι) {V : X.Opens} (x : Γ(twistUnit c, V)) :
    modRes (pfSec (twistUnitη f c) V x) (preimOpen f (V ⊓ U i))
        ((Opens.map f.base).monotone inf_le_left) =
      pbSec f (unitComp x i) • modRes (twistFrameη f c i) (preimOpen f (V ⊓ U i))
        ((Opens.map f.base).monotone inf_le_right) := by
  rw [← pfSec_res (twistUnitη f c) (inf_le_left : V ⊓ U i ≤ V), eq_smul_twistFrame i inf_le_right
      (TopCat.Presheaf.restrictOpen x (V ⊓ U i)
    inf_le_left), pfSec_smul, pfSec_res, twistSectionsEquiv_res_inf]
  rfl

lemma toPushforwardPbTwist_comp :
    toPushforwardPbTwist f c ≫
      ((SheafOfModules.pushforward f.toRingSheafHom).map (pbTwistToPullback f c hU) :
        ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwist f c) : X.Modules) ⟶
          ((SheafOfModules.pushforward f.toRingSheafHom).obj (pbTwistUnit f c) : X.Modules)) =
      twistUnitη f c := by
  refine Scheme.Modules.Hom.ext_apply fun V x ↦ ?_
  change pbTwistGlue f c hU (pfSec (toPushforwardPbTwist f c) V x) = pfSec (twistUnitη f c) V x
  refine (eq_pbTwistGlue hU _ _ fun i ↦ ?_).symm
  exact (pfSec_twistUnitη_res i x).trans rfl

lemma pullbackToPbTwist_comp :
    pullbackToPbTwist f c ≫ pbTwistToPullback f c hU = 𝟙 _ := by
  refine (f.pullbackModulesAdj.homEquiv (twistUnit c) (pbTwistUnit f c)).injective ?_
  refine (f.pullbackModulesAdj.homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact (toPushforwardPbTwist_comp hU).trans (f.pullbackModulesAdj.homEquiv_id _).symm

variable (f c) in
/-- **The pullback of a twisted structure sheaf is the twisted structure sheaf**:
`f^* L_c ≅ f^♯ L_c`, if the opens `Uᵢ` cover `X`. -/
noncomputable def pullbackTwistUnitIso : pbTwistUnit f c ≅ pbTwist f c where
  hom := pullbackToPbTwist f c
  inv := pbTwistToPullback f c hU
  hom_inv_id := pullbackToPbTwist_comp hU
  inv_hom_id := pbTwistToPullback_comp hU


section Trivialisation

/-! ### The trivialisation of `f^♯ L_c` over `f⁻¹ Uᵢ` -/

lemma pbG_mul (i j l : ι) (O : Opens Y.toPresheafedSpace)
    (hO : O ≤ preimOpen f (U i) ⊓ preimOpen f (U j) ⊓ preimOpen f (U l)) :
    TopCat.Presheaf.restrictOpen (pbG f c i j) O (hO.trans (by order)) *
      TopCat.Presheaf.restrictOpen (pbG f c j l) O (hO.trans (by order)) =
      TopCat.Presheaf.restrictOpen (pbG f c i l) O (hO.trans (by order)) := by
  have h := congrArg (fun x : Γ(X, U i ⊓ U j ⊓ U l) ↦
    TopCat.Presheaf.restrictOpen (pbSec f x) O hO) (c.mul i j l)
  simp only [pbSec_mul, yres_mul, pbSec_res, yres_res] at h
  exact h

lemma pbG_self (i : ι) (O : Opens Y.toPresheafedSpace)
    (hO : O ≤ preimOpen f (U i) ⊓ preimOpen f (U i)) :
    TopCat.Presheaf.restrictOpen (pbG f c i i) O hO = 1 := by
  change TopCat.Presheaf.restrictOpen (pbSec f (c.g i i)) O hO = 1
  rw [c.self, pbSec_one, yres_one]

variable (c) in
/-- **The trivialisation of `f^♯ L_c` over `W ≤ f⁻¹ Uᵢ`**: a section is determined by its
`i`-th component, `t ↦ tᵢ`, with inverse `s ↦ (f^♯ cⱼᵢ · s)ⱼ`. -/
noncomputable def pbTwistSectionsEquiv (i : ι) (hW : W ≤ preimOpen f (U i)) :
    (pbTwist f c).val.obj (op W) ≃+ Γᵧ(W) where
  toFun t := pbComp t i |ₒ W
  invFun s := pbMk (fun j ↦ (pbG f c j i |ₒ (W ⊓ preimOpen f (U j))) *
      (s |ₒ (W ⊓ preimOpen f (U j)))) fun j l ↦ by
    simp only [yres_mul, yres_res]
    rw [← mul_assoc, pbG_mul j l i _ (by order)]
  left_inv t := pbTwist_ext fun j ↦ by
    simp only [pbComp_pbMk]
    apply yres_injective_of_le (W' := W ⊓ (preimOpen f (U j) ⊓ preimOpen f (U i))) (by order)
      (by order)
    simp only [yres_mul, yres_res]
    rw [pbComp_compat t j i]
  right_inv s := by
    simp only [pbComp_pbMk, yres_res, pbG_self, one_mul]
    exact yres_self s
  map_add' t t' := by
    simp only [pbComp_add, yres_add]

lemma pbTwistSectionsEquiv_modRes (i : ι) (hW : W ≤ preimOpen f (U i))
    {W' : Opens Y.toPresheafedSpace} (h : W' ≤ W) (t : (pbTwist f c).val.obj (op W)) :
    pbTwistSectionsEquiv c i (h.trans hW) (modRes t W' h) =
      TopCat.Presheaf.restrictOpen (pbTwistSectionsEquiv c i hW t) W' h := by
  change pbComp (modRes t W' h) i |ₒ W' = _
  rw [pbComp_modRes]
  change _ = TopCat.Presheaf.restrictOpen (pbComp t i |ₒ W) W' h
  rw [yres_res, yres_res]

end Trivialisation

end AlgebraicGeometry.LocallyRingedSpace

end
