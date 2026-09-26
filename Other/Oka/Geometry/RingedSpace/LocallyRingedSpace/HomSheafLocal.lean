/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheaf
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModuleSections

/-!
# Sections of the sheaf of homomorphisms out of a locally presented sheaf

Let `F` be a sheaf of `𝒪_Y`-modules with *local generators* on an open `W`
(`AlgebraicGeometry.LocallyRingedSpace.LocalGenerators F W`), sections `s₁, …, sₙ` of `F` over `W`
which locally generate `F` on `W`, or with a *local presentation*
(`AlgebraicGeometry.LocallyRingedSpace.LocalPresentation F W`), which adds relations
`gₗ = (gₗᵢ)ᵢ` locally generating all relations between the `sᵢ`. Every coherent sheaf admits a
local presentation near every point
(`AlgebraicGeometry.LocallyRingedSpace.exists_localPresentation`).

For `V ≤ W` and any sheaf of modules `K`, a morphism `F ⟶ K_V` is determined by its values on the
generators (`AlgebraicGeometry.LocallyRingedSpace.LocalGenerators.homSec_eq_zero`), and every
family `kᵢ ∈ K(V)` satisfying the relations arises this way
(`AlgebraicGeometry.LocallyRingedSpace.LocalPresentation.homSecOf`,
`AlgebraicGeometry.LocallyRingedSpace.LocalPresentation.homSecOf_s`). So sections of `𝓗om(F, K)`
over `V` are the solutions of the relations in `K(V)ⁿ`.

We also define the evaluation `𝓗om(F, K) ⟶ K_W` at a section of `F` over `W`
(`AlgebraicGeometry.LocallyRingedSpace.homSheafEval`).
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

variable {Y : LocallyRingedSpace.{u}}

section Eval

variable {F : SheafOfModules.{u} Y.ringSheaf} (K : SheafOfModules.{u} Y.ringSheaf)
  {W : Opens Y.toPresheafedSpace} (t : F.val.obj (op W))

/-- **Evaluation at a section** `t` of `F` over `W`: `𝓗om(F, K) ⟶ K_W`, `h ↦ h(t)`. -/
def homSheafEval : homSheaf F K ⟶ restrictExtend K W :=
  modHomMk (fun U ↦
      { toFun h := restrictExtendMk (modRes (restrictExtendSec
          ((show F ⟶ restrictExtend K U from h).val.app (op W) t)) (U ⊓ W) (by order))
        map_zero' := modRes_zero _
        map_add' h h' := modRes_add (N := K) _ _ _ })
    (fun U a h ↦ by
      change modRes (N := K) ((a |ₒ (W ⊓ U)) • restrictExtendSec
          ((show F ⟶ restrictExtend K U from h).val.app (op W) t)) (U ⊓ W) (by order) =
        (a |ₒ (U ⊓ W)) • modRes (N := K) (restrictExtendSec
          ((show F ⟶ restrictExtend K U from h).val.app (op W) t)) (U ⊓ W) (by order)
      rw [modRes_smul, yres_res])
    (fun U V hVU h ↦ by
      change modRes (N := K) (modRes (N := K) (restrictExtendSec
          ((show F ⟶ restrictExtend K U from h).val.app (op W) t)) (W ⊓ V) (by order))
          (V ⊓ W) (by order) =
        modRes (N := K) (modRes (N := K) (restrictExtendSec
          ((show F ⟶ restrictExtend K U from h).val.app (op W) t)) (U ⊓ W) (by order))
          (V ⊓ W) (by order)
      rw [modRes_res, modRes_res])

lemma restrictExtendSec_homSheafEval {U : Opens Y.toPresheafedSpace}
    (h : (homSheaf F K).val.obj (op U)) :
    restrictExtendSec ((homSheafEval K t).val.app (op U) h) =
      modRes (restrictExtendSec ((show F ⟶ restrictExtend K U from h).val.app (op W) t))
        (U ⊓ W) (by order) :=
  rfl

end Eval

/-- **Local generators** of a sheaf of modules `F` on an open `W`: finitely many sections
`s₁, …, sₙ` of `F` over `W` which locally generate every section of `F` over every open subset
of `W`. -/
structure LocalGenerators (F : SheafOfModules.{u} Y.ringSheaf)
    (W : Opens Y.toPresheafedSpace) where
  /-- the number of generators -/
  n : ℕ
  /-- the generators -/
  s : Fin n → F.val.obj (op W)
  gen (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (t : F.val.obj (op W')) (y : Y)
    (hy : y ∈ W') : ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
      ∃ c : Fin n → Γᵧ(W''), modRes t W'' hW'' = ∑ i, c i • modRes (s i) W'' (hW''.trans hW')

/-- A **local presentation** of a sheaf of modules `F` on an open `W`: local generators
`s₁, …, sₙ` together with finitely many relations `gₗ` between them which locally generate all
relations. -/
structure LocalPresentation (F : SheafOfModules.{u} Y.ringSheaf)
    (W : Opens Y.toPresheafedSpace) extends LocalGenerators F W where
  /-- the number of relations -/
  m : ℕ
  /-- the relations -/
  g : Fin m → Fin n → Γᵧ(W)
  rel (l : Fin m) : ∑ i, g l i • s i = 0
  relgen (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (a : Fin n → Γᵧ(W'))
    (ha : ∑ i, a i • modRes (s i) W' hW' = 0) (y : Y) (hy : y ∈ W') :
    ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
      ∃ d : Fin m → Γᵧ(W''), ∀ i, TopCat.Presheaf.restrictOpen (a i) W'' hW'' =
        ∑ l, d l * TopCat.Presheaf.restrictOpen (g l i) W'' (hW''.trans hW')

/-- **A coherent sheaf has a local presentation near every point.** -/
theorem exists_localPresentation (F : SheafOfModules.{u} Y.ringSheaf) [F.IsCoherent] (y : Y) :
    ∃ W : Opens Y.toPresheafedSpace, y ∈ W ∧ Nonempty (LocalPresentation F W) := by
  obtain ⟨W₀, k, s, hy, hgen⟩ := isLocallyFinitelyGeneratedModule_of_isFiniteType F y
  obtain ⟨W, hWW₀, m, g, hyW, hrel, hrelgen⟩ := hasLocalModuleRelations_of_isCoherent F W₀ k s y hy
  refine ⟨W, hyW, ⟨⟨⟨k, fun i ↦ modRes (s i) W hWW₀, fun W' hW' t y' hy' ↦ ?_⟩, m, g, hrel,
    fun W' hW' a ha y' hy' ↦ ?_⟩⟩⟩
  · obtain ⟨W'', hW'', hy'', c, hc⟩ := hgen W' (hW'.trans hWW₀) t y' hy'
    refine ⟨W'', hW'', hy'', c, hc.trans (Finset.sum_congr rfl fun i _ ↦ ?_)⟩
    rw [modRes_res]
    rfl
  · refine hrelgen W' hW' a (Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) ha) y' hy'
    rw [modRes_res]
    rfl

/-- Restriction of a section of a sheaf of modules, the inclusion being proved by `order`. -/
local macro:80 x:term:80 " |ₘ " W:term:81 : term =>
  `(modRes $x $W (by order))

lemma modRes_sum {N : SheafOfModules.{u} Y.ringSheaf} {V V' : Opens Y.toPresheafedSpace}
    (h : V' ≤ V) {ι : Type*} (s : Finset ι) (f : ι → N.val.obj (op V)) :
    modRes (∑ i ∈ s, f i) V' h = ∑ i ∈ s, modRes (f i) V' h :=
  map_sum (N.val.map (homOfLE h).op).hom f s

lemma yres_sum {V V' : Opens Y.toPresheafedSpace} (h : V' ≤ V) {ι : Type*} (s : Finset ι)
    (f : ι → Γᵧ(V)) :
    TopCat.Presheaf.restrictOpen (∑ i ∈ s, f i) V' h =
      ∑ i ∈ s, TopCat.Presheaf.restrictOpen (f i) V' h :=
  map_sum (Y.presheaf.map (homOfLE h).op).hom f s

namespace LocalPresentation

variable {F : SheafOfModules.{u} Y.ringSheaf} {W : Opens Y.toPresheafedSpace}
  (P : LocalPresentation F W) (K : SheafOfModules.{u} Y.ringSheaf)

/-- Restricting a linear combination of the generators. -/
lemma modRes_sum_smul {W₀ W₁ : Opens Y.toPresheafedSpace} (h₀ : W₀ ≤ W) (h₁ : W₁ ≤ W₀)
    (c : Fin P.n → Γᵧ(W₀)) :
    modRes (∑ i, c i • modRes (P.s i) W₀ h₀) W₁ h₁ =
      ∑ i, TopCat.Presheaf.restrictOpen (c i) W₁ h₁ • modRes (P.s i) W₁ (h₁.trans h₀) := by
  rw [modRes_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [modRes_smul, modRes_res]

/-- Restricting a linear combination in `K`. -/
lemma modRes_sum_smul' {V W₀ W₁ : Opens Y.toPresheafedSpace} (k : Fin P.n → K.val.obj (op V))
    (h₀ : W₀ ≤ V) (h₁ : W₁ ≤ W₀) (c : Fin P.n → Γᵧ(W₀)) :
    modRes (∑ i, c i • modRes (k i) W₀ h₀) W₁ h₁ =
      ∑ i, TopCat.Presheaf.restrictOpen (c i) W₁ h₁ • modRes (k i) W₁ (h₁.trans h₀) := by
  rw [modRes_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [modRes_smul, modRes_res]

end LocalPresentation

namespace LocalGenerators

variable {F : SheafOfModules.{u} Y.ringSheaf} {W : Opens Y.toPresheafedSpace}
  (P : LocalGenerators F W) (K : SheafOfModules.{u} Y.ringSheaf)

/-- **A morphism `F ⟶ K_V` vanishing on the generators vanishes.** -/
lemma homSec_eq_zero {V : Opens Y.toPresheafedSpace} (hVW : V ≤ W)
    (h : F ⟶ restrictExtend K V)
    (hs : ∀ i, restrictExtendSec (h.val.app (op W) (P.s i)) = 0) : h = 0 := by
  refine modHom_ext fun U x ↦ ?_
  change restrictExtendSec (h.val.app (op U) x) = (0 : K.val.obj (op (U ⊓ V)))
  choose W'' hW'' hyW'' c hc using fun (y : ↥(U ⊓ V)) ↦
    P.gen (U ⊓ V) (inf_le_right.trans hVW) (modRes x (U ⊓ V) inf_le_left) y.1 y.2
  refine modRes_eq_of_cover K W'' (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW'' ⟨y, hy⟩⟩)
    hW'' _ _ fun y ↦ ?_
  rw [modRes_zero]
  have hle : W'' y ≤ U := (hW'' y).trans inf_le_left
  have hleV : W'' y ≤ V := (hW'' y).trans inf_le_right
  have e1 : modRes x (W'' y) hle =
      ∑ i, c y i • modRes (P.s i) (W'' y) ((hW'' y).trans (inf_le_right.trans hVW)) := by
    rw [← hc y, modRes_res]
  have e3 : ∀ i, h.val.app (op (W'' y))
      (modRes (P.s i) (W'' y) ((hW'' y).trans (inf_le_right.trans hVW))) = 0 := by
    intro i
    rw [modHom_modRes]
    refine restrictExtend_ext ?_
    rw [restrictExtendSec_modRes, hs i, modRes_zero]
    rfl
  have e4 : h.val.app (op (W'' y)) (modRes x (W'' y) hle) = 0 := by
    rw [e1, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [modHom_smul, e3, smul_zero]
  rw [modHom_modRes] at e4
  have e5 := congrArg restrictExtendSec e4
  rw [restrictExtendSec_modRes] at e5
  have e6 := congrArg (fun z ↦ modRes (N := K) z (W'' y) (le_inf le_rfl hleV)) e5
  simp only [modRes_res] at e6
  exact e6.trans (modRes_zero _)

end LocalGenerators

namespace LocalPresentation

variable {F : SheafOfModules.{u} Y.ringSheaf} {W : Opens Y.toPresheafedSpace}
  (P : LocalPresentation F W) (K : SheafOfModules.{u} Y.ringSheaf)

variable {V : Opens Y.toPresheafedSpace} (hVW : V ≤ W) (k : Fin P.n → K.val.obj (op V))
  (hk : ∀ l, ∑ i, TopCat.Presheaf.restrictOpen (P.g l i) V hVW • k i = 0)
include hk

/-- Two representations of a section by the generators give the same combination of the
`kᵢ`. -/
lemma sum_smul_eq_of_sum_smul_eq {W₀ : Opens Y.toPresheafedSpace} (h₀ : W₀ ≤ V)
    (c c' : Fin P.n → Γᵧ(W₀))
    (hcc' : ∑ i, c i • modRes (P.s i) W₀ (h₀.trans hVW) =
      ∑ i, c' i • modRes (P.s i) W₀ (h₀.trans hVW)) :
    ∑ i, c i • modRes (k i) W₀ h₀ = ∑ i, c' i • modRes (k i) W₀ h₀ := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hcc'
  simp_rw [← sub_smul] at hcc'
  have hrel := P.relgen W₀ (h₀.trans hVW) (fun i ↦ c i - c' i) hcc'
  choose W₁ hW₁ hyW₁ d hd using fun (y : ↥W₀) ↦ hrel y.1 y.2
  refine modRes_eq_of_cover K W₁ (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW₁ ⟨y, hy⟩⟩)
    hW₁ _ _ fun y ↦ ?_
  rw [modRes_zero, modRes_sum_smul' P K k h₀ (hW₁ y)]
  simp_rw [hd y, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [← Finset.smul_sum]
  have := congrArg (fun z ↦ modRes (N := K) z (W₁ y) ((hW₁ y).trans h₀)) (hk l)
  simp only [modRes_sum, modRes_smul, yres_res, modRes_zero] at this
  rw [this, smul_zero]

variable {U : Opens Y.toPresheafedSpace} (x : F.val.obj (op U))

/-- `w ∈ K(U ∩ V)` is the value of the morphism determined by the `kᵢ` at `x`: on every open
where `x` is a combination of the generators, `w` is the same combination of the `kᵢ`. -/
def IsValue (w : K.val.obj (op (U ⊓ V))) : Prop :=
  ∀ (W₀ : Opens Y.toPresheafedSpace) (h₀ : W₀ ≤ U ⊓ V) (c : Fin P.n → Γᵧ(W₀)),
    modRes x W₀ (h₀.trans inf_le_left) =
      ∑ i, c i • modRes (P.s i) W₀ (h₀.trans (inf_le_right.trans hVW)) →
    modRes w W₀ h₀ = ∑ i, c i • modRes (k i) W₀ (h₀.trans inf_le_right)

omit hk in
lemma isValue_unique {w w' : K.val.obj (op (U ⊓ V))} (hw : P.IsValue K hVW k x w)
    (hw' : P.IsValue K hVW k x w') : w = w' := by
  choose W₀ hW₀ hyW₀ c hc using fun (y : ↥(U ⊓ V)) ↦
    P.gen (U ⊓ V) (inf_le_right.trans hVW) (modRes x (U ⊓ V) inf_le_left) y.1 y.2
  refine modRes_eq_of_cover K W₀ (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW₀ ⟨y, hy⟩⟩)
    hW₀ _ _ fun y ↦ ?_
  have hrep : modRes x (W₀ y) ((hW₀ y).trans inf_le_left) =
      ∑ i, c y i • modRes (P.s i) (W₀ y) ((hW₀ y).trans (inf_le_right.trans hVW)) := by
    rw [← hc y, modRes_res]
  rw [hw _ _ _ hrep, hw' _ _ _ hrep]

lemma isValue_of_locally (w : K.val.obj (op (U ⊓ V)))
    (hw : ∀ y ∈ U ⊓ V, ∃ (W₀ : Opens Y.toPresheafedSpace) (h₀ : W₀ ≤ U ⊓ V), y ∈ W₀ ∧
      ∃ c : Fin P.n → Γᵧ(W₀), modRes x W₀ (h₀.trans inf_le_left) =
        ∑ i, c i • modRes (P.s i) W₀ (h₀.trans (inf_le_right.trans hVW)) ∧
        modRes w W₀ h₀ = ∑ i, c i • modRes (k i) W₀ (h₀.trans inf_le_right)) :
    P.IsValue K hVW k x w := by
  intro W₁ h₁ c₁ hc₁
  choose W₀ h₀ hyW₀ c hc hwc using hw
  refine modRes_eq_of_cover K (fun y : ↥W₁ ↦ W₁ ⊓ W₀ y.1 (h₁ y.2))
    (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hy, hyW₀ y (h₁ hy)⟩)
    (fun _ ↦ inf_le_left) _ _ fun y ↦ ?_
  have hA : W₁ ⊓ W₀ y.1 (h₁ y.2) ≤ W₀ y.1 (h₁ y.2) := inf_le_right
  have hB : W₁ ⊓ W₀ y.1 (h₁ y.2) ≤ W₁ := inf_le_left
  have e1 := congrArg (fun z ↦ modRes (N := K) z _ hA) (hwc y.1 (h₁ y.2))
  simp only [modRes_res] at e1
  rw [modRes_res, e1, modRes_sum_smul' P K k _ hA, modRes_sum_smul' P K k _ hB]
  refine P.sum_smul_eq_of_sum_smul_eq K hVW k hk (hB.trans (h₁.trans inf_le_right)) _ _ ?_
  have e2 := congrArg (fun z ↦ modRes (N := F) z _ hA) (hc y.1 (h₁ y.2))
  have e3 := congrArg (fun z ↦ modRes (N := F) z _ hB) hc₁
  simp only [modRes_res] at e2 e3
  rw [modRes_sum_smul P _ hA] at e2
  rw [modRes_sum_smul P _ hB] at e3
  exact e2.symm.trans e3

lemma exists_isValue : ∃ w, P.IsValue K hVW k x w := by
  choose W₀ hW₀ hyW₀ c hc using fun (y : ↥(U ⊓ V)) ↦
    P.gen (U ⊓ V) (inf_le_right.trans hVW) (modRes x (U ⊓ V) inf_le_left) y.1 y.2
  have hrep : ∀ y, modRes x (W₀ y) ((hW₀ y).trans inf_le_left) =
      ∑ i, c y i • modRes (P.s i) (W₀ y) ((hW₀ y).trans (inf_le_right.trans hVW)) := fun y ↦ by
    rw [← hc y, modRes_res]
  obtain ⟨w, hw, -⟩ := modRes_existsUnique_gluing K W₀
    (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW₀ ⟨y, hy⟩⟩) hW₀
    (fun y ↦ ∑ i, c y i • modRes (k i) (W₀ y) ((hW₀ y).trans inf_le_right)) fun a b ↦ by
      rw [modRes_sum_smul' P K k _ inf_le_left, modRes_sum_smul' P K k _ inf_le_right]
      refine P.sum_smul_eq_of_sum_smul_eq K hVW k hk (inf_le_left.trans
        ((hW₀ a).trans inf_le_right)) _ _ ?_
      have e2 := congrArg (fun z ↦ modRes (N := F) z (W₀ a ⊓ W₀ b) inf_le_left) (hrep a)
      have e3 := congrArg (fun z ↦ modRes (N := F) z (W₀ a ⊓ W₀ b) inf_le_right) (hrep b)
      simp only [modRes_res] at e2 e3
      rw [modRes_sum_smul P _ inf_le_left] at e2
      rw [modRes_sum_smul P _ inf_le_right] at e3
      exact e2.symm.trans e3
  exact ⟨w, P.isValue_of_locally K hVW k hk x w fun y hy ↦
    ⟨W₀ ⟨y, hy⟩, hW₀ _, hyW₀ _, c _, hrep _, hw _⟩⟩

/-- The value at `x` of the morphism `F ⟶ K_V` determined by the `kᵢ`. -/
def value : K.val.obj (op (U ⊓ V)) := (P.exists_isValue K hVW k hk x).choose

lemma isValue_value : P.IsValue K hVW k x (P.value K hVW k hk x) :=
  (P.exists_isValue K hVW k hk x).choose_spec

lemma value_eq {w : K.val.obj (op (U ⊓ V))} (hw : P.IsValue K hVW k x w) :
    P.value K hVW k hk x = w :=
  P.isValue_unique K hVW k x (P.isValue_value K hVW k hk x) hw
omit hk in
lemma exists_rep (y : Y) (hy : y ∈ U ⊓ V) :
    ∃ (W₀ : Opens Y.toPresheafedSpace) (h₀ : W₀ ≤ U ⊓ V), y ∈ W₀ ∧
      ∃ c : Fin P.n → Γᵧ(W₀), modRes x W₀ (h₀.trans inf_le_left) =
        ∑ i, c i • modRes (P.s i) W₀ (h₀.trans (inf_le_right.trans hVW)) := by
  obtain ⟨W₀, h₀, hy₀, c, hc⟩ :=
    P.gen (U ⊓ V) (inf_le_right.trans hVW) (modRes x (U ⊓ V) inf_le_left) y hy
  exact ⟨W₀, h₀, hy₀, c, by rw [← hc, modRes_res]⟩

lemma value_add (x' : F.val.obj (op U)) :
    P.value K hVW k hk (x + x') = P.value K hVW k hk x + P.value K hVW k hk x' := by
  refine P.value_eq K hVW k hk _ (P.isValue_of_locally K hVW k hk _ _ fun y hy ↦ ?_)
  obtain ⟨W₁, h₁, hy₁, c₁, hc₁⟩ := P.exists_rep hVW x y hy
  obtain ⟨W₂, h₂, hy₂, c₂, hc₂⟩ := P.exists_rep hVW x' y hy
  have hA : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have hB : W₁ ⊓ W₂ ≤ W₂ := inf_le_right
  have e₁ := congrArg (fun z ↦ modRes (N := F) z _ hA) hc₁
  have e₂ := congrArg (fun z ↦ modRes (N := F) z _ hB) hc₂
  simp only [modRes_res] at e₁ e₂
  rw [modRes_sum_smul P _ hA] at e₁
  rw [modRes_sum_smul P _ hB] at e₂
  refine ⟨W₁ ⊓ W₂, hA.trans h₁, ⟨hy₁, hy₂⟩,
    fun i ↦ TopCat.Presheaf.restrictOpen (c₁ i) _ hA +
      TopCat.Presheaf.restrictOpen (c₂ i) _ hB, ?_, ?_⟩
  · rw [modRes_add, e₁, e₂, ← Finset.sum_add_distrib]
    simp_rw [add_smul]
  · rw [modRes_add, P.isValue_value K hVW k hk x _ _ _ e₁,
      P.isValue_value K hVW k hk x' _ _ _ e₂, ← Finset.sum_add_distrib]
    simp_rw [add_smul]

lemma value_smul (r : Γᵧ(U)) :
    P.value K hVW k hk (r • x) =
      TopCat.Presheaf.restrictOpen r (U ⊓ V) inf_le_left • P.value K hVW k hk x := by
  refine P.value_eq K hVW k hk _ (P.isValue_of_locally K hVW k hk _ _ fun y hy ↦ ?_)
  obtain ⟨W₁, h₁, hy₁, c₁, hc₁⟩ := P.exists_rep hVW x y hy
  refine ⟨W₁, h₁, hy₁, fun i ↦ TopCat.Presheaf.restrictOpen r W₁ (h₁.trans inf_le_left) * c₁ i,
    ?_, ?_⟩
  · rw [modRes_smul, hc₁, Finset.smul_sum]
    simp_rw [mul_smul]
  · rw [modRes_smul, P.isValue_value K hVW k hk x _ _ _ hc₁, Finset.smul_sum, yres_res]
    simp_rw [mul_smul]

lemma value_modRes {U' : Opens Y.toPresheafedSpace} (hU : U' ≤ U) :
    P.value K hVW k hk (modRes x U' hU) =
      modRes (P.value K hVW k hk x) (U' ⊓ V) (inf_le_inf_right V hU) := by
  refine P.value_eq K hVW k hk _ fun W₀ h₀ c hc ↦ ?_
  rw [modRes_res] at hc ⊢
  exact P.isValue_value K hVW k hk x W₀ _ c hc

/-- **The morphism `F ⟶ K_V` with prescribed values `kᵢ` on the generators.** -/
def homSecOf : F ⟶ restrictExtend K V :=
  modHomMk (fun U ↦
      { toFun x := restrictExtendMk (P.value K hVW k hk x)
        map_zero' := by
          have := P.value_add K hVW k hk (0 : F.val.obj (op U)) 0
          rw [add_zero] at this
          exact (by simpa using this : P.value K hVW k hk (0 : F.val.obj (op U)) = 0)
        map_add' x x' := P.value_add K hVW k hk x x' })
    (fun U r x ↦ P.value_smul K hVW k hk x r)
    (fun U U' hU x ↦ P.value_modRes K hVW k hk x hU)

lemma restrictExtendSec_homSecOf_app (U : Opens Y.toPresheafedSpace) (x : F.val.obj (op U)) :
    restrictExtendSec ((P.homSecOf K hVW k hk).val.app (op U) x) = P.value K hVW k hk x :=
  rfl

/-- **The morphism `F ⟶ K_V` determined by the `kᵢ` takes the value `kᵢ` at `sᵢ`.** -/
lemma homSecOf_s (i : Fin P.n) :
    restrictExtendSec ((P.homSecOf K hVW k hk).val.app (op W) (P.s i)) =
      modRes (k i) (W ⊓ V) inf_le_right := by
  rw [restrictExtendSec_homSecOf_app]
  refine P.value_eq K hVW k hk _ fun W₀ h₀ c hc ↦ ?_
  have key : ∑ j, c j • modRes (k j) W₀ (h₀.trans inf_le_right) =
      ∑ j, (Pi.single i (1 : Γᵧ(W₀)) : Fin P.n → Γᵧ(W₀)) j •
        modRes (k j) W₀ (h₀.trans inf_le_right) := by
    refine P.sum_smul_eq_of_sum_smul_eq K hVW k hk _ _ _ ?_
    rw [← hc]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [modRes_res, key]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

end LocalPresentation

end AlgebraicGeometry.LocallyRingedSpace

end
