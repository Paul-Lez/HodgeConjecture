/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Coherent

/-!
# Coherence of a sheaf of modules from local generators and local relations

Let `M` be a sheaf of `𝒪_Y`-modules on a locally ringed space `Y`. We give a concrete criterion
for coherence of `M`, stated in terms of open subsets, sections and restriction maps only:

* `AlgebraicGeometry.LocallyRingedSpace.IsLocallyFinitelyGeneratedModule M`: every point has an
  open neighbourhood `W` with finitely many sections `s₁, …, s_k ∈ M(W)` which locally generate
  every section of `M` over every open subset of `W`;
* `AlgebraicGeometry.LocallyRingedSpace.HasLocalModuleRelations M`: every finite family of
  sections `f₁, …, f_m ∈ M(V)` admits, near every point of `V`, finitely many relations which
  locally generate all relations between the `fᵢ`.

Together they imply that `M` is coherent
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_hasLocalModuleRelations`); the first alone
implies that `M` is of finite type
(`AlgebraicGeometry.LocallyRingedSpace.isFiniteType_of_isLocallyFinitelyGeneratedModule`). This
generalises `AlgebraicGeometry.LocallyRingedSpace.isCoherentStructureSheaf_of_hasLocalRelations`
from `𝒪_Y` to arbitrary sheaves of modules.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} Y.ringSheaf)

/-- Restriction of a section of a sheaf of `𝒪_Y`-modules to a smaller open subset. -/
abbrev sectRes {U V : Opens Y} (h : U ≤ V) (s : M.val.obj (op V)) : M.val.obj (op U) :=
  M.val.map (homOfLE h).op s

lemma sectRes_smul {U V : Opens Y} (h : U ≤ V) (r : Y.presheaf.obj (op V))
    (s : M.val.obj (op V)) : sectRes M h (r • s) = Y.res h r • sectRes M h s :=
  M.val.map_smul _ _ _

lemma sectRes_sectRes {U V W : Opens Y} (h₁ : U ≤ V) (h₂ : V ≤ W) (s : M.val.obj (op W)) :
    sectRes M h₁ (sectRes M h₂ s) = sectRes M (h₁.trans h₂) s := by
  rw [sectRes, sectRes, sectRes, ← PresheafOfModules.map_comp_apply]
  rfl

lemma sectRes_sum {U V : Opens Y} (h : U ≤ V) {κ : Type*} (t : Finset κ)
    (u : κ → M.val.obj (op V)) : sectRes M h (∑ i ∈ t, u i) = ∑ i ∈ t, sectRes M h (u i) :=
  map_sum (M.val.map (homOfLE h).op).hom u t

lemma sectRes_zero {U V : Opens Y} (h : U ≤ V) : sectRes M h (0 : M.val.obj (op V)) = 0 :=
  map_zero (M.val.map (homOfLE h).op).hom

/-- `M` is **locally finitely generated**: every point has an open neighbourhood `W` and finitely
many sections `s₁, …, s_k` of `M` over `W` such that every section of `M` over an open subset
of `W` is, near every point, an `𝒪`-linear combination of the `sₗ`. -/
def IsLocallyFinitelyGeneratedModule : Prop :=
  ∀ x : Y, ∃ (W : Opens Y) (k : ℕ) (s : Fin k → M.val.obj (op W)), x ∈ W ∧
    ∀ (W' : Opens Y) (hW' : W' ≤ W) (t : M.val.obj (op W')), ∀ y ∈ W',
      ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin k → Y.presheaf.obj (op W''),
        sectRes M hW'' t = ∑ l, c l • sectRes M (hW''.trans hW') (s l)

/-- `M` has **locally finitely generated relations**: every finite family `f₁, …, f_m` of
sections of `M` over `V` admits, near every point of `V`, finitely many relations
`g₁, …, g_k` which generate all relations between the `fᵢ` locally. -/
def HasLocalModuleRelations : Prop :=
  ∀ (V : Opens Y) (m : ℕ) (f : Fin m → M.val.obj (op V)) (x : Y), x ∈ V →
    ∃ (W : Opens Y) (hWV : W ≤ V) (k : ℕ) (g : Fin k → (Fin m → Y.presheaf.obj (op W))),
      x ∈ W ∧ (∀ l, ∑ i, g l i • sectRes M hWV (f i) = 0) ∧
      ∀ (W' : Opens Y) (hW' : W' ≤ W) (a : Fin m → Y.presheaf.obj (op W')),
        (∑ i, a i • sectRes M (hW'.trans hWV) (f i) = 0) → ∀ y ∈ W',
          ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧
            ∃ c : Fin k → Y.presheaf.obj (op W''),
              ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans hW') (g l i)

/-- A locally finitely generated sheaf of modules is of finite type. -/
theorem isFiniteType_of_isLocallyFinitelyGeneratedModule
    (h : IsLocallyFinitelyGeneratedModule M) : M.IsFiniteType := by
  classical
  choose W k s hxW hgen using h
  have hcov : (Opens.grothendieckTopology Y).CoversTop W :=
    (Opens.coversTop_iff _ W).2 (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hxW y⟩)
  suffices (kernel (0 : M ⟶ M)).IsFiniteType from
    IsFiniteType.of_iso (M := kernel (0 : M ⟶ M)) kernelZeroIsoSource
  refine isFiniteType_kernel_of_coversTop_of_locally (0 : M ⟶ M) W hcov (fun a ↦ ?_)
  set L := ULift.{u} (Fin (k a))
  set ψ : free L ⟶ M.over (W a) :=
    (freeHomEquiv _).symm (fun l ↦ sectionOfTerminal Over.mkIdTerminal (M.over (W a))
      (s a l.down)) with hψ
  have key_ψ : ∀ (Z : Over (W a)) (c : (free (R := Y.ringSheaf.over (W a)) L).val.obj (op Z)),
      ψ.val.app (op Z) c =
        ∑ l : L, (show Y.presheaf.obj (op Z.left) from
          freeEval (R := Y.ringSheaf.over (W a)) (op Z) c l) •
          sectRes M (leOfHom Z.hom) (s a l.down) := by
    intro Z c
    rw [val_app_eq_sum]
    refine Finset.sum_congr rfl (fun l _ ↦ ?_)
    rw [hψ, Equiv.apply_symm_apply, sectionOfTerminal_val]
    rfl
  refine ⟨L, inferInstance, ψ, ?_, ?_⟩
  · simp only [Hom.over, Functor.map_zero, Limits.comp_zero]
  · intro Z b _
    have hZ : Z.left ≤ W a := leOfHom Z.hom
    choose Wy hWyle hyWy cy hcy using fun (y : Z.left) ↦ hgen a Z.left hZ b y.1 y.2
    set S₀ : Sieve (Z.left : Opens Y) :=
      ⟨fun Wo _ ↦ ∃ y : Z.left, Wo ≤ Wy y, by
        rintro W₁ W₂ f₁ ⟨y, hy⟩ gg; exact ⟨y, (leOfHom gg).trans hy⟩⟩ with hS₀def
    have hS₀mem : S₀ ∈ Opens.grothendieckTopology Y Z.left := by
      intro x hx
      exact ⟨Wy ⟨x, hx⟩, homOfLE (hWyle ⟨x, hx⟩), ⟨⟨x, hx⟩, le_rfl⟩, hyWy ⟨x, hx⟩⟩
    refine ⟨(Sieve.overEquiv Z).symm S₀, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
      exact hS₀mem
    · intro Z' ff hff
      rw [Sieve.overEquiv_symm_iff] at hff
      obtain ⟨y, hy⟩ := hff
      have hle : Z'.left ≤ Wy y := hy
      refine ⟨freeEvalSymm (R := Y.ringSheaf.over (W a)) (op Z')
        (fun l : L ↦ Y.res hle (cy y l.down)), ?_⟩
      rw [key_ψ]
      have h6 := congrArg (sectRes M hle) (hcy y)
      simp only [sectRes_sum, sectRes_smul, sectRes_sectRes] at h6
      have hsum : (∑ l : L, (show Y.presheaf.obj (op Z'.left) from
          freeEval (R := Y.ringSheaf.over (W a)) (op Z')
          (freeEvalSymm (R := Y.ringSheaf.over (W a)) (op Z')
            (fun l : L ↦ Y.res hle (cy y l.down))) l) •
            sectRes M (leOfHom Z'.hom) (s a l.down)) =
          ∑ l : Fin (k a), Y.res hle (cy y l) •
            sectRes M (hle.trans ((hWyle y).trans hZ)) (s a l) := by
        rw [freeEval_freeEvalSymm]
        exact Fintype.sum_equiv Equiv.ulift _ _ (fun _ ↦ rfl)
      rw [hsum, ← h6]
      rfl

set_option maxHeartbeats 1000000 in
-- the proof repeatedly identifies sections of the (iterated) restrictions of the sheaves of
-- modules involved with sections of `M` and of the structure sheaf
/-- A locally finitely generated sheaf of modules with locally finitely generated relations is
coherent. -/
theorem isCoherent_of_hasLocalModuleRelations (hfin : IsLocallyFinitelyGeneratedModule M)
    (h : HasLocalModuleRelations M) : M.IsCoherent := by
  classical
  haveI : M.IsFiniteType := isFiniteType_of_isLocallyFinitelyGeneratedModule M hfin
  refine isCoherent_of_forall_kernel_of_locally (M := M) ?_
  intro X I hI φ
  haveI := hI
  haveI : Fintype I := Fintype.ofFinite I
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  set f : Fin m → M.val.obj (op X) := fun i ↦
    PresheafOfModules.sections.eval (freeHomEquiv _ φ (e.symm i)) (op (Over.mk (𝟙 X))) with hf
  choose V hVX k g hxV hrel hgen using fun (x : X) ↦ h X m f x.1 x.2
  refine ⟨↥X, fun a ↦ Over.mk (homOfLE (hVX a)),
    X.coversTop_over V hVX (fun x hx ↦ ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩), fun a ↦ ?_⟩
  set Ya : Over X := Over.mk (homOfLE (hVX a))
  set L := ULift.{u} (Fin (k a))
  have hWV : ∀ W : (Over Ya)ᵒᵖ, W.unop.left.left ≤ V a := fun W ↦ leOfHom W.unop.hom.left
  have hWX : ∀ W : (Over Ya)ᵒᵖ, W.unop.left.left ≤ X := fun W ↦ (hWV W).trans (hVX a)
  set ψ : free L ⟶ (free I).over Ya :=
    (freeHomEquiv _).symm (fun l ↦ sectionOfTerminal Over.mkIdTerminal ((free I).over Ya)
      (freeEvalSymm (R := Y.ringSheaf.over X) (I := I) (op (Over.mk (𝟙 Ya)).left)
        (fun i ↦ g a l.down (e i)))) with hψ
  have key_φ : ∀ (W : (Over Ya)ᵒᵖ) (b : ((free I).over Ya).val.obj W)
      (bc : I → Y.presheaf.obj (op W.unop.left.left))
      (_ : ∀ i, bc i = freeEval (op W.unop.left) b i)
      (v : M.val.obj (op W.unop.left.left)) (_ : v = (φ.over Ya).val.app W b),
      v = ∑ i : I, bc i • sectRes M (hWX W) (f (e i)) := by
    intro W b bc hbc v hv
    have hsec : ∀ i : I, (PresheafOfModules.sections.eval (freeHomEquiv _ φ i)
        (op W.unop.left) : M.val.obj (op W.unop.left.left)) =
        sectRes M (hWX W) (f (e i)) := by
      intro i
      simp only [hf, Equiv.symm_apply_apply]
      exact (PresheafOfModules.sections_property (freeHomEquiv _ φ i)
        (Over.mkIdTerminal.from W.unop.left).op).symm
    rw [hv, show (φ.over Ya).val.app W b = φ.val.app (op W.unop.left) b from rfl,
      val_app_eq_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hbc i, ← hsec i]
    rfl
  have key_ψ : ∀ (W : (Over Ya)ᵒᵖ) (c : (free L).val.obj W)
      (cc : L → Y.presheaf.obj (op W.unop.left.left)) (_ : ∀ l, cc l = freeEval W c l) (i : I)
      (v : Y.presheaf.obj (op W.unop.left.left))
      (_ : v = freeEval (op W.unop.left) (ψ.val.app W c) i),
      v = ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i)) := by
    intro W c cc hcc i v hv
    obtain ⟨cc', hcc'⟩ : ∃ cc' : L → (Y.ringSheaf.over X).obj.obj (op W.unop.left),
        ∀ l, cc' l = cc l := ⟨fun l ↦ cc l, fun _ ↦ rfl⟩
    obtain ⟨vv, hvv⟩ : ∃ vv : L → I → (Y.ringSheaf.over X).obj.obj (op W.unop.left),
        ∀ l i, vv l i = Y.res (hWV W) (g a l.down (e i)) :=
      ⟨fun l i ↦ Y.res (hWV W) (g a l.down (e i)), fun _ _ ↦ rfl⟩
    have hsec : ∀ l : L, PresheafOfModules.sections.eval (freeHomEquiv _ ψ l) W =
        freeEvalSymm (op W.unop.left) (vv l) := by
      intro l
      rw [hψ, Equiv.apply_symm_apply, sectionOfTerminal_val,
        show vv l = fun i ↦ Y.res (hWV W) (g a l.down (e i)) from funext (hvv l)]
      exact map_freeEvalSymm (R := Y.ringSheaf.over X) (I := I)
        ((Over.mkIdTerminal.from W.unop).left).op (fun i ↦ g a l.down (e i))
    have h1 : ψ.val.app W c = freeEvalSymm (op W.unop.left)
        (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) := by
      have hrhs : freeEvalSymm (R := Y.ringSheaf.over X) (I := I) (op W.unop.left)
          (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) =
          ∑ l : L, cc' l • freeEvalSymm (op W.unop.left) (vv l) := by
        have hpi : (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) =
            ∑ l : L, cc' l • vv l := by
          funext i
          rw [Finset.sum_apply]
          refine Finset.sum_congr rfl (fun l _ ↦ ?_)
          rw [Pi.smul_apply, hcc', hvv]
          rfl
        refine (congrArg (freeEvalSymm (R := Y.ringSheaf.over X) (I := I)
          (op W.unop.left)) hpi).trans ((map_sum _ _ _).trans ?_)
        exact Finset.sum_congr rfl (fun l _ ↦ map_smul _ _ _)
      rw [val_app_eq_sum, hrhs]
      simp only [hsec, hcc', hcc]
      rfl
    rw [hv, h1]
    exact congrFun (freeEval_freeEvalSymm _ _) i
  have hgker : ∀ (W' : Opens Y) (hh : W' ≤ V a) (l : Fin (k a)),
      ∑ j : Fin m, Y.res hh (g a l j) • sectRes M (hh.trans (hVX a)) (f j) = 0 := by
    intro W' hh l
    have h0 := congrArg (sectRes M hh) (hrel a l)
    simp only [sectRes_sum, sectRes_smul, sectRes_sectRes, sectRes_zero] at h0
    exact h0
  refine ⟨L, inferInstance, ψ, ?_, ?_⟩
  · ext W c
    obtain ⟨cc, hcc⟩ : ∃ cc : L → Y.presheaf.obj (op W.unop.left.left),
        ∀ l, cc l = freeEval W c l := ⟨fun l ↦ freeEval W c l, fun _ ↦ rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : M.val.obj (op W.unop.left.left),
        v = (φ.over Ya).val.app W (ψ.val.app W c) := ⟨_, rfl⟩
    have h0 : v = 0 := by
      rw [key_φ W (ψ.val.app W c)
        (fun i ↦ ∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i)))
        (fun i ↦ (key_ψ W c cc hcc i _ rfl).symm) v hv]
      have hterm : ∀ i : I, (∑ l : L, cc l * Y.res (hWV W) (g a l.down (e i))) •
            sectRes M (hWX W) (f (e i)) =
          ∑ l : L, cc l • (Y.res (hWV W) (g a l.down (e i)) • sectRes M (hWX W) (f (e i))) := by
        intro i
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl (fun l _ ↦ mul_smul _ _ _)
      simp only [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun l _ ↦ ?_)
      rw [← Finset.smul_sum, Equiv.sum_comp e (fun j : Fin m ↦
        Y.res (hWV W) (g a l.down j) • sectRes M (hWX W) (f j)),
        hgker _ (hWV W) l.down, smul_zero]
    exact hv.symm.trans h0
  · intro Z b hb
    obtain ⟨bc, hbc⟩ : ∃ bc : I → Y.presheaf.obj (op Z.left.left),
        ∀ i, bc i = freeEval (op Z.left) b i :=
      ⟨fun i ↦ freeEval (op Z.left) b i, fun _ ↦ rfl⟩
    have hrelb : ∑ j : Fin m, bc (e.symm j) • sectRes M (hWX (op Z)) (f j) = 0 := by
      rw [← Equiv.sum_comp e (fun j : Fin m ↦ bc (e.symm j) • sectRes M (hWX (op Z)) (f j))]
      obtain ⟨v, hv⟩ : ∃ v : M.val.obj (op Z.left.left),
          v = (φ.over Ya).val.app (op Z) b := ⟨_, rfl⟩
      have h0 : v = 0 := hv.trans hb
      rw [key_φ (op Z) b bc hbc v hv] at h0
      simpa only [Equiv.symm_apply_apply] using h0
    choose Wy hWyle hyWy cy hcy using fun (y : Z.left.left) ↦
      hgen a Z.left.left (hWV (op Z)) (fun j ↦ bc (e.symm j)) hrelb y.1 y.2
    set S₀ : Sieve (Z.left.left : Opens Y) :=
      ⟨fun Wo _ ↦ ∃ y : Z.left.left, Wo ≤ Wy y, by
        rintro W₁ W₂ f₁ ⟨y, hy⟩ gg; exact ⟨y, (leOfHom gg).trans hy⟩⟩ with hS₀def
    have hS₀mem : S₀ ∈ Opens.grothendieckTopology Y Z.left.left := by
      intro x hx
      exact ⟨Wy ⟨x, hx⟩, homOfLE (hWyle ⟨x, hx⟩), ⟨⟨x, hx⟩, le_rfl⟩, hyWy ⟨x, hx⟩⟩
    refine ⟨(Sieve.overEquiv Z).symm ((Sieve.overEquiv Z.left).symm S₀), ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply,
        GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
      exact hS₀mem
    · intro Z' ff hff
      rw [Sieve.overEquiv_symm_iff, Sieve.overEquiv_symm_iff] at hff
      obtain ⟨y, hy⟩ := hff
      have hle : Z'.left.left ≤ Wy y := hy
      refine ⟨freeEvalSymm (op Z') (fun l : L ↦ Y.res hle (cy y l.down)), ?_⟩
      refine freeEval_injective (op Z'.left) (funext fun i ↦ ?_)
      have h1 := key_ψ (op Z')
        (freeEvalSymm (op Z') (fun l : L ↦ Y.res hle (cy y l.down)))
        (fun l ↦ Y.res hle (cy y l.down))
        (fun l ↦ (congrFun (freeEval_freeEvalSymm (R := (Y.ringSheaf.over X).over Ya) (I := L)
          (op Z') (fun l : L ↦ Y.res hle (cy y l.down))) l).symm) i _ rfl
      have hsum : (∑ l : L, Y.res hle (cy y l.down) *
          Y.res (hWV (op Z')) (g a l.down (e i))) =
          ∑ l : Fin (k a), Y.res hle (cy y l) * Y.res (hWV (op Z')) (g a l (e i)) :=
        Fintype.sum_equiv Equiv.ulift _ _ (fun _ ↦ rfl)
      have h3 : freeEval (op Z'.left) (((free I).over Ya).val.map ff.op b) i =
          Y.res (leOfHom ff.left.left) (bc i) := by
        rw [show (((free I).over Ya).val.map ff.op) b =
          (free I).val.map (ff.left).op b from rfl, freeEval_naturality, hbc i]
        rfl
      have h4 : (∑ l : Fin (k a), Y.res hle (cy y l) *
          Y.res (hWV (op Z')) (g a l (e i))) = Y.res (leOfHom ff.left.left) (bc i) := by
        have h5 := hcy y (e i)
        simp only [Equiv.symm_apply_apply] at h5
        have h6 := congrArg (Y.res hle) h5
        simp only [res_sum, res_mul, res_res] at h6
        exact h6.symm
      rw [h3, h1, hsum, h4]

end AlgebraicGeometry.LocallyRingedSpace

end
