/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Short exact representatives of degree-one Ext classes

In an abelian category with enough injectives, every class in `Ext X Y 1` is represented
by an extension of `X` by `Y`. We obtain the extension by pulling back an injective
presentation of `Y` along the degree-zero class furnished by the long exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]

set_option backward.isDefEq.respectTransparency false in
/-- Every degree-one Ext class has a short exact representative with the prescribed endpoints. -/
theorem exists_shortExact {X Y : C} (α : Ext.{w} X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ X) (w : i ≫ p = 0)
      (h : (ShortComplex.mk i p w).ShortExact), h.extClass = α := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨γ, hγ⟩ := covariant_sequence_exact₁ X hS α (eq_zero_of_injective _) (n₀ := 0) rfl
  let f : X ⟶ S.X₃ := homEquiv₀ γ
  have hf : (mk₀ f).comp hS.extClass (zero_add 1) = α := by
    simpa only [f, mk₀_homEquiv₀_apply] using hγ
  let E := pullback S.g f
  let i : Y ⟶ E := pullback.lift S.f 0 (by simp [S.zero])
  let p : E ⟶ X := pullback.snd S.g f
  have wi : i ≫ p = 0 := pullback.lift_snd _ _ _
  have hi : i ≫ pullback.fst S.g f = S.f := pullback.lift_fst _ _ _
  have : Mono i := mono_of_mono_fac hi
  let T := ShortComplex.mk i p wi
  have hT : T.ShortExact := by
    refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_ }
    apply KernelFork.IsLimit.ofι'
    intro A k hk
    have hk' : (k ≫ pullback.fst S.g f) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (k ≫ p) ≫ f = 0
      rw [hk, Limits.zero_comp]
    refine ⟨hS.fIsKernel.lift (KernelFork.ofι _ hk'), ?_⟩
    apply pullback.hom_ext
    · change (_ ≫ i) ≫ pullback.fst S.g f = _
      rw [Category.assoc, hi]
      exact Fork.IsLimit.lift_ι hS.fIsKernel
    · change (_ ≫ i) ≫ p = k ≫ p
      rw [Category.assoc, wi, Limits.comp_zero]
      exact hk.symm
  let φ : T ⟶ S :=
    { τ₁ := 𝟙 Y
      τ₂ := pullback.fst S.g f
      τ₃ := f
      comm₁₂ := by simpa only [T, Category.id_comp] using hi.symm
      comm₂₃ := pullback.condition }
  refine ⟨E, i, p, wi, hT, ?_⟩
  have hn := hT.extClass_naturality hS φ
  change hT.extClass.comp (mk₀ (𝟙 Y)) (add_zero 1) =
    (mk₀ f).comp hS.extClass (zero_add 1) at hn
  erw [comp_mk₀_id] at hn
  exact hn.trans hf

end CategoryTheory.Abelian.Ext
