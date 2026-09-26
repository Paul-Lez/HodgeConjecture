/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Naturality of `Ext.mapExactFunctor` in the functor

Let `Φ₁ : C ⥤ D`, `Φ₂ : D ⥤ E`, `Ψ₁ : C ⥤ D'`, `Ψ₂ : D' ⥤ E` be exact functors between abelian
categories and `τ : Φ₁ ⋙ Φ₂ ⟶ Ψ₁ ⋙ Ψ₂` a natural transformation (given
as a natural family of morphisms `τ_X : Φ₂ Φ₁ X ⟶ Ψ₂ Ψ₁ X`). If `C` has enough injectives,
then for every `x : Extⁿ(A, B)` the square

`Φ₂(Φ₁(x)) ∘ τ_B = τ_A ∘ Ψ₂(Ψ₁(x))` in `Extⁿ(Φ₂ Φ₁ A, Ψ₂ Ψ₁ B)`

commutes (`CategoryTheory.Abelian.Ext.mapExactFunctor_mapExactFunctor_comp_mk₀`). The
statement is phrased with two-step composites since Mathlib has no lemma identifying
`Ext.mapExactFunctor` of a composite functor with the composite of the `Ext.mapExactFunctor`s.
The proof is by dimension shifting along an injective presentation of `B`, using the naturality
of the extension class of a short exact sequence.
-/

@[expose] public section

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {D' : Type u₂} [Category.{v₂} D'] [Abelian D'] {E : Type u₃} [Category.{v₃} E] [Abelian E]
  [HasExt.{w} C] [HasExt.{w₁} D] [HasExt.{w₂} D'] [HasExt.{w₃} E] [EnoughInjectives C]
  {Φ₁ : C ⥤ D} [Φ₁.Additive] [PreservesFiniteLimits Φ₁] [PreservesFiniteColimits Φ₁]
  {Φ₂ : D ⥤ E} [Φ₂.Additive] [PreservesFiniteLimits Φ₂] [PreservesFiniteColimits Φ₂]
  {Ψ₁ : C ⥤ D'} [Ψ₁.Additive] [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁]
  {Ψ₂ : D' ⥤ E} [Ψ₂.Additive] [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂]
  (τ : ∀ X, Φ₂.obj (Φ₁.obj X) ⟶ Ψ₂.obj (Ψ₁.obj X))
  (hτ : ∀ {X Y : C} (f : X ⟶ Y), Φ₂.map (Φ₁.map f) ≫ τ Y = τ X ≫ Ψ₂.map (Ψ₁.map f))

include hτ in
attribute [local instance] Ext.subsingleton_of_injective in
/-- **`Ext.mapExactFunctor` is natural in the exact functor**: for a natural family
`τ_X : Φ₂ Φ₁ X ⟶ Ψ₂ Ψ₁ X` and `x : Extⁿ(A, B)`, `Φ₂(Φ₁(x)) ∘ τ_B = τ_A ∘ Ψ₂(Ψ₁(x))`. -/
lemma mapExactFunctor_mapExactFunctor_comp_mk₀ {A B : C} {n : ℕ} (x : Ext A B n) :
    ((x.mapExactFunctor Φ₁).mapExactFunctor Φ₂).comp (mk₀ (τ B)) (add_zero n) =
      (mk₀ (τ A)).comp ((x.mapExactFunctor Ψ₁).mapExactFunctor Ψ₂)
        (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective A B).2 x
    simp only [mapExactFunctor_mk₀, mk₀_comp_mk₀]
    exact congrArg mk₀ (hτ f)
  | succ n hn =>
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ _ hS x (by subsingleton) rfl
    let φ : (S.map Φ₁).map Φ₂ ⟶ (S.map Ψ₁).map Ψ₂ :=
      { τ₁ := τ _, τ₂ := τ _, τ₃ := τ _
        comm₁₂ := (hτ S.f).symm
        comm₂₃ := (hτ S.g).symm }
    have hΦ := (hS.map_of_exact Φ₁).map_of_exact Φ₂
    have hΨ := (hS.map_of_exact Ψ₁).map_of_exact Ψ₂
    obtain ⟨eΦ, heΦ⟩ : ∃ e : Ext (Φ₂.obj (Φ₁.obj S.X₃)) (Φ₂.obj (Φ₁.obj B)) 1,
        e = hΦ.extClass := ⟨_, rfl⟩
    obtain ⟨eΨ, heΨ⟩ : ∃ e : Ext (Ψ₂.obj (Ψ₁.obj S.X₃)) (Ψ₂.obj (Ψ₁.obj B)) 1,
        e = hΨ.extClass := ⟨_, rfl⟩
    have key : eΦ.comp (mk₀ (τ B)) (add_zero 1) =
        (mk₀ (τ S.X₃)).comp eΨ (zero_add 1) := by
      subst heΦ heΨ
      exact hΦ.extClass_naturality hΨ φ
    have h₁ : ((y.comp hS.extClass rfl).mapExactFunctor Φ₁).mapExactFunctor Φ₂ =
        ((y.mapExactFunctor Φ₁).mapExactFunctor Φ₂).comp eΦ rfl := by
      have e₂ : ((hS.map_of_exact Φ₁).extClass : Ext (Φ₁.obj S.X₃) (Φ₁.obj B) 1).mapExactFunctor
          Φ₂ = eΦ := heΦ ▸ mapExactFunctor_extClass _ _
      rw [mapExactFunctor_comp, mapExactFunctor_extClass, mapExactFunctor_comp]
      erw [e₂]
    have h₂ : ((y.comp hS.extClass rfl).mapExactFunctor Ψ₁).mapExactFunctor Ψ₂ =
        ((y.mapExactFunctor Ψ₁).mapExactFunctor Ψ₂).comp eΨ rfl := by
      have e₂ : ((hS.map_of_exact Ψ₁).extClass : Ext (Ψ₁.obj S.X₃) (Ψ₁.obj B) 1).mapExactFunctor
          Ψ₂ = eΨ := heΨ ▸ mapExactFunctor_extClass _ _
      rw [mapExactFunctor_comp, mapExactFunctor_extClass, mapExactFunctor_comp]
      erw [e₂]
    rw [h₁, h₂, comp_assoc _ _ _ rfl (add_zero 1) (by omega), key,
      ← comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega), hn (B := S.X₃) y,
      comp_assoc _ _ _ (zero_add n) rfl (by omega)]

end CategoryTheory.Abelian.Ext

end
