/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-! Change of universe preserves composition of localized shifted morphisms. -/

@[expose] public noncomputable section

universe w₁ w₂ v u t

namespace CategoryTheory.Localization.SmallShiftedHom

variable {C : Type u} [Category.{v} C] {M : Type t} [AddMonoid M] [HasShift C M]
  {W : MorphismProperty C} [W.IsCompatibleWithShift M] {X Y Z : C}

@[simp]
lemma chgUniv_chgUniv [HasSmallLocalizedShiftedHom.{w₁} W M X Y]
    [HasSmallLocalizedShiftedHom.{w₂} W M X Y] {n : M}
    (f : SmallShiftedHom.{w₁} W X Y n) :
    chgUniv.{w₁} (chgUniv.{w₂} f) = f := by
  apply (equiv W W.Q).injective
  simp only [equiv_chgUniv]

@[simp]
lemma chgUniv_comp [HasSmallLocalizedShiftedHom.{w₁} W M X Y]
    [HasSmallLocalizedShiftedHom.{w₁} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w₁} W M X Z]
    [HasSmallLocalizedShiftedHom.{w₁} W M Z Z]
    [HasSmallLocalizedShiftedHom.{w₂} W M X Y]
    [HasSmallLocalizedShiftedHom.{w₂} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w₂} W M X Z]
    [HasSmallLocalizedShiftedHom.{w₂} W M Z Z] {a b c : M}
    (f : SmallShiftedHom.{w₁} W X Y a) (g : SmallShiftedHom.{w₁} W Y Z b)
    (h : b + a = c) :
    chgUniv.{w₂} (f.comp g h) = (chgUniv.{w₂} f).comp (chgUniv.{w₂} g) h := by
  apply (equiv W W.Q).injective
  simp only [equiv_chgUniv, equiv_comp]

@[simp]
lemma chgUniv_mk₀ [HasSmallLocalizedShiftedHom.{w₁} W M X Y]
    [HasSmallLocalizedShiftedHom.{w₂} W M X Y] (n : M) (hn : n = 0) (f : X ⟶ Y) :
    chgUniv.{w₂} (mk₀.{w₁} W n hn f) = mk₀.{w₂} W n hn f := by
  apply (equiv W W.Q).injective
  simp only [equiv_chgUniv, equiv_mk₀]

end CategoryTheory.Localization.SmallShiftedHom
