/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionClassObligations

/-!
# Equal extension classes from a morphism of middle terms

If two short exact sequences with the same ends are related by a morphism of the middle terms
commuting with the inclusions and the projections, then their
`ShortComplex.ShortExact.extClass` agree. No invertibility of the middle map is needed:
`extClass_naturality` already gives the identity.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Two short exact sequences with the same ends related by a morphism of the middle terms
commuting with the inclusions and the projections have the same extension class. -/
theorem extClass_eq_of_middleHom {A B M M' : C} {i : A ⟶ M} {p : M ⟶ B} {w : i ≫ p = 0}
    {i' : A ⟶ M'} {p' : M' ⟶ B} {w' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p w).ShortExact) (h' : (ShortComplex.mk i' p' w').ShortExact)
    (ψ : M ⟶ M') (hi : i ≫ ψ = i') (hp : ψ ≫ p' = p) :
    h.extClass = h'.extClass := by
  let f : ShortComplex.mk i p w ⟶ ShortComplex.mk i' p' w' :=
    { τ₁ := 𝟙 A
      τ₂ := ψ
      τ₃ := 𝟙 B
      comm₁₂ := by simpa using hi.symm
      comm₂₃ := by simpa using hp }
  have hn := h.extClass_naturality h' f
  change h.extClass.comp (Abelian.Ext.mk₀ (𝟙 A)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 B)).comp h'.extClass (zero_add 1) at hn
  rw [Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_id_comp] at hn
  exact hn

end CategoryTheory.ShortComplex.ShortExact
