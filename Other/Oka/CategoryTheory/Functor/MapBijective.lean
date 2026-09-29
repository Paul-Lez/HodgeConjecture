/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Bijectivity of a functor on individual hom sets

For a functor `A : C ⥤ D` and objects `P Q : C`, we study when the map
`A.map : (P ⟶ Q) → (A P ⟶ A Q)` is bijective, and how this propagates:

- `CategoryTheory.Functor.bijective_map_of_iso_left`: along isomorphisms `P ≅ P'`;
- `CategoryTheory.Functor.bijective_map_sigma`: to coproducts `∐ Pᵢ` preserved by `A`;
- `CategoryTheory.Functor.injective_map_of_epi`, `CategoryTheory.Functor.surjective_map_of_epi`:
  along an epimorphism `p : P ⟶ F` (in an abelian category, for the surjectivity, using
  injectivity on `(ker p, Q)`);
- `CategoryTheory.Functor.bijective_map_of_natIso`: if `T ⋙ A ≅ A ⋙ T'` with `T` fully faithful
  and `T'` faithful, bijectivity on `(T P, T Q)` implies bijectivity on `(P, Q)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] (A : C ⥤ D)

/-- Bijectivity of `A.map` on `(P ⟶ Q)` transfers along an isomorphism `P ≅ P'`. -/
lemma bijective_map_of_iso_left {P P' : C} (e : P ≅ P') (Q : C)
    (h : Function.Bijective (A.map : (P ⟶ Q) → _)) :
    Function.Bijective (A.map : (P' ⟶ Q) → _) := by
  refine ⟨fun g g' hg ↦ ?_, fun ψ ↦ ?_⟩
  · refine (cancel_epi e.hom).1 (h.1 ?_)
    rw [A.map_comp, A.map_comp, hg]
  · obtain ⟨g, hg⟩ := h.2 (A.map e.hom ≫ ψ)
    refine ⟨e.inv ≫ g, ?_⟩
    rw [A.map_comp, hg, ← Category.assoc, ← A.map_comp, e.inv_hom_id, A.map_id,
      Category.id_comp]

/-- Bijectivity of `A.map` on `(Pᵢ ⟶ Q)` for all `i` implies bijectivity on `(∐ Pᵢ ⟶ Q)` if `A`
preserves the coproduct. -/
lemma bijective_map_sigma {I : Type*} (P : I → C) [HasCoproduct P]
    [hA : PreservesColimit (Discrete.functor P) A] (Q : C)
    (h : ∀ i, Function.Bijective (A.map : (P i ⟶ Q) → _)) :
    Function.Bijective (A.map : (∐ P ⟶ Q) → _) := by
  refine ⟨fun g g' hg ↦ Sigma.hom_ext _ _ fun i ↦ (h i).1 ?_, fun ψ ↦ ?_⟩
  · rw [A.map_comp, A.map_comp, hg]
  · choose g hg using fun i ↦ (h i).2 (A.map (Sigma.ι P i) ≫ ψ)
    refine ⟨Sigma.desc g, (isColimitOfPreserves A (coproductIsCoproduct P)).hom_ext
      fun ⟨i⟩ ↦ ?_⟩
    change A.map (Sigma.ι P i) ≫ _ = A.map (Sigma.ι P i) ≫ _
    rw [← A.map_comp, Sigma.ι_desc, hg]

/-- Injectivity of `A.map` on `(P ⟶ Q)` implies injectivity on `(F ⟶ Q)` for an epimorphism
`P ⟶ F`. -/
lemma injective_map_of_epi {P F : C} (p : P ⟶ F) [Epi p] (Q : C)
    (h : Function.Injective (A.map : (P ⟶ Q) → _)) :
    Function.Injective (A.map : (F ⟶ Q) → _) := fun g g' hg ↦
  (cancel_epi p).1 (h (by rw [A.map_comp, A.map_comp, hg]))

/-- **Surjectivity along a presentation.** For an epimorphism `p : P ⟶ F` in an abelian category
with `A.map p` epi, surjectivity of `A.map` on `(P ⟶ Q)` and injectivity on `(ker p ⟶ Q)` imply
surjectivity on `(F ⟶ Q)`. -/
lemma surjective_map_of_epi [Abelian C] [HasZeroMorphisms D] [hA : A.PreservesZeroMorphisms]
    {P F : C} (p : P ⟶ F) [Epi p] [hAp : Epi (A.map p)] (Q : C)
    (hP : Function.Surjective (A.map : (P ⟶ Q) → _))
    (hK : Function.Injective (A.map : (kernel p ⟶ Q) → _)) :
    Function.Surjective (A.map : (F ⟶ Q) → _) := by
  intro ψ
  obtain ⟨g, hg⟩ := hP (A.map p ≫ ψ)
  have hk : kernel.ι p ≫ g = 0 := hK (by
    rw [A.map_comp, hg, ← Category.assoc, ← A.map_comp, kernel.condition, A.map_zero,
      zero_comp, A.map_zero])
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) g hk
  have hl' : p ≫ l = g := hl
  refine ⟨l, (cancel_epi (A.map p)).1 ?_⟩
  rw [← A.map_comp, hl', hg]

/-- **Transport along a commuting autoequivalence.** If `T ⋙ A ≅ A ⋙ T'` with `T` fully faithful
and `T'` faithful, then bijectivity of `A.map` on `(T P ⟶ T Q)` implies bijectivity on
`(P ⟶ Q)`. -/
lemma bijective_map_of_natIso {T : C ⥤ C} {T' : D ⥤ D} (e : T ⋙ A ≅ A ⋙ T') [hTfull : T.Full]
    [hTfaith : T.Faithful] [hT' : T'.Faithful] (P Q : C)
    (h : Function.Bijective (A.map : (T.obj P ⟶ T.obj Q) → _)) :
    Function.Bijective (A.map : (P ⟶ Q) → _) := by
  have key (f : P ⟶ Q) :
      A.map (T.map f) = e.hom.app P ≫ T'.map (A.map f) ≫ e.inv.app Q :=
    (NatIso.naturality_2 e f).symm
  refine ⟨fun f f' hf ↦ T.map_injective (h.1 ?_), fun ψ ↦ ?_⟩
  · rw [key, key, hf]
  · obtain ⟨g, hg⟩ := h.2 (e.hom.app P ≫ T'.map ψ ≫ e.inv.app Q)
    refine ⟨T.preimage g, T'.map_injective ?_⟩
    have h1 : e.hom.app P ≫ T'.map (A.map (T.preimage g)) ≫ e.inv.app Q =
        e.hom.app P ≫ T'.map ψ ≫ e.inv.app Q := by
      rw [← key, T.map_preimage]
      exact hg
    exact ((e.app Q).cancel_iso_inv_right _ _).1 (((e.app P).cancel_iso_hom_left _ _).1 h1)

end CategoryTheory.Functor

end
