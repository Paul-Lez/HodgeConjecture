/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Factoring a cocycle through a morphism of single complexes

When precomposition is bijective on morphisms into every term of the target complex,
a cocycle factors through the corresponding morphism of single complexes. The closedness
of the factor follows from injectivity in the next degree; no derived-category assumption
is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace CochainComplex.HomComplex.Cocycle
variable {C : Type*} [Category* C] [Abelian C]
  {A B : C} (η : A ⟶ B) (J : CochainComplex C ℤ) (n : ℤ)
  (hbij : ∀ q : ℤ, Function.Bijective (fun b : B ⟶ J.X q => η ≫ b))

include hbij in
set_option backward.isDefEq.respectTransparency false in
/-- A termwise local target permits factorization of every cocycle from a single complex. -/
theorem exists_precomp_single_eq (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) J n) :
    ∃ w : Cocycle ((CochainComplex.singleFunctor C 0).obj B) J n,
      w.precomp ((CochainComplex.singleFunctor C 0).map η) = z := by
  obtain ⟨a, ha, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
  obtain ⟨b, hb⟩ := (hbij n).2 a
  replace hb : η ≫ b = a := hb
  subst hb
  have hb' : b ≫ J.d n (n + 1) = 0 := by
    apply (hbij (n + 1)).1
    show η ≫ b ≫ J.d n (n + 1) = η ≫ 0
    rw [← Category.assoc, ha, comp_zero]
  refine ⟨Cocycle.fromSingleMk b (zero_add n) (n + 1) rfl hb', ?_⟩
  rw [← Cocycle.fromSingleMk_precomp]

end CochainComplex.HomComplex.Cocycle
