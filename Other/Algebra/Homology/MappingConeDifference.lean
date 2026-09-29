/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Changing the second component of a map of cones

When two maps out of the middle term of a short complex differ by a map through its
quotient term, their induced cone maps differ by the same map, through the canonical
map from the cone to that quotient. This identifies the effect of changing a splitting
on a relative extension class before passing to the derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))
  {K L : CochainComplex C ℤ} (φ : K ⟶ L) (a : S.X₁ ⟶ K)
  (b₁ b₂ : S.X₂ ⟶ L) (s : S.X₃ ⟶ L)
  (h₁ : S.f ≫ b₁ = a ≫ φ) (h₂ : S.f ≫ b₂ = a ≫ φ)

/-- A change through the quotient changes the cone map by the corresponding map through
`descShortComplex` and the inclusion of the target of `φ`. -/
theorem map_sub_map_of_eq_add (h : b₂ = b₁ + S.g ≫ s) :
    map S.f φ a b₂ h₂ - map S.f φ a b₁ h₁ =
      descShortComplex S ≫ s ≫ inr φ := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map, descShortComplex, h,
    Preadditive.comp_sub, Preadditive.add_comp]

/-- After an additive functor makes the canonical map to the quotient invertible, the
difference of the two induced quotient classes is the boundary term `s ≫ inr φ`.
In particular this applies to localization in the derived category for a short exact
complex. -/
theorem inv_map_descShortComplex_comp_map_sub
    {D : Type*} [Category* D] [Preadditive D]
    (F : CochainComplex C ℤ ⥤ D) [F.Additive] [IsIso (F.map (descShortComplex S))]
    (h : b₂ = b₁ + S.g ≫ s) :
    inv (F.map (descShortComplex S)) ≫ F.map (map S.f φ a b₂ h₂) -
        inv (F.map (descShortComplex S)) ≫ F.map (map S.f φ a b₁ h₁) =
      F.map s ≫ F.map (inr φ) := by
  rw [← Preadditive.comp_sub, ← F.map_sub,
    map_sub_map_of_eq_add S φ a b₁ b₂ s h₁ h₂ h, F.map_comp, F.map_comp,
    IsIso.inv_hom_id_assoc]

end CochainComplex.mappingCone
