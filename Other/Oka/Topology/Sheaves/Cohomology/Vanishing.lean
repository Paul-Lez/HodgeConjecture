/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.Basic

/-!
# Elementary criteria for the vanishing of sheaf cohomology

Let `X` be a topological space. For abelian sheaves on `X` we record how vanishing of a
cohomology group `Hⁿ(X, -)` propagates:

* to retracts (`TopCat.Sheaf.subsingleton_H_of_retract`) and to objects which are finite sums of
  others in the sense `𝟙 F = ∑ᵢ pᵢ ≫ eᵢ` (`TopCat.Sheaf.subsingleton_H_of_sum`), since `Hⁿ` is
  an additive functor;
* along short exact sequences `0 → S.X₁ → S.X₂ → S.X₃ → 0`: if `Hⁿ(S.X₂) = 0` and
  `Hⁿ⁺¹(S.X₁) = 0` then `Hⁿ(S.X₃) = 0` (`TopCat.Sheaf.subsingleton_H_X₃_of_shortExact`), which is
  the dimension-shifting step.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The map on cohomology induced by a finite sum of morphisms is the sum of the maps. -/
lemma H.map_sum_apply {F G : AbSheaf X} {ι : Type*} (s : Finset ι) (φ : ι → (F ⟶ G)) {n : ℕ}
    (x : H F n) : H.map (∑ i ∈ s, φ i) n x = ∑ i ∈ s, H.map (φ i) n x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.map_zero_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.map_add_apply, ih]

/-- A retract of a sheaf with vanishing `Hⁿ` has vanishing `Hⁿ`. -/
lemma subsingleton_H_of_retract {F G : AbSheaf X} (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F)
    (n : ℕ) [Subsingleton (H G n)] : Subsingleton (H F n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← H.map_id_apply x, ← h, H.map_comp_apply, Subsingleton.elim (H.map i n x) 0, map_zero]

/-- If `𝟙 F = ∑_{i ∈ s} pᵢ ≫ eᵢ` with `pᵢ : F ⟶ Aᵢ` and `Hⁿ(Aᵢ) = 0` for `i ∈ s`, then
`Hⁿ(F) = 0`. -/
lemma subsingleton_H_of_sum {F : AbSheaf X} {ι : Type*} (s : Finset ι) (A : ι → AbSheaf X)
    (p : ∀ i, F ⟶ A i) (e : ∀ i, A i ⟶ F) (h : ∑ i ∈ s, p i ≫ e i = 𝟙 F) (n : ℕ)
    (hA : ∀ i ∈ s, Subsingleton (H (A i) n)) : Subsingleton (H F n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← H.map_id_apply x, ← h, H.map_sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  haveI := hA i hi
  rw [H.map_comp_apply, Subsingleton.elim (H.map (p i) n x) 0, map_zero]

/-- **Dimension shifting.** For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian
sheaves, if `Hⁿ(S.X₂) = 0` and `Hⁿ⁺¹(S.X₁) = 0`, then `Hⁿ(S.X₃) = 0`. -/
lemma subsingleton_H_X₃_of_shortExact {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (n : ℕ) [Subsingleton (H S.X₂ n)] [Subsingleton (H S.X₁ (n + 1))] :
    Subsingleton (H S.X₃ n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := (H.exact₃ hS n (n + 1) rfl x).1 (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- Isomorphic sheaves have simultaneously vanishing cohomology. -/
lemma subsingleton_H_of_iso {F G : AbSheaf X} (e : F ≅ G) (n : ℕ) [Subsingleton (H G n)] :
    Subsingleton (H F n) :=
  (H.addEquivOfIso e n).toEquiv.subsingleton

end TopCat.Sheaf

end
