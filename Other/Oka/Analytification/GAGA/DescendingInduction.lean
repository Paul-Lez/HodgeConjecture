/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ComparisonAdditive
public import Mathlib.Algebra.FiveLemma

/-!
# Serre's descending induction for the GAGA comparison map

Let `X` be a scheme locally of finite type over `ℂ` and `𝒞` a class of sheaves of modules on
`X` such that
1. for `F ∈ 𝒞` and `q > N`, both `Hᵠ(X, F)` and `Hᵠ(X^an, F^an)` vanish;
2. every `F ∈ 𝒞` is a quotient `0 → K → L → F → 0` with `K ∈ 𝒞` and `gagaMap X L q`
   bijective for all `q`.

Then `gagaMap X F q : Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all `F ∈ 𝒞` and all `q`
(`ComplexAnalytic.gagaMap_bijective_of_descending`). The proof is a descending induction on `q`:
the four lemmas applied to the long exact sequences of `0 → K → L → F → 0` and of its
analytification give first surjectivity in degree `q` for all `F ∈ 𝒞`
(`ComplexAnalytic.gagaMap_surjective_of_shortExact`), then injectivity
(`ComplexAnalytic.gagaMap_injective_of_shortExact`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

open LocallyRingedSpace

variable {X : SchemeLFTℂ.{u}}
  {S : ShortComplex (SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)}

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → K → L → F → 0`, if
`gagaMap` is surjective on `Hᵠ(L)` and `Hᵠ⁺¹(K)` and injective on `Hᵠ⁺¹(L)`, then it is
surjective on `Hᵠ(F)`. -/
lemma gagaMap_surjective_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (hL : Function.Surjective (gagaMap X S.X₂ q))
    (hK : Function.Surjective (gagaMap X S.X₁ (q + 1)))
    (hL' : Function.Injective (gagaMap X S.X₂ (q + 1))) :
    Function.Surjective (gagaMap X S.X₃ q) := by
  have hS' := shortExact_map_analytificationModules hS
  exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (H.map S.g q) (H.δ hS q (q + 1) rfl) (H.map S.f (q + 1))
    (H.map (S.map (analytificationModules X)).g q) (H.δ hS' q (q + 1) rfl)
    (H.map (S.map (analytificationModules X)).f (q + 1))
    (gagaMap X S.X₂ q) (gagaMap X S.X₃ q) (gagaMap X S.X₁ (q + 1)) (gagaMap X S.X₂ (q + 1))
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
    (H.exact₁ hS q (q + 1) rfl) (H.exact₃ hS' q (q + 1) rfl) (H.exact₁ hS' q (q + 1) rfl)
    hL hK hL'

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → K → L → F → 0`, if
`gagaMap` is surjective on `Hᵠ(K)` and injective on `Hᵠ(L)` and `Hᵠ⁺¹(K)`, then it is injective
on `Hᵠ(F)`. -/
lemma gagaMap_injective_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (hK : Function.Surjective (gagaMap X S.X₁ q))
    (hL : Function.Injective (gagaMap X S.X₂ q))
    (hK' : Function.Injective (gagaMap X S.X₁ (q + 1))) :
    Function.Injective (gagaMap X S.X₃ q) := by
  have hS' := shortExact_map_analytificationModules hS
  exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
    (H.map S.f q) (H.map S.g q) (H.δ hS q (q + 1) rfl)
    (H.map (S.map (analytificationModules X)).f q) (H.map (S.map (analytificationModules X)).g q)
    (H.δ hS' q (q + 1) rfl)
    (gagaMap X S.X₁ q) (gagaMap X S.X₂ q) (gagaMap X S.X₃ q) (gagaMap X S.X₁ (q + 1))
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
    (H.exact₂ hS q) (H.exact₃ hS q (q + 1) rfl) (H.exact₂ hS' q)
    hK hL hK'

/-- **Serre's descending induction for GAGA.** Let `𝒞` be a class of sheaves of modules on `X`
such that `Hᵠ(X, F)` and `Hᵠ(X^an, F^an)` vanish for `F ∈ 𝒞` and `q > N`, and such that every
`F ∈ 𝒞` sits in a short exact sequence `0 → K → L → F → 0` with `K ∈ 𝒞` and `gagaMap X L q`
bijective for all `q`. Then `gagaMap X F q` is bijective for all `F ∈ 𝒞` and all `q`. -/
theorem gagaMap_bijective_of_descending (N : ℕ)
    (𝒞 : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf → Prop)
    (hvan : ∀ F, 𝒞 F → ∀ q, N < q →
      Subsingleton (H F q) ∧ Subsingleton (H ((analytificationModules X).obj F) q))
    (hres : ∀ F, 𝒞 F →
      ∃ S : ShortComplex (SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf),
        S.ShortExact ∧ 𝒞 S.X₁ ∧ Nonempty (S.X₃ ≅ F) ∧
          ∀ q, Function.Bijective (gagaMap X S.X₂ q))
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) (hF : 𝒞 F) (q : ℕ) :
    Function.Bijective (gagaMap X F q) := by
  -- the inductive step: bijectivity in degree `q + 1` for `𝒞` implies it in degree `q`
  have step : ∀ q, (∀ F, 𝒞 F → Function.Bijective (gagaMap X F (q + 1))) →
      ∀ F, 𝒞 F → Function.Bijective (gagaMap X F q) := by
    intro q ih
    have surj : ∀ F, 𝒞 F → Function.Surjective (gagaMap X F q) := by
      intro F hF
      obtain ⟨S, hS, hK, ⟨e⟩, hL⟩ := hres F hF
      have h := gagaMap_surjective_of_shortExact hS q (hL q).2 (ih _ hK).2 (hL (q + 1)).1
      have h₁ : ⇑(gagaMap X F q) ∘ ⇑(H.map e.hom q) =
          ⇑(H.map ((analytificationModules X).map e.hom) q) ∘ ⇑(gagaMap X S.X₃ q) :=
        funext fun x ↦ gagaMap_map e.hom x
      have h₂ : Function.Surjective (⇑(gagaMap X F q) ∘ ⇑(H.map e.hom q)) := by
        rw [h₁]
        exact (bijective_H_map_hom ((analytificationModules X).mapIso e) q).2.comp h
      exact h₂.of_comp
    intro F hF
    obtain ⟨S, hS, hK, ⟨e⟩, hL⟩ := hres F hF
    refine (gagaMap_bijective_iff_of_iso e q).1 ⟨?_, ?_⟩
    · exact gagaMap_injective_of_shortExact hS q (surj _ hK) (hL q).1 (ih _ hK).1
    · exact gagaMap_surjective_of_shortExact hS q (hL q).2 (ih _ hK).2 (hL (q + 1)).1
  -- descending induction, starting from the vanishing range `q > N`
  have key : ∀ k q, N < q + k → ∀ F, 𝒞 F → Function.Bijective (gagaMap X F q) := by
    intro k
    induction k with
    | zero =>
      intro q hq F hF
      obtain ⟨h₁, h₂⟩ := hvan F hF q (by simpa using hq)
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    | succ k ih =>
      intro q hq
      exact step q (ih (q + 1) (by omega))
  exact key (N + 1) q (by omega) F hF

end ComplexAnalytic

end
