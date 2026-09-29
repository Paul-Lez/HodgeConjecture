/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.DescendingInduction

/-!
# The five lemma for the GAGA comparison map

Let `X` be a scheme locally of finite type over `ℂ` and `0 → F₁ → F₂ → F₃ → 0` a short exact
sequence of sheaves of modules on `X`. The comparison maps `Hᵠ(X, Fᵢ) → Hᵠ(X^an, Fᵢ^an)` form a
morphism between the long exact cohomology sequences of the sequence and of its analytification.
Hence, by the five lemma, if the comparison map is bijective in all degrees for two of the three
sheaves, it is bijective in all degrees for the third:

- `ComplexAnalytic.gagaMap_bijective_X₁_of_shortExact`,
- `ComplexAnalytic.gagaMap_bijective_X₂_of_shortExact`,
- `ComplexAnalytic.gagaMap_bijective_X₃_of_shortExact`.

The degreewise four lemmas are `ComplexAnalytic.gagaMap_surjective_X₁_of_shortExact`,
`ComplexAnalytic.gagaMap_injective_X₁_of_shortExact`,
`ComplexAnalytic.gagaMap_surjective_X₂_of_shortExact` and
`ComplexAnalytic.gagaMap_injective_X₂_of_shortExact` (for `F₃` see
`ComplexAnalytic.gagaMap_surjective_of_shortExact` and
`ComplexAnalytic.gagaMap_injective_of_shortExact`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

open LocallyRingedSpace

variable {X : SchemeLFTℂ.{u}}
  {S : ShortComplex (SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)}

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`,
if `gagaMap` is surjective on `Hᵠ(F₁)` and `Hᵠ(F₃)` and injective on `Hᵠ⁺¹(F₁)`, then it is
surjective on `Hᵠ(F₂)`. -/
lemma gagaMap_surjective_X₂_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (h₁ : Function.Surjective (gagaMap X S.X₁ q))
    (h₃ : Function.Surjective (gagaMap X S.X₃ q))
    (h₁' : Function.Injective (gagaMap X S.X₁ (q + 1))) :
    Function.Surjective (gagaMap X S.X₂ q) := by
  have hS' := shortExact_map_analytificationModules hS
  exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (H.map S.f q) (H.map S.g q) (H.δ hS q (q + 1) rfl)
    (H.map (S.map (analytificationModules X)).f q) (H.map (S.map (analytificationModules X)).g q)
    (H.δ hS' q (q + 1) rfl)
    (gagaMap X S.X₁ q) (gagaMap X S.X₂ q) (gagaMap X S.X₃ q) (gagaMap X S.X₁ (q + 1))
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
    (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
    (H.exact₃ hS q (q + 1) rfl) (H.exact₂ hS' q) (H.exact₃ hS' q (q + 1) rfl)
    h₁ h₃ h₁'

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`,
if `gagaMap` is injective on `Hᵠ(F₁)` and `Hᵠ(F₃)` and surjective on `Hᵠ⁻¹(F₃)`, then it is
injective on `Hᵠ(F₂)`. -/
lemma gagaMap_injective_X₂_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (h₃ : ∀ p, p + 1 = q → Function.Surjective (gagaMap X S.X₃ p))
    (h₁ : Function.Injective (gagaMap X S.X₁ q))
    (h₃' : Function.Injective (gagaMap X S.X₃ q)) :
    Function.Injective (gagaMap X S.X₂ q) := by
  have hS' := shortExact_map_analytificationModules hS
  cases q with
  | zero =>
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    have hg : H.map S.g 0 x = 0 := h₃' <| by
      rw [gagaMap_map, hx, map_zero, map_zero]
    obtain ⟨y, rfl⟩ := (H.exact₂ hS 0 x).1 hg
    have hy : gagaMap X S.X₁ 0 y = 0 := H.map_f_injective_zero hS' <| by
      refine ((gagaMap_map S.f y).symm.trans hx).trans ?_
      exact (map_zero _).symm
    rw [(injective_iff_map_eq_zero _).1 h₁ y hy, map_zero]
  | succ p =>
    exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (H.δ hS p (p + 1) rfl) (H.map S.f (p + 1)) (H.map S.g (p + 1))
      (H.δ hS' p (p + 1) rfl) (H.map (S.map (analytificationModules X)).f (p + 1))
      (H.map (S.map (analytificationModules X)).g (p + 1))
      (gagaMap X S.X₃ p) (gagaMap X S.X₁ (p + 1)) (gagaMap X S.X₂ (p + 1))
      (gagaMap X S.X₃ (p + 1))
      (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
      (H.exact₁ hS p (p + 1) rfl) (H.exact₂ hS (p + 1)) (H.exact₁ hS' p (p + 1) rfl)
      (h₃ p rfl) h₁ h₃'

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`,
if `gagaMap` is surjective on `Hᵠ(F₂)` and on `Hᵠ⁻¹(F₃)` and injective on `Hᵠ(F₃)`, then it
is surjective on `Hᵠ(F₁)`. -/
lemma gagaMap_surjective_X₁_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (h₃ : ∀ p, p + 1 = q → Function.Surjective (gagaMap X S.X₃ p))
    (h₂ : Function.Surjective (gagaMap X S.X₂ q))
    (h₃' : Function.Injective (gagaMap X S.X₃ q)) :
    Function.Surjective (gagaMap X S.X₁ q) := by
  have hS' := shortExact_map_analytificationModules hS
  cases q with
  | zero =>
    exact AddMonoidHom.surjective_of_surjective_of_injective_of_left_exact
      (H.map S.f 0) (H.map S.g 0)
      (H.map (S.map (analytificationModules X)).f 0) (H.map (S.map (analytificationModules X)).g 0)
      (gagaMap X S.X₁ 0) (gagaMap X S.X₂ 0) (gagaMap X S.X₃ 0)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
      (H.exact₂ hS 0) (H.exact₂ hS' 0) h₂ h₃' (H.map_f_injective_zero hS')
  | succ p =>
    exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (H.δ hS p (p + 1) rfl) (H.map S.f (p + 1)) (H.map S.g (p + 1))
      (H.δ hS' p (p + 1) rfl) (H.map (S.map (analytificationModules X)).f (p + 1))
      (H.map (S.map (analytificationModules X)).g (p + 1))
      (gagaMap X S.X₃ p) (gagaMap X S.X₁ (p + 1)) (gagaMap X S.X₂ (p + 1))
      (gagaMap X S.X₃ (p + 1))
      (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
      (H.exact₂ hS (p + 1)) (H.exact₁ hS' p (p + 1) rfl) (H.exact₂ hS' (p + 1))
      (h₃ p rfl) h₂ h₃'

/-- Four lemma for the GAGA comparison map: for a short exact sequence `0 → F₁ → F₂ → F₃ → 0`,
if `gagaMap` is injective on `Hᵠ(F₂)` and on `Hᵠ⁻¹(F₃)` and surjective on `Hᵠ⁻¹(F₂)`, then it
is injective on `Hᵠ(F₁)`. -/
lemma gagaMap_injective_X₁_of_shortExact (hS : S.ShortExact) (q : ℕ)
    (h₂ : ∀ p, p + 1 = q → Function.Surjective (gagaMap X S.X₂ p))
    (h₃ : ∀ p, p + 1 = q → Function.Injective (gagaMap X S.X₃ p))
    (h₂' : Function.Injective (gagaMap X S.X₂ q)) :
    Function.Injective (gagaMap X S.X₁ q) := by
  have hS' := shortExact_map_analytificationModules hS
  cases q with
  | zero =>
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ H.map_f_injective_zero hS ?_
    rw [map_zero]
    exact h₂' (by rw [gagaMap_map, hx, map_zero, map_zero])
  | succ p =>
    exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (H.map S.g p) (H.δ hS p (p + 1) rfl) (H.map S.f (p + 1))
      (H.map (S.map (analytificationModules X)).g p) (H.δ hS' p (p + 1) rfl)
      (H.map (S.map (analytificationModules X)).f (p + 1))
      (gagaMap X S.X₂ p) (gagaMap X S.X₃ p) (gagaMap X S.X₁ (p + 1)) (gagaMap X S.X₂ (p + 1))
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.g x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_δ hS rfl x).symm)
      (AddMonoidHom.ext fun x ↦ (gagaMap_map S.f x).symm)
      (H.exact₃ hS p (p + 1) rfl) (H.exact₁ hS p (p + 1) rfl) (H.exact₃ hS' p (p + 1) rfl)
      (h₂ p rfl) (h₃ p rfl) h₂'

/-- **Five lemma for GAGA**: in a short exact sequence `0 → F₁ → F₂ → F₃ → 0`, if the comparison
map is bijective in all degrees for `F₂` and `F₃`, then so it is for `F₁`. -/
theorem gagaMap_bijective_X₁_of_shortExact (hS : S.ShortExact)
    (h₂ : ∀ q, Function.Bijective (gagaMap X S.X₂ q))
    (h₃ : ∀ q, Function.Bijective (gagaMap X S.X₃ q)) (q : ℕ) :
    Function.Bijective (gagaMap X S.X₁ q) :=
  ⟨gagaMap_injective_X₁_of_shortExact hS q (fun p _ ↦ (h₂ p).2) (fun p _ ↦ (h₃ p).1) (h₂ q).1,
    gagaMap_surjective_X₁_of_shortExact hS q (fun p _ ↦ (h₃ p).2) (h₂ q).2 (h₃ q).1⟩

/-- **Five lemma for GAGA**: in a short exact sequence `0 → F₁ → F₂ → F₃ → 0`, if the comparison
map is bijective in all degrees for `F₁` and `F₃`, then so it is for `F₂`. -/
theorem gagaMap_bijective_X₂_of_shortExact (hS : S.ShortExact)
    (h₁ : ∀ q, Function.Bijective (gagaMap X S.X₁ q))
    (h₃ : ∀ q, Function.Bijective (gagaMap X S.X₃ q)) (q : ℕ) :
    Function.Bijective (gagaMap X S.X₂ q) :=
  ⟨gagaMap_injective_X₂_of_shortExact hS q (fun p _ ↦ (h₃ p).2) (h₁ q).1 (h₃ q).1,
    gagaMap_surjective_X₂_of_shortExact hS q (h₁ q).2 (h₃ q).2 (h₁ (q + 1)).1⟩

/-- **Five lemma for GAGA**: in a short exact sequence `0 → F₁ → F₂ → F₃ → 0`, if the comparison
map is bijective in all degrees for `F₁` and `F₂`, then so it is for `F₃`. -/
theorem gagaMap_bijective_X₃_of_shortExact (hS : S.ShortExact)
    (h₁ : ∀ q, Function.Bijective (gagaMap X S.X₁ q))
    (h₂ : ∀ q, Function.Bijective (gagaMap X S.X₂ q)) (q : ℕ) :
    Function.Bijective (gagaMap X S.X₃ q) :=
  ⟨gagaMap_injective_of_shortExact hS q (h₁ q).2 (h₂ q).1 (h₁ (q + 1)).1,
    gagaMap_surjective_of_shortExact hS q (h₂ q).2 (h₁ (q + 1)).2 (h₂ (q + 1)).1⟩

end ComplexAnalytic

end
