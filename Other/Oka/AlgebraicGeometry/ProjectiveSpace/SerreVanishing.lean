/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TheoremA
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Vanishing

/-!
# Serre's vanishing theorem on projective space

Let `R` be a noetherian ring and `F` a coherent sheaf on `ℙⁿ = ℙₒ(n; R)`. Then there is `m₀` such
that `Hᵠ(ℙⁿ, F(m)) = 0` for all `q ≥ 1` and `m ≥ m₀`
(`ProjectiveSpace.exists_H_twist_eq_zero`, and
`ProjectiveSpace.exists_locallyRingedSpaceH_twist_eq_zero` for the `LocallyRingedSpace.H`
spelling).

The proof is Serre's descending induction on `q`: for `q ≥ n + 1` all cohomology of
quasi-coherent sheaves vanishes. For smaller `q ≥ 1`, Theorem A gives a short exact sequence
`0 → K → ⊕ O(-m₁) → F → 0` with `K` coherent; twisting by `m` is exact, `Hᵠ(⊕ O(m - m₁)) = 0`
for `q ≥ 1` once `m - m₁ ≥ -n`, and `Hᵠ⁺¹(K(m)) = 0` for `m ≫ 0` by induction, so the long exact
sequence gives `Hᵠ(F(m)) = 0`.

We also record that cohomology of a finite coproduct of sheaves of modules vanishes if it
vanishes on every summand (`ProjectiveSpace.H_sigma_eq_zero`).
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProjectiveSpace

/-- The forgetful functor from `𝒪_X`-modules to abelian sheaves, `SheafOfModules.toSheaf` typed on
the category `X.Modules`. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.Modules.toAbFunctor (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.AbSheaf X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance (X : Scheme.{u}) : (Scheme.Modules.toAbFunctor X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance (X : Scheme.{u}) : PreservesFiniteLimits (Scheme.Modules.toAbFunctor X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

instance (X : Scheme.{u}) : PreservesFiniteColimits (Scheme.Modules.toAbFunctor X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf))

variable {n : ℕ} {R : Type u} [CommRing R]

/-- Cohomology of a finite coproduct of sheaves of modules vanishes in degree `q` if it vanishes
on every summand. -/
lemma H_sigma_eq_zero {X : Scheme.{u}} {I : Type u} [Finite I] (G : I → X.Modules) (q : ℕ)
    (h : ∀ i (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj (G i)) q), x = 0)
    (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj (∐ G)) q) : x = 0 := by
  have := Fintype.ofFinite I
  have := HasBiproduct.of_hasCoproduct G
  let T := Scheme.Modules.toAbFunctor X
  let e := T.mapIso (biproduct.isoCoproduct G)
  suffices hy : ∀ y : TopCat.Sheaf.H (T.obj (⨁ G)) q, y = 0 by
    have hx : x = TopCat.Sheaf.H.map e.hom q (TopCat.Sheaf.H.map e.inv q x) := by
      rw [← TopCat.Sheaf.H.map_comp_apply, e.inv_hom_id, TopCat.Sheaf.H.map_id_apply]
    rw [hx, hy (TopCat.Sheaf.H.map e.inv q x)]
    exact map_zero _
  intro y
  have htot : ∑ i, biproduct.π G i ≫ biproduct.ι G i = 𝟙 (⨁ G) :=
    IsBilimit.total (biproduct.isBilimit G)
  have hsum : ∀ (s : Finset I) (φ : I → (⨁ G ⟶ ⨁ G)),
      TopCat.Sheaf.H.map (T.map (∑ i ∈ s, φ i)) q y =
        ∑ i ∈ s, TopCat.Sheaf.H.map (T.map (φ i)) q y := by
    classical
    intro s φ
    induction s using Finset.induction_on with
    | empty => simp [TopCat.Sheaf.H.map_zero_apply]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, T.map_add,
        TopCat.Sheaf.H.map_add_apply, ih]
  rw [← TopCat.Sheaf.H.map_id_apply y, ← T.map_id, ← htot, hsum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [T.map_comp, TopCat.Sheaf.H.map_comp_apply, h i (TopCat.Sheaf.H.map _ q y), map_zero]

/-- `Hᵠ(ℙⁿ, 𝒪^I(k)) = 0` for `q ≥ 1`, `I` finite and `k ≥ -n`. -/
lemma H_succ_twist_free_eq_zero {I : Type u} [Finite I] (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj
      (twist (SheafOfModules.free I) k)) (q + 1)) : x = 0 := by
  let T := Scheme.Modules.toAbFunctor ℙₒ(n; R)
  let e := T.mapIso (twistFreeIso (n := n) (R := R) I k)
  have hx : x = TopCat.Sheaf.H.map e.inv (q + 1) (TopCat.Sheaf.H.map e.hom (q + 1) x) := by
    rw [← TopCat.Sheaf.H.map_comp_apply, e.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
  have h0 : TopCat.Sheaf.H.map e.hom (q + 1) x = 0 :=
    H_sigma_eq_zero _ (q + 1) (fun _ y ↦ H_succ_twistingSheafAb_eq_zero k hk q y) _
  rw [hx, h0]
  exact map_zero _

/-- The descending induction behind Serre's vanishing theorem: for every coherent `F` there is
`m₀` with `Hᵠ⁺¹(ℙⁿ, F(m)) = 0` whenever `m ≥ m₀` and `n + 1 ≤ q + 1 + k`. -/
theorem exists_H_twist_eq_zero_aux [IsNoetherianRing R] (k : ℕ) :
    ∀ (F : ℙₒ(n; R).Modules) [F.IsCoherent], ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ q : ℕ,
      n + 1 ≤ q + 1 + k → ∀ x : TopCat.Sheaf.H
        ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj (twist F m)) (q + 1), x = 0 := by
  induction k with
  | zero =>
    intro F _
    haveI := SheafOfModules.IsCoherent.isQuasicoherent F
    exact ⟨0, fun m _ q hq x ↦ H_eq_zero_of_le_of_isQuasicoherent (twist F m) (q + 1)
      (by omega) x⟩
  | succ k ih =>
    intro F _
    obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel F
    obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
    obtain ⟨m₂, hm₂⟩ := ih (kernel π)
    refine ⟨max m₂ ((m₁ : ℤ) - n), fun m hm q hq x ↦ ?_⟩
    let S : ShortComplex ℙₒ(n; R).Modules := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
        inferInstance inferInstance
    have hS' := (hS.map_of_exact (twistFunctor n R m)).map_of_exact
      (Scheme.Modules.toAbFunctor ℙₒ(n; R))
    have hδ : TopCat.Sheaf.H.δ hS' (q + 1) (q + 2) rfl x = 0 :=
      hm₂ m (le_of_max_le_left hm) (q + 1) (by omega) _
    obtain ⟨y, hyx⟩ := (TopCat.Sheaf.H.exact₃ hS' (q + 1) (q + 2) rfl x).1 hδ
    have e := twistTwistIso (SheafOfModules.free I : ℙₒ(n; R).Modules) (-(m₁ : ℤ)) m
    let T := Scheme.Modules.toAbFunctor ℙₒ(n; R)
    let e' := T.mapIso e
    have hy : ∀ z : TopCat.Sheaf.H (T.obj (twist (twist (SheafOfModules.free I) (-(m₁ : ℤ))) m))
        (q + 1), z = 0 := by
      intro z
      have hz : z = TopCat.Sheaf.H.map e'.inv (q + 1) (TopCat.Sheaf.H.map e'.hom (q + 1) z) := by
        rw [← TopCat.Sheaf.H.map_comp_apply, e'.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
      have h0 : TopCat.Sheaf.H.map e'.hom (q + 1) z = 0 :=
        H_succ_twist_free_eq_zero (-(m₁ : ℤ) + m) (by omega) q _
      rw [hz, h0]
      exact map_zero _
    rw [← hyx, hy y]
    exact map_zero _

/-- **Serre's vanishing theorem on `ℙⁿ`**: for a coherent sheaf `F` on `ℙₒ(n; R)` with `R`
noetherian there is `m₀` such that `Hᵠ(ℙⁿ, F(m)) = 0` for all `q ≥ 1` and `m ≥ m₀`. -/
theorem exists_H_twist_eq_zero [IsNoetherianRing R] (F : ℙₒ(n; R).Modules) [F.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ q : ℕ, ∀ x : TopCat.Sheaf.H
      ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj (twist F m)) (q + 1), x = 0 := by
  obtain ⟨m₀, h⟩ := exists_H_twist_eq_zero_aux n F
  exact ⟨m₀, fun m hm q ↦ h m hm q (by omega)⟩

/-- **Serre's vanishing theorem on `ℙⁿ`**, in the `LocallyRingedSpace.H` spelling. -/
theorem exists_locallyRingedSpaceH_twist_eq_zero [IsNoetherianRing R] (F : ℙₒ(n; R).Modules)
    [F.IsCoherent] : ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ q : ℕ,
      ∀ x : LocallyRingedSpace.H (Y := ℙₒ(n; R).toLocallyRingedSpace) (twist F m) (q + 1),
        x = 0 :=
  exists_H_twist_eq_zero F

end AlgebraicGeometry.ProjectiveSpace

end
