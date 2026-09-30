/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Localization.Submodule
public import Other.Oka.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Finite resolutions of finitely generated modules of finite projective dimension

Let `R` be a Noetherian ring and `M` a finitely generated `R`-module of projective dimension
`≤ n + 1`. Then there is a short exact sequence `0 → K → Rᵏ → M → 0` with `K` finitely generated
of projective dimension `≤ n` (`ModuleCat.exists_shortExact_of_hasProjectiveDimensionLE_succ`),
and a module of projective dimension `≤ 0` is projective. Iterating, `M` has a resolution
`0 → Pₙ₊₁ → Rᵏⁿ → ⋯ → Rᵏ⁰ → M → 0` with `Pₙ₊₁` finitely generated projective; we package this
as an induction principle (`ModuleCat.induction_of_hasProjectiveDimensionLE`).

Combined with Hilbert's syzygy theorem this applies to every finitely generated module over
`k[X₁, …, Xₙ]` and over its localisations, with `n` steps
(`ModuleCat.induction_of_isLocalization_mvPolynomial`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- A module of projective dimension `≤ 0` is projective. -/
lemma projective_of_hasProjectiveDimensionLE_zero (M : Type u) [AddCommGroup M] [Module R M]
    [h : HasProjectiveDimensionLE (ModuleCat.of R M) 0] : Module.Projective R M := by
  simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective] at h
  exact h

/-- A finitely generated module `M` of projective dimension `≤ n + 1` over a Noetherian ring is
the cokernel of an injection `K → Rᵏ` with `K` finitely generated of projective dimension
`≤ n`. -/
lemma exists_shortExact_of_hasProjectiveDimensionLE_succ [IsNoetherianRing R] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)] :
    ∃ (k : ℕ) (g : (Fin k → R) →ₗ[R] M), Function.Surjective g ∧
      Module.Finite R (LinearMap.ker g) ∧
      HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker g)) n := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' R M
  exact ⟨k, g, hg, inferInstance, hasProjectiveDimensionLE_of_exact (K := LinearMap.ker g)
    (LinearMap.ker g).subtype g (LinearMap.exact_subtype_ker_map g)
    (Submodule.injective_subtype _) hg n⟩

/-- Induction principle for finitely generated modules of projective dimension `≤ n` over a
Noetherian ring: a property which holds for finitely generated projective modules and passes
from `K` to `M` along every short exact sequence `0 → K → Rᵏ → M → 0` of finitely generated
modules holds for all such modules. -/
theorem induction_of_hasProjectiveDimensionLE [IsNoetherianRing R]
    (P : ∀ (M : Type u) [AddCommGroup M] [Module R M], Prop)
    (proj : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], P M)
    (step : ∀ (K M : Type u) [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
      [Module.Finite R K] [Module.Finite R M] (k : ℕ) (f : K →ₗ[R] (Fin k → R))
      (g : (Fin k → R) →ₗ[R] M), Function.Exact f g → Function.Injective f →
        Function.Surjective g → P K → P M)
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] : P M := by
  induction n generalizing M with
  | zero =>
    have := projective_of_hasProjectiveDimensionLE_zero (R := R) M
    exact proj M
  | succ n ih =>
    obtain ⟨k, g, hg, hK, hpd⟩ := exists_shortExact_of_hasProjectiveDimensionLE_succ (R := R) n M
    exact step _ M k (LinearMap.ker g).subtype g (LinearMap.exact_subtype_ker_map g)
      (Submodule.injective_subtype _) hg (ih _)

/-- Over a ring of global dimension `≤ n`, the induction principle
`induction_of_hasProjectiveDimensionLE` applies to every finitely generated module. -/
theorem HasGlobalDimensionLE.induction [IsNoetherianRing R] {n : ℕ}
    (hR : HasGlobalDimensionLE R n)
    (P : ∀ (M : Type u) [AddCommGroup M] [Module R M], Prop)
    (proj : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], P M)
    (step : ∀ (K M : Type u) [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
      [Module.Finite R K] [Module.Finite R M] (k : ℕ) (f : K →ₗ[R] (Fin k → R))
      (g : (Fin k → R) →ₗ[R] M), Function.Exact f g → Function.Injective f →
        Function.Surjective g → P K → P M)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : P M :=
  have := hR M
  induction_of_hasProjectiveDimensionLE P proj step n M

/-- **Hilbert's syzygy theorem, resolution form**: every finitely generated module over a
localisation `R'` of `k[X₁, …, Xₙ]` (e.g. `k[X₁, …, Xₙ]` itself, or `k[X₁, …, Xₙ][1/f]`)
satisfies every property which holds for finitely generated projective modules and passes from
`K` to `M` along short exact sequences `0 → K → R'ᵏ → M → 0` of finitely generated modules. -/
theorem induction_of_isLocalization_mvPolynomial (k : Type u) [Field k] (n : ℕ)
    (S : Submonoid (MvPolynomial (Fin n) k)) (R' : Type u) [CommRing R']
    [Algebra (MvPolynomial (Fin n) k) R'] [IsLocalization S R']
    (P : ∀ (M : Type u) [AddCommGroup M] [Module R' M], Prop)
    (proj : ∀ (M : Type u) [AddCommGroup M] [Module R' M] [Module.Finite R' M]
      [Module.Projective R' M], P M)
    (step : ∀ (K M : Type u) [AddCommGroup K] [Module R' K] [AddCommGroup M] [Module R' M]
      [Module.Finite R' K] [Module.Finite R' M] (k : ℕ) (f : K →ₗ[R'] (Fin k → R'))
      (g : (Fin k → R') →ₗ[R'] M), Function.Exact f g → Function.Injective f →
        Function.Surjective g → P K → P M)
    (M : Type u) [AddCommGroup M] [Module R' M] [Module.Finite R' M] : P M :=
  have : IsNoetherianRing R' := IsLocalization.isNoetherianRing S R' inferInstance
  (hasGlobalDimensionLE_of_isLocalization_mvPolynomial k n S R').induction P proj step M

end ModuleCat

end
