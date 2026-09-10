/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerrePsiAction
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.Dolbeault.CechFinitenessWiring

/-!
# Čech vanishing at large effective divisors — the cup-multiplication kill (rung 3, step 1)

For every class `ξ ∈ H¹(𝒪)` there is an effective divisor `A` with `incl_{0→A} ξ = 0`, and
hence an effective `A₀` with `H¹(𝒪_A) = 0` for EVERY `A ≥ A₀` (idea: Kirov `CechH1CupKill`,
`docs/planning/KIROV_ROUTE_IDEAS.md` item 4 step 1; implementation ours over the port's
`cup`/`h1InclMono`/`cohomological_riemannRoch` API).

* `exists_effective_h1InclMono_eq_zero` — the one-class kill.  Pigeonhole: the cup-at-`ξ` map
  `L(nP) → H¹(𝒪_{nP})`, `ψ ↦ ψ ⌣ ξ`, has `l(nP) = h¹(nP) + 1 > h¹(nP)` at `n := h¹(𝒪)`
  (cohomological RR), so some junk-free class `ψ ≠ 0` has `ψ ⌣ ξ = 0`; then with
  `A := nP + div ψ ≥ 0` the inclusion factors as
  `incl_{0→A} ξ = ψ⁻¹ ⌣ (ψ ⌣ ξ) = 0` (the germ inverse law `globalGerm_mul_inv`, exactly the
  `cupH1_surjective` factorization run in the killing direction).
* `exists_effective_h1Dim_eq_zero_forall_ge` — the headline: an effective `A₀` such that
  `h¹(𝒪_A) = 0` for all `A ≥ A₀`.  Kill a basis of the finite-dimensional `H¹(𝒪)`
  (`finiteDimensional_cechH1_wired`), sum the killing divisors, and use surjectivity of the
  monotone inclusion (`h1InclMono_surjective`, iterated skyscraper): an onto map that kills a
  basis has zero target.

Together with the (pending) Laurent-tail Riemann–Roch this yields `h¹(𝒪) = g` by subtracting
the two RRs at `A` — `TailGenusTarget.lean`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §16; Miranda (GSM 5), Ch. VI.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

/-! ## Part 0 — effective-divisor bookkeeping -/

/-- The degree of an effective divisor is nonnegative. -/
theorem deg_nonneg_of_effective {A : Divisor X} (hA : ∀ x, (0 : Divisor X) x ≤ A x) :
    0 ≤ Divisor.deg X A := by
  rw [show Divisor.deg X A = ∑ x ∈ A.support, A x from Finsupp.degree_apply _]
  refine Finset.sum_nonneg fun x _ => ?_
  have := hA x
  simp only [Finsupp.coe_zero, Pi.zero_apply] at this
  exact this

/-! ## Part 1 — the one-class kill -/

/-- **Every class of `H¹(𝒪)` dies in some effective level** (Forster §16 cup-multiplication
pigeonhole): for `ξ ∈ H¹(𝒪)` there is an effective `A` with `incl_{0→A} ξ = 0`.

Pigeonhole at `n := h¹(𝒪)`: cohomological RR gives `l(nP) = h¹(nP) + 1`, so the cup-at-`ξ`
map `L(nP) → H¹(𝒪_{nP})` has a nonzero kernel class `ψ`; with `A := nP + div ψ` (effective by
`ψ ∈ L(nP)`), the inclusion factors through the germ-inverse pair
`incl_{0→A} ξ = ψ⁻¹ ⌣ (ψ ⌣ ξ) = ψ⁻¹ ⌣ 0 = 0`. -/
theorem exists_effective_h1InclMono_eq_zero (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (P : X) (ξ : 𝔘.cechH1 (0 : Divisor X)) :
    ∃ (A : Divisor X) (hA : ∀ x, (0 : Divisor X) x ≤ A x), 𝔘.h1InclMono hA ξ = 0 := by
  classical
  set n : ℤ := (𝔘.h1Dim (0 : Divisor X) : ℤ) with hn
  set A1 : Divisor X := Finsupp.single P n with hA1
  haveI : FiniteDimensional ℂ (𝔘.cechH1 A1) := finiteDimensional_cechH1_wired 𝔘 A1
  -- the cup-at-`ξ` map
  set T : lSysModule (X := X) (A1 - 0) →ₗ[ℂ] 𝔘.cechH1 A1 :=
    (cup (𝔘 := 𝔘.toFiniteFamily) 0 A1).flip ξ with hT
  -- pigeonhole: `T` has a nonzero kernel class
  have hker : ∃ φ : lSysModule (X := X) (A1 - 0), φ ≠ 0 ∧ T φ = 0 := by
    by_contra hc
    simp only [not_exists, not_and] at hc
    have hinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro φ hφ
      by_contra hφ0
      exact hc φ hφ0 hφ
    have hle : lDim (X := X) (A1 - 0) ≤ 𝔘.h1Dim A1 :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have h0eq : 𝔘.h0Dim A1 = lDim (X := X) (A1 - 0) := by
      rw [sub_zero]
      exact 𝔘.h0Dim_eq_lDim A1
    have hdeg : Divisor.deg X A1 = n := by
      rw [hA1, Divisor.deg_single]
    have hRR := cohomological_riemannRoch 𝔘 hR A1
    rw [hdeg, h0eq] at hRR
    omega
  obtain ⟨φ, hφ0, hφT⟩ := hker
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ φ
  -- a germ-nonzero representative
  have hψ0 : ∃ x, (ψ : MeromorphicFunction X).orderW x ≠ ⊤ := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact hφ0 ((Submodule.Quotient.mk_eq_zero _).mpr fun x => hc x)
  have hne : ∀ x, (ψ : MeromorphicFunction X).orderW x ≠ ⊤ :=
    (ψ : MeromorphicFunction X).orderW_ne_top_of_exists hψ0
  -- the kill at level `A1`
  have hkill : cupH1 (𝔘 := 𝔘.toFiniteFamily) ψ.2 ξ = 0 := by
    have : T (Submodule.Quotient.mk ψ) = cupH1 (𝔘 := 𝔘.toFiniteFamily) ψ.2 ξ := by
      rw [hT, LinearMap.flip_apply, cup_mk]
    rw [← this]
    exact hφT
  -- the divisor lower bound from `ψ ∈ L(A1 − 0)`
  have hdiv : ∀ x, -(A1 x) ≤ MeromorphicFunction.div X ψ x := by
    intro x
    have h1 := ψ.2 x
    rw [← MeromorphicFunction.coe_div_eq_orderW hne x] at h1
    have h2 : -((A1 - 0 : Divisor X) x) ≤ MeromorphicFunction.div X ψ x := by
      exact_mod_cast h1
    have happ : (A1 - 0 : Divisor X) x = A1 x := by
      simp
    rw [happ] at h2
    exact h2
  -- the effective target level
  refine ⟨A1 + MeromorphicFunction.div X ψ, fun x => ?_, ?_⟩
  · simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply]
    have := hdiv x
    omega
  -- the reciprocal multiplies `𝒪_{A1}` into `𝒪_A`
  have hinv : (ψ : MeromorphicFunction X)⁻¹
      ∈ linearSystem (X := X) ((A1 + MeromorphicFunction.div X ψ) - A1) := by
    intro x
    rw [add_sub_cancel_left, MeromorphicFunction.orderW_inv,
      ← MeromorphicFunction.coe_div_eq_orderW hne x]
  -- the inclusion factors through the germ-inverse pair
  have hfact : ∀ (h0A : ∀ x, (0 : Divisor X) x ≤ (A1 + MeromorphicFunction.div X ψ) x),
      𝔘.h1InclMono h0A ξ
        = cupH1 (𝔘 := 𝔘.toFiniteFamily) hinv (cupH1 (𝔘 := 𝔘.toFiniteFamily) ψ.2 ξ) := by
    intro h0A
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [cupH1_mk, cupH1_mk, 𝔘.h1InclMono_mk]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    funext p
    simp only [cupCocyclesMap_coe, cupCochain1_apply, FiniteCover.cocyclesInclMono_coe]
    rw [← mul_assoc, mul_comm (globalGerm ((ψ : MeromorphicFunction X)⁻¹) _),
      globalGerm_mul_inv hne, one_mul]
  rw [hfact, hkill, map_zero]

/-! ## Part 2 — the headline: `H¹(𝒪_A) = 0` for all large effective `A` -/

/-- **Čech vanishing at large effective divisors**: there is an effective `A₀` with
`h¹(𝒪_A) = 0` for EVERY `A ≥ A₀`.  Kill a basis of the finite-dimensional `H¹(𝒪)` one class
at a time (`exists_effective_h1InclMono_eq_zero`), sum the killing divisors, and use
surjectivity of the monotone inclusion (`h1InclMono_surjective`): an onto linear map that
kills a basis has zero target. -/
theorem exists_effective_h1Dim_eq_zero_forall_ge (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) :
    ∃ A₀ : Divisor X, (∀ x, (0 : Divisor X) x ≤ A₀ x) ∧
      ∀ (A : Divisor X), (∀ x, A₀ x ≤ A x) → 𝔘.h1Dim A = 0 := by
  classical
  haveI : FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)) := finiteDimensional_cechH1_wired 𝔘 0
  obtain ⟨P⟩ : Nonempty X := inferInstance
  set b := Module.finBasis ℂ (𝔘.cechH1 (0 : Divisor X)) with hb
  choose Ai hAi hkill using fun i => exists_effective_h1InclMono_eq_zero 𝔘 hR P (b i)
  refine ⟨∑ i, Ai i, fun x => ?_, fun A hA => ?_⟩
  · -- effectivity of the sum
    rw [Finset.sum_apply']
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    have := hAi i x
    simpa using this
  · -- the inclusion `0 → A` kills the basis …
    have h0A : ∀ x, (0 : Divisor X) x ≤ A x := by
      intro x
      refine le_trans ?_ (hA x)
      rw [Finset.sum_apply']
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      refine Finset.sum_nonneg fun i _ => ?_
      simpa using hAi i x
    have hAiA : ∀ i x, Ai i x ≤ A x := by
      intro i x
      refine le_trans ?_ (hA x)
      rw [Finset.sum_apply']
      refine Finset.single_le_sum (f := fun j => Ai j x) (fun j _ => ?_) (Finset.mem_univ i)
      simpa using hAi j x
    have hzero : ∀ i, 𝔘.h1InclMono h0A (b i) = 0 := by
      intro i
      have hcomp := 𝔘.h1InclMono_comp (hAi i) (hAiA i)
      have happ := congrArg (fun g : 𝔘.cechH1 (0 : Divisor X) →ₗ[ℂ] 𝔘.cechH1 A => g (b i)) hcomp
      simp only [LinearMap.comp_apply] at happ
      calc 𝔘.h1InclMono h0A (b i)
          = 𝔘.h1InclMono (fun x => le_trans (hAi i x) (hAiA i x)) (b i) := rfl
        _ = 𝔘.h1InclMono (hAiA i) (𝔘.h1InclMono (hAi i) (b i)) := happ.symm
        _ = 0 := by rw [hkill i, map_zero]
    -- … and is onto, so the target is zero
    have hmap : 𝔘.h1InclMono h0A = (0 : 𝔘.cechH1 (0 : Divisor X) →ₗ[ℂ] 𝔘.cechH1 A) :=
      b.ext fun i => by rw [hzero i, LinearMap.zero_apply]
    have hall : ∀ η : 𝔘.cechH1 A, η = 0 := by
      intro η
      obtain ⟨ζ, rfl⟩ := 𝔘.h1InclMono_surjective hR h0A η
      rw [hmap, LinearMap.zero_apply]
    haveI : Subsingleton (𝔘.cechH1 A) := ⟨fun a c => by rw [hall a, hall c]⟩
    exact Module.finrank_zero_of_subsingleton

end Dolbeault

end Jacobians

end
