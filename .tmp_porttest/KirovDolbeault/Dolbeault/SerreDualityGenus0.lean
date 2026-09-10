/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreAssemblyPrep
import KirovDolbeault.RiemannRochDegree

/-!
# Keystone `g = 0` leg — Serre duality data at genus zero (route decision: `docs/planning/G0_ROUTE.md`)

This file closes the `g = 0` leg of the keystone `exists_serreDualityData` down to a SINGLE
scalar atom, the arithmetic-genus vanishing `hga : 𝔘.h1Dim 0 = 0`.  Per the lane-A finding
(`docs/planning/A_LANE_BLOCKER.md`) no landed machinery feeds a residue pairing at source genus
`0` (the `SerreResidueDirectGenus0*` capstones are `ω₀`-holomorphic, hence vacuous there), so the
leg is closed by the **bespoke shape** (blocker shape 2), exploiting two structural facts:

1. `SerreDualityData` constrains its fields only *dimensionally*: `K` need not be the order
   divisor of a meromorphic form — at `g = 0` the explicit divisor `K := −2·P` has
   `deg K = −2 < 0`, so `lDim K = 0 = kirovGenus X` by negative-degree vanishing
   (`lDim_eq_zero_of_deg_neg`, proven via the axiom-clean `deg_div` degree route).  No
   `CanonicalForm17Data`, no residue functional.
2. In finite dimension a bijective linear map `L(K−D) → (H¹(𝒪_D))*` exists **iff** the
   dimensions agree (`LinearEquiv.ofFinrankEq`), and the dimension equality
   `h1Dim D = lDim (K−D)` is exactly the content the structure carries downstream
   (`SerreDualityData.serre_eq`).  At `g = 0` that equality is PROVABLE from the landed
   cohomological Riemann–Roch once `h1Dim 0 = 0` is known:

   * `deg D ≥ −1`: `h¹(D) = 0` — h¹-monotonicity under adding points (the skyscraper LES's
     `surj₄`, `exists_skyscraperLES`) descends `D` to a degree-`(−1)` divisor, where RR +
     `h⁰ = l = 0` give vanishing; and `lDim (K−D) = 0` since `deg (K−D) ≤ −1 < 0`.
   * `deg D ≤ −2`: `h¹(D) = −deg D − 1` (RR with `h⁰(D) = 0`), and
     `lDim (K−D) = deg (K−D) + 1 = −deg D − 1` (RR at `K−D`, whose `h¹` vanishes since
     `deg (K−D) ≥ 0`).

The atom `hga` is a NAMED HYPOTHESIS (never a `sorry`), exactly parallel to the spine's
R-lane-gated inputs in `SerreAssemblyPrep`.  It is **minimal**: any `SerreDualityData` forces
`h1Dim 0 = kirovGenus X` (`SerreDualityData.arithmeticGenus`), so the `g = 0` leg is
mathematically equivalent to it.  Headline consumers:

* `exists_serreDualityData_of_arithmeticGenus_zero` — the `g = 0` leg, from
  `{hR, kirovGenus X = 0, h1Dim 0 = 0}`.
* `exists_serreDualityData_genus_split_arithmetic` — the lane-A spine's genus split with the
  abstract `hzero` leg *discharged* down to the scalar atom.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §16–17; parent-repo planning docs
`A_LANE_BLOCKER.md`, `R4_G0_NOTE.md`, `G0_ROUTE.md`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1 — h¹ monotonicity under adding a point (skyscraper LES, `surj₄`) -/

/-- **h¹ is non-increasing under adding a point.**  The skyscraper long exact sequence ends
`… → H¹(𝒪_D) →[h1Map] H¹(𝒪_{D+P}) → 0` (`surj₄`, the skyscraper has `H^{≥1} = 0`), so the
surjection bounds `h¹(D+P) ≤ h¹(D)`. -/
theorem h1Dim_add_single_le (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) :
    𝔘.h1Dim (D + Finsupp.single P 1) ≤ 𝔘.h1Dim D := by
  obtain ⟨S⟩ := 𝔘.exists_skyscraperLES hR D P
  haveI := S.finH1D
  exact LinearMap.finrank_le_finrank_of_surjective S.surj₄

/-- Iterated h¹ monotonicity: `h¹(D + n·P) ≤ h¹(D)` for every `n : ℕ`. -/
theorem h1Dim_add_single_nat_le (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (D : Divisor X) (P : X) (n : ℕ) :
    𝔘.h1Dim (D + Finsupp.single P (n : ℤ)) ≤ 𝔘.h1Dim D := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := h1Dim_add_single_le 𝔘 hR (D + Finsupp.single P (n : ℤ)) P
    rw [add_assoc, ← Finsupp.single_add] at hstep
    push_cast
    exact hstep.trans ih

/-! ## Part 2 — h¹ vanishing and the h¹ formula at arithmetic genus 0 -/

/-- **h¹ vanishing for `deg D ≥ −1` at arithmetic genus `0`.**  Descend `D` by
`n = deg D + 1` copies of a point `P` to a divisor `E` of degree `−1`, where cohomological RR
(`χ(E) = deg E + 1 − h¹(0) = 0`) and negative-degree `h⁰`-vanishing force `h¹(E) = 0`; then
climb back up by h¹-monotonicity. -/
theorem h1Dim_eq_zero_of_arithmeticGenus_zero (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (hga : 𝔘.h1Dim 0 = 0) {D : Divisor X}
    (hD : -1 ≤ Divisor.deg X D) :
    𝔘.h1Dim D = 0 := by
  obtain ⟨P⟩ : Nonempty X := inferInstance
  set n : ℕ := (Divisor.deg X D + 1).toNat with hn
  set E : Divisor X := D - Finsupp.single P (n : ℤ) with hE
  have hcast : (n : ℤ) = Divisor.deg X D + 1 := Int.toNat_of_nonneg (by omega)
  have hdegE : Divisor.deg X E = -1 := by
    rw [hE, Divisor.deg_sub, Divisor.deg_single, hcast]; ring
  -- `h¹(E) = 0` from RR at the degree-(−1) divisor `E`.
  have hRR := cohomological_riemannRoch 𝔘 hR E
  rw [𝔘.h0Dim_eq_lDim E, lDim_eq_zero_of_deg_neg E (by rw [hdegE]; norm_num), hga, hdegE] at hRR
  -- Climb back up: `D = E + n·P`.
  have hclimb := h1Dim_add_single_nat_le 𝔘 hR E P n
  have hED : E + Finsupp.single P (n : ℤ) = D := by rw [hE]; abel
  rw [hED] at hclimb
  omega

/-- **The h¹ formula for negative degree at arithmetic genus `0`:** `h¹(D) = −deg D − 1`
(cohomological RR with `h⁰(D) = l(D) = 0`). -/
theorem h1Dim_cast_eq_of_deg_neg (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (hga : 𝔘.h1Dim 0 = 0) {D : Divisor X} (hD : Divisor.deg X D < 0) :
    (𝔘.h1Dim D : ℤ) = -Divisor.deg X D - 1 := by
  have hRR := cohomological_riemannRoch 𝔘 hR D
  rw [𝔘.h0Dim_eq_lDim D, lDim_eq_zero_of_deg_neg D hD, hga] at hRR
  omega

/-! ## Part 3 — the Serre dimension equality at genus 0, for the explicit `K = −2·P` -/

/-- **The Serre duality dimension equality at arithmetic genus `0`**, for the explicit
degree-`(−2)` divisor `K = −2·P`: `h¹(D) = l(K − D)` for EVERY divisor `D`.  Case split on
`deg D` (see the module docstring); both sides are computed by RR + h¹-vanishing. -/
theorem h1Dim_eq_lDim_single_neg_two_sub (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (hga : 𝔘.h1Dim 0 = 0) (P : X) (D : Divisor X) :
    𝔘.h1Dim D = lDim (X := X) (Finsupp.single P (-2) - D) := by
  have hdegK : Divisor.deg X (Finsupp.single P (-2 : ℤ)) = -2 := Divisor.deg_single X P (-2)
  have hdegE : Divisor.deg X (Finsupp.single P (-2) - D) = -2 - Divisor.deg X D := by
    rw [Divisor.deg_sub, hdegK]
  by_cases hD : (-1 : ℤ) ≤ Divisor.deg X D
  · -- `deg D ≥ −1`: both sides vanish.
    rw [h1Dim_eq_zero_of_arithmeticGenus_zero 𝔘 hR hga hD,
      lDim_eq_zero_of_deg_neg _ (by rw [hdegE]; omega)]
  · -- `deg D ≤ −2`: both sides equal `−deg D − 1`.
    have h1D := h1Dim_cast_eq_of_deg_neg 𝔘 hR hga (by omega : Divisor.deg X D < 0)
    have hE1 : 𝔘.h1Dim (Finsupp.single P (-2) - D) = 0 :=
      h1Dim_eq_zero_of_arithmeticGenus_zero 𝔘 hR hga (by rw [hdegE]; omega)
    have hRR := cohomological_riemannRoch 𝔘 hR (Finsupp.single P (-2) - D)
    rw [𝔘.h0Dim_eq_lDim, hE1, hga, hdegE] at hRR
    omega

/-! ## Part 4 — the `g = 0` keystone leg -/

/-- **The `g = 0` keystone leg, reduced to the arithmetic-genus atom.**  From
`{hR, kirovGenus X = 0, h1Dim 0 = 0}`, the full keystone conclusion
`Nonempty (SerreDualityData 𝔘)`:

* `K := −2·P` with `lDim K = 0 = kirovGenus X` (negative-degree vanishing);
* `ι_D` := a linear equivalence `L(K−D) ≃ (H¹(𝒪_D))*` from the PROVEN dimension equality
  `h1Dim D = lDim (K−D)` (Part 3) — honest, since in finite dimension a bijective linear map
  exists iff the dimensions agree, and the dimension equality is exactly what the structure
  carries downstream (`serre_eq`);
* `finH1` := the landed Čech finiteness.

The named hypothesis `hga : 𝔘.h1Dim 0 = 0` (Čech `H¹(𝒪) = 0` at genus `0`) is the ONE remaining
analytic atom of the `g = 0` leg, and it is minimal: any `SerreDualityData` forces it
(`SerreDualityData.arithmeticGenus`). -/
theorem exists_serreDualityData_of_arithmeticGenus_zero (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (hg0 : kirovGenus X = 0) (hga : 𝔘.h1Dim 0 = 0) :
    Nonempty (SerreDualityData 𝔘) := by
  obtain ⟨P⟩ : Nonempty X := inferInstance
  -- The pairing equivalences, one per divisor, from the Part-3 dimension equality.
  have hequiv : ∀ D : Divisor X,
      Nonempty (lSysModule (X := X) (Finsupp.single P (-2) - D) ≃ₗ[ℂ]
        Module.Dual ℂ (𝔘.cechH1 D)) := by
    intro D
    haveI : FiniteDimensional ℂ (𝔘.cechH1 D) := finiteDimensional_cechH1_wired 𝔘 D
    haveI : FiniteDimensional ℂ (lSysModule (X := X) (Finsupp.single P (-2) - D)) :=
      (𝔘.globalSectionsEquivQuot (Finsupp.single P (-2) - D)).symm.finiteDimensional
    refine FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_
    rw [Subspace.dual_finrank_eq]
    exact (h1Dim_eq_lDim_single_neg_two_sub 𝔘 hR hga P D).symm
  have e : ∀ D : Divisor X,
      lSysModule (X := X) (Finsupp.single P (-2) - D) ≃ₗ[ℂ] Module.Dual ℂ (𝔘.cechH1 D) :=
    fun D => Classical.choice (hequiv D)
  refine ⟨{ K := Finsupp.single P (-2)
            hKgenus := ?_
            ι := fun D => (e D).toLinearMap
            ι_inj := fun D => (e D).injective
            ι_surj := fun D => (e D).surjective
            finH1 := fun D => finiteDimensional_cechH1_wired 𝔘 D }⟩
  rw [hg0]
  exact lDim_eq_zero_of_deg_neg _ (by rw [Divisor.deg_single]; norm_num)

/-! ## Part 5 — the genus split with the `g = 0` leg discharged to the atom -/

/-- **The lane-A genus split with the `g = 0` leg discharged down to the scalar atom.**
Identical to `exists_serreDualityData_genus_split` (the keystone assembly spine) except that the
abstract `hzero : kirovGenus X = 0 → Nonempty (SerreDualityData 𝔘)` is REPLACED by the strictly
weaker arithmetic-genus atom `kirovGenus X = 0 → 𝔘.h1Dim 0 = 0`.  The keystone discharge is now:
the lane-R provision (`hpos`, the `g ≥ 1` leg) plus this one scalar input. -/
theorem exists_serreDualityData_genus_split_arithmetic (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable)
    (hpos : 0 < kirovGenus X →
      ∃ (ω₀ : HolomorphicOneForms X) (K : Divisor X), ω₀ ≠ 0 ∧
        (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
        ∃ G : GlobalResidue 𝔘 K, ∀ D : Divisor X, G.UnwindRegularity D)
    (hga : kirovGenus X = 0 → 𝔘.h1Dim 0 = 0) :
    Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_genus_split 𝔘 hR hpos
    (fun h0 => exists_serreDualityData_of_arithmeticGenus_zero 𝔘 hR h0 (hga h0))

end Jacobians.Dolbeault

end
