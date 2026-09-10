/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.RiemannRoch
import KirovDolbeault.Dolbeault.FormRemovableSingularity

/-!
# Abel ⊆ campaign, TK-block: third-kind differentials from Riemann–Roch

Route-B reserve bricks of the Abel-⊆ route (`docs/planning/AB_ROUTE.md`, rungs TK0/TK1):
existence of a meromorphic 1-form with a simple pole inside a two-point divisor, by pure
`lDim` counting — "nearly free" now that Riemann–Roch is a theorem.  Also consumed by the
Forster 21.4 lattice program (B-4 reads residues of `f·ωᵢ` at exhibited simple poles).

The key coherence problem this file solves: the RR theorem (`exists_riemannRoch_divisor`)
exhibits SOME divisor `K` with the RR identity, while the 1-form system `Ω_D ≅ 𝒪_{D+K'}`
(`CanonicalForm17Data.lDim_add_K_eq_omegaDim`) works with a **canonical-form divisor**
`K' = div ω₀` — and the two existentials don't share their `K`.  At `0 < kirovGenus X` we
re-run the keystone assembly KEEPING the frame:

* `exists_canonical_serreData_of_kirovGenus_pos` (**TK0**) — a chart-disk Leray cover with
  `SerreDualityData` whose `K` field IS `div ω₀` of an exhibited nonzero **holomorphic**
  `ω₀` (the lane-R provision `exists_separating_unwindRegularity` + the assembly spine
  `GlobalResidue.toSerreDualityData`, whose `K := K` definitionally).
* `exists_riemannRoch_at_form_divisor` (**TK0b**) — hence the RR identity AND
  `deg K = 2g − 2` both hold at that form divisor (ladder composition + `deg_canonical`).
* `exists_thirdKind_pole` (**TK1**) — for `P ≠ Q` at `0 < kirovGenus X`: a meromorphic
  1-form `α ∈ Ω((P) + (Q))` with `ord_P α = −1` or `ord_Q α = −1`.  Count:
  `omegaDim ((P)+(Q)) = lDim ((P)+(Q)+K) = g + 1 > g = omegaDim 0` (RR at `(P)+(Q)+K`,
  `lDim(−(P)−(Q)) = 0` by negative degree, §17.4 iso, `omegaDim_zero_eq_genus`); if no
  member had a pole, `Ω((P)+(Q)) ⊆ Ω(0)` would force `g + 1 ≤ g` through the junk-free
  quotient inclusion.

The residue refinement (poles at BOTH points with opposite nonzero residues, via the
residue atom at `F = α/ω₀`) is TK2 — follow-up.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4, §21.7 (Route B);
Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI.
-/

noncomputable section

open Complex Module
open scoped Manifold ContDiff Topology Classical

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## TK0 — Serre-duality data whose `K` is an exhibited holomorphic-form divisor -/

/-- **TK0: the keystone with the canonical frame KEPT** (at `0 < kirovGenus X`): a
chart-disk Leray + locally-realizable cover `𝔇` carrying `SerreDualityData` whose `K`
field equals `div ω₀` for an exhibited nonzero holomorphic 1-form `ω₀`.  Re-runs the
`g > 0` keystone leg (`exists_separating_unwindRegularity` → §17.9 surjectivity →
`GlobalResidue.toSerreDualityData`) without erasing the frame. -/
theorem exists_canonical_serreData_of_kirovGenus_pos (hg : 0 < kirovGenus X) :
    ∃ (𝔇 : ChartDiskCover X) (ω₀ : HolomorphicOneForms X) (K : Divisor X),
      ω₀ ≠ 0 ∧ (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
      𝔇.toFiniteCover.IsLeray ∧ 𝔇.toFiniteCover.LocallyRealizable ∧
      ∃ data : SerreDualityData 𝔇.toFiniteCover, data.K = K := by
  obtain ⟨𝔇, ρ, href, hL, hR, ω₀, K, hω, hK, G, hreg⟩ :=
    exists_separating_unwindRegularity (chartDiskCover (X := X)).toFiniteCover hg
  refine ⟨𝔇, ω₀, K, hω, hK, hL, hR,
    G.toSerreDualityData (lDim_eq_genus_of_holomorphic_order_eq ω₀ hω hK)
      (fun D =>
        pairing_surjective_of_globalResidue G D (Classical.arbitrary X) hR (hreg D))
      (fun D => finiteDimensional_cechH1_wired 𝔇.toFiniteCover D), rfl⟩

/-! ## TK0b — Riemann–Roch AND `deg K = 2g−2` at the form divisor -/

/-- **TK0b: the RR identity at an exhibited canonical-form divisor** (at
`0 < kirovGenus X`): a nonzero holomorphic `ω₀` with order-divisor `K` such that the full
Riemann–Roch identity holds **with this `K`**, and `deg K = 2g − 2`.  This is the
coherence the third-kind count needs: the same `K` serves the §17.4 iso
`Ω_D ≅ 𝒪_{D+K}` and the RR arithmetic. -/
theorem exists_riemannRoch_at_form_divisor (hg : 0 < kirovGenus X) :
    ∃ (ω₀ : HolomorphicOneForms X) (K : Divisor X), ω₀ ≠ 0 ∧
      (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
      (∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (kirovGenus X : ℤ)) ∧
      Divisor.deg X K = 2 * (kirovGenus X : ℤ) - 2 := by
  obtain ⟨𝔇, ω₀, K, hω, hK, hL, hR, data, hKeq⟩ :=
    exists_canonical_serreData_of_kirovGenus_pos (X := X) hg
  have hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (kirovGenus X : ℤ) := by
    intro D
    have h := cohomological_riemannRoch 𝔇.toFiniteCover hR D
    rw [𝔇.toFiniteCover.h0Dim_eq_lDim D, data.serre_eq D, data.arithmeticGenus, hKeq] at h
    exact h
  exact ⟨ω₀, K, hω, hK, hrr, deg_canonical hrr⟩

/-! ## TK1 — a third-kind pole exists inside `(P) + (Q)` -/

/-- In `WithTop ℤ`: `≥ −1` and `≠ −1` force `≥ 0`. -/
private theorem withTop_nonneg_of_ge_neg_one_ne {o : WithTop ℤ}
    (h1 : ((-1 : ℤ) : WithTop ℤ) ≤ o) (h2 : o ≠ ((-1 : ℤ) : WithTop ℤ)) :
    (0 : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe n =>
    have hn1 : (-1 : ℤ) ≤ n := by exact_mod_cast h1
    have hn2 : n ≠ -1 := fun h => h2 (by rw [h])
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

/-- **TK1: third-kind pole existence** (Forster §17.4 + RR counting; at
`0 < kirovGenus X`): for distinct points `P ≠ Q` there is a meromorphic 1-form
`α ∈ Ω((P) + (Q))` (poles bounded by simple poles at `P` and `Q`) with a GENUINE simple
pole at `P` or at `Q`.  Count: `omegaDim ((P)+(Q)) = g + 1 > g = omegaDim 0`; were every
member pole-free, the junk-free quotient of `Ω((P)+(Q))` would inject into that of
`Ω(0)`, forcing `g + 1 ≤ g`.

(The refinement — poles at BOTH points, residues `c, −c ≠ 0` — is TK2, via the residue
atom at `F = α/ω₀`.) -/
theorem exists_thirdKind_pole (hg : 0 < kirovGenus X) {P Q : X} (hPQ : P ≠ Q) :
    ∃ α : MeromorphicOneForm X,
      α ∈ omegaD (X := X) (Finsupp.single P 1 + Finsupp.single Q 1) ∧
      (α.formOrderW P = ((-1 : ℤ) : WithTop ℤ) ∨
        α.formOrderW Q = ((-1 : ℤ) : WithTop ℤ)) := by
  classical
  obtain ⟨ω₀, K, hω, hK, hrr, hdeg⟩ := exists_riemannRoch_at_form_divisor (X := X) hg
  set Dv : Divisor X := Finsupp.single P 1 + Finsupp.single Q 1 with hDv
  -- the §17.4 datum with THIS `K`
  set data : CanonicalForm17Data X :=
    { ω₀ := holToMero ω₀
      nontrivial := exists_formOrderW_holToMero_ne_top ω₀ hω
      K := K
      order_eq := hK } with hdata
  -- degree bookkeeping: `deg Dv = 2`, `deg (−Dv) = −2 < 0`
  have hdegDv : Divisor.deg X Dv = 2 := by
    rw [hDv, Divisor.deg_add, Divisor.deg_single, Divisor.deg_single]
    norm_num
  -- `lDim (Dv + K) = g + 1` from RR at `Dv + K`
  have hlneg : lDim (X := X) (K - (Dv + K)) = 0 := by
    apply lDim_eq_zero_of_deg_neg
    have hKDvK : K - (Dv + K) = -Dv := by abel
    rw [hKDvK, Divisor.deg_neg, hdegDv]
    norm_num
  have hlDvK : lDim (X := X) (Dv + K) = kirovGenus X + 1 := by
    have h := hrr (Dv + K)
    rw [hlneg, Divisor.deg_add, hdegDv, hdeg] at h
    omega
  -- `omegaDim Dv = g + 1` (the §17.4 iso at the SAME `K`) and `omegaDim 0 = g`
  have homega : omegaDim (X := X) Dv = kirovGenus X + 1 := by
    have h := data.lDim_add_K_eq_omegaDim Dv
    rw [show data.K = K from rfl] at h
    rw [← h, hlDvK]
  -- the contradiction skeleton
  by_contra hcon
  push Not at hcon
  -- pole-freeness: every member of `Ω(Dv)` lies in `Ω(0)`
  have hle : omegaD (X := X) Dv ≤ omegaD (X := X) 0 := by
    intro α hα
    obtain ⟨hP, hQ⟩ := hcon α hα
    intro x
    have hbound := hα x
    rcases eq_or_ne x P with hxP | hxP
    · rw [hxP] at hbound ⊢
      have hDvP : Dv P = 1 := by
        rw [hDv, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hPQ]
        norm_num
      rw [hDvP] at hbound
      have h0 : (0 : WithTop ℤ) ≤ α.formOrderW P :=
        withTop_nonneg_of_ge_neg_one_ne (by exact_mod_cast hbound) hP
      simpa using h0
    · rcases eq_or_ne x Q with hxQ | hxQ
      · rw [hxQ] at hbound ⊢
        have hDvQ : Dv Q = 1 := by
          rw [hDv, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hPQ),
            Finsupp.single_eq_same]
          norm_num
        rw [hDvQ] at hbound
        have h0 : (0 : WithTop ℤ) ≤ α.formOrderW Q :=
          withTop_nonneg_of_ge_neg_one_ne (by exact_mod_cast hbound) hQ
        simpa using h0
      · have hDvx : Dv x = 0 := by
          rw [hDv, Finsupp.add_apply, Finsupp.single_eq_of_ne hxP,
            Finsupp.single_eq_of_ne hxQ]
          norm_num
        rw [hDvx] at hbound
        simpa using hbound
  -- the junk-free quotient of `Ω(Dv)` injects into that of `Ω(0)`
  set inc : ↥(omegaD (X := X) Dv) →ₗ[ℂ] ↥(omegaD (X := X) 0) := Submodule.inclusion hle
    with hinc
  set q : ↥(omegaD (X := X) Dv) →ₗ[ℂ] omegaDModule (X := X) 0 :=
    (Submodule.mkQ _).comp inc with hq
  have hkerq : LinearMap.ker q
      = (formGermZeroSubmodule (X := X)).submoduleOf (omegaD (X := X) Dv) := by
    ext a
    rw [LinearMap.mem_ker, hq, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  set φ : omegaDModule (X := X) Dv →ₗ[ℂ] omegaDModule (X := X) 0 :=
    ((formGermZeroSubmodule (X := X)).submoduleOf (omegaD (X := X) Dv)).liftQ q hkerq.ge
    with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, hφ]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hkerq.le
  have hdim : omegaDim (X := X) Dv ≤ omegaDim (X := X) 0 := by
    rw [omegaDim_eq_finrank, omegaDim_eq_finrank]
    exact LinearMap.finrank_le_finrank_of_injective hφinj
  rw [homega, omegaDim_zero_eq_genus] at hdim
  omega

end Dolbeault

end Jacobians

end
