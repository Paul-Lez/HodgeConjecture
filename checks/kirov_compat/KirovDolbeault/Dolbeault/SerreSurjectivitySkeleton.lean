/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreResiduePairing
import KirovDolbeault.Dolbeault.SerreOmega0
import KirovDolbeault.Dolbeault.CechFinitenessWiring
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.RiemannRochDegree

/-!
# Forster §17.9 — the surjectivity dimension-count skeleton

The HARD half of Serre duality is the surjectivity of the residue pairing
`ι_D : L(K−D) → (H¹(𝒪_D))*` (Forster 17.9). Forster's proof is a pigeonhole dimension count
over the divisors `D − nP` whose only *geometric* inputs are Lemma 17.7 (restriction
compatibility + the `ω/ψ` unwinding) and Lemma 17.8 (injectivity of the `ψ`-action
`ψ ↦ ψλ` on `H⁰(𝒪_{nP})`); everything else is Riemann–Roch arithmetic — and every RR input
is already PROVEN in this tree (`cohomological_riemannRoch` / `riemannRoch_inequality` via the
skyscraper χ-jump `chi_add_single`, the `h⁰ = l` bridge `h0Dim_eq_lDim`, negative-degree
vanishing `lDim_eq_zero_of_deg_neg`, and Čech finiteness `finiteDimensional_cechH1_wired`),
as is the abstract pigeonhole core (`SerreDuality.serre_surjectivity_dim_core`).

This file isolates the *entire* §17.9 half to those two named geometric lemmas:

* `SurjectivityInputs R D` — a structure whose fields are exactly Forster 17.7 and 17.8,
  stated against the residue-realization interface `SerreResidueRealization 𝔘 K` (which is
  itself derived from the `GlobalResidue` interface, `SerreResidueRealizationAssembly` —
  so this skeleton is invariant under the architecture choice for the global residue
  functional `res`: Cousin solve or Forster's fine-sheaf/Dolbeault integral);
* `SurjectivityInputs.pairing_surjective` — the §17.9 count: from those inputs, the pairing
  `ι_D = R.pairing D` is surjective. **Axiom-free and sorry-free** — conditional only on the
  structure's fields.

## The count (Forster 17.9, p. 138)

Fix `0 ≠ λ ∈ (H¹(𝒪_D))*` and a point `P`; write `D_n := D − nP`, `g := h¹(0)`, `d := deg D`.
Inside `V n := (H¹(𝒪_{D_n}))*` sit two subspaces:

* `Λ n := range (ψ ↦ ψλ)` with `dim Λ n = l(nP) ≥ n + 1 − g` (17.8 injectivity +
  `riemannRoch_inequality`);
* `I n := range ι_{D_n}` with `dim I n = l(K − D_n) ≥ n + (deg K + 1 − g) − d` (17.6
  injectivity `pairing_injective` + `riemannRoch_inequality`);

while `dim V n = h¹(D_n) = n + g − 1 − d` for `n > d` (`cohomological_riemannRoch` +
`h0Dim_eq_lDim` + `lDim_eq_zero_of_deg_neg`, dualized by `Subspace.dual_finrank_eq`). For `n`
large the dimensions sum past `dim V n`, so `Λ n ⊓ I n ≠ ⊥`
(`serre_surjectivity_dim_core`): some `0 ≠ ψλ = ι_{D_n}(ω)`, whence `ψ ≠ 0` and the 17.7
unwinding (`ω/ψ ∈ L(K−D)` and `ι_D(ω/ψ) = λ`) puts `λ` in the range of `ι_D`.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.6–17.9.
* `docs/planning/KEYSTONE_GAP_ANALYSIS.md` (parent repo), step S7.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The geometric inputs of Forster §17.9** (Lemmas 17.7 and 17.8), stated against the
residue-realization interface `R : SerreResidueRealization 𝔘 K` for a fixed divisor `D`.
These are the ONLY unproven inputs of the surjectivity count
(`SurjectivityInputs.pairing_surjective`); all Riemann–Roch arithmetic is supplied by the
proven API.

* `psiAct` is the §17.8 action: for a functional `λ ∈ (H¹(𝒪_D))*` and `n : ℕ`, the map
  `ψ ↦ ψ·λ` from `H⁰(𝒪_{nP}) = L(nP)` to `(H¹(𝒪_{D−nP}))*` (Forster: `ψλ := λ ∘ (·ψ)`
  through the multiplication map `H¹(𝒪_{D−nP}) → H¹(𝒪_D)`), bundled ℂ-linearly in `ψ`.
* `psiAct_injective` is **Lemma 17.8**: the action is injective for `λ ≠ 0` (key input:
  multiplication by `ψ ≠ 0` is surjective on `H¹`, via the iterated skyscraper LES).
* `unwind` is **Lemma 17.7**: if `ψλ = ι_{D−nP}(ω)` with `ψ ≠ 0` then `ω/ψ ∈ L(K−D)` and
  `ι_D(ω/ψ) = λ` — recorded directly as its consequence `λ ∈ range ι_D`. -/
structure SurjectivityInputs {𝔘 : FiniteCover X} {K : Divisor X}
    (R : SerreResidueRealization 𝔘 K) (D : Divisor X) where
  /-- The auxiliary point `P` along which the divisor is shrunk (`D_n = D − nP`). -/
  P : X
  /-- **Forster §17.8 — the `ψ`-action.** `ψ ↦ ψ·λ : L(nP) → (H¹(𝒪_{D−nP}))*`, ℂ-linear
  in `ψ`. -/
  psiAct : ∀ (_lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ),
    lSysModule (X := X) (Finsupp.single P (n : ℤ)) →ₗ[ℂ]
      Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single P (n : ℤ)))
  /-- **Forster §17.8 — injectivity of the `ψ`-action** for `λ ≠ 0` (`Λ_n ≅ H⁰(𝒪_{nP})`). -/
  psiAct_injective : ∀ (lam : Module.Dual ℂ (𝔘.cechH1 D)), lam ≠ 0 →
    ∀ n : ℕ, Function.Injective (psiAct lam n)
  /-- **Forster §17.7 — the unwinding.** A nonzero intersection witness `ψλ = ι_{D−nP}(ω)`
  (with `ψ ≠ 0`) unwinds to `λ = ι_D(ω/ψ)`, i.e. `λ` lies in the range of the pairing at `D`. -/
  unwind : ∀ (lam : Module.Dual ℂ (𝔘.cechH1 D)), lam ≠ 0 →
    ∀ (n : ℕ) (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ)))
      (w : lSysModule (X := X) (K - (D - Finsupp.single P (n : ℤ)))),
      ψ ≠ 0 → psiAct lam n ψ = R.pairing (D - Finsupp.single P (n : ℤ)) w →
      lam ∈ Set.range (R.pairing D)

namespace SurjectivityInputs

variable {𝔘 : FiniteCover X} {K : Divisor X} {R : SerreResidueRealization 𝔘 K} {D : Divisor X}

/-- **Forster §17.9 — surjectivity of the residue pairing from the 17.7/17.8 inputs**
(the HARD half of Serre duality, reduced to its two geometric lemmas). The proof is the
pigeonhole dimension count `serre_surjectivity_dim_core` instantiated over the PROVEN
Riemann–Roch API: `riemannRoch_inequality` (twice, for the `Λ` and `Im ι` lower bounds, with
17.8/17.6 injectivity converting ranks), and `cohomological_riemannRoch` + `h0Dim_eq_lDim` +
`lDim_eq_zero_of_deg_neg` (the exact `dim V n` formula past `n = deg D`), with finiteness from
`finiteDimensional_cechH1_wired`. -/
theorem pairing_surjective (S : SurjectivityInputs R D) (hR : 𝔘.LocallyRealizable) :
    Function.Surjective (R.pairing D) := by
  intro lam
  -- `λ = 0` is hit by `0`.
  rcases eq_or_ne lam 0 with rfl | hlam
  · exact ⟨0, map_zero _⟩
  -- Finiteness of every `H¹(𝒪_{D−nP})` and of its dual (Forster §14, unconditional).
  haveI hfin : ∀ n : ℕ, FiniteDimensional ℂ (𝔘.cechH1 (D - Finsupp.single S.P (n : ℤ))) :=
    fun n => finiteDimensional_cechH1_wired 𝔘 _
  haveI : ∀ n : ℕ,
      FiniteDimensional ℂ (Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single S.P (n : ℤ)))) :=
    fun n => inferInstance
  -- `dim Λ n = l(nP) ≥ n + 1 − g` (17.8 injectivity + the RR inequality).
  have hΛ : ∀ n : ℕ, (1 : ℤ) - (𝔘.h1Dim 0 : ℤ) + (n : ℤ) ≤
      (finrank ℂ (LinearMap.range (S.psiAct lam n)) : ℤ) := by
    intro n
    have hrk : finrank ℂ (LinearMap.range (S.psiAct lam n))
        = lDim (X := X) (Finsupp.single S.P (n : ℤ)) :=
      ((LinearEquiv.ofInjective (S.psiAct lam n)
        (S.psiAct_injective lam hlam n)).finrank_eq).symm
    have hRR := riemannRoch_inequality hR (Finsupp.single S.P (n : ℤ))
    rw [Divisor.deg_single] at hRR
    rw [hrk]
    linarith
  -- `dim I n = l(K − (D − nP)) ≥ n + (deg K + 1 − g) − d` (17.6 injectivity + RR inequality).
  have hI : ∀ n : ℕ, (n : ℤ) + (Divisor.deg X K + 1 - (𝔘.h1Dim 0 : ℤ)) - Divisor.deg X D ≤
      (finrank ℂ
        (LinearMap.range (R.pairing (D - Finsupp.single S.P (n : ℤ)))) : ℤ) := by
    intro n
    have hrk : finrank ℂ (LinearMap.range (R.pairing (D - Finsupp.single S.P (n : ℤ))))
        = lDim (X := X) (K - (D - Finsupp.single S.P (n : ℤ))) :=
      ((LinearEquiv.ofInjective (R.pairing (D - Finsupp.single S.P (n : ℤ)))
        (R.pairing_injective (D - Finsupp.single S.P (n : ℤ)))).finrank_eq).symm
    have hRR := riemannRoch_inequality hR (K - (D - Finsupp.single S.P (n : ℤ)))
    rw [Divisor.deg_sub, Divisor.deg_sub, Divisor.deg_single] at hRR
    rw [hrk]
    linarith
  -- `dim V n = h¹(D − nP) = n + g − 1 − d` once `n > d` (cohomological RR; `h⁰ = l = 0`).
  have hV : ∀ n : ℕ, Divisor.deg X D < (n : ℤ) →
      ((finrank ℂ (Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single S.P (n : ℤ)))) : ℤ))
        = (n : ℤ) + (𝔘.h1Dim 0 : ℤ) - 1 - Divisor.deg X D := by
    intro n hdn
    have hdual : finrank ℂ (Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single S.P (n : ℤ))))
        = 𝔘.h1Dim (D - Finsupp.single S.P (n : ℤ)) :=
      Subspace.dual_finrank_eq
    have hRR := cohomological_riemannRoch 𝔘 hR (D - Finsupp.single S.P (n : ℤ))
    rw [𝔘.h0Dim_eq_lDim] at hRR
    have h0 : lDim (X := X) (D - Finsupp.single S.P (n : ℤ)) = 0 := by
      refine lDim_eq_zero_of_deg_neg _ ?_
      rw [Divisor.deg_sub, Divisor.deg_single]
      linarith
    rw [h0, Divisor.deg_sub, Divisor.deg_single] at hRR
    push_cast at hRR
    rw [hdual]
    linarith
  -- The pigeonhole count: for large `n` the two subspaces of `(H¹(𝒪_{D−nP}))*` meet.
  obtain ⟨N, hN⟩ :=
    SerreDuality.serre_surjectivity_dim_core
      (V := fun n => Module.Dual ℂ (𝔘.cechH1 (D - Finsupp.single S.P (n : ℤ))))
      (fun n => LinearMap.range (S.psiAct lam n))
      (fun n => LinearMap.range (R.pairing (D - Finsupp.single S.P (n : ℤ))))
      (𝔘.h1Dim 0 : ℤ) (Divisor.deg X D)
      (Divisor.deg X K + 1 - (𝔘.h1Dim 0 : ℤ)) hΛ hI hV
  -- Extract a nonzero witness `v = ψλ = ι_{D−NP}(ω)`.
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (hN N le_rfl)
  rw [Submodule.mem_inf] at hv
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hv.1
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv.2
  -- `ψ ≠ 0` since the witness is nonzero, so the 17.7 unwinding applies.
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hψ
    exact hv0 hψ.symm
  exact S.unwind lam hlam N ψ w hψ0 (hψ.trans hw.symm)

end SurjectivityInputs

/-- **§17.9 packaged for the `SerreDualityData` assembly** (`toSerreDualityData`'s `ι_surj`
argument): inputs at every divisor give surjectivity at every divisor. -/
theorem pairing_surjective_of_inputs {𝔘 : FiniteCover X} {K : Divisor X}
    {R : SerreResidueRealization 𝔘 K} (hR : 𝔘.LocallyRealizable)
    (S : ∀ D : Divisor X, SurjectivityInputs R D) :
    ∀ D : Divisor X, Function.Surjective (R.pairing D) :=
  fun D => (S D).pairing_surjective hR

end Jacobians.Dolbeault

end
