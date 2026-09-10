/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.KeystonePackaging
import KirovDolbeault.Dolbeault.DolbeaultComparisonEquiv

/-!
# Abel ⊆ campaign, S-block: the ∂̄-solvability criterion skeleton from Serre duality

First bricks of the Abel-⊆ route (`docs/planning/AB_ROUTE.md`, rungs S1–S4): the Forster
19.10 solvability criterion — "`∂̄u = σ` is solvable iff `σ` pairs to zero against every
holomorphic 1-form" — IS Serre duality for `H^{0,1}`, and post-keystone its deep half is
free.  This file extracts that half:

* `exists_serreDualityData_chartDiskCover` (**S1**) — the unconditional ∃-cover keystone
  (`KeystonePackaging.exists_serreDualityData_cover`) strengthened to exhibit a
  **ChartDiskCover**: both legs of the genus split already produce one (the canonical
  cover at `g = 0`, the separating refinement at `g > 0`); only the existential's type
  erased it.  A chart-disk cover is what the Dolbeault comparison consumes.
* `h1Dim_zero_eq_kirovGenus_chartDiskCover` (**S2**) — `h¹(𝒪) = g` at that cover
  (`SerreDualityData.arithmeticGenus` re-read; E3a of the Abel route, no fresh content).
* `finiteDimensional_dolbeaultH01`, `finrank_real_dolbeaultH01_eq_two_mul_kirovGenus`
  (**S3**) — the intrinsic payoff: `dim_ℝ H^{0,1}_∂̄(X) = 2·g`, by transporting S2 across
  `comparison_linearEquiv`.  This is the dimension count the ∂̄-engine's kill step rests
  on.
* `mem_dbarImage_of_periodFunctional` (**S4**) — the ABSTRACT solvability criterion: any
  ℝ-linear period functional `Λ : A^{0,1} → (Fin g → ℂ)` that kills `im ∂̄` and is
  surjective has `ker Λ = im ∂̄`; in particular `Λ σ = 0` makes `∂̄u = σ` solvable.
  (Descend `Λ` to `DolbeaultH01`, then S3 + `finrank (Fin g → ℂ) = 2g` + the
  injective-iff-surjective finrank argument.)  The P-block instantiates `Λ` by the
  PoU-planar pairing `σ ↦ (∫_X σ∧ωᵢ)ᵢ` (`FineResidue.resIntegral`); the Stokes kill and
  the Gram-positivity surjectivity are exactly its two hypotheses.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §19.10, §20; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI, X §2.
-/

noncomputable section

open Complex Module
open scoped Manifold ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## S1 — the keystone at an exhibited chart-disk cover -/

/-- **S1: the unconditional keystone, chart-disk form.**  A **chart-disk** Leray +
locally-realizable cover carrying the Forster-§17 Serre-duality data exists on every
compact connected Riemann surface.  Same proof as
`exists_serreDualityData_cover_of_genus_split_residueAtom` + the T-lane atom — both genus
legs of the split already exhibit a `ChartDiskCover`; this re-statement just keeps the
fact in the type, so the Dolbeault comparison (`comparison_linearEquiv`, stated over
`ChartDiskCover`) can consume the same cover. -/
theorem exists_serreDualityData_chartDiskCover :
    ∃ 𝔇 : ChartDiskCover X, 𝔇.toFiniteCover.IsLeray ∧ 𝔇.toFiniteCover.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔇.toFiniteCover) := by
  obtain ⟨data, hres⟩ := exists_canonicalData_residueAtom (X := X)
  rcases Nat.eq_zero_or_pos (kirovGenus X) with hg0 | hgpos
  · exact ⟨chartDiskCover (X := X), ChartDiskCover.isLeray _,
      ChartDiskCover.locallyRealizable _,
      exists_serreDualityData_of_genus_zero_of_residueAtom _
        (ChartDiskCover.locallyRealizable _) data hres hg0⟩
  · obtain ⟨𝔇, ρ, href, hL, hR, ω₀, K, hω, hK, G, hreg⟩ :=
      exists_separating_unwindRegularity (chartDiskCover (X := X)).toFiniteCover hgpos
    exact ⟨𝔇, hL, hR,
      exists_serreDualityData_genus_split_of_tailRR 𝔇.toFiniteCover hR
        (tailRiemannRoch_of_kirovGenus_pos hgpos) (fun _ => ⟨ω₀, K, hω, hK, G, hreg⟩)⟩

/-! ## S2 — `h¹(𝒪) = g` at the exhibited chart-disk cover -/

/-- **S2: `h¹(X, 𝒪) = g` at an exhibited chart-disk Leray cover** — the E3a input of the
Abel-⊆ ∂̄-engine, free from the keystone (`SerreDualityData.arithmeticGenus`). -/
theorem h1Dim_zero_eq_kirovGenus_chartDiskCover :
    ∃ 𝔇 : ChartDiskCover X, 𝔇.toFiniteCover.IsLeray ∧
      𝔇.toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X := by
  obtain ⟨𝔇, hL, -, ⟨data⟩⟩ := exists_serreDualityData_chartDiskCover (X := X)
  exact ⟨𝔇, hL, data.arithmeticGenus⟩

/-! ## S3 — `dim_ℝ H^{0,1}(X) = 2·g`, intrinsic -/

/-- `H^{0,1}_∂̄(X)` is finite-dimensional over ℝ: transport `FiniteDimensional ℂ (H¹(𝒪))`
(the keystone data's `finH1` field) across the Dolbeault comparison. -/
theorem finiteDimensional_dolbeaultH01 : FiniteDimensional ℝ (DolbeaultH01 X) := by
  obtain ⟨𝔇, hL, -, ⟨data⟩⟩ := exists_serreDualityData_chartDiskCover (X := X)
  haveI : FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) := data.finH1 0
  haveI : FiniteDimensional ℝ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) :=
    FiniteDimensional.complexToReal _
  exact (comparison_linearEquiv 𝔇 hL).symm.finiteDimensional

/-- **S3: the Dolbeault dimension count** `dim_ℝ H^{0,1}_∂̄(X) = 2·g` — intrinsic (no
cover in the statement): S2 transported across `comparison_linearEquiv`.  This is the
dimension on which the ∂̄-engine's kill step (`mem_dbarImage_of_periodFunctional`)
counts. -/
theorem finrank_real_dolbeaultH01_eq_two_mul_kirovGenus :
    finrank ℝ (DolbeaultH01 X) = 2 * kirovGenus X := by
  obtain ⟨𝔇, hL, -, ⟨data⟩⟩ := exists_serreDualityData_chartDiskCover (X := X)
  rw [cechH1_dolbeault_comparison_proof 𝔇 hL]
  have h : finrank ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) = kirovGenus X :=
    data.arithmeticGenus
  rw [h]

/-! ## S4 — the abstract solvability criterion -/

/-- `dim_ℝ (Fin n → ℂ) = 2·n` (the period-functional target). -/
theorem finrank_real_pi_fin_complex (n : ℕ) : finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype ℝ]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- **S4: the abstract ∂̄-solvability criterion** (Forster 19.10, dimension-count form).
Let `Λ : A^{0,1}(X) →ₗ[ℝ] (Fin g → ℂ)` be a period functional that

* kills the image of `∂̄` (`hker` — the Stokes input, P4 of the route), and
* is surjective (`hsurj` — the Gram-positivity input, P5 of the route).

Then every `(0,1)`-form annihilated by `Λ` is `∂̄`-exact: `Λ σ = 0 → ∃ u, ∂̄u = σ`.

Proof: `Λ` descends to `Λ̄ : H^{0,1} → (Fin g → ℂ)`, an ℝ-linear surjection between
spaces of equal finite dimension `2g` (S3 and `finrank_real_pi_fin_complex`), hence
injective; so `[σ] = 0` in `H^{0,1}`, i.e. `σ ∈ im ∂̄`. -/
theorem mem_dbarImage_of_periodFunctional
    (Λ : ↥(OneFormsZeroOne X) →ₗ[ℝ] (Fin (kirovGenus X) → ℂ))
    (hker : ∀ u : SmoothCFunctions X, Λ ⟨dbarL u, dbarL_mem_zeroOne u⟩ = 0)
    (hsurj : Function.Surjective Λ)
    (σ : ↥(OneFormsZeroOne X)) (hσ : Λ σ = 0) :
    ∃ u : SmoothCFunctions X, dbarL u = (σ : SmoothCOneForms X) := by
  -- `im ∂̄ ⊆ ker Λ`, so `Λ` descends to the Dolbeault quotient.
  have hle : dbarImageInZeroOne X ≤ LinearMap.ker Λ := by
    intro τ hτ
    obtain ⟨u, hu⟩ : (τ : SmoothCOneForms X) ∈ LinearMap.range (dbarL (X := X)) := hτ
    have hτu : τ = ⟨dbarL u, dbarL_mem_zeroOne u⟩ := Subtype.ext hu.symm
    rw [LinearMap.mem_ker, hτu]
    exact hker u
  set Λbar : DolbeaultH01 X →ₗ[ℝ] (Fin (kirovGenus X) → ℂ) :=
    (dbarImageInZeroOne X).liftQ Λ hle with hΛbar
  -- `Λ̄` is surjective (factors `Λ`), between spaces of equal finite dimension `2g`.
  have hbar_surj : Function.Surjective Λbar := by
    intro w
    obtain ⟨τ, hτ⟩ := hsurj w
    exact ⟨Submodule.Quotient.mk τ, by rwa [hΛbar, Submodule.liftQ_apply]⟩
  haveI : FiniteDimensional ℝ (DolbeaultH01 X) := finiteDimensional_dolbeaultH01
  have hdim : finrank ℝ (DolbeaultH01 X) = finrank ℝ (Fin (kirovGenus X) → ℂ) := by
    rw [finrank_real_dolbeaultH01_eq_two_mul_kirovGenus, finrank_real_pi_fin_complex]
  have hbar_inj : Function.Injective Λbar :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hbar_surj
  -- `Λ̄ [σ] = Λ σ = 0 = Λ̄ 0`, so `[σ] = 0`, i.e. `σ ∈ im ∂̄`.
  have hzero : (Submodule.Quotient.mk σ : DolbeaultH01 X) = 0 := by
    apply hbar_inj
    rw [hΛbar, Submodule.liftQ_apply, hσ, map_zero]
  have hmem : σ ∈ dbarImageInZeroOne X := (Submodule.Quotient.mk_eq_zero _).mp hzero
  obtain ⟨u, hu⟩ : (σ : SmoothCOneForms X) ∈ LinearMap.range (dbarL (X := X)) := hmem
  exact ⟨u, hu⟩

end Dolbeault

end Jacobians

end
