/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.DescentVanish
import KirovDolbeault.Dolbeault.CanonicalFormDifferential

/-!
# R7c — the `SlotMatchesK` witness: `ω₀`'s chart coefficients match `K = div ω₀`

`DescentVanish.SlotMatchesK 𝔇 g K` demands that at every K-point `a` (where `0 < K a`) and
every cover chart containing it, the `dz`-slot `g j₀` factor as `(ζ − α)^{K a} · u` with `u`
analytic — the slot zero that cancels the `𝒪_K` scalar pole in the product-germ trick.  For
the canonical-form slot `g = omegaCoeff 𝔇 ω₀` with `K = div ω₀` this is *the definition* of
the divisor of a holomorphic form, transported through charts:

* `formOrderW_chart_invariant` reads the form order at `a` as the `meromorphicOrderAt` of the
  chart-`j₀` coefficient at `chartMap 𝔇 j₀ a`;
* `formCoeff_holToSection` identifies that coefficient with `coeffAt α (𝔇.center j₀)
  = omegaCoeff 𝔇 α j₀`;
* the coefficient is **analytic** there (`coeffAt_analyticAt`), so its meromorphic order is its
  analytic order (`AnalyticAt.meromorphicOrderAt_eq`), and the Mathlib factorization
  `AnalyticAt.analyticOrderAt_eq_natCast` produces exactly the `(ζ − α)^{(K a).toNat} · u` shape
  `SlotMatchesK` asks for (`Int.toNat` collapses nothing since `0 < K a`).

The divisor hypothesis is consumed in the output shape of `exists_form_divisor`
(`CanonicalFormDifferential`): `∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)`.

## Main declarations

* `slotMatchesK_omegaCoeff` — **the witness**: `SlotMatchesK 𝔇 (omegaCoeff 𝔇 α) K` whenever
  `K` is the form divisor of `α`.
* `resH1_omegaCoeff` / `cousinResidueData_omegaCoeff` — the unconditional descent and the
  Cousin assembly for the canonical-form slot: every analytic hypothesis of the R-lane descent
  is now discharged for `g = omegaCoeff 𝔇 α`; only `SeparatesPoles` (cover geometry) and
  `CupMLWitnessR` (§17.6 transport) remain.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.3–17.4.
-/

open Complex Filter
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-- **The `SlotMatchesK` witness for the canonical-form slot**: if `K` is the form divisor of
the global holomorphic 1-form `α` (the `exists_form_divisor` output shape,
`∀ x, formOrderW x = K x`), then the chart-coefficient family `omegaCoeff 𝔇 α` vanishes to
order `K a` at every K-point in every cover chart containing it — the
`(ζ − α)^{K a} · (analytic)` factorization `DescentVanish` consumes. -/
theorem slotMatchesK_omegaCoeff (α : HolomorphicOneForms X) {K : Divisor X}
    (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)) :
    SlotMatchesK 𝔇 (omegaCoeff 𝔇 α) K := by
  intro a haK j₀ haU
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 haU
  have htgt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have han : AnalyticAt ℂ (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) :=
    coeffAt_analyticAt α (𝔇.center j₀) htgt
  -- the meromorphic order of the chart coefficient at the K-point is `K a`
  have hmero : meromorphicOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a)
      = (K a : WithTop ℤ) := by
    have h := formOrderW_chart_invariant (holToMero α) (𝔇.center j₀) a hsrc
    rw [hK a] at h
    have hcoeff : formCoeff (holToMero α).toFun (𝔇.center j₀) = coeffAt α (𝔇.center j₀) :=
      formCoeff_holToSection α (𝔇.center j₀)
    rw [hcoeff] at h
    exact h.symm
  -- hence the analytic order is the natural number `(K a).toNat`
  have hord : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a)
      = ((K a).toNat : ℕ∞) := by
    rw [han.meromorphicOrderAt_eq] at hmero
    cases hcase : analyticOrderAt (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) with
    | top =>
      rw [hcase, ENat.map_top] at hmero
      exact absurd hmero.symm (WithTop.coe_ne_top)
    | coe n =>
      rw [hcase, ENat.map_coe] at hmero
      have hn : (n : ℤ) = K a := WithTop.coe_inj.mp hmero
      rw [show (K a).toNat = n by rw [← hn]; exact Int.toNat_natCast n]
  -- Mathlib's analytic-order factorization is exactly the `SlotMatchesK` shape
  obtain ⟨u, hu_an, _, hfac⟩ := han.analyticOrderAt_eq_natCast.mp hord
  refine ⟨u, hu_an, ?_⟩
  filter_upwards [hfac] with ζ hζ
  simpa [smul_eq_mul] using hζ

variable {𝔇}

/-- **The unconditional residue descent for the canonical-form slot**: with `K = div α` the
full analytic side of the R-lane descent is discharged — `IsOneZeroCoeff` by the R4 witness,
`SlotMatchesK` by `slotMatchesK_omegaCoeff` — leaving only the cover geometry
(`SeparatesPoles`). -/
noncomputable def resH1_omegaCoeff {K : Divisor X} (hsep : SeparatesPoles 𝔇 K)
    (α : HolomorphicOneForms X) (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)) :
    𝔇.toFiniteCover.toFiniteFamily.cechH1 K →ₗ[ℂ] ℂ :=
  resH1_of_slotMatches hsep (omegaCoeff 𝔇 α) (isOneZeroCoeff_omegaCoeff 𝔇 α)
    (slotMatchesK_omegaCoeff 𝔇 α hK)

/-- **`CousinResidueData` for the canonical-form slot from the §17.6 witness alone**: the
preferred R7 assembly specialized to `g = omegaCoeff 𝔇 α`, `K = div α`.  Every analytic leg is
proven; `SeparatesPoles` (cover geometry) and `CupMLWitnessR` (§17.6 transport) are the only
remaining hypotheses. -/
noncomputable def cousinResidueData_omegaCoeff {K : Divisor X} (hsep : SeparatesPoles 𝔇 K)
    (α : HolomorphicOneForms X) (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ))
    (hwit : CupMLWitnessR 𝔇 hsep (omegaCoeff 𝔇 α)) :
    CousinResidueData 𝔇.toFiniteCover K :=
  cousinResidueData_of_witnessR hsep (omegaCoeff 𝔇 α) (isOneZeroCoeff_omegaCoeff 𝔇 α)
    (slotMatchesK_omegaCoeff 𝔇 α hK) hwit

end Jacobians.Dolbeault.FineResidue
