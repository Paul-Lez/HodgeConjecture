/-
  Dolbeault ladder — the ladder statements (light scaffold).

  The deep analytic content, stated as isolated leaves *about the concrete Čech objects* built in
  `CechComplex` (no `Data`-typeclass relocation). Each is a named classical theorem; the bottom-out
  pass discharges them. Dependency spine:

    exists_riemannRoch_divisor  (RiemannRoch.lean)
      ⟸ cohomological_riemannRoch (χ-additivity) + serre_h1_eq (general Serre) + h0Dim_eq_lDim bridge
           ⟸ finiteDimensional_cechH1 (G3b finiteness)
      ⟸ arithmeticGenus_eq_genus (Serre at D=0)

  Leaf taxonomy:
    * `finiteDimensional_cechH1` — G3b finiteness (Forster 14.9): disk-Montel + Schwartz/Riesz–Schauder.
    * `cohomological_riemannRoch` — χ-additivity (Forster 16.x): skyscraper SES + LES + Liouville `h⁰(0)=1`.
    * `arithmeticGenus_eq_genus`  — Serre duality at `D=0` (the Dolbeault nugget `H¹(𝒪)≅Ω(X)^*`).
    * `serre_h1_eq`               — general Serre duality `h¹(D) = l(K−D)` (residue pairing perfectness).
    * `h0Dim_eq_lDim`             — bridge: Čech global `𝒪_D`-sections = the linear system `L(D)`.

  All five are unproved obligations here; the first three are the genuine analytic wall, the last two are the
  remaining (Serre / bookkeeping) pieces for wiring to `exists_riemannRoch_divisor`.
-/
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.Dolbeault.SerreDualityPairing
import KirovDolbeault.Dolbeault.CechFinitenessWiring

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **G3b — finiteness (Forster Thm 14.9).** `H¹(𝔘, 𝒪_D)` is finite-dimensional. Engine: the cochain
restriction between a cover and a relatively-compact shrinking is *compact* (disk-Montel: Mathlib
`Analysis.Complex.LocallyUniformLimit` + Arzelà–Ascoli), and a compact perturbation has finite-codim
image (Schwartz / Riesz–Schauder, via Mathlib `IsCompactOperator` + `RieszLemma`). **Deep analytic
leaf.** -/
theorem finiteDimensional_cechH1 (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  finiteDimensional_cechH1_wired 𝔘 D

/- **Cohomological Riemann–Roch (χ-additivity, Forster §16)** is now PROVEN in `CohomologicalRR.lean`
(imported above) modulo the single isolated kernel `exists_skyscraperLES` (the skyscraper-SES connecting
map + `skyDim=1`); base `h⁰(0)=1` + divisor induction + the 6-term alternating-sum crank are axiom-clean.
So `cohomological_riemannRoch` is in scope here via the import — no longer an unproved leaf of this file. -/

/- The former ∀-cover wrappers `arithmeticGenus_eq_genus`, `serre_h1_eq`, and
`riemannRoch_equality_of_ladder` lived here, routed through the ∀-cover keystone sorry
`exists_serreDualityData` (`SerreDualityPairing.lean`). The keystone flip replaced that
sorry by the PROVEN ∃-cover keystone (`KeystonePackaging.exists_serreDualityData_cover`),
so the ladder composition is now data-parametrized: the consumer takes the cover and
`SerreDualityData` EXHIBITED by the keystone. -/

/- **Bridge: Čech global sections = the linear system** (`h⁰(𝔘, 𝒪_D) = l(D)`). PROVEN in
`CechH0` (`FiniteCover.h0Dim_eq_lDim`) modulo the single gluing/surjectivity gap
(`cechRestrictL_surjective`) — no longer a leaf of this file. -/

/-- **The ladder composes** (complete; no new content). Given `SerreDualityData` on a
locally-realizable cover `𝔘`, the canonical divisor `data.K` satisfies the classical
Riemann–Roch equality `l(D) − l(K−D) = deg D + 1 − g` for every `D`. It falls out of the
ladder by substitution: cohomological RR + the `h⁰ = l` bridge + general Serre
`h¹(D)=l(K−D)` (`data.serre_eq`) + Serre-at-0 `h¹(0)=g` (`data.arithmeticGenus`). The
data is EXHIBITED, cover included, by the unconditional ∃-cover keystone
`KeystonePackaging.exists_serreDualityData_cover`. -/
theorem riemannRoch_equality_of_data (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (data : SerreDualityData 𝔘) :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim D : ℤ) - lDim (K - D) = Divisor.deg X D + 1 - kirovGenus X := by
  refine ⟨data.K, fun D => ?_⟩
  have h := cohomological_riemannRoch 𝔘 hR D
  rw [𝔘.h0Dim_eq_lDim D, data.serre_eq D, data.arithmeticGenus] at h
  exact h

end Jacobians.Dolbeault
