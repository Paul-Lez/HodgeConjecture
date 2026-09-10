/-
  Dolbeault ladder — the Čech finiteness ASSEMBLY (the 14.7 route, D = 0).

  Combines the two now-proven structural pieces with the analytic Montel finiteness:
    * **Forster 12.4** (`refineH1_injective_unconditional`, `CechRefinementInjective`): refinement maps
      on `H¹` are injective UNCONDITIONALLY (germ-class `𝒪_D` sheaf-gluing).
    * **chart-disk refinement existence** (`exists_chartDiskCover_refinement`, `ChartDiskRefinement`):
      every finite cover is refined by a `ChartDiskCover` (ball sets).
    * **Montel finiteness** (`ChartDiskCover.finiteDimensional_cechH1_chartDisk_complete`,
      `ChartDiskFinitenessComplete.lean`): `cechH1 𝔇 0` is finite-dimensional for a
      `ChartDiskCover 𝔇` — the analytic heart (Forster 14.6/14.7), complete and axiom-clean.

  Given the Montel finiteness, finiteness for an ARBITRARY cover follows by the injection
  `cechH1 𝔘 0 ↪ cechH1 𝔇 0` (12.4) into the finite-dimensional `cechH1 𝔇 0` — NO cover-independence
  isomorphism (hence NO Riemann mapping) is needed.  This is the key to the 14.7 route.

  The Montel finiteness is taken in the assembly lemmas as an explicit HYPOTHESIS `hMontel` (so they
  are parametric in the analytic input); the wiring below discharges `hMontel` with that theorem.
-/
import KirovDolbeault.Dolbeault.CechRefinementInjective
import KirovDolbeault.Dolbeault.ChartDiskRefinement
import KirovDolbeault.Dolbeault.CechModelArtificial
import KirovDolbeault.Dolbeault.ChartDiskFinitenessComplete

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Finiteness of `H¹(𝔘, 𝒪_D)` for an arbitrary finite cover, from the chart-disk Montel finiteness
(any divisor `D`).** `cechH1 𝔘 D ↪ cechH1 𝔇 D` (Forster 12.4 injectivity along a chart-disk refinement
`𝔇 ⪯ 𝔘`, which is UNCONDITIONAL in `D`) injects into the finite-dimensional `cechH1 𝔇 D`; a linear
injection into a finite-dimensional space has a finite-dimensional domain.  No cover-independence
isomorphism is used.  The proof is `D`-agnostic — `D` enters only through the Montel hypothesis. -/
theorem finiteDimensional_cechH1_of_chartDiskMontel (D : Divisor X)
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 D))
    (𝔘 : FiniteCover X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  obtain ⟨𝔇, r, hr⟩ := exists_chartDiskCover_refinement 𝔘
  haveI : FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 D) := hMontel 𝔇
  have hinj : Function.Injective (hr.refineH1 D) :=
    FiniteCover.IsRefinement.refineH1_injective_unconditional (D := D) hr
  exact FiniteDimensional.of_injective _ hinj

/-- **`exists_cechModel 𝔘 D` from the chart-disk Montel finiteness (the 14.7 route, any divisor `D`).**
Combines the arbitrary-cover finiteness above with the artificial single-point model
(`exists_cechModel_of_finiteDimensional`).  This discharges `CechFinitenessWiring.exists_cechModel 𝔘 D`
for every finite cover `𝔘`, modulo only the Montel hypothesis `hMontel`. -/
theorem exists_cechModel_of_chartDiskMontel (D : Divisor X)
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 D))
    (𝔘 : FiniteCover X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  haveI : FiniteDimensional ℂ (𝔘.cechH1 D) :=
    finiteDimensional_cechH1_of_chartDiskMontel D hMontel 𝔘
  exists_cechModel_of_finiteDimensional 𝔘 D

/-- D = 0 specialization of `finiteDimensional_cechH1_of_chartDiskMontel`. -/
theorem finiteDimensional_cechH1_zero_of_chartDiskMontel
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)))
    (𝔘 : FiniteCover X) :
    FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)) :=
  finiteDimensional_cechH1_of_chartDiskMontel (0 : Divisor X) hMontel 𝔘

/-- D = 0 specialization of `exists_cechModel_of_chartDiskMontel`. -/
theorem exists_cechModel_zero_of_chartDiskMontel
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)))
    (𝔘 : FiniteCover X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔘.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel_of_chartDiskMontel (0 : Divisor X) hMontel 𝔘

/-- **The chart-disk Montel finiteness, discharged unconditionally** (Forster 14.9, D = 0).  This is
exactly `ChartDiskCover.finiteDimensional_cechH1_chartDisk_complete` — now complete and axiom-clean
(the `leray` field / global Bott–Tu (0,1)-form is proven) — packaged as the `hMontel` hypothesis the
assembly above consumes.  `[Nonempty X]` is supplied by `[ConnectedSpace X]`. -/
theorem chartDiskMontel_zero :
    ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) :=
  fun 𝔇 => 𝔇.finiteDimensional_cechH1_chartDisk_complete

/-- **Finiteness of `H¹(𝔘, 𝒪)` for an arbitrary finite cover (Forster 14.9, D = 0) — UNCONDITIONAL.**
Discharges the Montel hypothesis of `finiteDimensional_cechH1_zero_of_chartDiskMontel` with the proven
`chartDiskMontel_zero`. -/
theorem finiteDimensional_cechH1_zero (𝔘 : FiniteCover X) :
    FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)) :=
  finiteDimensional_cechH1_zero_of_chartDiskMontel chartDiskMontel_zero 𝔘

/-- **`exists_cechModel 𝔘 0` — UNCONDITIONAL (the 14.7 route, D = 0, fully discharged).**  Combines the
arbitrary-cover finiteness `finiteDimensional_cechH1_zero` with the artificial single-point model.  This
is the complete, axiom-clean D = 0 instance of `CechFinitenessWiring.exists_cechModel`. -/
theorem exists_cechModel_zero (𝔘 : FiniteCover X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔘.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel_zero_of_chartDiskMontel chartDiskMontel_zero 𝔘

end Jacobians.Dolbeault
