/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.GoodCover
import KirovDolbeault.Dolbeault.LerayCoverExists

/-!
# The arithmetic-genus atom is cover-free: `h¹(𝒪)` transfer via the Dolbeault comparison

The `g = 0` keystone leg (`SerreDualityGenus0`) is reduced to the single scalar atom
`hga : 𝔘.h1Dim 0 = 0` — but stated at a *given* cover `𝔘`, while the keystone's ∃-cover
weakening and the R-lane capstone (`exists_separating_cousinResidueData`) each choose their
*own* chart-disk cover.  This file removes the cover dependence:

The `IsLeray`-free Čech↔Dolbeault comparison (`GoodCover.cechH1_dolbeault_comparison'`)
pins `finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔇 0)` for EVERY chart-disk cover
`𝔇` — the left side is cover-free, so `h¹(𝔇, 𝒪) = h¹(𝔇', 𝒪)` for any two chart-disk covers
(`h1Dim_zero_chartDiskCover_invariant`), and the atom proven at ANY one of them (e.g. the
canonical `chartDiskCover`) feeds ALL of them (`hga_transfer` /
`h1Dim_zero_eq_canonical`).

**What this file does NOT do**: prove the atom itself.  `h1Dim 0 = 0` at `kirovGenus X = 0`
remains the genuine analytic wall (`G0_BLOCKER.md`: needs `H^{0,1} = 0` from the absence of
holomorphic 1-forms — Hodge-flavoured — or the meromorphic-`ω₀'` residue route).  What is
banked is that the wall need only be climbed ONCE, at whichever cover is most convenient.

## Main declarations

* `h1Dim_zero_chartDiskCover_invariant` — `h¹(𝒪)` agrees on all chart-disk covers.
* `hga_transfer` — the genus-0 atom transfers between chart-disk covers.
* `h1Dim_zero_eq_canonical` — every chart-disk cover's `h¹(𝒪)` equals the canonical one's.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §15.14, §19; `G0_BLOCKER.md`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`h¹(𝒪)` is the same on every chart-disk cover**: both equal half the (cover-free)
real dimension of `DolbeaultH01 X`, by the `IsLeray`-free comparison
(`cechH1_dolbeault_comparison'`). -/
theorem h1Dim_zero_chartDiskCover_invariant (𝔇₁ 𝔇₂ : ChartDiskCover X) :
    𝔇₁.toFiniteCover.h1Dim 0 = 𝔇₂.toFiniteCover.h1Dim 0 := by
  have h1 := cechH1_dolbeault_comparison' 𝔇₁
  have h2 := cechH1_dolbeault_comparison' 𝔇₂
  have e1 : 𝔇₁.toFiniteCover.h1Dim 0
      = Module.finrank ℂ (𝔇₁.toFiniteCover.cechH1 0) := rfl
  have e2 : 𝔇₂.toFiniteCover.h1Dim 0
      = Module.finrank ℂ (𝔇₂.toFiniteCover.cechH1 0) := rfl
  omega

/-- **The genus-0 arithmetic atom transfers between chart-disk covers**: `hga` proven at any
one chart-disk cover (e.g. the canonical `chartDiskCover`) feeds every other — in particular
the separating cover of the R-lane capstone. -/
theorem hga_transfer {𝔇₁ 𝔇₂ : ChartDiskCover X} (h : 𝔇₁.toFiniteCover.h1Dim 0 = 0) :
    𝔇₂.toFiniteCover.h1Dim 0 = 0 :=
  (h1Dim_zero_chartDiskCover_invariant 𝔇₂ 𝔇₁).trans h

/-- Every chart-disk cover's `h¹(𝒪)` equals the canonical cover's — the canonical normal form
of the cover-free atom. -/
theorem h1Dim_zero_eq_canonical (𝔇 : ChartDiskCover X) :
    𝔇.toFiniteCover.h1Dim 0 = (chartDiskCover (X := X)).toFiniteCover.h1Dim 0 :=
  h1Dim_zero_chartDiskCover_invariant 𝔇 (chartDiskCover (X := X))

end Jacobians.Dolbeault
