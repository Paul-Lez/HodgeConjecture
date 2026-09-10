/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.CechH1CupKill
import KirovDolbeault.Dolbeault.ArithmeticGenusTransfer
import KirovDolbeault.Dolbeault.ChartDiskCoverGeneric
import KirovDolbeault.Dolbeault.SerreDualityGenus0
import KirovDolbeault.Genus

/-!
# The uniform `h¹(𝒪) = g` by subtracting the two Riemann–Rochs (rung 3, steps 2–3)

The Miranda-route genus identity (idea: Kirov `CechH1Genus.h1Dim_zero_eq_genus`,
`docs/planning/KIROV_ROUTE_IDEAS.md` item 4; implementation ours): at a large effective `A`
where the cup-kill makes `H¹(𝒪_A) = 0` (`CechH1CupKill.lean`, proven), compare

* **cohomological RR** (proven, `cohomological_riemannRoch`):  `l(A) = deg A + 1 − h¹(𝒪)`;
* **Laurent-tail RR** (the `TailRiemannRoch` input below — the single remaining analytic
  input of the rung, supplied by the item-3 tail tower; `docs/planning/TAIL_BLOCKER.md`):
  `l(A) = deg A + 1 − g` for effective `A` of degree `> 2g − 2`, `g := kirovGenus X`;

and subtract: `h¹(𝒪) = g`, **uniformly in the genus** — no Hodge theory, no Dolbeault
vanishing, no uniformization.  At `g = 0` this is exactly the `hga` atom
(`G0_BLOCKER.md` / `SerreDualityGenus0.lean` input), and at the canonical chart-disk cover it
is the exact port-side fact the Layer-3 flip of `h1coh_zero_finrank`
(`Jacobians/Layer3/Cohomology.lean`, axiom at the `CechH1Bridge` cover pin
`chartDiskCover X`) will consume.

## Statements

* `TailRiemannRoch X` — the isolated tail-RR input (Miranda VI.3.11 RR + the
  degree-vanishing of `h¹_tail`; NOT proven here — see `docs/planning/TAIL_BLOCKER.md`).
* `h1Dim_zero_eq_kirovGenus_of_tailRR` — `h¹(𝒪) = kirovGenus X` at ANY locally realizable
  finite cover, conditional on `TailRiemannRoch X` only.
* `h1Dim_zero_eq_zero_of_kirovGenus_zero` — the `hga` shape `h¹(𝒪) = 0` at `kirovGenus X = 0`.
* `h1Dim_zero_chartDiskCover_eq_kirovGenus` — the canonical-cover normal form (the Layer-3
  flip target), and `h1Dim_zero_anyChartDiskCover_eq_kirovGenus` for every chart-disk cover
  via the `IsLeray`-free transfer (`ArithmeticGenusTransfer.lean`).

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI; Prop. X.2.6
(GAGA-free `h¹ = g`); Forster (GTM 81) §§16–17.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

/-- **The Laurent-tail Riemann–Roch input** (Miranda Ch. VI; the single remaining analytic
input of rung 3 — the item-3 tail tower's output): for every effective divisor `A` of degree
`> 2g − 2` (`g := kirovGenus X`), the junk-free linear-system dimension is
`l(A) = deg A + 1 − g`.

This is full RR in the large-degree range, where the tail-`h¹` correction term vanishes
(tail Serre duality `h¹_tail(A) = l(K − A)` plus `deg(K − A) < 0`).  Discharge plan:
`docs/planning/TAIL_BLOCKER.md`. -/
def TailRiemannRoch (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ A : Divisor X, (∀ x, (0 : Divisor X) x ≤ A x) →
    2 * (kirovGenus X : ℤ) - 2 < Divisor.deg X A →
    (lDim (X := X) A : ℤ) = Divisor.deg X A + 1 - kirovGenus X

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The uniform genus identity `h¹(𝒪) = g`** at any locally realizable finite cover,
conditional on the tail-RR input only: pick the cup-kill level `A₀` (`H¹(𝒪_A) = 0` for all
`A ≥ A₀`, proven), enlarge by `(2g+1)·P` to push the degree past `2g − 2`, and subtract the
two Riemann–Rochs at `A`. -/
theorem h1Dim_zero_eq_kirovGenus_of_tailRR (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (htail : TailRiemannRoch X) : 𝔘.h1Dim (0 : Divisor X) = kirovGenus X := by
  classical
  obtain ⟨A₀, hA₀eff, hkill⟩ := exists_effective_h1Dim_eq_zero_forall_ge 𝔘 hR
  obtain ⟨P⟩ : Nonempty X := inferInstance
  set m : ℤ := 2 * (kirovGenus X : ℤ) + 1 with hm
  set A : Divisor X := A₀ + Finsupp.single P m with hA
  have hA₀A : ∀ x, A₀ x ≤ A x := by
    intro x
    rw [hA, Finsupp.add_apply, Finsupp.single_apply]
    split <;> omega
  have hAeff : ∀ x, (0 : Divisor X) x ≤ A x := fun x => le_trans (hA₀eff x) (hA₀A x)
  have hdegA : Divisor.deg X A = Divisor.deg X A₀ + m := by
    rw [hA, Divisor.deg_add, Divisor.deg_single]
  have hdeg0 : 0 ≤ Divisor.deg X A₀ := deg_nonneg_of_effective hA₀eff
  have hbig : 2 * (kirovGenus X : ℤ) - 2 < Divisor.deg X A := by omega
  have h1A : 𝔘.h1Dim A = 0 := hkill A hA₀A
  have hRR := cohomological_riemannRoch 𝔘 hR A
  have htailA := htail A hAeff hbig
  rw [𝔘.h0Dim_eq_lDim A, h1A] at hRR
  omega

/-- **The `hga` shape**: `h¹(𝒪) = 0` at `kirovGenus X = 0` — the genus-0 arithmetic atom
(`G0_BLOCKER.md`; input of `SerreDualityGenus0.lean`), conditional on the tail-RR input. -/
theorem h1Dim_zero_eq_zero_of_kirovGenus_zero (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (htail : TailRiemannRoch X) (hg : kirovGenus X = 0) :
    𝔘.h1Dim (0 : Divisor X) = 0 := by
  rw [h1Dim_zero_eq_kirovGenus_of_tailRR 𝔘 hR htail, hg]

/-- **The canonical-cover normal form** — the exact port-side fact the Layer-3 flip of the
`h1coh_zero_finrank` axiom will consume (`Jacobians/Layer3/Cohomology.lean` at the
`CechH1Bridge` cover pin `chartDiskCover X`), conditional on the tail-RR input. -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus (htail : TailRiemannRoch X) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_eq_kirovGenus_of_tailRR _ (chartDiskCover (X := X)).locallyRealizable htail

/-- Every chart-disk cover computes `h¹(𝒪) = g` (the `IsLeray`-free invariance transfer of
`ArithmeticGenusTransfer.lean` composed with the canonical normal form). -/
theorem h1Dim_zero_anyChartDiskCover_eq_kirovGenus (𝔇 : ChartDiskCover X)
    (htail : TailRiemannRoch X) :
    𝔇.toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X :=
  (h1Dim_zero_eq_canonical 𝔇).trans (h1Dim_zero_chartDiskCover_eq_kirovGenus htail)

/-! ## Keystone collapse: the `g = 0` leg and the genus split under the tail-RR input -/

/-- **The keystone's `g = 0` leg under the tail-RR input**: `exists_serreDualityData` at
`kirovGenus X = 0` with the scalar atom `hga` discharged by the rung-3 subtraction —
the `hga` hypothesis of `exists_serreDualityData_of_arithmeticGenus_zero` is gone. -/
theorem exists_serreDualityData_of_genus_zero_of_tailRR (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (htail : TailRiemannRoch X) (hg0 : kirovGenus X = 0) :
    Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_of_arithmeticGenus_zero 𝔘 hR hg0
    (h1Dim_zero_eq_zero_of_kirovGenus_zero 𝔘 hR htail hg0)

/-- **The keystone genus split with the `g = 0` leg fully discharged**: under the tail-RR
input, `exists_serreDualityData` needs only the lane-R `g ≥ 1` provision `hpos` — the
`hga` scalar atom of `exists_serreDualityData_genus_split_arithmetic` is supplied by
rung 3.  (And `hpos`'s `UnwindRegularity ∀ D` is exactly what rung 4 re-points at the
Čech↔tail comparison, `TailUnwind.lean`.) -/
theorem exists_serreDualityData_genus_split_of_tailRR (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (htail : TailRiemannRoch X)
    (hpos : 0 < kirovGenus X →
      ∃ (ω₀ : HolomorphicOneForms X) (K : Divisor X), ω₀ ≠ 0 ∧
        (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
        ∃ G : GlobalResidue 𝔘 K, ∀ D : Divisor X, G.UnwindRegularity D) :
    Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_genus_split_arithmetic 𝔘 hR hpos
    (fun hg0 => h1Dim_zero_eq_zero_of_kirovGenus_zero 𝔘 hR htail hg0)

end Dolbeault

end Jacobians

end
