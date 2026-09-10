/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailGenusTarget
import KirovDolbeault.Dolbeault.TailFrameGenus0
import KirovDolbeault.Dolbeault.TailDictionaryFull
import KirovDolbeault.Dolbeault.FineResidue.CupWitness
import KirovDolbeault.Dolbeault.ChartDiskCoverGeneric
import KirovDolbeault.Dolbeault.FrameTrace

/-!
# Keystone packaging: `exists_serreDualityData` (∃-cover) from the residue atom alone

The P-lane capstone (`docs/planning/P_LANE_PROGRESS.log`): everything between the single
remaining analytic input — the meromorphic-frame residue atom
`CanonicalForm17Data.ResidueAtom` (`TailFrameGenus0.lean`, A-lane) — and the keystone
`exists_serreDualityData` is packaged here, so the final flip is a tiny PR.

## Cover quantification of the keystone

The keystone sorry (`SerreDualityPairing.lean`, `exists_serreDualityData`) is stated
∀-cover (`(𝔘) (hL) (hR) → Nonempty (SerreDualityData 𝔘)`), but its unique top-level
consumer CHOOSES the cover (`RiemannRoch.exists_riemannRoch_divisor` via
`exists_realizableLerayCover`; census in `docs/planning/COVER_WIRING.md`).  The agreed
flip weakens the keystone to the honest **∃-cover form** produced here —

  `∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧ Nonempty (SerreDualityData 𝔘)`

— landing the consumer's one-line re-pin in the same commit.

## The two P1 closures and the assembly

* `slotExactK_omegaCoeff` — **P1a**: the exact-order slot hypothesis `SlotExactK` holds
  for the canonical-form slot `omegaCoeff 𝔇 α` with `K = div α`, at EVERY point of every
  chart: the chart coefficient is analytic of meromorphic order exactly `K a`
  (`formOrderW_chart_invariant` + `formCoeff_holToSection`), and Mathlib's analytic-order
  factorization supplies the `(ζ−α)^{K a}·(unit)` shape with NONVANISHING unit.
  Strengthens `slotMatchesK_omegaCoeff` (`FineResidue/SlotMatch.lean`).
* `ChartDiskCover.exactOrderWitness` — every chart-disk cover carries the exact-order
  Mittag-Leffler witness (`ChartDiskCoverGeneric.exists_orderExact_witness`, repackaged
  in the `ExactOrderWitness` shape the W-engine consumes).
* `exists_separating_unwindRegularity` — **P1b, the `hpos` packaging**: at
  `0 < kirovGenus X`, a separating chart-disk cover (Leray, locally realizable, refining
  any given cover) carrying the FULL lane-R provision of
  `exists_serreDualityData_genus_split_of_tailRR`: the canonical frame `(ω₀, K)`,
  `ω₀ ≠ 0`, `K = div ω₀`, and a `GlobalResidue` with `UnwindRegularity` at EVERY `D`
  (`unwindRegularity_concrete`, the unconditional §17.7 dictionary engine).
* `exists_serreDualityData_cover_of_genus_split_residueAtom` /
  `exists_serreDualityData_cover_of_residueAtom` — **the conditional keystone capstone**:
  the ∃-cover keystone from the residue atom alone, both genus legs:
  - `g = 0`: `TailFrameGenus0`'s chain (atom → frame → tail-RR → `hga` →
    `SerreDualityGenus0`) at the canonical chart-disk cover;
  - `g > 0`: the PROVEN frame witness (`nonempty_tailPairFrame_of_kirovGenus_pos`) +
    `TailPairFrame.tailRiemannRoch` supply `htail`, and P1a/P1b supply `hpos` at the
    separating cover, through `exists_serreDualityData_genus_split_of_tailRR`.
* `tailRiemannRoch_of_kirovGenus_pos` — the compiled witness that the merged tail tower
  closes at `g > 0` with NO residue atom: frame witness (PR #189) + pairing surjectivity
  (PR #188) ⊢ `TailRiemannRoch X`.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17; Miranda, *Algebraic
Curves and Riemann Surfaces* (GSM 5), Ch. VI.
-/

noncomputable section

open Complex Filter
open scoped Manifold ContDiff Topology Classical

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

open FineResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## P1a — `SlotExactK` for the canonical-form slot -/

/-- **The exact-order slot witness for the canonical-form slot** (P1, codex review of
PR #190): if `K` is the form divisor of the global holomorphic 1-form `α`
(`∀ x, formOrderW x = K x`), then at EVERY point `a` of every cover chart the coefficient
family `omegaCoeff 𝔇 α` factors as `(ζ − α)^{K a} · u` with `u` analytic and
**nonvanishing** at the centre — the meromorphic order of the chart coefficient is exactly
`K a`, so Mathlib's analytic-order factorization yields the unit.  Strengthens
`slotMatchesK_omegaCoeff` from K-points/possibly-vanishing units to all points/units. -/
theorem slotExactK_omegaCoeff (𝔇 : ChartDiskCover X) (α : HolomorphicOneForms X)
    {K : Divisor X} (hK : ∀ x, (holToMero α).formOrderW x = (K x : WithTop ℤ)) :
    SlotExactK 𝔇 (omegaCoeff 𝔇 α) K := by
  intro a j₀ haU
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 haU
  have htgt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have han : AnalyticAt ℂ (coeffAt α (𝔇.center j₀)) (chartMap 𝔇 j₀ a) :=
    coeffAt_analyticAt α (𝔇.center j₀) htgt
  -- the meromorphic order of the chart coefficient at `a` is exactly `K a`
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
  -- Mathlib's analytic-order factorization, KEEPING the nonvanishing unit
  obtain ⟨u, hu_an, hu_ne, hfac⟩ := han.analyticOrderAt_eq_natCast.mp hord
  refine ⟨u, hu_an, hu_ne, ?_⟩
  filter_upwards [hfac] with ζ hζ
  simpa [smul_eq_mul] using hζ

/-! ## The exact-order ML witness on every chart-disk cover -/

/-- **Every chart-disk cover carries the exact-order Mittag-Leffler witness**: the
chart-generic factorized-rational product witness
(`ChartDiskCover.exists_orderExact_witness`), repackaged in the `ExactOrderWitness` shape
consumed by the test-cocycle layers of the W-engine (`SerreUnwindDetect`,
`TailDictionaryFull`).  Generalizes `exactOrderWitness_chartDiskCover` from the canonical
cover to all chart-disk covers. -/
theorem ChartDiskCover.exactOrderWitness (𝔇 : ChartDiskCover X) : ExactOrderWitness 𝔇 := by
  intro D j P hP
  obtain ⟨γ, hmem, hord⟩ := ChartDiskCover.exists_orderExact_witness 𝔇 D j P hP
  exact ⟨γ, hmem, hord⟩

/-! ## P1b — the cover-level `hpos` packaging -/

/-- **The lane-R `g ≥ 1` provision, packaged at an exhibited cover** (the `hpos` input of
`exists_serreDualityData_genus_split_of_tailRR`, with the cover produced rather than
given): at `0 < kirovGenus X` there is a separating chart-disk cover `𝔇` — refining any
prescribed cover `𝔘₀`, Leray, locally realizable — together with the canonical frame
`(ω₀, K)`, `ω₀ ≠ 0`, `K = div ω₀`, and a concrete `GlobalResidue 𝔇.toFiniteCover K`
satisfying `UnwindRegularity` at EVERY level `D`.

Assembly: `exists_separating_cousinResidueData` (cover + `SeparatesPoles` + inhabited
`CupMLWitnessR`) + `slotExactK_omegaCoeff` (P1a) + `ChartDiskCover.exactOrderWitness`
feed `unwindRegularity_concrete` (the unconditional §17.7 dictionary engine, PR #190). -/
theorem exists_separating_unwindRegularity (𝔘₀ : FiniteCover X) (hg : 0 < kirovGenus X) :
    ∃ (𝔇 : ChartDiskCover X) (ρ : 𝔇.ι → 𝔘₀.ι),
      FiniteCover.IsRefinement 𝔇.toFiniteCover 𝔘₀ ρ ∧
      𝔇.toFiniteCover.IsLeray ∧ 𝔇.toFiniteCover.LocallyRealizable ∧
      ∃ (ω₀ : HolomorphicOneForms X) (K : Divisor X), ω₀ ≠ 0 ∧
        (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
        ∃ G : GlobalResidue 𝔇.toFiniteCover K, ∀ D : Divisor X, G.UnwindRegularity D := by
  classical
  -- a nonzero holomorphic 1-form exists at positive genus
  haveI : Nontrivial (HolomorphicOneForms X) := Module.nontrivial_of_finrank_pos hg
  obtain ⟨α, hα⟩ := exists_ne (0 : HolomorphicOneForms X)
  -- its form divisor `K = div α`
  obtain ⟨K, hK⟩ := exists_form_divisor (holToMero α)
    (MeromorphicOneForm.formOrderW_ne_top_of_exists (holToMero α)
      (exists_formOrderW_holToMero_ne_top α hα))
  -- the separating cover with the inhabited §17.6 witness (R-lane capstone)
  obtain ⟨𝔇, ρ, href, hL, hR, hsep, hwit, -⟩ := exists_separating_cousinResidueData 𝔘₀ α hK
  refine ⟨𝔇, ρ, href, hL, hR, α, K, hα, hK,
    (cousinResidueData_of_witnessR hsep (omegaCoeff 𝔇 α) (isOneZeroCoeff_omegaCoeff 𝔇 α)
      (SlotMatchesK_of_exact (slotExactK_omegaCoeff 𝔇 α hK)) hwit).toGlobalResidue,
    fun D => ?_⟩
  exact unwindRegularity_concrete hsep (isOneZeroCoeff_omegaCoeff 𝔇 α)
    (slotExactK_omegaCoeff 𝔇 α hK) hwit (ChartDiskCover.exactOrderWitness 𝔇)
    (formDivisor_nonneg α hK) D

/-! ## The compiled tail-tower closure at `g > 0` (PR #189 + PR #188) -/

/-- **`TailRiemannRoch X` is a THEOREM at positive genus** — the compiled composition of
the tail-pair-frame witness (`nonempty_tailPairFrame_of_kirovGenus_pos`, PR #189) with
the frame-only tail tower (`TailPairFrame.pairingSurjective` →
`TailPairFrame.tailRiemannRoch`, PR #188).  No residue atom, no axiom. -/
theorem tailRiemannRoch_of_kirovGenus_pos (hg : 0 < kirovGenus X) : TailRiemannRoch X :=
  (nonempty_tailPairFrame_of_kirovGenus_pos hg).elim fun P => P.tailRiemannRoch

/-! ## The conditional keystone capstone -/

/-- **The `g > 0` keystone leg, unconditional given tail-RR**: at positive genus, an
exhibited Leray + locally-realizable cover carrying `SerreDualityData` — `htail` feeds the
genus split and P1a/P1b feed its lane-R provision `hpos` at the separating cover. -/
theorem exists_serreDualityData_cover_of_tailRR_of_kirovGenus_pos
    (htail : TailRiemannRoch X) (hg : 0 < kirovGenus X) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) := by
  obtain ⟨𝔇, ρ, href, hL, hR, ω₀, K, hω, hK, G, hreg⟩ :=
    exists_separating_unwindRegularity (chartDiskCover (X := X)).toFiniteCover hg
  exact ⟨𝔇.toFiniteCover, hL, hR,
    exists_serreDualityData_genus_split_of_tailRR 𝔇.toFiniteCover hR htail
      (fun _ => ⟨ω₀, K, hω, hK, G, hreg⟩)⟩

/-- **THE CONDITIONAL KEYSTONE CAPSTONE (genus-split input)** — the ∃-cover keystone
`∃ 𝔘, IsLeray ∧ LocallyRealizable ∧ Nonempty (SerreDualityData 𝔘)` from the residue atom
in the `kirovGenus X = 0` case ONLY (`g > 0` needs no atom: `residueAtom_of_form` makes it
a theorem there).  This is the exact statement the A-lane flip will instantiate:

* `g = 0` — `TailFrameGenus0`'s chain (atom → frame → tail-RR → `hga` → the genus-0
  assembly) at the canonical chart-disk cover;
* `g > 0` — `tailRiemannRoch_of_kirovGenus_pos` (PROVEN) supplies `htail`, and the
  packaged `hpos` (`exists_separating_unwindRegularity`) closes the genus split at the
  separating cover. -/
theorem exists_serreDualityData_cover_of_genus_split_residueAtom
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) := by
  rcases Nat.eq_zero_or_pos (kirovGenus X) with hg0 | hgpos
  · obtain ⟨data, hres⟩ := h0 hg0
    exact ⟨(chartDiskCover (X := X)).toFiniteCover,
      ChartDiskCover.isLeray _, ChartDiskCover.locallyRealizable _,
      exists_serreDualityData_of_genus_zero_of_residueAtom _
        (ChartDiskCover.locallyRealizable _) data hres hg0⟩
  · exact exists_serreDualityData_cover_of_tailRR_of_kirovGenus_pos
      (tailRiemannRoch_of_kirovGenus_pos hgpos) hgpos

/-- **The conditional keystone capstone (single-datum input)** — the work-order shape:
ANY canonical datum satisfying its residue atom yields the ∃-cover keystone, both genus
legs.  (The A-lane discharge of the atom for the canonical datum is the final flip.) -/
theorem exists_serreDualityData_cover_of_residueAtom (data : CanonicalForm17Data X)
    (hres : data.ResidueAtom) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_cover_of_genus_split_residueAtom fun _ => ⟨data, hres⟩

/-! ## THE KEYSTONE, unconditional -/

/-- **THE KEYSTONE, unconditional**: an exhibited Leray + locally-realizable cover carrying
the Forster-§17 Serre-duality data, on EVERY compact connected Riemann surface — the T-lane
frame-trace assembly (`FrameTrace.exists_canonicalData_residueAtom`: the canonical
`ω₀ = df` datum satisfies its own residue atom) fed through the #194 genus split and the
#193 capstone. This replaces the former ∀-cover keystone sorry
(`SerreDualityPairing.exists_serreDualityData`); the sole top-level consumer
(`RiemannRoch.exists_riemannRoch_divisor`) takes the cover exhibited here. -/
theorem exists_serreDualityData_cover :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable ∧
      Nonempty (SerreDualityData 𝔘) := by
  obtain ⟨data, hres⟩ := exists_canonicalData_residueAtom (X := X)
  exact exists_serreDualityData_cover_of_residueAtom data hres

end Dolbeault

end Jacobians

end
