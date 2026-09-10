/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreUnwind
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.Dolbeault.GlobalResidueConstruct

/-!
# Keystone assembly prep — lane A (S1 datum alignment, S9 genus routing, assembly spine)

This file pre-assembles everything of the keystone `exists_serreDualityData`
(`SerreDualityPairing.lean`) that is provable TODAY against the landed interfaces, so that the
final discharge is a near-mechanical instantiation of ONE theorem
(`exists_serreDualityData_genus_split` below).  Per
`docs/planning/KEYSTONE_GAP_ANALYSIS.md` (steps S1/S2/S4/S9) and
`docs/planning/CAMPAIGN_KEYSTONE.md` (lane A), against the merged S5/S6/S7 engines
(`SerreUnwind` / `SerrePsiAction` / `SerreSurjectivitySkeleton`).  The `GlobalResidue`
construction (lane R, R6/R7) is NOT landed: it is consumed **abstractly** here — every theorem
below is parametric in `G : GlobalResidue 𝔘 K` and the §17.7 regularity law
`G.UnwindRegularity` (the two R-lane-gated named hypotheses; NO new interface is introduced).

## The assembly spine (proven, unconditional given the named inputs)

* `GlobalResidue.exists_serreDualityData_of` — from `{G, hR, hKgenus, UnwindRegularity ∀ D}`,
  the keystone conclusion `Nonempty (SerreDualityData 𝔘)`.  `finH1` is discharged by the proven
  `finiteDimensional_cechH1_wired`; `ι_surj` by the landed §17.9 chain
  (`pairing_surjective_of_globalResidue` = S7 count + S6 ψ-action + S5 unwind); `ι_inj` is
  derived inside `toSerreDualityData`.  Note the keystone's `hL : IsLeray` is NOT needed by any
  input of this spine — only `hR : LocallyRealizable` is.
* `CousinResidueData.exists_serreDualityData_of` — the same spine at the `CousinResidueData`
  level (the exact R7 landing target, `GlobalResidueConstruct.lean`), so lane R can discharge at
  either rung.

## S1 — canonical-datum alignment (`hKgenus` for the residue chain's own `K`)

The residue/fine-sheaf machinery fixes `ω₀` and `K = div ω₀`; `hKgenus` must hold for the SAME
`K`.  We close this for ANY divisor that reads off the orders of a germ-nonzero meromorphic
1-form — in particular the order-divisor of the lane-R holomorphic `ω₀`:

* `lDim_eq_genus_of_order_eq` — `K = div ω₀'` (meromorphic, germ-nonzero) ⟹
  `lDim K = kirovGenus X` (any genus; via `CanonicalForm17Data.hKgenus_unconditional`).
* `holToMero_formOrderW_ne_top` / `lDim_eq_genus_of_holomorphic_order_eq` /
  `exists_canonicalDivisor_of_holomorphic` — the holomorphic-`ω₀` forms (`g ≥ 1` leg), including
  existence of the order-divisor (`exists_form_divisor`).
* `exists_holomorphicOneForms_ne_zero` — at `0 < kirovGenus X` a nonzero holomorphic `ω₀`
  exists (`kirovGenus = finrank HolomorphicOneForms`).

## S9 — genus-0 routing (the case split of `docs/planning/R4_G0_NOTE.md`, Decision 5)

Lane R's fine-sheaf functional requires a nonzero **holomorphic** `ω₀`, which exists only at
`g ≥ 1`.  The keystone discharge is therefore a case split at the instantiation point:

* `exists_serreDualityData_of_globalResidue_holomorphic` — the `0 < kirovGenus X` leg, reduced
  to EXACTLY the lane-R outputs `{ω₀ ≠ 0 holomorphic, K = div ω₀, G, UnwindRegularity}`;
  `hKgenus` is eliminated (proven via S1).
* `exists_serreDualityData_of_globalResidue_meromorphic` — the genus-uniform variant over a
  germ-nonzero meromorphic `ω₀'` (valid at `g = 0`, where `deg K = −2 < 0` and
  `lDim K = 0 = kirovGenus` still holds via S1) — the shape of the `g = 0` leg IF that leg is
  closed by a meromorphic-`ω₀` residue functional.
* `exists_serreDualityData_genus_split` — the case split itself.  The `g = 0` leg is the named
  hypothesis `hzero : kirovGenus X = 0 → Nonempty (SerreDualityData 𝔘)` (kept maximally
  general).  **Routing finding (recorded in `docs/planning/A_LANE_PROGRESS.log`):** the
  snapshot's `SerreResidueDirectGenus0*` files discharge Gate A's residual #5 (the trace-side
  `∞`-vanishing) and still take `ω₀ : HolomorphicOneForms X` — at source-genus `0` they do NOT
  by themselves provide a meromorphic-`ω₀` residue theorem, so the `g = 0` leg remains a genuine
  (small) construction: either a meromorphic-`ω₀` `CousinResidueData` over the direct route, or
  a bespoke `g = 0` `SerreDualityData`.  Both shapes are accepted by this file
  (`..._meromorphic` resp. `hzero` directly).

## S2 / S4 status (no Lean artifact here, by design)

* **S2 (`vanish` descent)** belongs to the *retired* meromorphic-Cousin feeder
  (`MeromorphicCousinSolutions.vanish`): under the adopted fine-sheaf architecture
  (`docs/planning/S3_FINESHEAF_RES_SCOPING.md` §1.2) the coboundary-vanishing is the landed
  R5 Stokes theorem (`FineResidue/CoboundaryVanish.lean`, `resFunctional_eq_zero_of_coboundary`)
  and enters as the `vanish_coboundary` FIELD of `CousinResidueData` — lane R work, consumed
  abstractly by the spine here.
* **S4 (`dz/z` witness transport)** is the `nondegenerate` FIELD of `GlobalResidue` /
  `CousinResidueData` (= R8 of the S3 scoping); its construction is gated on the R6 simple-pole
  Mittag–Leffler tie.  The spine consumes it abstractly; adding a finer interface for it here
  would violate the no-unilateral-interface-extension rule (cf. `UnwindRegularity`'s isolation
  in `SerreUnwind.lean`).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17; parent-repo planning docs
`KEYSTONE_GAP_ANALYSIS.md`, `CAMPAIGN_KEYSTONE.md`, `R4_G0_NOTE.md`, `S3_FINESHEAF_RES_SCOPING.md`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1 — S1: canonical-datum alignment (`hKgenus` for the chain's own `K`) -/

/-- **S1 (meromorphic core).** ANY divisor reading off the orders of a germ-nonzero meromorphic
1-form is genus-canonical: `lDim K = kirovGenus X`.  Valid at every genus (at `g = 0` it says
`lDim K = 0` for the degree-`−2` canonical divisor).  This is Forster §17.4 at `D = 0`
(`CanonicalForm17Data.hKgenus_unconditional`), restated so the keystone assembly can align the
`hKgenus` field with whatever `K = div ω₀` the residue chain fixes. -/
theorem lDim_eq_genus_of_order_eq (ω₀' : MeromorphicOneForm X)
    (h0 : ∃ x, ω₀'.formOrderW x ≠ ⊤) {K : Divisor X}
    (hK : ∀ x, ω₀'.formOrderW x = (K x : WithTop ℤ)) :
    lDim (X := X) K = kirovGenus X :=
  CanonicalForm17Data.hKgenus_unconditional ⟨ω₀', h0, K, hK⟩

/-- A nonzero holomorphic 1-form is germ-nonzero at every point (`holToMero` + the form
identity theorem): the `nontrivial` field of the §17.4 datum for the lane-R `ω₀`. -/
theorem holToMero_formOrderW_ne_top (ω₀ : HolomorphicOneForms X) (hω : ω₀ ≠ 0) (x : X) :
    (holToMero ω₀).formOrderW x ≠ ⊤ := by
  refine MeromorphicOneForm.formOrderW_ne_top_of_exists _ ?_ x
  by_contra hc
  simp only [not_exists, ne_eq, not_not] at hc
  exact hω (holToMero_eq_zero_of_germZero ω₀ hc)

/-- **S1 (holomorphic form, the `g ≥ 1` leg).** The order-divisor of a NONZERO holomorphic
1-form is genus-canonical: `lDim K = kirovGenus X`.  This eliminates the `hKgenus` input of the
keystone assembly for exactly the `K = div ω₀` lane R fixes. -/
theorem lDim_eq_genus_of_holomorphic_order_eq (ω₀ : HolomorphicOneForms X) (hω : ω₀ ≠ 0)
    {K : Divisor X} (hK : ∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) :
    lDim (X := X) K = kirovGenus X :=
  lDim_eq_genus_of_order_eq (holToMero ω₀)
    ⟨Classical.arbitrary X, holToMero_formOrderW_ne_top ω₀ hω _⟩ hK

/-- **S1 (existence form).** A nonzero holomorphic 1-form HAS an order-divisor, and it is
genus-canonical (`exists_form_divisor` + the alignment above). -/
theorem exists_canonicalDivisor_of_holomorphic (ω₀ : HolomorphicOneForms X) (hω : ω₀ ≠ 0) :
    ∃ K : Divisor X, (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
      lDim (X := X) K = kirovGenus X := by
  obtain ⟨K, hK⟩ := exists_form_divisor (holToMero ω₀) (holToMero_formOrderW_ne_top ω₀ hω)
  exact ⟨K, hK, lDim_eq_genus_of_holomorphic_order_eq ω₀ hω hK⟩

/-- **S1 (supply).** At positive genus a nonzero holomorphic 1-form exists
(`kirovGenus X = finrank ℂ (HolomorphicOneForms X) > 0`). -/
theorem exists_holomorphicOneForms_ne_zero (hg : 0 < kirovGenus X) :
    ∃ ω₀ : HolomorphicOneForms X, ω₀ ≠ 0 := by
  have : Nontrivial (HolomorphicOneForms X) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (M := HolomorphicOneForms X) hg
  exact exists_ne 0

/-! ## Part 2 — the keystone assembly spine

`SerreDualityData`'s six fields from the two R-lane-gated named inputs (`G : GlobalResidue`,
`UnwindRegularity`) plus `hKgenus` (eliminated by Part 1 when `K` is an order-divisor):
`finH1` is the proven `finiteDimensional_cechH1_wired`; `ι_surj` is the landed S5+S6+S7 chain
`pairing_surjective_of_globalResidue`; `ι_inj` is derived in `toSerreDualityData`. -/

namespace GlobalResidue

/-- **The keystone assembly spine.**  From the global residue functional (lane R), the §17.7
regularity law at every divisor (R6-gated, `SerreUnwind.lean`), local realizability of the
cover, and the canonical-divisor alignment `hKgenus` (Part 1), the full keystone conclusion
`Nonempty (SerreDualityData 𝔘)` follows.  The auxiliary point `P` of the §17.9 count is any
point of the (connected, hence nonempty) `X`. -/
theorem exists_serreDualityData_of {𝔘 : FiniteCover X} {K : Divisor X}
    (G : GlobalResidue 𝔘 K) (hR : 𝔘.LocallyRealizable)
    (hKgenus : lDim (X := X) K = kirovGenus X)
    (hreg : ∀ D : Divisor X, G.UnwindRegularity D) :
    Nonempty (SerreDualityData 𝔘) :=
  ⟨G.toSerreDualityData hKgenus
    (fun D =>
      pairing_surjective_of_globalResidue G D (Classical.arbitrary X) hR (hreg D))
    (fun D => finiteDimensional_cechH1_wired 𝔘 D)⟩

end GlobalResidue

namespace CousinResidueData

/-- **The assembly spine at the `CousinResidueData` rung** — the exact landing target of the
fine-sheaf descent (R7, `S3_FINESHEAF_RES_SCOPING.md` §1.2): a cocycle-level residue functional
killing coboundaries with the §17.6 witness, plus the §17.7 regularity law, closes the
keystone. -/
theorem exists_serreDualityData_of {𝔘 : FiniteCover X} {K : Divisor X}
    (C : CousinResidueData 𝔘 K) (hR : 𝔘.LocallyRealizable)
    (hKgenus : lDim (X := X) K = kirovGenus X)
    (hreg : ∀ D : Divisor X, C.toGlobalResidue.UnwindRegularity D) :
    Nonempty (SerreDualityData 𝔘) :=
  C.toGlobalResidue.exists_serreDualityData_of hR hKgenus hreg

end CousinResidueData

/-! ## Part 3 — S9: the genus case split at the keystone instantiation
(`docs/planning/R4_G0_NOTE.md`, Decision 5) -/

/-- **The `0 < kirovGenus X` leg, fully reduced to lane-R outputs.**  Given a nonzero
holomorphic `ω₀`, its order-divisor `K`, a `GlobalResidue 𝔘 K`, and the §17.7 regularity law,
the keystone conclusion follows — `hKgenus` is GONE (discharged by S1).  This is the exact
statement the R-lane endgame (R7 + R6-discharged `UnwindRegularity` + the R4 `ω₀`-witness)
must instantiate. -/
theorem exists_serreDualityData_of_globalResidue_holomorphic {𝔘 : FiniteCover X}
    (hR : 𝔘.LocallyRealizable) (ω₀ : HolomorphicOneForms X) (hω : ω₀ ≠ 0) {K : Divisor X}
    (hK : ∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ))
    (G : GlobalResidue 𝔘 K) (hreg : ∀ D : Divisor X, G.UnwindRegularity D) :
    Nonempty (SerreDualityData 𝔘) :=
  G.exists_serreDualityData_of hR (lDim_eq_genus_of_holomorphic_order_eq ω₀ hω hK) hreg

/-- **The genus-uniform meromorphic variant** (valid at `g = 0`): same reduction over a
germ-nonzero meromorphic `ω₀'` and its order-divisor.  If the `g = 0` leg is closed by a
meromorphic-`ω₀` residue functional (the natural shape after `R4_G0_NOTE.md` rules holomorphic
`ω₀` out at `g = 0`), this is its consumption point. -/
theorem exists_serreDualityData_of_globalResidue_meromorphic {𝔘 : FiniteCover X}
    (hR : 𝔘.LocallyRealizable) (ω₀' : MeromorphicOneForm X)
    (h0 : ∃ x, ω₀'.formOrderW x ≠ ⊤) {K : Divisor X}
    (hK : ∀ x, ω₀'.formOrderW x = (K x : WithTop ℤ))
    (G : GlobalResidue 𝔘 K) (hreg : ∀ D : Divisor X, G.UnwindRegularity D) :
    Nonempty (SerreDualityData 𝔘) :=
  G.exists_serreDualityData_of hR (lDim_eq_genus_of_order_eq ω₀' h0 hK) hreg

/-- **S9 — the genus case split at the keystone instantiation point** (`R4_G0_NOTE.md`,
Decision 5).  The keystone conclusion from:

* `hpos` — the `0 < kirovGenus X` leg: EXACTLY the lane-R outputs (nonzero holomorphic `ω₀`,
  its order-divisor `K`, the global residue functional, the §17.7 regularity law); and
* `hzero` — the `kirovGenus X = 0` leg, kept maximally general (any route producing the data;
  e.g. a meromorphic-`ω₀` functional via `exists_serreDualityData_of_globalResidue_meromorphic`,
  or a bespoke explicit construction).

Once lane R lands, the keystone sorry's discharge is this theorem applied to the R-lane
provision and the `g = 0` leg.  (`hL : IsLeray` is not needed by any input; the keystone's
signature keeps it, so the final wrapper just drops it.) -/
theorem exists_serreDualityData_genus_split (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable)
    (hpos : 0 < kirovGenus X →
      ∃ (ω₀ : HolomorphicOneForms X) (K : Divisor X), ω₀ ≠ 0 ∧
        (∀ x, (holToMero ω₀).formOrderW x = (K x : WithTop ℤ)) ∧
        ∃ G : GlobalResidue 𝔘 K, ∀ D : Divisor X, G.UnwindRegularity D)
    (hzero : kirovGenus X = 0 → Nonempty (SerreDualityData 𝔘)) :
    Nonempty (SerreDualityData 𝔘) := by
  rcases Nat.eq_zero_or_pos (kirovGenus X) with h0 | hg
  · exact hzero h0
  · obtain ⟨ω₀, K, hω, hK, G, hreg⟩ := hpos hg
    exact exists_serreDualityData_of_globalResidue_holomorphic hR ω₀ hω hK G hreg

end Jacobians.Dolbeault

end
