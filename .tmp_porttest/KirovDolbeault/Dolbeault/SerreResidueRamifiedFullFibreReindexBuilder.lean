/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibreReindex
import KirovDolbeault.Dolbeault.SerreResidueRamifiedClusterTopology

/-!
# Building the SOUND `FullFibreCenterReindex` from the per-slit conservation-of-number geometry

`SerreResidueRamifiedFullFibreReindex.lean` fixed the full-fibre-vs-pole inconsistency of
`FibreClusterReindex` by introducing the SOUND `FullFibreCenterReindex` (whole-fibre `D`, non-poles →
residue `0`, **no `hD_mem`**), and proved Gate-A `∑Res = 0` from a per-centre family of these.  This file
discharges the per-centre `FullFibreCenterReindex` from the SAME per-slit conservation-of-number geometry
the unsound `FibreClusterReindex` chain consumed (the `ClusterReindexData` / `FibreClusterTopology`
families of `SerreResidueRamifiedClusterPartition.lean` / `SerreResidueRamifiedClusterTopology.lean`) —
but with the inconsistent all-poles assumption removed.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `FullFibreCenterReindex.ofClusterReindexFamily` — the SOUND analogue of
  `FibreClusterReindex.ofClusterReindexFamily`: builds the per-centre `FullFibreCenterReindex` from the
  whole pole-value fibre `D`, the per-preimage cluster data, the meromorphy bound, the
  **non-pole-residue-`0`** datum + the pole surjectivity (replacing `hD_mem`), and a slit-wide
  `ClusterReindexData` family (`hgeom_fibre` discharged pointwise).
* `FullFibreCenterReindex.ofFibreClusterTopologyFamily` — the same from a slit-wide `FibreClusterTopology`
  family (the conservation-of-number datum, `hcard = deg f`).
* `residueSum_eq_zero_of_fullFibreTopology` — Gate-A `∑Res = 0` from an `AdaptedFRamified` + a per-centre
  `FullFibreCenterReindex`, anchoring the SOUND reduction to the Gate-A goal.

So the residue theorem `∑_{a ∈ poles} formFnResidue ω₀ g a = 0` is reduced, for the real cover, to
**exactly** the per-slit `FibreClusterTopology` (Forster §4 conservation-of-number + §5 normal-form
geometry — the genuine remaining wall, *unchanged* in content from the unsound chain) plus the discharged
`AdaptedFRamified`/`GateAInftyData` bundle, with the full-fibre-vs-pole inconsistency **resolved**: `D` is
the whole fibre and the non-pole preimages drop out at the residue level (`residueSum_full_eq_poleOnly`).

## ⚠ Soundness

`D` = the WHOLE fibre.  **No `hD_mem` (no all-poles assumption).**  The per-slit geometry
(`ClusterReindexData` / `FibreClusterTopology`) is the *same* genuine §4/§5 content as the unsound chain,
now consistent with the whole fibre (`hcard = deg f`).  The residue reconciliation is the PROVEN
`residueSum_full_eq_poleOnly` (non-poles → `0`).  No custom axiom; no unproved obligation on a false statement; no
false/junk/circular field.

## References

* `SerreResidueRamifiedFullFibreReindex.lean` (`FullFibreCenterReindex`, the residue-split reconciliation),
  `SerreResidueRamifiedClusterTopology.lean` (`FibreClusterTopology`, `ClusterReindexData.ofFibreClusterTopology`),
  `SerreResidueRamifiedClusterPartition.lean` (`ClusterReindexData`,
  `valueChartTrace_eq_clusterSum_of_clusterReindexData`),
  `SerreResidueRamifiedRealCover.lean` (`meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §5 (`z = wᵐ`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`FullFibreCenterReindex` from a slit-wide family of `ClusterReindexData`** (the SOUND builder).
Given the **whole** pole-value fibre `D` over `c` (injective; enumerating all `deg f` preimages — the
`hcard` consistency), per-preimage cluster data `Cl` on the slit `Sset`, the eventual off-centre
analyticity + finite pole-order bound (for the meromorphy `hvct_mero`), the slit accumulation, the
non-pole-residue-`0` datum `hnonpole`, the pole surjectivity `hD_surj`, **and** a `ClusterReindexData` at
every slit value `z`, the SOUND per-centre residual `FullFibreCenterReindex` holds.

`hgeom_fibre` is discharged pointwise on the slit by `valueChartTrace_eq_clusterSum_of_clusterReindexData`;
`hvct_mero` by the removable-singularity atom `meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto`.
**No `hD_mem`** (no all-poles assumption) — the corrected design that fixes the full-fibre-vs-pole
inconsistency of `FibreClusterReindex.ofClusterReindexFamily`. -/
noncomputable def FullFibreCenterReindex.ofClusterReindexFamily {ω₀ : HolomorphicOneForms X}
    {g : X → ℂ} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X}
    {c : ℂ} {Sset : Set ℂ}
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) z)
    (D : FibreRamifiedData g f c) (hD_inj : Function.Injective D.xs)
    (hnonpole : ∀ i, D.xs i ∉ poles → formFnResidue ω₀ g (D.xs i) = 0)
    (hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, D.xs i = a)
    (hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset)
    (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset)
    (hmult : ∀ i, (Cl i).m = D.mult i)
    (hsplit0 : ∀ i, straightenedIntegrand ω₀ g (D.xs i) (Cl i).s =ᶠ[𝓝[≠] 0]
      fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u)
    (ppord : ℕ)
    (hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z) (𝓝[≠] c) (𝓝 0))
    (hfam : ∀ z ∈ Sset, ClusterReindexData (canonicalFibreSelection g f hdiv) D Cl z) :
    FullFibreCenterReindex ω₀ g f hdiv poles c where
  F :=
    { D := D
      hD_inj := hD_inj
      S := Sset
      hS_acc := hS_acc
      Cl := Cl
      hmult := hmult
      hsplit0 := hsplit0
      hvct_mero := Jacobians.meromorphicAt_of_analyticOn_punctured_of_pow_mul_sub_tendsto ppord
        hanalytic hbnd
      hgeom_fibre := fun z hz =>
        valueChartTrace_eq_clusterSum_of_clusterReindexData (hfam z hz) }
  hnonpole := hnonpole
  hD_surj := hD_surj

/-- **`FullFibreCenterReindex` from a slit-wide family of `FibreClusterTopology`** (the SOUND full
reduction).  The corrected analogue of `FibreClusterReindex.ofFibreClusterTopologyFamily`: the per-centre
SOUND residual follows from the routine bookkeeping + the non-pole-residue-`0` datum + the pole
surjectivity + a `FibreClusterTopology` (the conservation-of-number datum, `hcard = deg f`) at every slit
value.  **No `hD_mem`** — `D` is the whole fibre and non-poles drop out at the residue level.  The genuine
remaining content is exactly the per-slit `FibreClusterTopology` (and via `ofClusterFibrePoints`, the
three minimal facts: the cluster sheets are distinct fibre points numbering `deg f`). -/
noncomputable def FullFibreCenterReindex.ofFibreClusterTopologyFamily {ω₀ : HolomorphicOneForms X}
    {g : X → ℂ} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X}
    {c : ℂ} {Sset : Set ℂ}
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) z)
    (D : FibreRamifiedData g f c) (hD_inj : Function.Injective D.xs)
    (hnonpole : ∀ i, D.xs i ∉ poles → formFnResidue ω₀ g (D.xs i) = 0)
    (hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, D.xs i = a)
    (hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset)
    (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset)
    (hmult : ∀ i, (Cl i).m = D.mult i)
    (hsplit0 : ∀ i, straightenedIntegrand ω₀ g (D.xs i) (Cl i).s =ᶠ[𝓝[≠] 0]
      fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u)
    (ppord : ℕ)
    (hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z) (𝓝[≠] c) (𝓝 0))
    (hfam : ∀ z ∈ Sset, FibreClusterTopology (canonicalFibreSelection g f hdiv) D Cl z) :
    FullFibreCenterReindex ω₀ g f hdiv poles c :=
  FullFibreCenterReindex.ofClusterReindexFamily hanalytic D hD_inj hnonpole hD_surj hS_acc Cl hmult
    hsplit0 ppord hbnd (fun z hz => ClusterReindexData.ofFibreClusterTopology (hfam z hz))

/-- **`hnonpole` is automatic from an `AdaptedFRamified` datum.**  A non-pole preimage `x ∉ poles` of a
genuine meromorphic numerator has `g` analytic there (`A.hg_an_offpoles`), so `α = ω₀·g` is holomorphic
and its form residue vanishes (`formFnResidue_eq_zero_of_analyticAt`).  This discharges the
non-pole-residue-`0` field of `FullFibreCenterReindex` for free — it is **not** a hidden wall. -/
theorem hnonpole_of_adaptedFRamified {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X}
    {poles : Finset X} (A : AdaptedFRamified ω₀ g poles) {x : X} (hx : x ∉ poles) :
    formFnResidue ω₀ g.toFun x = 0 :=
  formFnResidue_eq_zero_of_analyticAt ω₀ g.toFun x (A.hg_an_offpoles x hx)

/-- **The SOUND per-centre residual from an `AdaptedFRamified` + a `FibreClusterTopology` family**, with
`hnonpole` AUTOMATIC.  The maximally-clean builder: from an `AdaptedFRamified` datum `A` (so `hnonpole`
comes free via `hnonpole_of_adaptedFRamified`), the whole pole-value fibre `D`, the per-preimage cluster
data, the meromorphy bound, the slit accumulation, the pole surjectivity, and a slit-wide
`FibreClusterTopology` family, build the SOUND `FullFibreCenterReindex`.  **No `hD_mem`, no separate
`hnonpole` obligation** — the genuinely-remaining content is exactly the per-slit `FibreClusterTopology`
(the conservation-of-number geometry). -/
noncomputable def FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified
    {ω₀ : HolomorphicOneForms X} {g : MeromorphicFunction X} {poles : Finset X}
    (A : AdaptedFRamified ω₀ g poles) {c : ℂ} {Sset : Set ℂ}
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ A.f (canonicalFibreSelection g.toFun A.f A.hdiv)) z)
    (D : FibreRamifiedData g.toFun A.f c) (hD_inj : Function.Injective D.xs)
    (hD_surj : ∀ a ∈ poles, A.f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, D.xs i = a)
    (hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset)
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun (D.xs i) c Sset)
    (hmult : ∀ i, (Cl i).m = D.mult i)
    (hsplit0 : ∀ i, straightenedIntegrand ω₀ g.toFun (D.xs i) (Cl i).s =ᶠ[𝓝[≠] 0]
      fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u)
    (ppord : ℕ)
    (hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ A.f (canonicalFibreSelection g.toFun A.f A.hdiv) z) (𝓝[≠] c) (𝓝 0))
    (hfam : ∀ z ∈ Sset, FibreClusterTopology (canonicalFibreSelection g.toFun A.f A.hdiv) D Cl z) :
    FullFibreCenterReindex ω₀ g.toFun A.f A.hdiv poles c :=
  FullFibreCenterReindex.ofFibreClusterTopologyFamily hanalytic D hD_inj
    (fun _ hi => hnonpole_of_adaptedFRamified A hi) hD_surj hS_acc Cl hmult hsplit0 ppord hbnd hfam

/-- **Gate A `∑Res = 0` from per-centre `FullFibreCenterReindex` families** (the SOUND residual
exhibited).  For a genuine meromorphic numerator `g`, an `AdaptedFRamified` datum `A`, and at each finite
pole-value centre a per-centre `FullFibreCenterReindex` (e.g. built via
`FullFibreCenterReindex.ofFibreClusterTopologyFamily` from a slit-wide family of `FibreClusterTopology`),
the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This anchors the conservation-of-number datum to the Gate-A goal: the *only* genuinely-remaining content
is the per-centre `FibreClusterTopology` — and, via `ofClusterFibrePoints`, exactly the three minimal
clustering facts (cluster sheets are distinct fibre points numbering `deg f`).  The full-fibre-vs-pole
inconsistency that made the old `FibreClusterReindex` route vacuous is resolved here: `D` is the WHOLE
fibre, non-poles → residue `0`. -/
theorem residueSum_eq_zero_of_fullFibreTopology {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, FullFibreCenterReindex ω₀ g.toFun A.f A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified A R

end Jacobians.Dolbeault.SerreResidueTheorem
