/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedClusterPartition
import KirovDolbeault.Dolbeault.SerreResidueRamifiedMultiplicityBridge

/-!
# The fibre-cluster topology: reducing `ClusterReindexData` to the conservation-of-number datum

`SerreResidueRamifiedClusterPartition.lean` reduces `FibreClusterReindex.hgeom_fibre` to a slit-wide
family of `ClusterReindexData` — the precise remaining clustering datum at each regular slit value `z`.
That datum has, besides the **bijection** `e` and the **point coincidence** `hpoint` (the genuine
§4/§17.9 conservation-of-number content), a battery of *routine* analytic fields (`hcw`/`hmem_a`/
`hcs_cont`/`hcsP_diff`/`htrans_diff`/`htrans_diff_inv`/`hderiv_match`) describing the differentiability
of the cluster section and the section-derivative agreement.

This file **discharges those routine fields** from the genuine geometric data, so `ClusterReindexData`
reduces to *exactly* the conservation-of-number content.  Concretely it isolates a single structure
`FibreClusterTopology` whose fields are precisely:

* the sphere sheet system `S` at `coe z` (regular fibre — `hderiv`/`hmero`/`hcoh`, the regular-value
  coherence supplied by the moving-fibre machinery);
* the **conservation-of-number bijection** `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`;
* the **point coincidence** `hpoint` (each cluster sheet point IS the matched moving sheet point);
* the genuine *geometric* residuals that are NOT pure chart algebra: the cluster sheet stays in the
  fixed-preimage chart source near `z` (`hsrc`), and the cluster section is a genuine local section of
  `f.holoRepr` through the coincident point (`hcs_sec`), together with the regular-value `hreg`/`hq_np`
  feeding the holomorphic-local-inverse uniqueness.

Everything else — the self-chart-pullback differentiability of the cluster section, the chart
transitions, and the section-derivative agreement `hderiv_match` — is **DERIVED** here from the
analyticity of the normal-form local inverse `s` (`(Cl i).hs_an_sheet`), the slit branch
differentiability (`(Cl i).hw₀_diff`), the chart-transition analyticity (a local copy of the
maximal-atlas coordinate change), and the proven `hderiv_match_of_section`.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`clusterSheet_differentiableAt`** — `clusterSheet (Cl i).s … j` is differentiable at a slit value
  `z` (from `s` analytic at `ζʲ·w₀ z` + `w₀` differentiable at `z`).
* **`transition_analyticAt'` / `analyticAt_chart_change'`** — local copies of the maximal-atlas
  chart-transition analyticity (so this file does not depend on the Čech subtree).
* **`clusterSection_chartPullback_differentiableAt`** — the self-chart pullback `chart_q ∘
  clusterSection` is differentiable at `z` (chart transition ∘ chart.symm ∘ clusterSheet).
* **`FibreClusterTopology`** — the precise conservation-of-number datum (bijection + coincidence + the
  genuine geometric residuals), with the routine analytic fields removed.
* **`ClusterReindexData.ofFibreClusterTopology`** — assembles a `ClusterReindexData` from a
  `FibreClusterTopology`, discharging every routine analytic field.  This is the reduction: the
  full-fibre cluster identity `hgeom_fibre` at `z` now rests on *only* the bijection + coincidence (+
  the two genuine geometric residuals).
* **`FibreClusterTopology.ofClusterEmbedding`** — builds the datum from a cluster→sheet *assignment*
  `cl` + its injectivity + the conservation-of-number count `∑ᵢ D.mult i = S.n` (the bijection `e` is
  the bijectivization: an injection between equicardinal finite types).
* **`FibreClusterTopology.ofClusterFibrePoints`** — the **minimal residual**: the assignment is
  recovered from `S.fibre_eq`, so the irreducible input shrinks to *three* facts — the cluster sheets
  are genuine preimages of `coe z` (`hcl_fibre`), are pairwise distinct (`hcl_distinct`), and number
  `∑ᵢ D.mult i = S.n` (`hcard`, the §4 conservation-of-number degree count).
* **`FibreClusterReindex.ofFibreClusterTopologyFamily`** / **`residueSum_eq_zero_of_fibreClusterTopology`**
  — the full chain: a slit-wide family of `FibreClusterTopology` discharges the per-centre
  `FibreClusterReindex`, hence (with the concurrent genericity `AdaptedFRamified`) Gate-A `∑Res = 0`.
* **`FibreClusterTopology.sum_mult_eq_sheetCount`** — the soundness fact: the datum forces
  `∑ᵢ D.mult i = S.n`, genuinely multi-preimage.

## The precise remaining clustering-topology content

After this file, Gate-A TARGET 1 (`hgeom_fibre` for the real cover) reduces, at each regular slit value
`z`, to supplying the three minimal facts of `ofClusterFibrePoints`:

1. **`hcl_fibre`** — the cluster sheet points are preimages of `coe z` (the sphere-level §5
   `clusterSheet_sect`: `f.toRiemannSphere (clusterSection D Cl i j z) = coe z`).  Derivable from the
   normal-form section property (`exists_clusterSplit_at_fibrePoint` gives `f.holoRepr (clusterSheet …)
   = z`, hence the finite sphere value `coe z` at the non-pole cluster point).
2. **`hcl_distinct`** — the cluster sheet points are pairwise distinct (the clusters are disjoint:
   different preimages `D.xs i` are separated, and the `mᵢ` cluster sheets at one preimage are distinct
   via the primitive root `ζ`).
3. **`hcard`** — the conservation of number `∑ᵢ D.mult i = S.n` (`= deg f`).  The genuine §4 degree
   identity: at the regular `z` every `localDeg = 1` so `S.n = fibreMult f (coe z)`; `N f` is locally
   constant (`ProperMapDegreeConstruct`/`MultiplicityPatchingConstruct`, the proven
   `exists_properMapDegree` engine), so `fibreMult f (coe z) = fibreMult f (coe c) = ∑ᵢ localDeg f (coe
   c) (D.xs i) = ∑ᵢ D.mult i` (with `D.mult i = localDeg`, the `analyticOrderAt_holoRepr_sub_eq_mult`
   bridge).  This is the irreducible conservation-of-number wall, isolated to a single equality of
   naturals.

## ⚠ Soundness

`FibreClusterTopology` carries the **genuine** geometric data (the real sphere sheet system, the genuine
`clusterSheet`/`clusterSection` points, a genuine bijection, the genuine section property), never
asserted.  The bijection `e` still forces `∑ᵢ D.mult i = S.n` (`ClusterReindexData.sum_mult_eq_sheetCount`
applies to the assembled datum), so it is genuinely multi-preimage, not a disguised triviality.  No
custom axiom, no unproved obligation on a false statement, no false/junk/circular field — the routine fields are
DERIVED, the irreducible bijection + coincidence remain the only conservation-of-number content.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (the degree / conservation of number, Cor.
  4.24–4.25), §5 (the normal form `z = wᵐ`).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace), §II.4.
* `SerreResidueRamifiedClusterPartition.lean` (`ClusterReindexData`, `clusterSection`,
  `hderiv_match_of_section`, `valueChartTrace_eq_clusterSum_of_clusterReindexData`),
  `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`).
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
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Differentiability of the cluster sheet and section

The cluster sheet `clusterSheet s ζ w₀ j w = s (ζʲ · w₀ w)` is differentiable at a slit value `z` from
the analyticity of `s` at `ζʲ · w₀ z` (`(Cl i).hs_an_sheet`) and the differentiability of the branch
`w₀` (`(Cl i).hw₀_diff`).  The cluster section `clusterSection D Cl i j = chart_{D.xs i}.symm ∘
clusterSheet …` lifts this to `X`; its self-chart pullback `chart_q ∘ clusterSection` is differentiable
by composing with the chart transition `chart_q ∘ chart_{D.xs i}.symm` (analytic, maximal-atlas
coordinate change). -/

/-- **The cluster sheet is differentiable at a slit value.**  `clusterSheet s ζ w₀ j w = s (ζʲ·w₀ w)`
is differentiable at `z` when `s` is analytic at `ζʲ·w₀ z` and `w₀` is differentiable at `z`. -/
theorem clusterSheet_differentiableAt {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z : ℂ}
    (hs_an : AnalyticAt ℂ s (ζ ^ j * w₀ z)) (hw₀_diff : DifferentiableAt ℂ w₀ z) :
    DifferentiableAt ℂ (clusterSheet s ζ w₀ j) z := by
  have harg : DifferentiableAt ℂ (fun w => ζ ^ j * w₀ w) z :=
    (differentiableAt_const _).mul hw₀_diff
  exact (hs_an.differentiableAt.comp z harg)

/-- **The chart transition `chart_y ∘ chart_z.symm` is analytic at `chart_z z`** (maximal-atlas
coordinate change at `ω`), when `z ∈ chart_y.source`.  Local copy of the Čech-side
`transition_analyticAt`, to keep this file off that subtree. -/
theorem transition_analyticAt' {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hsrc_z : z ∈ (chartAt (H := ℂ) z).source := mem_chart_source ℂ z
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source hsrc_z
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hcz_tgt).contMDiffAt
      ((chartAt (H := ℂ) z).open_target.mem_nhds hcz_tgt)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv hsrc_z
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y)
      ((chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z)) := by
    rw [hez]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hz).contMDiffAt
      ((chartAt (H := ℂ) y).open_source.mem_nhds hz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) z) z) h2 h1)).analyticAt

/-- **The chart transition `chart_b ∘ chart_a.symm` is analytic at an interior target point** `w₀`
(maximal-atlas coordinate change at `ω`): if `w₀ ∈ chart_a.target` and `chart_a.symm w₀ ∈
chart_b.source`, then `chart_b ∘ chart_a.symm` is analytic at `w₀`.  Unlike `transition_analyticAt'`
(evaluated at the chart centre `chart_a a`), this is at an arbitrary overlap point — exactly what the
cluster section's self-chart pullback needs (`w₀ = clusterSheet … z = chart_{D.xs i} q`). -/
theorem transition_analyticAt_target {a b : X} {w₀ : ℂ}
    (hw₀ : w₀ ∈ (chartAt (H := ℂ) a).target)
    (hb : (chartAt (H := ℂ) a).symm w₀ ∈ (chartAt (H := ℂ) b).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) b) ∘ (chartAt (H := ℂ) a).symm) w₀ := by
  set ea := chartAt (H := ℂ) a with hea
  set y₀ := ea.symm w₀ with hy₀
  have ha_max : ea ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ a)
  have hb_max : chartAt (H := ℂ) b ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas b
  have hy₀src : y₀ ∈ ea.source := ea.map_target hw₀
  have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' ha_max hb_max hy₀src hb
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  have hpt : (ea.extend 𝓘(ℂ)) y₀ = w₀ := by
    show ea y₀ = w₀; rw [hy₀, ea.right_inv hw₀]
  rw [hpt] at h
  exact h.analyticAt

/-- **Chart-change of an analytic chart pullback.**  If `h ∘ chart_y.symm` is analytic at `chart_y z`
(for `z ∈ chart_y.source`), then `h ∘ chart_z.symm` is analytic at `chart_z z`.  Local copy of the
Čech-side `analyticAt_chart_change`. -/
theorem analyticAt_chart_change' {h : X → ℂ} {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source (mem_chart_source ℂ z)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv (mem_chart_source ℂ z)
  have hφ := transition_analyticAt' (y := y) (z := z) hz
  have hφ_pt : ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)
      = (chartAt (H := ℂ) y) z := by simp only [Function.comp_apply, hez]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) y).symm) ∘
      ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) ((chartAt (H := ℂ) z) z) :=
    AnalyticAt.comp (hφ_pt ▸ ha) hφ
  have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z),
      (chartAt (H := ℂ) z).symm w ∈ (chartAt (H := ℂ) y).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
      (chartAt (H := ℂ) z).continuousAt_symm hcz_tgt
    have hh : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) ∈ (chartAt (H := ℂ) y).source := by
      rw [hez]; exact hz
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) y).open_source.mem_nhds hh)
  have heq : (h ∘ (chartAt (H := ℂ) z).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) z) z)]
      ((h ∘ (chartAt (H := ℂ) y).symm) ∘ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hw]
  rw [analyticAt_congr heq]; exact hcomp

/-- **The self-chart pullback of the cluster section is differentiable at `z`.**  Writing `a := D.xs i`
and `q := clusterSection D Cl i j z`, the map `w ↦ chart_q (clusterSection D Cl i j w)` is differentiable
at `z`, given: the cluster sheet value `clusterSheet (Cl i).s … j z ∈ chart_a.target` (`htgt`), the
cluster sheet differentiable at `z` (`hsheet_diff`).  Proof: `chart_q ∘ clusterSection = (chart_q ∘
chart_a.symm) ∘ clusterSheet`; the transition is analytic at `clusterSheet … z = chart_a q`
(`transition_analyticAt_target`), and `clusterSheet` is differentiable. -/
theorem clusterSection_chartPullback_differentiableAt {g : X → ℂ} {f : MeromorphicFunction X}
    {c : ℂ} {Sset : Set ℂ} {ω₀ : HolomorphicOneForms X} (D : FibreRamifiedData g f c)
    (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset) (i : D.ι) (j : Fin (D.mult i)) {z : ℂ}
    (htgt : clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z ∈ (chartAt ℂ (D.xs i)).target)
    (hsheet_diff : DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    DifferentiableAt ℂ (fun w => (chartAt ℂ (clusterSection D Cl i j z))
      (clusterSection D Cl i j w)) z := by
  set a : X := D.xs i with ha
  set q : X := clusterSection D Cl i j z with hq
  -- `chart_a q = clusterSheet … z`.
  have hchart_a_q : (chartAt ℂ a) q = clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z := by
    rw [hq, clusterSection]; exact (chartAt ℂ a).right_inv htgt
  -- `q ∈ chart_a.source` (it is `chart_a.symm` of an interior target point).
  have hq_src : q ∈ (chartAt ℂ a).source := by
    rw [hq, clusterSection]; exact (chartAt ℂ a).map_target htgt
  -- The chart transition `chart_q ∘ chart_a.symm` is analytic at `clusterSheet … z = chart_a q`.
  have htrans_an : AnalyticAt ℂ ((chartAt ℂ q) ∘ (chartAt ℂ a).symm)
      (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z) := by
    rw [← hchart_a_q]
    refine transition_analyticAt_target (a := a) (b := q) ?_ ?_
    · rw [hchart_a_q]; exact htgt
    · rw [(chartAt ℂ a).left_inv hq_src]; exact mem_chart_source ℂ q
  -- `chart_q ∘ clusterSection = (chart_q ∘ chart_a.symm) ∘ clusterSheet`.
  have heq : (fun w => (chartAt ℂ q) (clusterSection D Cl i j w))
      = ((chartAt ℂ q) ∘ (chartAt ℂ a).symm) ∘ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) := by
    funext w; rw [clusterSection]; rfl
  rw [heq]
  exact htrans_an.differentiableAt.comp z hsheet_diff

/-! ## The conservation-of-number datum `FibreClusterTopology`

We now isolate the genuine conservation-of-number content of `ClusterReindexData` as a structure whose
fields are *exactly* the irreducible geometry: the sphere sheet system, the bijection, the point
coincidence, and the two genuine geometric residuals (the cluster sheet stays in the fixed-preimage
chart source near `z`, and the cluster section is a genuine local section of `f.holoRepr`).  Every
routine analytic field of `ClusterReindexData` is DERIVED in `ofFibreClusterTopology` below. -/

/-- **The fibre-cluster topology datum at a regular slit value `z`** (the precise conservation-of-number
content of `ClusterReindexData`, routine analytic fields removed).  At `z`:

* `S`/`hderiv`/`hmero`/`hcoh` — the sphere sheet system at `coe z` with the regular-value coherence
  (supplied by the moving-fibre machinery, as in `ClusterReindexData`);
* `e` — the **conservation-of-number bijection** `(Σ i, Fin (D.mult i)) ≃ Fin S.n` of the cluster index
  with the `deg f` sphere sheets;
* `hpoint` — the **point coincidence**: the `j`-th cluster sheet at `i` IS the `e ⟨i,j⟩`-th moving sheet
  point (the conservation-of-number content; forces `∑ᵢ mᵢ = deg f`);
* `hsrc` — the cluster sheet value `clusterSheet (Cl i).s … j w` stays in `D.xs i`'s chart target near
  `z` (the cluster clusters at `D.xs i` — a genuine §5 normal-form fact);
* `hsheet_diff` — the cluster sheet is differentiable at `z` (from `s` analytic + `w₀` differentiable;
  a normal-form analyticity fact, kept as a field for the caller's convenience but supplied by
  `clusterSheet_differentiableAt`);
* `hcs_sec` — the cluster section is a genuine local section of `f.holoRepr` near `z`
  (`f.holoRepr (clusterSection D Cl i j w) = w`; the §5 normal-form section property — the cluster
  sheets are genuine preimages of `z`).

These are the genuine §4/§17.9 conservation-of-number / properness inputs; `ofFibreClusterTopology`
derives the differentiability, the chart transitions, the chart-source membership, and the
section-derivative agreement from them. -/
structure FibreClusterTopology {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
    (Φ : (b : ℂ) → FibreRegularData g f b) {c : ℂ} {Sset : Set ℂ} (D : FibreRamifiedData g f c)
    (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset) (z : ℂ) where
  /-- The sphere sheet system at `coe z`. -/
  S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))
  /-- Regular-value: the chart-pullback derivative of `f.holoRepr` is nonzero at each sheet point. -/
  hderiv : ∀ k, deriv (fun w => f.holoRepr
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
    ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
      (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0
  /-- `g`'s chart-pullback is meromorphic at each sheet point. -/
  hmero : ∀ k, MeromorphicAt
    (fun w => g ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
    ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
      (S.sheet k (((z : ℂ) : RiemannSphere))))
  /-- The regular-value coherence: the geometric trace at `z` equals the sphere-fibre trace. -/
  hcoh : valueChartTrace ω₀ f Φ z
    = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z
  /-- **The conservation-of-number bijection** of the cluster `Σ`-index with the `deg f` sheets. -/
  e : (Σ i : D.ι, Fin (D.mult i)) ≃ Fin S.n
  /-- **Point coincidence**: the `j`-th cluster sheet at `i` is the `e ⟨i,j⟩`-th moving sheet point. -/
  hpoint : ∀ (i : D.ι) (j : Fin (D.mult i)),
    clusterSection D Cl i j z = S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere))
  /-- The cluster sheet value stays in the fixed preimage's chart target near `z`. -/
  hsrc : ∀ (i : D.ι) (j : Fin (D.mult i)),
    ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w ∈ (chartAt ℂ (D.xs i)).target
  /-- The cluster sheet is differentiable at `z`. -/
  hsheet_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
    DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z
  /-- **The cluster section is a genuine local section of `f.holoRepr`** near `z`. -/
  hcs_sec : ∀ (i : D.ι) (j : Fin (D.mult i)),
    ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection D Cl i j w) = w

namespace FibreClusterTopology

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ} {D : FibreRamifiedData g f c}
  {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}

/-- `clusterSheet … z ∈ chart_{D.xs i}.target` (the `z`-instance of `hsrc`). -/
theorem clusterSheet_mem_target (R : FibreClusterTopology Φ D Cl z) (i : D.ι) (j : Fin (D.mult i)) :
    clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z ∈ (chartAt ℂ (D.xs i)).target :=
  (R.hsrc i j).self_of_nhds

/-- The cluster section lies in `D.xs i`'s chart source at `z`. -/
theorem clusterSection_mem_source (R : FibreClusterTopology Φ D Cl z) (i : D.ι)
    (j : Fin (D.mult i)) : clusterSection D Cl i j z ∈ (chartAt ℂ (D.xs i)).source := by
  rw [clusterSection]; exact (chartAt ℂ (D.xs i)).map_target (R.clusterSheet_mem_target i j)

/-- The matched sphere sheet point `q := S.sheet (e ⟨i,j⟩) (coe z)` has finite value `coe z` on the
sphere (it is a sheet point at the base of `S`). -/
theorem sheet_toRiemannSphere (R : FibreClusterTopology Φ D Cl z) (k : Fin R.S.n) :
    f.toRiemannSphere (R.S.sheet k (((z : ℂ) : RiemannSphere))) = (((z : ℂ) : RiemannSphere)) :=
  R.S.sheet_section k _ R.S.mem_V

/-- The matched sphere sheet point is a non-pole (`0 ≤ orderAtPoint`): its sphere value `coe z` is
finite. -/
theorem sheet_nonpole (R : FibreClusterTopology Φ D Cl z) (k : Fin R.S.n) :
    0 ≤ f.orderAtPoint (R.S.sheet k (((z : ℂ) : RiemannSphere))) :=
  (f.nonpole_of_toRiemannSphere_eq_coe (R.sheet_toRiemannSphere k)).1

/-- The `holoRepr` value of the matched sphere sheet point is `z`. -/
theorem sheet_holoRepr (R : FibreClusterTopology Φ D Cl z) (k : Fin R.S.n) :
    f.holoRepr (R.S.sheet k (((z : ℂ) : RiemannSphere))) = z :=
  (f.nonpole_of_toRiemannSphere_eq_coe (R.sheet_toRiemannSphere k)).2

/-- The cluster section is continuous at `z` (cluster sheet differentiable + chart.symm continuous at
the interior target point). -/
theorem clusterSection_continuousAt (R : FibreClusterTopology Φ D Cl z) (i : D.ι)
    (j : Fin (D.mult i)) : ContinuousAt (clusterSection D Cl i j) z := by
  have hsymm_cont : ContinuousAt (chartAt ℂ (D.xs i)).symm
      (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z) :=
    (chartAt ℂ (D.xs i)).continuousAt_symm (R.clusterSheet_mem_target i j)
  exact hsymm_cont.comp (R.hsheet_diff i j).continuousAt

end FibreClusterTopology

/-- **`ClusterReindexData` from a `FibreClusterTopology`** (the reduction).  Assembles a
`ClusterReindexData` from the conservation-of-number datum, DERIVING every routine analytic field:

* `hcw` — from `hsrc` (`chart_a (chart_a.symm x) = x` on the chart target);
* `hmem_a` — `clusterSection_mem_source` (the `z`-instance of `hsrc`);
* `hcs_cont` — `clusterSection_continuousAt` (cluster sheet diff + chart.symm continuity);
* `hcsP_diff` — `clusterSection_chartPullback_differentiableAt`;
* `htrans_diff`/`htrans_diff_inv` — `transition_analyticAt_target` (the chart transitions between `D.xs
  i` and the cluster point `q`, both in each other's chart source);
* `hderiv_match` — `hderiv_match_of_section` (both `clusterSection` and `holoReprSheet (e ⟨i,j⟩)` are
  sections of `f.holoRepr` through the coincident point `q`, with the regular-value `hderiv`).

So the full-fibre cluster identity at `z` rests on *only* the bijection `e` + the point coincidence
`hpoint` + the two genuine geometric residuals `hsrc`/`hcs_sec` — the conservation-of-number content. -/
noncomputable def ClusterReindexData.ofFibreClusterTopology {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (R : FibreClusterTopology Φ D Cl z) :
    ClusterReindexData Φ D Cl z where
  S := R.S
  hderiv := R.hderiv
  hmero := R.hmero
  hcoh := R.hcoh
  e := R.e
  hpoint := R.hpoint
  hcw := by
    intro i j
    filter_upwards [R.hsrc i j] with w hw
    rw [clusterSection]
    exact (chartAt ℂ (D.xs i)).right_inv hw
  hmem_a := R.clusterSection_mem_source
  hcs_cont := R.clusterSection_continuousAt
  hcsP_diff := fun i j =>
    clusterSection_chartPullback_differentiableAt D Cl i j (R.clusterSheet_mem_target i j)
      (R.hsheet_diff i j)
  htrans_diff := by
    intro i j
    -- `chart_{D.xs i} ∘ chart_q.symm` analytic at `chart_q q` (transition target at the chart centre).
    set q : X := clusterSection D Cl i j z with hq
    have hq_src_a : q ∈ (chartAt ℂ (D.xs i)).source := R.clusterSection_mem_source i j
    exact (transition_analyticAt_target (a := q) (b := D.xs i)
      ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
      (by rw [(chartAt ℂ q).left_inv (mem_chart_source ℂ q)]; exact hq_src_a)).differentiableAt
  htrans_diff_inv := by
    intro i j
    set q : X := clusterSection D Cl i j z with hq
    have hq_src_a : q ∈ (chartAt ℂ (D.xs i)).source := R.clusterSection_mem_source i j
    exact (transition_analyticAt_target (a := D.xs i) (b := q)
      ((chartAt ℂ (D.xs i)).map_source hq_src_a)
      (by rw [(chartAt ℂ (D.xs i)).left_inv hq_src_a]; exact mem_chart_source ℂ q)).differentiableAt
  hderiv_match := by
    intro i j
    set q : X := clusterSection D Cl i j z with hq
    -- `q = S.sheet (e ⟨i,j⟩) (coe z)` (the point coincidence).
    have hqpt : q = R.S.sheet (R.e ⟨i, j⟩) (((z : ℂ) : RiemannSphere)) := R.hpoint i j
    -- The regular-value data at `q` (transported from the sphere sheet via the coincidence).
    have hq_np : 0 ≤ f.orderAtPoint q := by rw [hqpt]; exact R.sheet_nonpole _
    have hq_val : f.holoRepr q = z := by rw [hqpt]; exact R.sheet_holoRepr _
    have hreg : deriv (fun u => f.holoRepr ((chartAt ℂ q).symm u)) ((chartAt ℂ q) q) ≠ 0 := by
      rw [hqpt]; exact R.hderiv _
    -- Both sections of `f.holoRepr` through `q`; the matched sheet at `z` is `q` (coincidence).
    have hs₂z : R.S.holoReprSheet (R.e ⟨i, j⟩) z = q := by
      rw [hqpt]; rfl
    -- The cluster section continuous + a section near `z`.
    have hs₁_cont : ContinuousAt (clusterSection D Cl i j) z := R.clusterSection_continuousAt i j
    have hs₁_src : ∀ᶠ w in 𝓝 z, clusterSection D Cl i j w ∈ (chartAt ℂ q).source := by
      have := (R.clusterSection_continuousAt i j).preimage_mem_nhds
        ((chartAt ℂ q).open_source.mem_nhds (by rw [← hq]; exact mem_chart_source ℂ q))
      simpa using this
    have hs₁_sec : ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection D Cl i j w) = w := R.hcs_sec i j
    -- The sphere sheet section data (continuity + chart source + section, near `z`).
    have hs₂_cont : ContinuousAt (R.S.holoReprSheet (R.e ⟨i, j⟩)) z :=
      (R.S.holoReprSheet_contMDiffAt (R.e ⟨i, j⟩)).continuousAt
    have hs₂_src : ∀ᶠ w in 𝓝 z, R.S.holoReprSheet (R.e ⟨i, j⟩) w ∈ (chartAt ℂ q).source := by
      have := hs₂_cont.preimage_mem_nhds
        ((chartAt ℂ q).open_source.mem_nhds (by rw [← hs₂z]; exact mem_chart_source ℂ _))
      simpa using this
    have hs₂_sec : ∀ᶠ w in 𝓝 z, f.holoRepr (R.S.holoReprSheet (R.e ⟨i, j⟩) w) = w :=
      R.S.holoReprSheet_section (R.e ⟨i, j⟩)
    -- Apply the holomorphic-local-inverse uniqueness discharger.
    have hderiv := hderiv_match_of_section (s₁ := clusterSection D Cl i j)
      (s₂ := R.S.holoReprSheet (R.e ⟨i, j⟩)) (z := z)
      (by rw [← hq]; exact hq_np) (by rw [← hq]; exact hq_val) (by rw [← hq]; exact hreg)
      hs₂z hs₁_cont hs₂_cont (by rw [← hq]; exact hs₁_src) (by rw [← hq]; exact hs₂_src)
      hs₁_sec hs₂_sec
    exact hderiv

/-! ## The bijection skeleton: building `FibreClusterTopology` from a cluster→sheet embedding

The bijection `e` and the point coincidence `hpoint` are the genuine conservation-of-number content.
We package the cleanest form of that content as a **cluster→sheet assignment** `cl : (i) → Fin
(D.mult i) → Fin S.n` together with:

* `hcl_point` — each cluster sheet point IS the assigned moving sheet point (`clusterSection D Cl i j z
  = S.sheet (cl i j) (coe z)`);
* `hcl_inj` — distinct cluster `(i,j)` go to distinct sheets (the clusters are disjoint — different
  preimages are far apart, cluster sheets at one preimage are distinct by the primitive root);
* `hcard` — the **conservation of number** `∑ᵢ D.mult i = S.n` (the §4 degree identity: the `deg f`
  regular sheets partition into the per-preimage clusters of total size `∑ᵢ mᵢ`).

From these, `e := Equiv.ofBijective` of the injective+equicardinal assignment, and `hpoint` is exactly
`hcl_point` (`e ⟨i,j⟩ = cl i j` by construction).  This is the precise remaining clustering-topology
input: the assignment + its injectivity + the degree count.  Everything else is DERIVED. -/

/-- **`FibreClusterTopology` from a cluster→sheet embedding** (the bijection skeleton).  Given the
sphere sheet system data, the cluster→sheet assignment `cl` with the point coincidence `hcl_point`, its
injectivity `hcl_inj`, the conservation-of-number count `hcard : ∑ᵢ D.mult i = S.n`, and the two
genuine geometric residuals (`hsrc`, `hcs_sec`) plus the cluster sheet differentiability, the
`FibreClusterTopology` datum holds — with `e` the bijectivization of `cl` (an injection between
equicardinal finite types is a bijection) and `hpoint` exactly `hcl_point`. -/
noncomputable def FibreClusterTopology.ofClusterEmbedding {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ k, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ k, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))))
    (hcoh : valueChartTrace ω₀ f Φ z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z)
    (cl : (i : D.ι) → Fin (D.mult i) → Fin S.n)
    (hcl_point : ∀ (i : D.ι) (j : Fin (D.mult i)),
      clusterSection D Cl i j z = S.sheet (cl i j) (((z : ℂ) : RiemannSphere)))
    (hcl_inj : Function.Injective (fun p : Σ i : D.ι, Fin (D.mult i) => cl p.1 p.2))
    (hcard : ∑ i, D.mult i = S.n)
    (hsrc : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w ∈ (chartAt ℂ (D.xs i)).target)
    (hsheet_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
      DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z)
    (hcs_sec : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection D Cl i j w) = w) :
    FibreClusterTopology Φ D Cl z where
  S := S
  hderiv := hderiv
  hmero := hmero
  hcoh := hcoh
  e := by
    -- The assignment as a single function `(Σ i, Fin (mult i)) → Fin S.n`.
    refine Equiv.ofBijective (fun p : Σ i : D.ι, Fin (D.mult i) => cl p.1 p.2) ?_
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hcl_inj, ?_⟩
    rw [Fintype.card_sigma, Fintype.card_fin,
      Finset.sum_congr rfl (fun i _ => Fintype.card_fin (D.mult i)), hcard]
  hpoint := hcl_point
  hsrc := hsrc
  hsheet_diff := hsheet_diff
  hcs_sec := hcs_sec

/-! ## The minimal conservation-of-number residual: fibre points + distinctness + degree count

We refine the embedding once more, deriving the assignment `cl` and its injectivity `hcl_inj` from the
genuine geometry, so the irreducible input shrinks to **three** facts:

* `hcl_fibre` — each cluster sheet point is a genuine preimage of `coe z`
  (`f.toRiemannSphere (clusterSection D Cl i j z) = coe z`; the sphere-level form of the §5
  `clusterSheet_sect`, that the cluster sheets are preimages);
* `hcl_distinct` — the cluster sheet points are pairwise distinct
  (`Function.Injective (fun p ↦ clusterSection D Cl p.1 p.2 z)`; the clusters are disjoint);
* `hcard` — the conservation of number `∑ᵢ D.mult i = S.n`.

The assignment `cl i j` is then the unique sheet index with `S.sheet (cl i j) (coe z) = clusterSection
D Cl i j z` (existence by `S.fibre_eq`, uniqueness by `S.sheet_inj`), and `hcl_inj` follows from
`hcl_distinct` (distinct points ⟹ distinct sheets, the sheet points being injective in the index).
This is the precise remaining clustering-topology content of the whole Gate-A TARGET 1, stated
minimally. -/

/-- **`FibreClusterTopology` from the minimal conservation-of-number residual.**  Given the sphere
sheet system data, the cluster-sheet-points-are-fibre-points fact `hcl_fibre`, their pairwise
distinctness `hcl_distinct`, the conservation-of-number count `hcard`, and the two geometric residuals
(`hsrc`, `hcs_sec`) + cluster sheet differentiability, the `FibreClusterTopology` datum holds.

The cluster→sheet assignment `cl i j` is recovered as the unique sheet index over the cluster point
(`S.fibre_eq` + `S.sheet_inj`); its injectivity reduces to `hcl_distinct`.  This is the cleanest
statement of the genuine §4/§17.9 conservation-of-number / properness wall: the cluster sheets are
preimages, are distinct, and number `∑ᵢ mᵢ = deg f`. -/
noncomputable def FibreClusterTopology.ofClusterFibrePoints {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ k, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ k, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))))
    (hcoh : valueChartTrace ω₀ f Φ z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z)
    (hcl_fibre : ∀ (i : D.ι) (j : Fin (D.mult i)),
      f.toRiemannSphere (clusterSection D Cl i j z) = (((z : ℂ) : RiemannSphere)))
    (hcl_distinct : Function.Injective
      (fun p : Σ i : D.ι, Fin (D.mult i) => clusterSection D Cl p.1 p.2 z))
    (hcard : ∑ i, D.mult i = S.n)
    (hsrc : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w ∈ (chartAt ℂ (D.xs i)).target)
    (hsheet_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
      DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z)
    (hcs_sec : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection D Cl i j w) = w) :
    FibreClusterTopology Φ D Cl z := by
  classical
  -- `coe z ∈ S.V`, so the fibre `F⁻¹(coe z)` is the range of the sheet map there.
  have hfib := S.fibre_eq (((z : ℂ) : RiemannSphere)) S.mem_V
  -- Each cluster point is in the fibre, hence `= S.sheet k (coe z)` for some `k`.
  have hmem : ∀ (i : D.ι) (j : Fin (D.mult i)),
      clusterSection D Cl i j z ∈ Set.range (fun k => S.sheet k (((z : ℂ) : RiemannSphere))) := by
    intro i j
    rw [← hfib]; exact hcl_fibre i j
  -- The assignment `cl i j := the chosen sheet index`.
  set cl : (i : D.ι) → Fin (D.mult i) → Fin S.n :=
    fun i j => (hmem i j).choose with hcl_def
  have hcl_point : ∀ (i : D.ι) (j : Fin (D.mult i)),
      clusterSection D Cl i j z = S.sheet (cl i j) (((z : ℂ) : RiemannSphere)) :=
    fun i j => (hmem i j).choose_spec.symm
  -- Injectivity of `cl` from the point distinctness (the sheet points are injective in the index).
  have hcl_inj : Function.Injective (fun p : Σ i : D.ι, Fin (D.mult i) => cl p.1 p.2) := by
    intro p q hpq
    apply hcl_distinct
    show clusterSection D Cl p.1 p.2 z = clusterSection D Cl q.1 q.2 z
    rw [hcl_point p.1 p.2, hcl_point q.1 q.2]
    show S.sheet (cl p.1 p.2) _ = S.sheet (cl q.1 q.2) _
    rw [show (fun p : Σ i : D.ι, Fin (D.mult i) => cl p.1 p.2) p = cl p.1 p.2 from rfl,
      show (fun p : Σ i : D.ι, Fin (D.mult i) => cl p.1 p.2) q = cl q.1 q.2 from rfl] at hpq
    rw [hpq]
  exact FibreClusterTopology.ofClusterEmbedding S hderiv hmero hcoh cl hcl_point hcl_inj hcard
    hsrc hsheet_diff hcs_sec

/-! ## Soundness: the datum genuinely encodes conservation of number (multi-preimage, not vacuous)

The decisive #13-style check.  A `FibreClusterTopology`'s bijection field `e` forces the
conservation-of-number identity `∑ᵢ D.mult i = S.n` (`= deg f`), so the datum is genuinely
multi-preimage — not a disguised single-preimage placeholder or a vacuous triviality.  The minimal
constructor `ofClusterFibrePoints` accepts *any* `hcard : ∑ᵢ D.mult i = S.n` with ramified
multiplicities (several preimages with `mᵢ > 1`), confirming the wall is the genuine multi-cluster
content. -/

/-- **Conservation of number, encoded by the topology datum.**  A `FibreClusterTopology` forces
`∑ᵢ D.mult i = R.S.n` (`= deg f`): the bijection `e` of the cluster `Σ`-index with the `deg f` sheets
has matching `Fintype.card`.  Confirms the datum is genuinely multi-preimage, not vacuous. -/
theorem FibreClusterTopology.sum_mult_eq_sheetCount {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (R : FibreClusterTopology Φ D Cl z) :
    ∑ i, D.mult i = R.S.n :=
  ClusterReindexData.sum_mult_eq_sheetCount (ClusterReindexData.ofFibreClusterTopology R)

/-! ## Wiring the full chain: `FibreClusterTopology` family ⟹ `FibreClusterReindex` ⟹ `∑Res = 0`

Composing `ClusterReindexData.ofFibreClusterTopology` with the PROVEN
`FibreClusterReindex.ofClusterReindexFamily` (`SerreResidueRamifiedClusterPartition.lean`), a slit-wide
family of `FibreClusterTopology` discharges the whole per-centre `FibreClusterReindex` — i.e. building
the cover's `FibreClusterReindex` reduces to supplying, at each slit value, the conservation-of-number
datum (bijection + coincidence + the geometric residuals), or — via `ofClusterFibrePoints` — the three
minimal facts (cluster sheets are distinct fibre points numbering `deg f`). -/

/-- **`FibreClusterReindex` from a slit-wide family of `FibreClusterTopology`.**  The full reduction:
the per-centre fibre-cluster reindexing follows from the routine bookkeeping plus a `FibreClusterTopology`
at every slit value `z` (the conservation-of-number datum).  Discharges `hgeom_fibre` pointwise by
`ClusterReindexData.ofFibreClusterTopology` ∘ `valueChartTrace_eq_clusterSum_of_clusterReindexData`. -/
noncomputable def FibreClusterReindex.ofFibreClusterTopologyFamily {ω₀ : HolomorphicOneForms X}
    {g : X → ℂ} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X}
    {c : ℂ} {Sset : Set ℂ}
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) z)
    (D : FibreRamifiedData g f c) (hD_inj : Function.Injective D.xs)
    (hD_mem : ∀ i, D.xs i ∈ poles)
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
    FibreClusterReindex ω₀ g f hdiv poles c :=
  FibreClusterReindex.ofClusterReindexFamily hanalytic D hD_inj hD_mem hD_surj hS_acc Cl hmult
    hsplit0 ppord hbnd (fun z hz => ClusterReindexData.ofFibreClusterTopology (hfam z hz))

/-- **Gate A `∑Res = 0` from per-centre `FibreClusterTopology` families** (the precise residual
exhibited).  For a genuine meromorphic numerator `g`, an `AdaptedFRamified` datum `A`, and at each finite
pole-value centre a per-centre `FibreClusterReindex` (e.g. built via
`FibreClusterReindex.ofFibreClusterTopologyFamily` from a slit-wide family of `FibreClusterTopology`),
the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This anchors the conservation-of-number datum to the Gate-A goal: the *only* genuinely-remaining content
is the per-centre `FibreClusterTopology` — and, via `ofClusterFibrePoints`, exactly the three minimal
clustering facts (cluster sheets are distinct fibre points numbering `deg f`). -/
theorem residueSum_eq_zero_of_fibreClusterTopology {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, FibreClusterReindex ω₀ g.toFun A.f A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_clusterReindex A R

end Jacobians.Dolbeault.SerreResidueTheorem
