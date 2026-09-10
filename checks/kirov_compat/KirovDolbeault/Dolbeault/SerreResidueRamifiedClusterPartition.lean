/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedFullFibreBuilder
import KirovDolbeault.Dolbeault.SerreResidueRamifiedMultiplicityBridge
import KirovDolbeault.Dolbeault.SerreResidueGateAInftyBuilder

/-!
# The fibre-cluster partition: reducing `FibreClusterReindex.hgeom_fibre` to the bijection (TARGET 1)

`FibreClusterReindex.hgeom_fibre` (`SerreResidueRamifiedFullFibreBuilder.lean`) is the single
genuinely-remaining geometric input of the `hoff_cs`-free Gate-A residue route.  On the slit near a
finite pole-value centre `c`, it asks for

> `valueChartTrace ω₀ f Φ z = ∑ᵢ ∑_{j<mᵢ} chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s … j z)
>     · deriv (clusterSheet (Cl i).s … j z)`,

the full-fibre cluster identity.  This file **reduces that identity to exactly the
conservation-of-number bijection** — the precise multi-hundred-LoC topological wall — by reusing the
PROVEN machinery:

* `valueChartTrace_eq_sphereSheetFibreTrace` (`FormTraceBundleBridge.lean`) — at a regular slit value
  `z`, the geometric trace equals the `traceCoeff` of the **whole** sphere fibre `F⁻¹(coe z)`
  (`LocalSheetSystem S` of `deg f` moving sheets);
* `fibreTrace_eventuallyEq_movingSum` (`FormTraceMovingFibre.lean`) — that `traceCoeff` reads, AT `z`,
  as the moving fibre sum `∑ₖ chartIntegrand ω₀ g (S.sheet k (coe z)) … · deriv …` along the sheets
  `holoReprSheet`;
* `movingSummand_chartIndep` (`FormTraceMovingFibre.lean`) — the source-chart independence of each
  summand (Miranda §VIII.3's "the trace is a well-defined form").

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`valueChartTrace_eq_clusterSum_of_reindex`** — the **pure-reindexing reduction** of `hgeom_fibre`:
  given (i) the regular-value sphere coherence at `z`, (ii) a bijection `e : (Σ i, Fin (D.mult i)) ≃
  Fin S.n` of the cluster `Σ`-index with the sphere sheets, and (iii) the per-`(i,j)` summand equality
  matching the cluster summand to the `e ⟨i,j⟩`-th moving summand, the full-fibre cluster identity holds.
  This is the combinatorial spine: it turns the whole-fibre moving sum into the per-preimage cluster
  double sum.

* **`ClusterReindexData`** — the **precise remaining clustering datum** at a regular slit value `z`,
  isolating exactly the conservation-of-number content: the sphere sheet system `S` (with the
  regular-value `hderiv`/`hmero`), the bijection `e`, and the **point coincidence**
  `clusterSheet … j z` is the `D.xs i`-chart coordinate of the moving sheet point `S.sheet (e ⟨i,j⟩)
  (coe z)`, together with the differentiability data feeding the chart-reconciliation.

* **`clusterSummand_eq_sphereSummand`** — the per-`(i,j)` chart reconciliation: the fixed-preimage
  cluster summand equals the moving sphere summand at the coincident point (via `movingSummand_chartIndep`
  + the section-derivative agreement).

* **`valueChartTrace_eq_clusterSum_of_sphereReindex`** — the moving-sheet form of the reduction (working
  directly with a sphere sheet system `S` at `coe z`, the `holoReprSheet` moving sum).

* **`ClusterReindexData`** + **`valueChartTrace_eq_clusterSum_of_clusterReindexData`** — the **precise
  remaining clustering datum** at a regular slit value `z` (the sphere system, the bijection `e`, the
  point coincidence, the differentiability + section-derivative agreement) and the discharge of
  `hgeom_fibre` at `z` from it: the chart reconciliation is proven, so this consumes only the bijection +
  coincidence (the genuine wall).

* **`FibreClusterReindex.ofClusterReindexFamily`** — builds the whole per-centre `FibreClusterReindex`
  (the input `residueSum_eq_zero_of_reindex_adaptedFRamified` consumes) from the routine fields + a
  slit-wide family `∀ z ∈ Sset, ClusterReindexData …`.

* **`ClusterReindexData.sum_mult_eq_sheetCount`** / **`hderiv_match_of_section`** — the soundness facts
  (the bijection forces `∑ᵢ mᵢ = deg f`; the section-derivative agreement is derivable).

* **`residueSum_eq_zero_of_clusterReindex`** — the Gate-A capstone: `∑Res = 0` from `AdaptedFRamified`
  (TARGET 2, discharged) + per-centre `FibreClusterReindex` (TARGET 1).

So `FibreClusterReindex.hgeom_fibre` is reduced, for the real cover, to **exactly** the
conservation-of-number bijection between the `deg f` moving sheets of a nearby regular fibre and the
per-preimage clusters — the genuine §VIII.3/Forster §4–5 finite-cover clustering topology, with every
algebraic/chart-reconciliation step PROVEN.

## ⚠ Soundness

The reduction is sound: `ClusterReindexData` carries the **genuine** geometric data (the real sphere
sheet system, the genuine `clusterSheet` points, a genuine bijection), supplied as data exactly as
`RamifiedSheetData`/`FullFibreClusterData` supply their geometric fields — never asserted, no
false/junk/circular field, no custom axiom.  The per-summand equality is DERIVED from the proven
chart-reconciliation (`clusterSummand_eq_sphereSummand`), not assumed.  Two soundness facts confirm the
structure is genuine and not single-preimage:

* `ClusterReindexData.sum_mult_eq_sheetCount` — the bijection field **forces** the conservation-of-number
  identity `∑ᵢ D.mult i = S.n` (`= deg f`); the structure is therefore meaningfully multi-preimage, not a
  disguised single-preimage placeholder, and its `e`/`hpoint` fields carry genuine content.
* `hderiv_match_of_section` — the `hderiv_match` field is **derivable** (holomorphic-local-inverse
  uniqueness), so the only irreducible fields are the bijection `e` and the point coincidence `hpoint`
  (the genuine §17.9/Forster §4 conservation-of-number / properness topology).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5 (sheets / normal form / properness).
* `FormTraceBundleBridge.lean` (`valueChartTrace_eq_sphereSheetFibreTrace`),
  `FormTraceMovingFibre.lean` (`fibreTrace_eventuallyEq_movingSum`, `movingSummand_chartIndep`),
  `FormTraceSheetFibreBridge.lean` (`eventuallyEq_of_rightInverse_of_rightInverse`),
  `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`).
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

/-! ## The pure-reindexing reduction (the combinatorial spine)

`valueChartTrace_eq_sphereSheetFibreTrace` writes the geometric trace at a regular slit value `z` as a
sum over the whole sphere fibre `F⁻¹(coe z)` — `(fibreTrace ω₀ f (ofSphereSheetSystem S …)).traceCoeff
z`, a single sum over the `deg f` moving sheets `Fin S.n`.  The full-fibre cluster identity rewrites
this as the **double** sum over preimages × cluster index `Σ i, Fin (D.mult i)`.  The two index sets
have the same cardinality (conservation of number: `∑ᵢ mᵢ = deg f`), and the bijection `e` matches each
cluster sheet to a moving sheet.  Given the matching, the reduction is a pure reindexing. -/

/-- **Pure-reindexing reduction of the full-fibre cluster identity.**  Let `D : FibreRamifiedData g f c`
be the pole fibre, `Cl i : ClusterTraceData ω₀ g (D.xs i) c S` the per-preimage cluster data, and at a
slit value `z` let `T : FibreTrace` be any sphere-fibre trace with `valueChartTrace ω₀ f Φ z =
T.traceCoeff z` (the regular-value sphere coherence).  Given a bijection `e : (Σ i, Fin (D.mult i)) ≃
T.ι` of the cluster `Σ`-index with the sheets, and the per-`(i,j)` summand equality matching the cluster
summand to the `e ⟨i,j⟩`-th sheet summand of `T.traceCoeff`, the full-fibre cluster identity holds at
`z`:

> `valueChartTrace ω₀ f Φ z = ∑ᵢ ∑_{j<mᵢ} chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s … j z)
>     · deriv (clusterSheet (Cl i).s … j z)`.

*Proof.*  `T.traceCoeff z = ∑ₖ T.coeff k (T.sheet k z)·deriv (T.sheet k) z`; reindex the `∑ₖ` along `e⁻¹`
into a `Σ`-sum, then the summand equality identifies each `e ⟨i,j⟩`-summand with the cluster summand;
flatten `Σ i, Fin (D.mult i)` into the `∑ᵢ ∑_{j ∈ range (mult i)}` double sum. -/
theorem valueChartTrace_eq_clusterSum_of_reindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {S : Set ℂ}
    (D : FibreRamifiedData g f c) (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c S) {z : ℂ}
    (T : FibreTrace)
    (hcoh : valueChartTrace ω₀ f Φ z = T.traceCoeff z)
    (e : (Σ i : D.ι, Fin (D.mult i)) ≃ T.ι)
    (hsummand : ∀ (i : D.ι) (j : Fin (D.mult i)),
      T.coeff (e ⟨i, j⟩) (T.sheet (e ⟨i, j⟩) z) * deriv (T.sheet (e ⟨i, j⟩)) z
        = chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    valueChartTrace ω₀ f Φ z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z := by
  classical
  rw [hcoh]
  -- `T.traceCoeff z = ∑ₖ (sheet summand k)`; reindex `∑ₖ` along `e : (Σ i, Fin (mult i)) ≃ T.ι`.
  show (∑ k, T.coeff k (T.sheet k z) * deriv (T.sheet k) z) = _
  rw [← Equiv.sum_comp e (fun k => T.coeff k (T.sheet k z) * deriv (T.sheet k) z)]
  -- The `Σ`-sum over `(Σ i, Fin (mult i))` flattens to the `∑ᵢ ∑_{j : Fin (mult i)}` double sum.
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  -- Per outer `i`, convert the inner `Fin (mult i)`-sum to the `range (mult i)`-sum and match.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_range fun j => chartIntegrand ω₀ g (D.xs i)
      (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
    * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z]
  exact Finset.sum_congr rfl (fun j _ => hsummand i j)

/-! ## The per-summand chart reconciliation (Miranda §VIII.3 well-definedness)

The pure-reindexing reduction's per-`(i,j)` summand match equates the cluster summand (read in the
**fixed preimage** `D.xs i`'s chart) with the moving sphere summand (read in the **moving sheet point**'s
own chart, along the section `holoReprSheet k`).  Both are pushforwards of `α = ω₀·g` along a local
section of `f` through the *same* fibre point `q = S.sheet k (coe z)`; they agree by the source-chart
independence of the trace summand (`movingSummand_chartIndep`) once the two sections germ-agree (both are
holomorphic right-inverses of `f`'s chart-pullback through `q`).  This is the §VIII.3 fact that "the
trace `Tr_F α` is a well-defined form", applied at the cluster.

We isolate the reconciliation as a standalone lemma taking the genuine geometric residuals as
hypotheses: the point coincidence (`cs z = q`), the section-derivative agreement (`deriv (chart_q ∘ cs) z
= deriv (chart_q ∘ holoReprSheet k) z`, the holomorphic-local-inverse uniqueness), and the
differentiability data feeding `movingSummand_chartIndep`. -/

/-- **Per-summand chart reconciliation at a cluster point.**  Let `q := S.sheet k (coe z)` be a sphere
sheet point at the regular slit value `z`, and `cs : ℂ → X` a local section of `f` through `q` with
`cs z = q` and chart coordinate `chart_{a} (cs w) = cw w` near `z` (so `cw z = chart_a q`), where `a` is
the fixed preimage chart base.  Then the **fixed-preimage cluster summand** equals the **moving sphere
summand**:

> `chartIntegrand ω₀ g a (cw z)·deriv cw z
>    = chartIntegrand ω₀ g q (chart_q (holoReprSheet k z))·deriv (fun w => chart_q (holoReprSheet k w)) z`,

given: `q ∈ chart_a.source`; `cs` continuous at `z`; the chart-pullbacks `chart_q ∘ cs`, `chart_a ∘ cs`
differentiable at `z`; the two chart transitions (`a ↔ q`) differentiable both ways; and the
section-derivative agreement `deriv (chart_q ∘ cs) z = deriv (chart_q ∘ holoReprSheet k) z` (the
holomorphic-local-inverse uniqueness, both sections being right-inverses of `f` through `q`).  Pure
chart algebra: rewrite the cluster summand as the `a`-chart `movingSummand` of `cs`, apply
`movingSummand_chartIndep` to switch to the `q`-chart, then the section-derivative agreement. -/
theorem clusterSummand_eq_sphereSummand (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (k : Fin S.n) (a : X) (cs : ℂ → X) (cw : ℂ → ℂ)
    (hq : cs z = S.sheet k (((z : ℂ) : RiemannSphere)))
    (hcw : ∀ᶠ w in 𝓝 z, (chartAt ℂ a) (cs w) = cw w)
    (hmem_a : cs z ∈ (chartAt ℂ a).source)
    (hcs_cont : ContinuousAt cs z)
    (hcsP_diff : DifferentiableAt ℂ (fun w => (chartAt ℂ (cs z)) (cs w)) z)
    (htrans_diff_a : DifferentiableAt ℂ
      (fun w => (chartAt ℂ a) ((chartAt ℂ (cs z)).symm w)) ((chartAt ℂ (cs z)) (cs z)))
    (htrans_diff_inv_a : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (cs z)) ((chartAt ℂ a).symm w)) ((chartAt ℂ a) (cs z)))
    (hderiv_match : deriv (fun w => (chartAt ℂ (cs z)) (cs w)) z
      = deriv (fun w => (chartAt ℂ (cs z)) (S.holoReprSheet k w)) z) :
    chartIntegrand ω₀ g a (cw z) * deriv cw z
      = chartIntegrand ω₀ g (S.sheet k (((z : ℂ) : RiemannSphere)))
          ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet k z))
        * deriv (fun w => (chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet k w)) z := by
  classical
  -- Abbreviate `q := cs z = S.sheet k (coe z) = holoReprSheet k z`.
  set q : X := cs z with hqdef
  -- (1) Rewrite the cluster summand into the `a`-chart `movingSummand` of the section `cs`.
  -- `cw z = chart_a (cs z)` and `deriv cw z = deriv (chart_a ∘ cs) z` (congr via `hcw`).
  have hcwz : cw z = (chartAt ℂ a) (cs z) := (hcw.self_of_nhds).symm
  have hderiv_cw : deriv cw z = deriv (fun w => (chartAt ℂ a) (cs w)) z :=
    Filter.EventuallyEq.deriv_eq (hcw.mono (fun w h => h.symm))
  rw [hcwz, hderiv_cw]
  -- (2) Self-chart transition `chart_q ∘ chart_q.symm =ᶠ id` is differentiable (for `chartIndep`).
  have hself_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ q) ((chartAt ℂ q).symm w)) ((chartAt ℂ q) q) := by
    have heqid : (fun w => (chartAt ℂ q) ((chartAt ℂ q).symm w))
        =ᶠ[𝓝 ((chartAt ℂ q) q)] id := by
      filter_upwards [(chartAt ℂ q).open_target.mem_nhds
        ((chartAt ℂ q).map_source (mem_chart_source ℂ q))] with w hw
      simp only [(chartAt ℂ q).right_inv hw, id_eq]
    exact differentiableAt_id.congr_of_eventuallyEq heqid
  -- (3) `movingSummand_chartIndep` (section `cs`, charts `a` and `q`): switch to the `q`-chart.
  have hindep := movingSummand_chartIndep ω₀ g cs a q hcs_cont hcsP_diff hmem_a
    (mem_chart_source ℂ q) htrans_diff_a hself_diff htrans_diff_inv_a hself_diff
  -- `hindep : (a-chart summand of cs) = (q-chart summand of cs)`.
  rw [hindep]
  -- (4) The `q`-chart summand of `cs` equals the `q = S.sheet k (coe z)`-chart summand of
  -- `holoReprSheet k`: `cs z = q = S.sheet k (coe z) = holoReprSheet k z`, so the `chartIntegrand`
  -- arguments and the chart match (rewrite `q` via `hq`); the section derivs match (`hderiv_match`).
  have hcs_eq : cs z = S.holoReprSheet k z := hq
  rw [hderiv_match, hcs_eq, hq]

/-! ## The sphere-based reduction (moving-sheet form)

Composing the pure reindexing with the moving-sheet form of the sphere-fibre trace
(`fibreTrace_eventuallyEq_movingSum` at `z`, along `holoReprSheet`), we obtain `hgeom_fibre` at `z`
directly from a sphere sheet system `S` at `coe z`, a bijection `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`,
and the per-`(i,j)` summand match **in the moving (holoReprSheet) form** — exactly what
`clusterSummand_eq_sphereSummand` produces. -/

/-- **The full-fibre cluster identity from a sphere sheet system + bijection (moving-sheet form).**  At
a regular slit value `z` with a sphere sheet system `S` of `F = f.toRiemannSphere` at `coe z` (regular
fibre — `hderiv`, `hmero`), the regular-value coherence
`valueChartTrace ω₀ f Φ z = (fibreTrace ω₀ f (ofSphereSheetSystem S …)).traceCoeff z`, a bijection
`e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`, and the per-`(i,j)` summand equality matching the cluster summand
to the `e ⟨i,j⟩`-th **moving (holoReprSheet) summand**, the full-fibre cluster identity holds at `z`.

*Proof.*  Rewrite the coherence's RHS via `fibreTrace_eventuallyEq_movingSum` (at `z`, sections
`holoReprSheet`) into the moving fibre sum `∑ₖ chartIntegrand ω₀ g (S.sheet k (coe z)) …·deriv …`, then
apply `valueChartTrace_eq_clusterSum_of_reindex` with `T` the moving sum (packaged as the trivial
`FibreTrace` whose `traceCoeff` *is* that sum) — i.e. directly reindex the moving sum. -/
theorem valueChartTrace_eq_clusterSum_of_sphereReindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    (D : FibreRamifiedData g f c) (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset) {z : ℂ}
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
    (e : (Σ i : D.ι, Fin (D.mult i)) ≃ Fin S.n)
    (hsummand : ∀ (i : D.ι) (j : Fin (D.mult i)),
      chartIntegrand ω₀ g (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere)))
          ((chartAt ℂ (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet (e ⟨i, j⟩) z))
        * deriv (fun w => (chartAt ℂ (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet (e ⟨i, j⟩) w)) z
        = chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    valueChartTrace ω₀ f Φ z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z := by
  classical
  -- The moving-sheet form of the sphere-fibre trace at `z` (sections `holoReprSheet`).
  set D' := FibreRegularData.ofSphereSheetSystem S hderiv hmero with hD'
  have hmoving : (fibreTrace ω₀ f D').traceCoeff z
      = ∑ k, chartIntegrand ω₀ g (D'.xs k) ((chartAt ℂ (D'.xs k)) (S.holoReprSheet k z))
        * deriv (fun w => (chartAt ℂ (D'.xs k)) (S.holoReprSheet k w)) z :=
    (fibreTrace_eventuallyEq_movingSum ω₀ f D' (fun k => S.holoReprSheet k)
      (fun _ => rfl) (fun k => (S.holoReprSheet_contMDiffAt k).continuousAt)
      (fun k => S.holoReprSheet_section k)).self_of_nhds
  -- The moving summand as a function `F : Fin S.n → ℂ`.
  set F : Fin S.n → ℂ := fun k => chartIntegrand ω₀ g (D'.xs k)
      ((chartAt ℂ (D'.xs k)) (S.holoReprSheet k z))
    * deriv (fun w => (chartAt ℂ (D'.xs k)) (S.holoReprSheet k w)) z with hF
  rw [hcoh, hmoving]
  -- (a) Flatten the cluster double sum to a single `Σ`-sum, matching each term to `F (e ⟨i,j⟩)`.
  have hRHS : (∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z)
      = ∑ p : (Σ i : D.ι, Fin (D.mult i)), F (e p) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_range fun j => chartIntegrand ω₀ g (D.xs i)
        (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
      * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z]
    exact Finset.sum_congr rfl (fun j _ => (hsummand i j).symm)
  rw [hRHS]
  -- (b) Reindex the moving sum `∑ k, F k` along `e : (Σ…) ≃ Fin S.n`.
  exact (Fintype.sum_equiv e (fun p => F (e p)) F (fun _ => rfl)).symm

/-! ## The precise remaining clustering datum `ClusterReindexData`

We now isolate the **genuine remaining content** of `FibreClusterReindex.hgeom_fibre` at a single
regular slit value `z` as a named datum, with the chart-reconciliation half DISCHARGED.  Its fields are
exactly the conservation-of-number content: a sphere sheet system `S` at `coe z` (with the regular-value
`hderiv`/`hmero` and the coherence `hcoh`), the **bijection** `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`
between the cluster `Σ`-index and the `deg f` sphere sheets, the **point coincidence** that each cluster
sheet point is the matched moving sheet point, and the routine analytic data feeding the
chart-reconciliation (the cluster section's differentiability + the section-derivative agreement, the
holomorphic-local-inverse uniqueness).  From it we prove `hgeom_fibre` at `z`.

The cluster section at preimage `i`, cluster index `j` is `clusterSection D i j Cl :=
fun w ↦ chart_{D.xs i}.symm (clusterSheet (Cl i).s … j w)` — the genuine `clusterSheet` point, lifted to
`X` through the chart at the fixed preimage `D.xs i`. -/

/-- The cluster section at preimage `i`, cluster index `j`: `w ↦ chart_{D.xs i}.symm (clusterSheet
(Cl i).s (Cl i).ζ (Cl i).w₀ j w)`, the genuine `clusterSheet` point lifted to `X`. -/
noncomputable def clusterSection {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
    {c : ℂ} {Sset : Set ℂ} (D : FibreRamifiedData g f c)
    (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset) (i : D.ι) (j : Fin (D.mult i)) : ℂ → X :=
  fun w => (chartAt ℂ (D.xs i)).symm (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w)

/-- **The precise remaining clustering datum at a regular slit value `z`** (the genuine
conservation-of-number content, chart-reconciliation discharged).  At `z`, a sphere sheet system `S` of
`F = f.toRiemannSphere` at `coe z` with the regular-value coherence, a bijection `e : (Σ i,
Fin (D.mult i)) ≃ Fin S.n`, and, for each preimage `i` and cluster index `j` (writing
`q := S.sheet (e ⟨i,j⟩) (coe z)` and `cs := clusterSection D Cl i j`):

* `hpoint` — the **point coincidence**: `cs z = q` (the `j`-th cluster sheet at `i` *is* the
  `e ⟨i,j⟩`-th moving sheet point — the conservation-of-number content);
* `hcw` — `chart_{D.xs i} (cs w) = clusterSheet (Cl i).s … j w` near `z` (the cluster point stays in
  `D.xs i`'s chart source);
* the differentiability data `hmem_a`/`hcs_cont`/`hcsP_diff`/`htrans_diff`/`htrans_diff_inv` (routine
  analyticity of `clusterSheet` + the chart transitions);
* `hderiv_match` — the **section-derivative agreement** `deriv (chart_q ∘ cs) z = deriv (chart_q ∘
  holoReprSheet (e ⟨i,j⟩)) z` (the holomorphic-local-inverse uniqueness: both `cs` and `holoReprSheet
  (e ⟨i,j⟩)` are right-inverses of `f` through `q`).

This is the single residual the `hoff_cs`-free Gate-A route still needs at each slit value; everything
else (the residue calculus, the per-cluster collapse, the meromorphy reduction, the off-centre/∞
machinery, the chart reconciliation) is PROVEN. -/
structure ClusterReindexData {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
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
  /-- The cluster point stays in the fixed preimage's chart source: `chart_{D.xs i}(cs w) =
  clusterSheet … j w` near `z`. -/
  hcw : ∀ (i : D.ι) (j : Fin (D.mult i)),
    ∀ᶠ w in 𝓝 z, (chartAt ℂ (D.xs i)) (clusterSection D Cl i j w)
      = clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w
  /-- The cluster point lies in `D.xs i`'s chart source. -/
  hmem_a : ∀ (i : D.ι) (j : Fin (D.mult i)),
    clusterSection D Cl i j z ∈ (chartAt ℂ (D.xs i)).source
  /-- The cluster section is continuous at `z`. -/
  hcs_cont : ∀ (i : D.ι) (j : Fin (D.mult i)), ContinuousAt (clusterSection D Cl i j) z
  /-- The self-chart pullback of the cluster section is differentiable at `z`. -/
  hcsP_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
    DifferentiableAt ℂ (fun w => (chartAt ℂ (clusterSection D Cl i j z))
      (clusterSection D Cl i j w)) z
  /-- The chart transition `chart_{D.xs i} ∘ chart_{cs z}.symm` is differentiable at the cluster point. -/
  htrans_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
    DifferentiableAt ℂ
      (fun w => (chartAt ℂ (D.xs i)) ((chartAt ℂ (clusterSection D Cl i j z)).symm w))
      ((chartAt ℂ (clusterSection D Cl i j z)) (clusterSection D Cl i j z))
  /-- The inverse chart transition `chart_{cs z} ∘ chart_{D.xs i}.symm` is differentiable. -/
  htrans_diff_inv : ∀ (i : D.ι) (j : Fin (D.mult i)),
    DifferentiableAt ℂ
      (fun w => (chartAt ℂ (clusterSection D Cl i j z)) ((chartAt ℂ (D.xs i)).symm w))
      ((chartAt ℂ (D.xs i)) (clusterSection D Cl i j z))
  /-- **Section-derivative agreement** (holomorphic-local-inverse uniqueness): the cluster section and
  the matched moving sheet `holoReprSheet (e ⟨i,j⟩)` have the same self-chart-pullback derivative at `z`
  (both are right-inverses of `f` through the coincident point). -/
  hderiv_match : ∀ (i : D.ι) (j : Fin (D.mult i)),
    deriv (fun w => (chartAt ℂ (clusterSection D Cl i j z)) (clusterSection D Cl i j w)) z
      = deriv (fun w => (chartAt ℂ (clusterSection D Cl i j z))
          (S.holoReprSheet (e ⟨i, j⟩) w)) z

/-- **`hgeom_fibre` at `z` from a `ClusterReindexData`.**  The full-fibre cluster identity at the regular
slit value `z` follows from the clustering datum: the per-`(i,j)` summand match is discharged by the
chart reconciliation (`clusterSummand_eq_sphereSummand`, using the point coincidence + the
section-derivative agreement + the differentiability), and the reindexing is
`valueChartTrace_eq_clusterSum_of_sphereReindex`.  This consumes **only** the conservation-of-number
bijection + point coincidence (the genuine wall); the chart algebra is PROVEN. -/
theorem valueChartTrace_eq_clusterSum_of_clusterReindexData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (R : ClusterReindexData Φ D Cl z) :
    valueChartTrace ω₀ f Φ z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z := by
  refine valueChartTrace_eq_clusterSum_of_sphereReindex D Cl R.S R.hderiv R.hmero R.hcoh R.e
    (fun i j => ?_)
  -- Per-`(i,j)`: the moving summand equals the cluster summand (chart reconciliation).
  exact (clusterSummand_eq_sphereSummand ω₀ g R.S (R.e ⟨i, j⟩) (D.xs i)
    (clusterSection D Cl i j) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j)
    (R.hpoint i j) (R.hcw i j) (R.hmem_a i j) (R.hcs_cont i j) (R.hcsP_diff i j)
    (R.htrans_diff i j) (R.htrans_diff_inv i j) (R.hderiv_match i j)).symm

/-! ## Building `FibreClusterReindex` from a slit-wide family of clustering data

The `FibreClusterReindex` structure (`SerreResidueRamifiedFullFibreBuilder.lean`) — the precise input
the `hoff_cs`-free Gate-A capstone `residueSum_eq_zero_of_reindex` consumes — has, besides the routine
bookkeeping (`hanalytic`/`hD_*`/`hS_acc`/`hmult`/`hsplit0`/`ppord`/`hbnd`), the single hard field
`hgeom_fibre`.  We discharge `hgeom_fibre` from a **slit-wide family** of `ClusterReindexData` (one per
slit value `z`), so building the cover's `FibreClusterReindex` reduces to supplying that family — i.e.,
at each slit value, the conservation-of-number bijection + point coincidence (the genuine wall). -/

/-- **`FibreClusterReindex` from a slit-wide family of `ClusterReindexData`.**  Given the pole fibre `D`
(injective, enumerating the `α`-poles of the fibre), the per-preimage cluster data `Cl` on the slit
`Sset` (with matching multiplicity + the residue split), the eventual off-centre analyticity, the slit
accumulation, the finite pole-order bound, **and** a `ClusterReindexData` at every slit value `z`
(the conservation-of-number bijection + point coincidence), the per-centre fibre-cluster reindexing
`FibreClusterReindex` holds.  The hard `hgeom_fibre` field is discharged pointwise on the slit by
`valueChartTrace_eq_clusterSum_of_clusterReindexData`; all other fields are passed through. -/
noncomputable def FibreClusterReindex.ofClusterReindexFamily {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {c : ℂ}
    {Sset : Set ℂ}
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
    (hfam : ∀ z ∈ Sset, ClusterReindexData (canonicalFibreSelection g f hdiv) D Cl z) :
    FibreClusterReindex ω₀ g f hdiv poles c where
  hanalytic := hanalytic
  D := D
  hD_inj := hD_inj
  hD_mem := hD_mem
  hD_surj := hD_surj
  S := Sset
  hS_acc := hS_acc
  Cl := Cl
  hmult := hmult
  hsplit0 := hsplit0
  ppord := ppord
  hbnd := hbnd
  hgeom_fibre := fun z hz =>
    valueChartTrace_eq_clusterSum_of_clusterReindexData (hfam z hz)

/-! ## Soundness: `ClusterReindexData` genuinely encodes conservation of number

The decisive #13-style check on the new datum: its bijection field `e` is **not** a vacuous or
single-preimage placeholder — it forces the conservation-of-number identity `∑ᵢ mᵢ = deg f`
(`= S.n`, the number of sphere sheets).  A `ClusterReindexData` at a genuinely ramified fibre (several
preimages with multiplicities `> 1`) is therefore exactly a witness that the `deg f` moving sheets
partition into the per-preimage clusters of total size `∑ᵢ mᵢ` — the genuine §17.9/Forster §4
conservation-of-number content, not a disguised triviality. -/

/-- **Conservation of number, encoded by the clustering datum.**  A `ClusterReindexData` forces the
total cluster multiplicity to equal the sheet count `S.n` (`= deg f`):

> `∑ᵢ D.mult i = R.S.n`.

This is `Fintype.card` of the bijection `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`
(`card (Σ i, Fin (mult i)) = ∑ᵢ mult i`, `card (Fin S.n) = S.n`).  It confirms the bijection field is
the genuine conservation-of-number content — no single-preimage restriction, not a vacuous placeholder. -/
theorem ClusterReindexData.sum_mult_eq_sheetCount {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (R : ClusterReindexData Φ D Cl z) :
    ∑ i, D.mult i = R.S.n := by
  have hcard := Fintype.card_congr R.e
  rwa [Fintype.card_sigma, Fintype.card_fin, Finset.sum_congr rfl (fun i _ => Fintype.card_fin (D.mult i))]
    at hcard

/-! ## The section-derivative agreement is DERIVABLE (holomorphic-local-inverse uniqueness)

The `hderiv_match` field of `ClusterReindexData` is **not** an extra assumption: it is the genuine fact
that two holomorphic local sections of `f` through the *same* fibre point germ-agree (uniqueness of the
holomorphic local inverse).  We isolate the discharger, so `hderiv_match` reduces to the two sections
being genuine local sections of `f.holoRepr` through the coincident point `q` (the `clusterSection`
section property is `clusterSheet_sect`; the `holoReprSheet` one is `holoReprSheet_section`).  This
confirms the only irreducible fields of `ClusterReindexData` are the **bijection** and the **point
coincidence** (the conservation-of-number content). -/

/-- **The section-derivative agreement from the two right-inverse properties** (holomorphic-local-inverse
uniqueness).  Let `q := s₁ z` be a regular non-pole with `f.holoRepr q = z` (so the chart-pullback
`φ = f.holoRepr ∘ chart_q.symm` is analytic at `chart_q q` with nonzero derivative).  If two sections
`s₁ s₂ : ℂ → X` both pass through `q` at `z` (`s₁ z = q = s₂ z`), are continuous at `z`, lie in `q`'s
chart source near `z`, and are sections of `f.holoRepr` near `z` (`f.holoRepr (sₖ w) = w`), then their
self-chart pullbacks have equal derivatives at `z`:

> `deriv (fun w => chart_q (s₁ w)) z = deriv (fun w => chart_q (s₂ w)) z`.

*Proof.*  The chart-pullbacks `chart_q ∘ sₖ` are continuous right-inverses of `φ` through `chart_q q`
(`φ (chart_q (sₖ w)) = f.holoRepr (sₖ w) = w` near `z`, using `sₖ w ∈ chart_q.source`), so they
germ-agree by `eventuallyEq_of_rightInverse_of_rightInverse`; equal germs have equal derivatives. -/
theorem hderiv_match_of_section {f : MeromorphicFunction X} {s₁ s₂ : ℂ → X} {z : ℂ}
    (hq_np : 0 ≤ f.orderAtPoint (s₁ z)) (hq_val : f.holoRepr (s₁ z) = z)
    (hreg : deriv (fun u => f.holoRepr ((chartAt ℂ (s₁ z)).symm u)) ((chartAt ℂ (s₁ z)) (s₁ z)) ≠ 0)
    (hs₂z : s₂ z = s₁ z)
    (hs₁_cont : ContinuousAt s₁ z) (hs₂_cont : ContinuousAt s₂ z)
    (hs₁_src : ∀ᶠ w in 𝓝 z, s₁ w ∈ (chartAt ℂ (s₁ z)).source)
    (hs₂_src : ∀ᶠ w in 𝓝 z, s₂ w ∈ (chartAt ℂ (s₁ z)).source)
    (hs₁_sec : ∀ᶠ w in 𝓝 z, f.holoRepr (s₁ w) = w)
    (hs₂_sec : ∀ᶠ w in 𝓝 z, f.holoRepr (s₂ w) = w) :
    deriv (fun w => (chartAt ℂ (s₁ z)) (s₁ w)) z
      = deriv (fun w => (chartAt ℂ (s₁ z)) (s₂ w)) z := by
  classical
  set q : X := s₁ z with hqdef
  set φ : ℂ → ℂ := fun u => f.holoRepr ((chartAt ℂ q).symm u) with hφ
  -- `φ` is analytic at `chart_q q` (q non-pole) with `φ (chart_q q) = z` (q's holoRepr value).
  have hφ_an : AnalyticAt ℂ φ ((chartAt ℂ q) q) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hq_np
  have hφ_base : φ ((chartAt ℂ q) q) = z := by
    show f.holoRepr ((chartAt ℂ q).symm ((chartAt ℂ q) q)) = z
    rw [(chartAt ℂ q).left_inv (mem_chart_source ℂ q)]; exact hq_val
  -- `chart_q` is continuous at `q`.
  have hchart_cont : ContinuousAt (chartAt ℂ q) q := (chartAt ℂ q).continuousAt (mem_chart_source ℂ q)
  -- Each `chart_q ∘ sₖ` is a continuous right-inverse of `φ` through `chart_q q`.
  have hcont : ∀ {s : ℂ → X}, s z = q → ContinuousAt s z →
      ContinuousAt (fun w => (chartAt ℂ q) (s w)) z := by
    intro s hsz hsc
    refine ContinuousAt.comp ?_ hsc
    rw [hsz]; exact hchart_cont
  have hrinv : ∀ {s : ℂ → X}, (∀ᶠ w in 𝓝 z, s w ∈ (chartAt ℂ q).source) →
      (∀ᶠ w in 𝓝 z, f.holoRepr (s w) = w) → ∀ᶠ w in 𝓝 z, φ ((chartAt ℂ q) (s w)) = w := by
    intro s hsrc hsec
    filter_upwards [hsrc, hsec] with w hw hsw
    show f.holoRepr ((chartAt ℂ q).symm ((chartAt ℂ q) (s w))) = w
    rw [(chartAt ℂ q).left_inv hw]; exact hsw
  -- The two chart-pullbacks germ-agree (uniqueness of the holomorphic local inverse).
  have hbase₁ : (fun w => (chartAt ℂ q) (s₁ w)) z = (chartAt ℂ q) q := by
    show (chartAt ℂ q) (s₁ z) = _; rw [hqdef]
  have hbase₂ : (fun w => (chartAt ℂ q) (s₂ w)) z = (chartAt ℂ q) q := by
    show (chartAt ℂ q) (s₂ z) = _; rw [hs₂z, hqdef]
  have heq : (fun w => (chartAt ℂ q) (s₁ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ q) (s₂ w)) :=
    Jacobians.Dolbeault.FormTraceSheet.eventuallyEq_of_rightInverse_of_rightInverse
      hφ_an hreg hφ_base hbase₁ hbase₂
      (hcont rfl hs₁_cont) (hcont hs₂z hs₂_cont)
      (hrinv hs₁_src hs₁_sec) (hrinv hs₂_src hs₂_sec)
  exact heq.deriv_eq

/-! ## The Gate-A capstone via the clustering datum

Composing `FibreClusterReindex.ofClusterReindexFamily` with the PROVEN Gate-A theorem
`residueSum_eq_zero_of_reindex_adaptedFRamified` exhibits the full reduction: for a genuine meromorphic
numerator `g`, the total residue `∑Res = 0` follows from an `AdaptedFRamified` (TARGET 2's off-centre/∞
genericity, already discharged into `GateAInftyData`) together with, at each finite pole-value centre, a
per-centre `FibreClusterReindex` built from a slit-wide family of `ClusterReindexData` (TARGET 1, with
the chart reconciliation discharged — only the conservation-of-number bijection + point coincidence
remain). -/

/-- **Gate A `∑Res = 0` from the clustering datum** (the precise residual exhibited).  For a genuine
meromorphic numerator `g`, an `AdaptedFRamified` datum `A`, and at each finite pole-value centre `A.cs i`
a per-centre `FibreClusterReindex` (e.g. built via `FibreClusterReindex.ofClusterReindexFamily` from a
slit-wide family of `ClusterReindexData`), the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This is `residueSum_eq_zero_of_reindex_adaptedFRamified`, restated here to anchor the partition skeleton
to the Gate-A goal: the *only* genuinely-remaining analytic content is the per-centre
`FibreClusterReindex`, whose hard `hgeom_fibre` field is now reduced (via this file's
`valueChartTrace_eq_clusterSum_of_clusterReindexData`) to the conservation-of-number bijection + point
coincidence at each slit value. -/
theorem residueSum_eq_zero_of_clusterReindex {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, FibreClusterReindex ω₀ g.toFun A.f A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_reindex_adaptedFRamified A R

end Jacobians.Dolbeault.SerreResidueTheorem
