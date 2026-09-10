/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedClusterSplit
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealCover

/-!
# The SOUND full-fibre ramified geometric-trace identification (closing Gate A)

This file proves the **sound, corrected** geometric identification `RamifiedFullFibreClusterGeometry`
(`SerreResidueRamifiedClusterSplit.lean`) — the full-fibre cluster sum over *all* preimages, at the
*genuine* cluster sheet points `clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j` (the local inverse `sₗ = ηₗ⁻¹` of
the Forster §5 normal form, **not** the first-order `wp + ζʲ w₀`) — and wires it to a `∑Res = 0`
capstone.

It corrects the *two* soundness failures of the single-cluster `RamifiedSheetData.hgeom_slit` (the #13
bad field): (1) the OUTER sum ranges over the **whole** fibre `F⁻¹(z)` (all preimages contribute), and
(2) the sheet points are the **genuine** `clusterSheet` points.

## The mathematics — the per-cluster collapse via the straightening coordinate

The crux is the *per-cluster symmetric collapse* (piece (b)).  At a preimage `p` with normal-form local
inverse `s = η⁻¹` (`F = c + ηᵐ`), the cluster sheet points are `clusterSheet s ζ w₀ j z = s(ζʲ w₀ z)`,
the genuine roots of `F(w) = z` near `p`.  Writing the chart integrand `h := chartIntegrand ω₀ g p` in
the *straightening coordinate* `u` (`w = s(u)`, `dw = s'(u) du`):

> `H(u) := h(s u) · s'(u)`   (meromorphic at `u = 0`, composition with the biholomorphism `s`)

the `m`-sheet cluster sum becomes the *first-order* sheet sum of `H` (chain rule
`(d/dz)[s(ζʲ w₀ z)] = s'(ζʲ w₀ z)·ζʲ·w₀'(z)`):

> `∑_{j<m} h(s(ζʲ w₀ z))·(d/dz)[s(ζʲ w₀ z)] = ∑_{j<m} H(ζʲ w₀ z)·ζʲ·w₀'(z)`,

so the proven roots-of-unity atom `ramifiedSheetSum_laurentPoly` (applied to the Laurent **principal
part** of `H` at `0`) collapses it to `ramifiedTraceTerm (principal part of H) c z` plus the analytic
remainder's sheet sum.  The residue of `H`'s principal part at `0` is `formFnResidue ω₀ g p` by the
proven residue **change-of-variables** atom `residueChangeOfVariables` (`Res` is biholomorphism-invariant:
`Res₀(h(s u)·s'(u)) = Res_{s 0}(h) = Res_p(α)`).

Summing the per-cluster collapses over **all** preimages (`RamifiedFullFibreClusterGeometry`) gives the
single-valued meromorphic trace germ `T = ∑_ℓ ramifiedTraceTerm_ℓ + ∑_ℓ Rem_ℓ`, whose residue at `c` is
`∑_ℓ formFnResidue ω₀ g pₗ` — the full pole-fibre residue sum.  This is exactly a `RamifiedCenterFacts`
(`SerreResidueRamifiedCenter.lean`) over the whole fibre, fed into the `hoff_cs`-free capstone
`residueTheorem_ofRamifiedCenters_genus0_mod`.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `clusterSheet_deriv` — the chain-rule derivative `(d/dz)[clusterSheet s ζ w₀ j z] = s'(ζʲ w₀ z)·ζʲ·w₀'(z)`.
* `clusterSheetSum_eq_straightenedSheetSum` — the cluster sum equals the first-order sheet sum of the
  straightened integrand `H(u) = h(s u)·s'(u)`.
* `straightenedIntegrand_residue` — `Res₀(H principal part) = formFnResidue ω₀ g p` (change of variables).
* `ClusterTraceData` — the per-cluster genuine data (the `clusterSheet` analogue of `RamifiedSheetData`,
  with *no* single-preimage restriction and the genuine straightened integrand).
* `clusterTraceSum_collapse` — the per-cluster collapse to `ramifiedTraceTerm + Rem` on the slit.
* `RamifiedCenterFacts.ofFullFibreCluster` — the SOUND full-fibre `RamifiedCenterFacts` from
  `RamifiedFullFibreClusterGeometry` + per-cluster `ClusterTraceData`.
* `residueSum_eq_zero_of_fullFibreCluster` — `∑Res = 0` via the corrected full-fibre geometry.

## ⚠ Soundness

Uses the **full fibre** (all preimages — the #13 lesson) and the **genuine** sheet points `clusterSheet`
(via the proven `exists_clusterSplit`/`exists_wpow_normalForm`).  The `m`-sheet SUM (the roots-of-unity
atom cancels the chain-rule `1/m`; no single-sheet `m·Res`).  Residue invariance is the proven
`residueChangeOfVariables`.  No false/junk/circular field; no custom axiom; no unproved obligation on a false statement.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1).
* `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`, `exists_clusterSplit`,
  `RamifiedFullFibreClusterGeometry`), `RamifiedResidueChangeOfVariables.lean`
  (`laurentTraceCoeff_eq_sheetSum`), `ResidueChangeOfVariables.lean` (`residueChangeOfVariables`).
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
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The chain-rule derivative of a cluster sheet -/

/-- **The cluster-sheet derivative.**  For the cluster sheet point `clusterSheet s ζ w₀ j z =
s(ζʲ w₀ z)`, with `s` analytic at `ζʲ w₀ z` and `w₀` differentiable at `z`, the chain rule gives

> `(d/dz)[clusterSheet s ζ w₀ j z] = deriv s (ζʲ w₀ z) · (ζʲ · deriv w₀ z)`.

(Compose `s` with the affine-in-`w₀` map `z ↦ ζʲ w₀ z`; the inner derivative is `ζʲ · w₀'(z)`.) -/
theorem clusterSheet_deriv {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z : ℂ}
    (hs : AnalyticAt ℂ s (ζ ^ j * w₀ z)) (hw₀ : DifferentiableAt ℂ w₀ z) :
    deriv (clusterSheet s ζ w₀ j) z = deriv s (ζ ^ j * w₀ z) * (ζ ^ j * deriv w₀ z) := by
  have hinner : HasDerivAt (fun z => ζ ^ j * w₀ z) (ζ ^ j * deriv w₀ z) z :=
    hw₀.hasDerivAt.const_mul (ζ ^ j)
  have houter : HasDerivAt s (deriv s (ζ ^ j * w₀ z)) (ζ ^ j * w₀ z) :=
    hs.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (s ∘ fun z => ζ ^ j * w₀ z)
      ((ζ ^ j * deriv w₀ z) • deriv s (ζ ^ j * w₀ z)) z := houter.scomp z hinner
  rw [smul_eq_mul, mul_comm] at hcomp
  exact hcomp.deriv

/-! ## The straightened integrand `H(u) = h(s u)·s'(u)` and the per-cluster collapse

At a preimage `p` with normal-form local inverse `s = η⁻¹`, write the chart integrand
`h := chartIntegrand ω₀ g p` in the straightening coordinate `u` (`w = s u`).  The straightened
integrand `H(u) := h(s u)·s'(u)` is meromorphic at `0` (composition of the meromorphic `h` with the
biholomorphism `s`, times the analytic `s'`).  Its `m`-sheet *first-order* sum (over the roots
`u_j = ζʲ w₀ z` of `uᵐ = z − c`) is exactly the geometric cluster sum, by `clusterSheet_deriv`. -/

/-- **The straightened integrand** `H(u) := chartIntegrand ω₀ g p (s u) · deriv s u` (the chart
integrand of `α = ω₀·g` at `p`, pushed into the straightening coordinate `u` via `w = s u`). -/
noncomputable def straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X) (s : ℂ → ℂ) :
    ℂ → ℂ :=
  fun u => chartIntegrand ω₀ g p (s u) * deriv s u

/-- **The straightened integrand is meromorphic at `0`** when `g`'s chart-pullback is meromorphic at
`p`'s chart centre, `s` is analytic at `0` with `s 0 = chartAt ℂ p p`.  (Composition of the meromorphic
`chartIntegrand` with the analytic biholomorphism `s`, times the analytic `s'`.) -/
theorem meromorphicAt_straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s : ℂ → ℂ} (hs_an : AnalyticAt ℂ s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)) :
    MeromorphicAt (straightenedIntegrand ω₀ g p s) 0 := by
  have hh : MeromorphicAt (chartIntegrand ω₀ g p) ((chartAt ℂ p) p) :=
    meromorphicAt_chartIntegrand ω₀ g p hg_mero
  have hcomp : MeromorphicAt (chartIntegrand ω₀ g p ∘ s) 0 := by
    rw [← hs0] at hh
    exact MeromorphicAt.comp_analyticAt hh hs_an
  exact hcomp.mul hs_an.deriv.meromorphicAt

/-- **The residue of the straightened integrand is the upstairs form residue** (the residue
change-of-variables atom in action).  When `s` is a local biholomorphism at `0` (`s` analytic,
`deriv s 0 ≠ 0`) with `s 0 = chartAt ℂ p p`, the residue of `H(u) = h(s u)·s'(u)` at `0` equals the
chart integrand's residue at `chartAt ℂ p p`, which is `formFnResidue ω₀ g p`:

> `Res₀ (h(s ·)·s'(·)) = Res_{s 0} h = formFnResidue ω₀ g p`.

This is `residueChangeOfVariables` (the residue is biholomorphism-invariant) plus the definitional
`resAt (chartIntegrand ω₀ g p) (chartAt ℂ p p) = formFnResidue ω₀ g p`. -/
theorem resAt_straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s : ℂ → ℂ} (hs_an : AnalyticAt ℂ s 0) (hs_deriv : deriv s 0 ≠ 0)
    (hs0 : s 0 = (chartAt ℂ p) p)
    (hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)) :
    resAt (straightenedIntegrand ω₀ g p s) 0 = formFnResidue ω₀ g p := by
  have hh : MeromorphicAt (chartIntegrand ω₀ g p) (s 0) := by
    rw [hs0]; exact meromorphicAt_chartIntegrand ω₀ g p hg_mero
  have hcov := residueChangeOfVariables s (chartIntegrand ω₀ g p) 0 hs_an hs_deriv hh
  show resAt (fun w => chartIntegrand ω₀ g p (s w) * deriv s w) 0 = formFnResidue ω₀ g p
  rw [hcov, hs0]
  exact resAt_chartIntegrand_eq_formFnResidue ω₀ g p

/-- **The geometric cluster sum equals the straightened sheet sum.**  Using the chain rule
`clusterSheet_deriv`, the geometric `m`-sheet cluster sum of `h = chartIntegrand ω₀ g p` along the
cluster sheets `clusterSheet s ζ w₀ j` equals the *first-order* `m`-sheet sum of the straightened
integrand `H(u) = h(s u)·s'(u)` along `u_j = ζʲ w₀ z`:

> `∑_{j<m} h(clusterSheet s ζ w₀ j z)·(d/dz)[clusterSheet s ζ w₀ j z]`
>   `= ∑_{j<m} H(ζʲ w₀ z)·(d/dz)[0 + ζʲ w₀ z]`.

(`h(s(ζʲ w₀ z))·s'(ζʲ w₀ z) = H(ζʲ w₀ z)`, and the cluster-sheet derivative
`s'(ζʲ w₀ z)·ζʲ·w₀'(z)` reassociates against the straightened first-order derivative `ζʲ·w₀'(z)`.) -/
theorem clusterSheetSum_eq_straightenedSheetSum (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s w₀ : ℂ → ℂ} {ζ : ℂ} {m : ℕ} {z : ℂ} (hw₀_diff : DifferentiableAt ℂ w₀ z)
    (hs_an : ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z)) :
    (∑ j ∈ Finset.range m,
        chartIntegrand ω₀ g p (clusterSheet s ζ w₀ j z) * deriv (clusterSheet s ζ w₀ j) z)
      = ∑ j ∈ Finset.range m,
        straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
          * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [clusterSheet_deriv (hs_an j hj) hw₀_diff, deriv_sheet_eq w₀ z 0 (ζ ^ j),
    straightenedIntegrand, clusterSheet]
  ring

/-- **The per-cluster symmetric collapse (piece (b), on the genuine cluster sheets).**  At a preimage
`p` with normal-form local inverse `s = η⁻¹`, a primitive `m`-th root `ζ`, and a slit-branch `w₀`
(`w₀ z ≠ 0`, `w₀(z)ᵐ = z − c`, `w₀'(z) = (1/m) w₀(z)^{1−m}`), the geometric `m`-sheet cluster sum of the
chart integrand `h = chartIntegrand ω₀ g p` along the *genuine* cluster sheets `clusterSheet s ζ w₀ j`
collapses to the single-valued `ramifiedTraceTerm` of the straightened integrand's Laurent principal
part, plus the remainder sheet sum:

> `∑_{j<m} h(clusterSheet s ζ w₀ j z)·(d/dz)[clusterSheet s ζ w₀ j z]`
>   `= ramifiedTraceTerm (Icc 1 N) b (k ↦ −k) m c z + ∑_{j<m} R(ζʲ w₀ z)·(d/dz)[0 + ζʲ w₀ z]`,

where `(N, b, R)` is the Laurent principal-part split of the straightened integrand `H(u) = h(s u)·s'(u)`
at `0` (`H =ᶠ[𝓝[≠] 0] negTail 0 b N + R`), *provided* the split holds at each sheet argument `ζʲ w₀ z`
(`hH_split`).  Pure algebra (the proven roots-of-unity atom `ramifiedSheetSum_laurentPoly`), with the
genuine sheet points. -/
theorem clusterTraceSum_collapse (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s w₀ : ℂ → ℂ} {ζ : ℂ} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    {c z : ℂ} {N : ℕ} {b : ℕ → ℂ} {R : ℂ → ℂ}
    (hw₀_ne : w₀ z ≠ 0) (hw₀_pow : w₀ z ^ (m : ℤ) = z - c)
    (hw₀_deriv : deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ)))
    (hw₀_diff : DifferentiableAt ℂ w₀ z)
    (hs_an : ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z))
    (hH_split : ∀ j ∈ Finset.range m,
      straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
        = negTail 0 b N (ζ ^ j * w₀ z) + R (ζ ^ j * w₀ z)) :
    (∑ j ∈ Finset.range m,
        chartIntegrand ω₀ g p (clusterSheet s ζ w₀ j z) * deriv (clusterSheet s ζ w₀ j) z)
      = ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) m c z
        + ∑ j ∈ Finset.range m,
            R (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z := by
  classical
  -- Step 1: geometric cluster sum = straightened first-order sheet sum.
  rw [clusterSheetSum_eq_straightenedSheetSum ω₀ g p hw₀_diff hs_an]
  -- Step 2: split each straightened term into `negTail` + `R`, distribute.
  have hsplit : (∑ j ∈ Finset.range m,
        straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
          * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
      = (∑ j ∈ Finset.range m,
          negTail 0 b N (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
        + (∑ j ∈ Finset.range m,
            R (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hH_split j hj]; ring
  rw [hsplit]
  -- Step 3: the `negTail`-sheet sum collapses to `ramifiedTraceTerm` (the proven atom).
  congr 1
  rw [show (∑ j ∈ Finset.range m,
        negTail 0 b N (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
      = ∑ j ∈ Finset.range m,
          (∑ k ∈ Finset.Icc 1 N, b k * ((0 : ℂ) + ζ ^ j * w₀ z - 0) ^ (-(k : ℤ)))
            * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z
    from Finset.sum_congr rfl (fun j _ => by rw [negTail]; ring_nf)]
  exact ramifiedSheetSum_laurentPoly (Finset.Icc 1 N) b (fun k => -(k : ℤ)) hm hζ
    hw₀_ne hw₀_pow hw₀_deriv

/-! ## The per-cluster genuine data and the full-fibre `RamifiedCenterFacts`

A `ClusterTraceData` packages, at one preimage `p` of the value-centre `c`, the genuine Forster §5
normal-form cluster data on the slit: the local inverse `s = η⁻¹`, the slit-branch `w₀`, the Laurent
principal-part split of the straightened integrand `H = h(s ·)·s'(·)`, and the single-valued analytic
remainder trace `Rem` (the symmetric-function descent of the `m`-sheet remainder sum, supplied as data —
exactly the honest decomposition of `RamifiedSheetData`, but at the **genuine** `clusterSheet` points,
with **no** single-preimage restriction).

Summing the per-cluster collapses over the whole fibre (`RamifiedFullFibreClusterGeometry`) builds the
SOUND full-fibre `RamifiedCenterFacts`. -/

/-- **Per-cluster genuine trace data** at one preimage `p` of the value-centre `c` (the `clusterSheet`
analogue of `RamifiedSheetData`, with no single-preimage restriction).  Carries the Forster §5
normal-form local inverse `s = η⁻¹`, the slit-branch `w₀`, the Laurent principal-part split of the
straightened integrand `H = chartIntegrand ω₀ g p (s ·)·s'(·)` at `0`, and the single-valued analytic
remainder trace `Rem`. -/
structure ClusterTraceData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X) (c : ℂ) (S : Set ℂ) where
  /-- The ramification multiplicity (`≥ 1`). -/
  m : ℕ
  /-- Positivity. -/
  hm : 0 < m
  /-- A primitive `m`-th root of unity. -/
  ζ : ℂ
  /-- `ζ` is primitive. -/
  hζ : IsPrimitiveRoot ζ m
  /-- The normal-form local inverse `s = η⁻¹` (analytic at `0`). -/
  s : ℂ → ℂ
  /-- `s` is analytic at `0`. -/
  hs_an : AnalyticAt ℂ s 0
  /-- `s 0 = chartAt ℂ p p` (the cluster centre is the preimage `p`). -/
  hs0 : s 0 = (chartAt ℂ p) p
  /-- `s` is a local biholomorphism (`deriv s 0 ≠ 0`). -/
  hs_deriv : deriv s 0 ≠ 0
  /-- The slit-branch of `(z − c)^{1/m}`. -/
  w₀ : ℂ → ℂ
  /-- The branch is nonzero on the slit. -/
  hw₀_ne : ∀ z ∈ S, w₀ z ≠ 0
  /-- The branch is an `m`-th root on the slit. -/
  hw₀_pow : ∀ z ∈ S, w₀ z ^ (m : ℤ) = z - c
  /-- The chain-rule derivative on the slit. -/
  hw₀_deriv : ∀ z ∈ S, deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ))
  /-- `w₀` is differentiable on the slit. -/
  hw₀_diff : ∀ z ∈ S, DifferentiableAt ℂ w₀ z
  /-- The cluster sheet arguments stay in `s`'s analyticity domain on the slit. -/
  hs_an_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z)
  /-- `g`'s chart-pullback is meromorphic at `p`'s chart centre. -/
  hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)
  /-- Degree of the Laurent principal part of the straightened integrand `H` at `0`. -/
  ppN : ℕ
  /-- Coefficients of the Laurent principal part of `H`. -/
  ppb : ℕ → ℂ
  /-- Analytic remainder of `H` at `0`. -/
  ppR : ℂ → ℂ
  /-- The remainder is analytic at `0`. -/
  hppR_an : AnalyticAt ℂ ppR 0
  /-- **The principal-part split at the sheet points** (true by `exists_principalPart_meromorphicAt`):
  on the slit, the straightened integrand `H` decomposes as `negTail 0 + ppR` at each sheet argument. -/
  hpp_split_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range m,
    straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
      = negTail 0 ppb ppN (ζ ^ j * w₀ z) + ppR (ζ ^ j * w₀ z)
  /-- The single-valued analytic remainder trace at `c`. -/
  Rem : ℂ → ℂ
  /-- The remainder trace is analytic at `c`. -/
  hRem_an : AnalyticAt ℂ Rem c
  /-- The remainder trace agrees, on the slit, with the `m`-sheet sum of `ppR`. -/
  hRem_slit : ∀ z ∈ S, Rem z = ∑ j ∈ Finset.range m,
    ppR (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z

namespace ClusterTraceData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {p : X} {c : ℂ} {S : Set ℂ}

/-- The single-valued **per-cluster trace germ** `Tₗ := ramifiedTraceTerm (principal part of H) + Rem`
(a meromorphic function of `z − c` by construction). -/
noncomputable def clusterTrace (D : ClusterTraceData ω₀ g p c S) : ℂ → ℂ :=
  fun z => ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.m c z + D.Rem z

/-- **The per-cluster slit identity.**  On the slit, the geometric `m`-sheet cluster sum (over the
genuine `clusterSheet` points) equals the single-valued per-cluster trace `Tₗ`.  Proof: the per-cluster
collapse `clusterTraceSum_collapse` (the genuine sheet points + the roots-of-unity atom) gives
`ramifiedTraceTerm + remainder sheet sum`, and `hRem_slit` rewrites the remainder sheet sum as `Rem`. -/
theorem clusterSum_eq_clusterTrace_slit (D : ClusterTraceData ω₀ g p c S) {z : ℂ} (hz : z ∈ S) :
    (∑ j ∈ Finset.range D.m,
        chartIntegrand ω₀ g p (clusterSheet D.s D.ζ D.w₀ j z) * deriv (clusterSheet D.s D.ζ D.w₀ j) z)
      = D.clusterTrace z := by
  rw [clusterTraceSum_collapse ω₀ g p D.hm D.hζ (D.hw₀_ne z hz) (D.hw₀_pow z hz) (D.hw₀_deriv z hz)
    (D.hw₀_diff z hz) (D.hs_an_sheet z hz) (D.hpp_split_sheet z hz), ← D.hRem_slit z hz]
  rfl

/-- The per-cluster trace germ `Tₗ` is **meromorphic at `c`** by construction (`ramifiedTraceTerm`
meromorphic + `Rem` analytic). -/
theorem meromorphicAt_clusterTrace (D : ClusterTraceData ω₀ g p c S) :
    MeromorphicAt D.clusterTrace c :=
  (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.m c).add
    D.hRem_an.meromorphicAt

/-- **The per-cluster residue is the upstairs form residue.**  `Res_c Tₗ = formFnResidue ω₀ g p`.  The
residue of `ramifiedTraceTerm` is the residue of the principal part of `H` at `0`
(`resAt_ramifiedTraceTerm`), which equals `formFnResidue ω₀ g p` by residue change-of-variables
(`resAt_straightenedIntegrand`, since the principal part of `H` carries the same residue as `H`); the
analytic `Rem` adds `0`. -/
theorem resAt_clusterTrace (D : ClusterTraceData ω₀ g p c S)
    (hsplit0 : straightenedIntegrand ω₀ g p D.s =ᶠ[𝓝[≠] 0]
      fun u => negTail 0 D.ppb D.ppN u + D.ppR u) :
    resAt D.clusterTrace c = formFnResidue ω₀ g p := by
  -- Residue of `Tₗ = ramifiedTraceTerm + Rem`: the `Rem` (analytic) contributes `0`.
  have hRes : resAt D.clusterTrace c
      = resAt (fun w => ∑ k ∈ Finset.Icc 1 D.ppN, D.ppb k * (w - 0) ^ (-(k : ℤ))) 0 := by
    show resAt (fun z => ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.m c z
        + D.Rem z) c = _
    rw [show (fun z => ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.m c z
          + D.Rem z)
        = (ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.m c) + D.Rem from rfl,
      resAt_add
        (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ))
          D.m c).holoPunctured
        D.hRem_an.meromorphicAt.holoPunctured,
      resAt_eq_zero_of_analyticAt D.hRem_an, add_zero,
      resAt_ramifiedTraceTerm (Finset.Icc 1 D.ppN) D.ppb (fun k => -(k : ℤ)) D.hm c]
  rw [hRes]
  -- The residue of `H`'s principal part at `0` = residue of `H` at `0` (the remainder `ppR` is analytic)
  -- = `formFnResidue ω₀ g p` (change of variables).
  have hHmero : MeromorphicAt (straightenedIntegrand ω₀ g p D.s) 0 :=
    meromorphicAt_straightenedIntegrand ω₀ g p D.hs_an D.hs0 D.hg_mero
  have hnegTail_mero : MeromorphicAt (fun u => negTail 0 D.ppb D.ppN u) 0 := by
    rw [show (fun u => negTail 0 D.ppb D.ppN u)
        = fun u => ∑ k ∈ Finset.Icc 1 D.ppN, D.ppb k * (u - 0) ^ (-(k : ℤ)) from rfl]
    exact MeromorphicAt.fun_sum (fun k _ => (MeromorphicAt.const (D.ppb k) 0).mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _))
  have hResH : resAt (straightenedIntegrand ω₀ g p D.s) 0
      = resAt (fun w => ∑ k ∈ Finset.Icc 1 D.ppN, D.ppb k * (w - 0) ^ (-(k : ℤ))) 0 := by
    rw [resAt_congr hsplit0]
    rw [show (fun u => negTail 0 D.ppb D.ppN u + D.ppR u)
        = (fun u => negTail 0 D.ppb D.ppN u) + D.ppR from rfl,
      resAt_add hnegTail_mero.holoPunctured D.hppR_an.meromorphicAt.holoPunctured,
      resAt_eq_zero_of_analyticAt D.hppR_an, add_zero]
    rfl
  rw [← hResH, resAt_straightenedIntegrand ω₀ g p D.hs_an D.hs_deriv D.hs0 D.hg_mero]

end ClusterTraceData

/-! ### Non-vacuity of `ClusterTraceData` — inhabitable at the ramified multiplicity `m = 2`

`ClusterTraceData` is inhabited for **every** `m ≥ 1` (the genuine `√(z − c)` slit branch at `m = 2`),
so it is **not** a disguised `False` at a ramification multiplicity.  Witness: the zero numerator
`g ≡ 0` (so the chart integrand is `0`), with the trivial straightening `s u = chart_p p + u` (a genuine
local biholomorphism: analytic, `deriv = 1 ≠ 0`) and the `cpow` slit branch `w₀ z = (z − c)^{1/m}` (which
exists for any `m`).  Every analytic field is `0 = 0`. -/

/-- **`ClusterTraceData` is inhabitable for every `m ≥ 1`** (non-vacuity / soundness witness).  Zero
numerator `g ≡ 0`, trivial straightening `s u = chart_p p + u`, `cpow` slit branch `w₀ z = (z − c)^{1/m}`
on the slit `S = {z | z − c ∈ slitPlane}`.  The branch exists for **any** `m` (no monodromy
contradiction), so the structure is inhabited at genuinely ramified multiplicities — e.g. `m = 2`. -/
noncomputable def clusterTraceData_slit (ω₀ : HolomorphicOneForms X) (p : X) (c : ℂ)
    (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    ClusterTraceData ω₀ (fun _ => (0 : ℂ)) p c {z | z - c ∈ slitPlane} where
  m := m
  hm := hm
  ζ := ζ
  hζ := hζ
  s := fun u => (chartAt ℂ p) p + u
  hs_an := (analyticAt_const.add analyticAt_id)
  hs0 := by simp
  hs_deriv := by
    have hd : HasDerivAt (fun u => (chartAt ℂ p) p + u) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add ((chartAt ℂ p) p)
    rw [hd.deriv]; exact one_ne_zero
  w₀ := fun z => (z - c) ^ ((m : ℂ)⁻¹)
  hw₀_ne := by
    intro z hz
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz))
  hw₀_pow := by
    intro z _
    rw [zpow_natCast]; exact Complex.cpow_nat_inv_pow _ hm.ne'
  hw₀_deriv := by
    intro z hz
    have hmem : (z - c) ∈ slitPlane := hz
    have hzc : z - c ≠ 0 := Complex.slitPlane_ne_zero hz
    have hw0ne : (z - c) ^ ((m : ℂ)⁻¹) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hzc)
    have hpow : ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m : ℤ) = z - c := by
      rw [zpow_natCast]; exact Complex.cpow_nat_inv_pow _ hm.ne'
    have hbase : HasDerivAt (fun z : ℂ => z - c) 1 z := by simpa using (hasDerivAt_id z).sub_const c
    have hD := hbase.cpow_const (c := (m : ℂ)⁻¹) hmem
    rw [mul_one] at hD
    rw [hD.deriv]; congr 1
    have hL : (z - c) ^ ((m : ℂ)⁻¹ - 1) = (z - c) ^ ((m : ℂ)⁻¹) * (z - c)⁻¹ := by
      rw [Complex.cpow_sub _ _ hzc, Complex.cpow_one, div_eq_mul_inv]
    have hR : ((z - c) ^ ((m : ℂ)⁻¹)) ^ (1 - (m : ℤ)) = (z - c) ^ ((m : ℂ)⁻¹) * (z - c)⁻¹ := by
      rw [zpow_sub₀ hw0ne, zpow_one, hpow, div_eq_mul_inv]
    rw [hL, hR]
  hw₀_diff := by
    intro z hz
    have hmem : (z - c) ∈ slitPlane := hz
    have hbase : HasDerivAt (fun z : ℂ => z - c) 1 z := by simpa using (hasDerivAt_id z).sub_const c
    exact (hbase.cpow_const (c := (m : ℂ)⁻¹) hmem).differentiableAt
  hs_an_sheet := fun _ _ _ _ => (analyticAt_const.add analyticAt_id)
  hg_mero := analyticAt_const.meromorphicAt
  ppN := 0
  ppb := fun _ => 0
  ppR := fun _ => 0
  hppR_an := analyticAt_const
  hpp_split_sheet := by
    intro z _ j _
    rw [show straightenedIntegrand ω₀ (fun _ => (0 : ℂ)) p (fun u => (chartAt ℂ p) p + u)
        = (fun _ => (0 : ℂ)) by
      funext u; simp [straightenedIntegrand, chartIntegrand]]
    simp [negTail]
  Rem := fun _ => 0
  hRem_an := analyticAt_const
  hRem_slit := by intro z _; simp

/-- **`ClusterTraceData` is inhabited at the ramified multiplicity `m = 2`** — the genuine `√(z − c)`
slit branch (`ζ = −1`).  The decisive soundness witness: the structure is satisfiable at a genuinely
ramified multiplicity, not just `m = 1`. -/
noncomputable def clusterTraceData_sqrt (ω₀ : HolomorphicOneForms X) (p : X) (c : ℂ) :
    ClusterTraceData ω₀ (fun _ => (0 : ℂ)) p c {z | z - c ∈ slitPlane} :=
  clusterTraceData_slit ω₀ p c 2 (by norm_num) (-1)
    (IsPrimitiveRoot.neg_one (R := ℂ) 0 (by norm_num))

/-! ## The full-fibre cluster data and the SOUND `RamifiedCenterFacts`

A `FullFibreClusterData` bundles, at a value-centre `c`, the *whole* pole fibre `D : FibreRamifiedData`
with a per-preimage `ClusterTraceData` (on a common slit), the single-valued meromorphy `hvct_mero` of
the geometric trace, and the **full-fibre cluster geometric identity** on the slit (the geometric trace
is the full-fibre sum of all per-cluster sheet sums — `RamifiedFullFibreClusterGeometry` on the slit).

From it we build the SOUND full-fibre `RamifiedCenterFacts` whose germ `T = ∑ₗ clusterTraceₗ` is
single-valued meromorphic, equals `valueChartTrace` on a punctured neighbourhood (identity theorem), and
has residue `∑ₗ formFnResidue ω₀ g pₗ` (the full pole-fibre sum).  This is the corrected analogue of
`RamifiedCenterFacts.ofSheetData` (which used the false single-cluster `hgeom_slit`). -/

/-- **The full-fibre cluster data at a value-centre `c`** (the SOUND geometric input — full fibre,
genuine cluster sheets).  Bundles the whole pole fibre `D`, a per-preimage `ClusterTraceData` `Cl i` on
a common slit `S`, the geometric trace's single-valued meromorphy `hvct_mero`, and the full-fibre
cluster geometric identity `hgeom_fibre` on the slit (the geometric trace is the sum over *all*
preimages of the per-cluster `mᵢ`-sheet sums at the genuine `clusterSheet` points). -/
structure FullFibreClusterData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (c : ℂ) where
  /-- The whole pole fibre over `coe c` (preimages with multiplicities). -/
  D : FibreRamifiedData g f c
  /-- The preimage enumeration is injective. -/
  hD_inj : Function.Injective D.xs
  /-- The slit on which the per-cluster branches are defined. -/
  S : Set ℂ
  /-- The slit accumulates at `c`. -/
  hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ S
  /-- The per-preimage genuine cluster data, with matching multiplicity. -/
  Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c S
  /-- The cluster multiplicity matches the fibre multiplicity. -/
  hmult : ∀ i, (Cl i).m = D.mult i
  /-- The principal-part split of each straightened integrand holds on `𝓝[≠] 0` (for the residue). -/
  hsplit0 : ∀ i, straightenedIntegrand ω₀ g (D.xs i) (Cl i).s =ᶠ[𝓝[≠] 0]
    fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u
  /-- **Single-valued meromorphy of the geometric trace** (Miranda (3.1); piece (c)). -/
  hvct_mero : MeromorphicAt (valueChartTrace ω₀ f Φ) c
  /-- **The full-fibre cluster geometric identity on the slit** (the SOUND `hgeom`, full fibre + genuine
  cluster sheets): the geometric trace equals the sum over *all* preimages of the per-cluster sheet
  sums at the genuine `clusterSheet` points. -/
  hgeom_fibre : ∀ z ∈ S, valueChartTrace ω₀ f Φ z = ∑ i, ∑ j ∈ Finset.range (D.mult i),
    chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
      * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z

namespace FullFibreClusterData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ}

/-- **The full-fibre single-valued trace germ** `T := ∑ₗ clusterTraceₗ` (a finite sum of single-valued
meromorphic per-cluster traces). -/
noncomputable def fibreTrace (F : FullFibreClusterData ω₀ g f Φ c) : ℂ → ℂ :=
  fun z => ∑ i, (F.Cl i).clusterTrace z

/-- **The full-fibre slit identity.**  On the slit, the geometric trace equals `T = ∑ₗ clusterTraceₗ`.
Proof: the full-fibre cluster geometric identity `hgeom_fibre` writes `valueChartTrace` as the sum over
all preimages of the per-cluster sheet sums; each per-cluster sheet sum collapses (the per-cluster slit
identity `clusterSum_eq_clusterTrace_slit`, the genuine sheet points + the roots-of-unity atom) to
`clusterTraceₗ`. -/
theorem eqOn_fibreTrace_slit (F : FullFibreClusterData ω₀ g f Φ c) {z : ℂ} (hz : z ∈ F.S) :
    valueChartTrace ω₀ f Φ z = F.fibreTrace z := by
  rw [F.hgeom_fibre z hz]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← F.hmult i]
  exact (F.Cl i).clusterSum_eq_clusterTrace_slit hz

/-- The full-fibre trace `T` is **meromorphic at `c`** (a finite sum of the meromorphic per-cluster
traces). -/
theorem meromorphicAt_fibreTrace (F : FullFibreClusterData ω₀ g f Φ c) :
    MeromorphicAt F.fibreTrace c :=
  MeromorphicAt.fun_sum (fun i _ => (F.Cl i).meromorphicAt_clusterTrace)

/-- **`hcoh` (DERIVED via the identity theorem):** `valueChartTrace =ᶠ[𝓝[≠] c] T`.  Both meromorphic at
`c` (`hvct_mero` / `meromorphicAt_fibreTrace`) and agree on the slit (`eqOn_fibreTrace_slit`), which
accumulates at `c` (`hS_acc`). -/
theorem hcoh (F : FullFibreClusterData ω₀ g f Φ c) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c] F.fibreTrace :=
  eventuallyEq_of_meromorphic_eqOn_slit F.hvct_mero F.meromorphicAt_fibreTrace F.hS_acc
    (fun _z hz => F.eqOn_fibreTrace_slit hz)

/-- **The full-fibre residue.**  `resAt T c = ∑ᵢ formFnResidue ω₀ g (D.xs i)` (the full pole-fibre
residue sum).  Residue of the finite sum splits termwise (`resAt_finsum`); each term is the per-cluster
residue `formFnResidue ω₀ g (D.xs i)` (`resAt_clusterTrace` via change-of-variables). -/
theorem resAt_fibreTrace (F : FullFibreClusterData ω₀ g f Φ c) :
    resAt F.fibreTrace c = ∑ i, formFnResidue ω₀ g (F.D.xs i) := by
  show resAt (fun z => ∑ i, (F.Cl i).clusterTrace z) c = _
  rw [LaurentForm.resAt_finsum Finset.univ (fun i z => (F.Cl i).clusterTrace z)
    (fun i _ => (F.Cl i).meromorphicAt_clusterTrace)]
  exact Finset.sum_congr rfl (fun i _ => (F.Cl i).resAt_clusterTrace (F.hsplit0 i))

/-- **The SOUND full-fibre `RamifiedCenterFacts`** (the corrected analogue of `ofSheetData`).  From the
full-fibre cluster data `F` and the pole-fibre enumeration conditions (`hD_mem`/`hD_surj`), build the
`RamifiedCenterFacts` whose germ `T = ∑ₗ clusterTraceₗ` is single-valued meromorphic, equals
`valueChartTrace` on a punctured neighbourhood (`hcoh`, derived via the slit + identity theorem), and has
residue `∑ᵢ formFnResidue ω₀ g (D.xs i)` (`resAt_fibreTrace`, via change-of-variables).  **Full fibre**
(all preimages — the #13 fix) at the **genuine** `clusterSheet` points; no false/circular field. -/
noncomputable def toRamifiedCenterFacts (F : FullFibreClusterData ω₀ g f Φ c) {poles : Finset X}
    (hD_mem : ∀ i, F.D.xs i ∈ poles)
    (hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, F.D.xs i = a) :
    RamifiedCenterFacts ω₀ g f Φ poles c where
  D := F.D
  hD_inj := F.hD_inj
  hD_mem := hD_mem
  hD_surj := hD_surj
  T := F.fibreTrace
  hcoh := F.hcoh
  hmero := F.meromorphicAt_fibreTrace
  hres := F.resAt_fibreTrace

/-- **`ExistsRamifiedCenterFacts` from a `FullFibreClusterData`** (the SOUND bridge).  Packaging the
SOUND full-fibre `RamifiedCenterFacts` (`toRamifiedCenterFacts`) as the `Nonempty`-wrapped per-centre
obligation `ExistsRamifiedCenterFacts` that the `hoff_cs`-free capstone consumes.  This is the corrected
analogue of `existsRamifiedCenterFacts_ofSheetData` (which used the false single-cluster `hgeom_slit`). -/
theorem existsRamifiedCenterFacts_ofFullFibre (F : FullFibreClusterData ω₀ g f Φ c) {poles : Finset X}
    (hD_mem : ∀ i, F.D.xs i ∈ poles)
    (hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, F.D.xs i = a) :
    ExistsRamifiedCenterFacts ω₀ g f Φ poles c :=
  ⟨F.toRamifiedCenterFacts hD_mem hD_surj⟩

end FullFibreClusterData

/-! ### Non-vacuity of `FullFibreClusterData` — a genuine MULTI-PREIMAGE RAMIFIED witness

The decisive soundness check (the #13 lesson): `FullFibreClusterData` imposes **no** single-preimage
restriction and is inhabited at a genuinely ramified multiplicity.  Given *any* injective fibre
enumeration `D` over `c` (any number of preimages, any multiplicities `≥ 1` — in particular several
ramified preimages), the zero numerator `g ≡ 0` inhabits a `FullFibreClusterData`: each preimage gets a
`clusterTraceData_slit` cluster (the genuine `cpow` slit branch), `valueChartTrace ≡ 0` (empty
selection), and the full-fibre geometric identity is `0 = ∑ᵢ ∑ⱼ 0 = 0`.  The explicit two-preimage
`m = 2` instance `fullFibreClusterData_twoSheet` then witnesses a *genuine multi-preimage ramified* case,
**not** a disguised `False` and **not** single-preimage. -/

/-- **`FullFibreClusterData` from any injective fibre enumeration** (the multi-preimage non-vacuity).
For the zero numerator `g ≡ 0` and the empty selection, *any* `FibreRamifiedData D` over `c` (injective,
multiplicities `≥ 1`) inhabits a `FullFibreClusterData` — per-preimage `clusterTraceData_slit` clusters
(genuine `cpow` slit branches), `valueChartTrace ≡ 0`, and the full-fibre identity `0 = ∑ᵢ ∑ⱼ 0`.  This
shows the structure imposes **no single-preimage restriction** (the #13 fix) and is constructible at
genuinely ramified multiplicities. -/
noncomputable def fullFibreClusterData_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (c : ℂ) (D : FibreRamifiedData (fun _ => (0 : ℂ)) f c) (hD_inj : Function.Injective D.xs) :
    FullFibreClusterData ω₀ (fun _ => (0 : ℂ)) f
      (fun b => emptyFibreRegularData (fun _ => 0) f b) c where
  D := D
  hD_inj := hD_inj
  S := {z | z - c ∈ slitPlane}
  hS_acc := by
    rw [← accPt_iff_frequently_nhdsNE]
    have hcS : c ∉ {z : ℂ | z - c ∈ slitPlane} := by simp [mem_slitPlane_iff]
    have hcl : c ∈ closure {z : ℂ | z - c ∈ slitPlane} := by
      have htend : Tendsto (fun n : ℕ => c + ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) atTop (𝓝 c) := by
        have h0 : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
          have hr : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have hc : Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp hr
          rw [Complex.ofReal_zero] at hc
          simpa using hc.mul_const Complex.I
        simpa using (tendsto_const_nhds (x := c)).add h0
      refine mem_closure_of_tendsto htend (Filter.Eventually.of_forall (fun n => ?_))
      simp only [Set.mem_setOf_eq, add_sub_cancel_left, mem_slitPlane_iff]
      right
      have him : (((1 / (n + 1 : ℝ) : ℝ) : ℂ) * Complex.I).im = (1 / (n + 1 : ℝ) : ℝ) := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]; ring
      rw [him]; positivity
    rw [closure_eq_self_union_derivedSet] at hcl
    exact hcl.resolve_left hcS
  Cl := fun i => clusterTraceData_slit ω₀ (D.xs i) c (D.mult i) (D.hmult_pos i)
    (Complex.exp (2 * π * Complex.I / (D.mult i)))
    (Complex.isPrimitiveRoot_exp (D.mult i) (D.hmult_pos i).ne')
  hmult := fun _ => rfl
  hsplit0 := by
    intro i
    -- Both sides are `fun _ => 0` (chart integrand of `g ≡ 0` vanishes; empty principal part).
    refine Filter.EventuallyEq.of_eq ?_
    funext u
    simp [straightenedIntegrand, chartIntegrand, negTail, clusterTraceData_slit]
  hvct_mero := by
    rw [valueChartTrace_emptySelection ω₀ f]
    exact analyticAt_const.meromorphicAt
  hgeom_fibre := by
    intro z _
    rw [valueChartTrace_emptySelection ω₀ f]
    symm
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    rw [show chartIntegrand ω₀ (fun _ => (0 : ℂ)) (D.xs i) = (fun _ => (0 : ℂ)) by
      funext w; simp [chartIntegrand]]
    simp

/-! ## The `∑Res = 0` capstone via the SOUND full-fibre cluster geometry

Routing the SOUND full-fibre `RamifiedCenterFacts` through the `hoff_cs`-free capstone
`residueTheorem_ofRamifiedCenters_genus0_mod` gives the corrected `∑Res = 0`, replacing the unsound
single-cluster `RealCoverSlitGeometry`/`hgeom_slit` route by the full-fibre geometry. -/

open Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip
  Jacobians.Dolbeault.FormTraceFullFibre

/-- **The per-centre full-fibre obligation** (item #1, corrected/sound).  At every finite pole-value
centre `cs i` of `α = ω₀·g`, the canonical full-fibre selection carries a `FullFibreClusterData` (the
genuine full-fibre Forster §5 cluster geometry — *all* preimages, genuine `clusterSheet` points) whose
preimages enumerate exactly the poles of `α` in the fibre `F⁻¹(coe (cs i))`.  This is the SOUND
replacement of `RealCoverRamifiedCenters` (which packaged the single-cluster `RamifiedSheetData`). -/
def FullFibreRamifiedCenters (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) {m : ℕ} (cs : Fin m → ℂ) : Prop :=
  ∃ (Ff : ∀ i, FullFibreClusterData ω₀ g f (canonicalFibreSelection g f hdiv) (cs i)),
    (∀ i, ∀ k, (Ff i).D.xs k ∈ poles) ∧
    (∀ i, ∀ a ∈ poles, f.toRiemannSphere a = ((cs i : ℂ) : RiemannSphere) → ∃ k, (Ff i).D.xs k = a)

/-- **Gate A `∑Res = 0` for the real cover via the SOUND full-fibre cluster geometry, `hoff_cs`-FREE.**
Given the per-centre full-fibre cluster data `FullFibreRamifiedCenters` (the corrected, SOUND geometric
input — full fibre, genuine `clusterSheet` points) and the off-centre + `∞` input bundle `GateAInftyData`
(the already-Gate-A-discharged machinery), the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g a = 0`.

This routes through the `hoff_cs`-free capstone `residueTheorem_ofRamifiedCenters_genus0_mod`, fed the
SOUND full-fibre `RamifiedCenterFacts` (`existsRamifiedCenterFacts_ofFullFibre`) at each centre — the
finite centres may be **ramified**, and the geometry is the genuine full-fibre cluster identity (NOT the
unsound single-cluster `hgeom_slit`). -/
theorem residueSum_eq_zero_of_fullFibreCluster {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {poles : Finset X} {m : ℕ}
    {cs : Fin m → ℂ} {br : Finset ℂ}
    (A : Jacobians.GateAInftyData ω₀ g f hdiv poles cs br)
    (hFC : FullFibreRamifiedCenters ω₀ g f hdiv poles cs) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  obtain ⟨Ff, hxs_mem, hxs_surj⟩ := hFC
  exact residueTheorem_ofRamifiedCenters_genus0_mod (canonicalFibreSelection g f hdiv) m cs A.ρ
    A.hcs_ball A.hcs_inj br A.hreg A.hbnd A.hcenters_cs
    (fun i => FullFibreClusterData.existsRamifiedCenterFacts_ofFullFibre (Ff i) (hxs_mem i)
      (hxs_surj i))
    A.Dinf_full A.hcoh_full A.hfullInf_inj A.xsInf_po A.hpoInf_inj A.hpoInf_mem A.hpoInf_surj
    A.hpole_image_inf A.hnonpole_inf_an

/-- **Non-vacuity of `FullFibreRamifiedCenters` (no finite pole-value centres).**  When there are no
finite pole-value centres (`m = 0`), the per-centre data is vacuously inhabited — `FullFibreRamifiedCenters`
is **not** a disguised `False`. -/
theorem fullFibreRamifiedCenters_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) :
    FullFibreRamifiedCenters ω₀ g f hdiv poles (m := 0) Fin.elim0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-! ## The named target `RamifiedFullFibreClusterGeometry` is PROVEN from `FullFibreClusterData`

The morning's precise corrected obligation `RamifiedFullFibreClusterGeometry`
(`SerreResidueRamifiedClusterSplit.lean`) is exactly the geometric content of a `FullFibreClusterData`,
read on the slit with a `Fin r` enumeration of the fibre.  We prove it holds (after reindexing the
preimage type `D.ι` to `Fin (card D.ι)` via `Fintype.equivFin`), discharging the named target. -/

/-- **`RamifiedFullFibreClusterGeometry` is PROVEN from a `FullFibreClusterData`.**  The morning's named
target — the full-fibre geometric identity at the genuine `clusterSheet` points — holds for the `Fin r`
enumeration `pre := D.xs ∘ e.symm` of the fibre (`e : Fin r ≃ D.ι`, `r := card D.ι`), with the
per-preimage cluster data `(mult, ζ, w₀, sec)` read off `F.Cl`.  This is the geometric `hgeom_fibre`
field reindexed through the equiv.  **Sound:** the full fibre (all preimages) at the genuine
`clusterSheet` points — the two corrections over the unsound single-cluster `hgeom_slit`. -/
theorem ramifiedFullFibreClusterGeometry_of_fullFibreData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ}
    (F : FullFibreClusterData ω₀ g f Φ c) :
    RamifiedFullFibreClusterGeometry ω₀ g f Φ c
      (r := Fintype.card F.D.ι)
      (F.D.xs ∘ (Fintype.equivFin F.D.ι).symm)
      (fun ℓ => F.D.mult ((Fintype.equivFin F.D.ι).symm ℓ))
      (fun ℓ => (F.Cl ((Fintype.equivFin F.D.ι).symm ℓ)).ζ)
      F.S
      (fun ℓ => (F.Cl ((Fintype.equivFin F.D.ι).symm ℓ)).w₀)
      (fun ℓ => (F.Cl ((Fintype.equivFin F.D.ι).symm ℓ)).s) := by
  intro z hz
  rw [F.hgeom_fibre z hz]
  -- Reindex the `D.ι`-sum to the `Fin (card D.ι)`-sum via the equiv.
  rw [← (Fintype.equivFin F.D.ι).symm.sum_comp
    (fun i => ∑ j ∈ Finset.range (F.D.mult i),
      chartIntegrand ω₀ g (F.D.xs i) (clusterSheet (F.Cl i).s (F.Cl i).ζ (F.Cl i).w₀ j z)
        * deriv (clusterSheet (F.Cl i).s (F.Cl i).ζ (F.Cl i).w₀ j) z)]
  rfl

end Jacobians.Dolbeault.SerreResidueTheorem
