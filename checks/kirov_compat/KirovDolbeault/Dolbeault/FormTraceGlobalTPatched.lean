/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceBranchValueOff
import KirovDolbeault.Dolbeault.FormTraceBranchAwareSelection

/-!
# The branch-value-patched global trace `Tᵉˣᵗ` and Gate A `∑Res = 0` (Miranda §VIII.3 — the close)

This file is the **unification step** for Gate A (`∑ₐ Resₐ(α) = 0`, `α = ω₀·g`).  All conceptual walls
are down; the proven engines are wired into one instantiation of `globalTrace_of_glue`
(`FormTraceGlobalTAssemble`), using the **value-correct branch-patched trace** — *not* the false
`hbranch`/`BranchAwareTraceSelection` continuity route (the raw `valueChartTrace` value at a branch
value is a *partial* sheet sum, not the analytic-continuation limit, so it is discontinuous there).

The fix — exactly Miranda's "the trace is a single (mero)morphic function on `ℂℙ¹`, extending across
branch points" — is to **patch** the geometric trace to its removable limit at each branch value, so
that the patched trace `Tᵉˣᵗ` is genuinely `AnalyticAt` everywhere off the pole-values, via the proven
planar removable engine `FormTraceBranchPlanarExtend`/`FormTraceBranchValueOff`.

## The patched trace

For a finite branch-value set `br : Finset ℂ`,

> `valueChartTracePatched ω₀ f Φ br z := if z ∈ br then limUnder (𝓝[≠] z) (valueChartTrace ω₀ f Φ)
>                                       else valueChartTrace ω₀ f Φ z`,

i.e. `valueChartTrace` everywhere except at the (finitely many) branch values, where it is replaced by
its punctured-limit value (the multi-point `Function.update` form of `valueChartTrace_branchExtension`).
The patch only changes the value at the finitely-many branch values, so it shares **all** the
finite/`∞` glue with `valueChartTrace`, while being analytic *at* each branch value (the partial-sum
junk is repaired to the limit).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `valueChartTracePatched` — the multi-point branch-patched trace, with `…_eventuallyEq` (germ-equal to
  `valueChartTrace` off `br`) and `…_of_not_mem` (equal off `br`).
* `analyticAt_valueChartTracePatched_off_centres` — the full `hT_off` for `Tᵉˣᵗ`: at every value off the
  pole-centres, `Tᵉˣᵗ` is analytic — regular values via the moving-sheet coherence (germ-transport),
  branch values via the **patched** removable engine (`analyticAt_branchExtension_valueChartTrace`,
  needing punctured analyticity + the boundedness crux — *no* false continuity demand).
* `PatchedTraceSelection` — the assembled Gate-A input using `Tᵉˣᵗ`: the per-value moving-sheet
  coherence (no labeling, via the symmetric lever), the **branch-value boundedness crux** (the genuine
  §VIII.3 analytic content, reduced sheet-by-sheet to the proven ratio atom), the `∞`-glue,
  junk-freeness, and the kirovGenus-`0` `∞`-vanishing.
* `residueSum_eq_zero_of_patchedTraceSelection` — **Gate A `∑Res = 0`** from it, via the proven
  `residueSum_eq_zero_of_glue`.
* `patchedTraceSelection_empty` / `…_holomorphic` — end-to-end non-vacuity (empty-pole case).

## The genuine remaining obligation

After this unification the *only* non-bookkeeping content carried by `PatchedTraceSelection` is exactly
Miranda's §VIII.3 geometry:

1. the **branch-value boundedness crux** `(z − b₀)·valueChartTrace z → 0` (the §VIII.3 analytic heart;
   reduced sheet-by-sheet to the proven `FormTraceBranchPlanarExtend.tendsto_zero_section_deriv`);
2. the **germ-coherence** (the per-value moving-sheet data + the `∞`-glue) — the branched-cover
   monodromy, handled labeling-free by the symmetric lever; and
3. the kirovGenus-`0` `∞`-vanishing + junk-freeness.

The false `hbranch` continuity route is *not* revived: branch values are handled by the value-correct
patch, whose analyticity rests on the boundedness crux (genuine, partially proven) — never on
continuity of the raw partial-sum trace.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr` is single-valued by
  *symmetry* and extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceBranchPlanar
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The multi-point branch-patched trace -/

/-- **The branch-value-patched global trace.**  `valueChartTrace ω₀ f Φ` everywhere except at the
finitely-many branch values `br`, where it is replaced by its punctured-limit value (the
removable-singularity limit).  This is the multi-point form of `valueChartTrace_branchExtension`: the
value-correct trace, analytic across branch points (the partial-sum junk repaired to the limit). -/
noncomputable def valueChartTracePatched (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) : ℂ → ℂ :=
  fun z => if z ∈ br then limUnder (𝓝[≠] z) (valueChartTrace ω₀ f Φ) else valueChartTrace ω₀ f Φ z

/-- Off `br` the patched trace equals `valueChartTrace` (the patch only touches branch values). -/
theorem valueChartTracePatched_of_not_mem (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) {z : ℂ} (hz : z ∉ br) :
    valueChartTracePatched ω₀ f Φ br z = valueChartTrace ω₀ f Φ z := by
  rw [valueChartTracePatched, if_neg hz]

/-- At a branch value `b₀ ∈ br`, the patched trace coincides with the single-point removable extension
`valueChartTrace_branchExtension` (both replace the value by the punctured limit). -/
theorem valueChartTracePatched_eq_branchExtension (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) {b₀ : ℂ}
    (hb₀ : b₀ ∈ br) :
    valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝 b₀] valueChartTrace_branchExtension ω₀ f Φ b₀ := by
  -- A punctured neighbourhood of `b₀` avoids the finite set `br \ {b₀}`; there both sides equal
  -- `valueChartTrace`.  At `b₀` both equal the punctured limit.
  have hfin : ((br : Set ℂ) \ {b₀}).Finite := (br.finite_toSet).diff
  have hcompl : (((br : Set ℂ) \ {b₀}))ᶜ ∈ 𝓝 b₀ :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [hcompl] with z hz_compl
  by_cases hzb : z = b₀
  · -- At `b₀`: both equal the punctured limit.
    subst hzb
    rw [valueChartTracePatched, if_pos hb₀, valueChartTrace_branchExtension, Function.update_self]
  · -- Off `b₀`: `z ∉ br` (else `z ∈ br \ {b₀}`, contradicting `hz_compl`), so both `= valueChartTrace`.
    have hznotbr : z ∉ br := by
      intro hzbr; exact hz_compl ⟨hzbr, fun h => hzb (by simpa using h)⟩
    rw [valueChartTracePatched_of_not_mem ω₀ f Φ br hznotbr,
      valueChartTrace_branchExtension, Function.update_of_ne hzb]

/-- The patched trace germ-equals `valueChartTrace` on the punctured neighbourhood of *any* point: off
`br` they agree on a full neighbourhood (branch values are isolated), and at a branch value they agree
off the point (the patch only changes the value there). -/
theorem valueChartTracePatched_eventuallyEq (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) (z : ℂ) :
    valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝[≠] z] valueChartTrace ω₀ f Φ := by
  -- A punctured neighbourhood of `z` avoids `br \ {z}` (finite); there `z' ∉ br` so the patch is inert.
  have hfin : ((br : Set ℂ) \ {z}).Finite := (br.finite_toSet).diff
  have hcompl : (((br : Set ℂ) \ {z}))ᶜ ∈ 𝓝 z := hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with z' hz'_ne hz'_compl
  have hz'b : z' ≠ z := by simpa using hz'_ne
  have hz'notbr : z' ∉ br := fun hz'br => hz'_compl ⟨hz'br, fun h => hz'b (by simpa using h)⟩
  rw [valueChartTracePatched_of_not_mem ω₀ f Φ br hz'notbr]

/-- The reciprocal coefficient of the patched trace germ-equals that of `valueChartTrace` near `0`:
for `ζ ≠ 0` small, `ζ⁻¹` is large (escapes the finite `br`), so `Tᵉˣᵗ (ζ⁻¹) = valueChartTrace (ζ⁻¹)`,
hence the `recipCoeff`s (`−·(ζ⁻¹)·ζ⁻²`) agree.  This carries the `∞`-glue from `valueChartTrace` to
`Tᵉˣᵗ` unchanged. -/
theorem recipCoeff_valueChartTracePatched_eventuallyEq (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) :
    recipCoeff (valueChartTracePatched ω₀ f Φ br) =ᶠ[𝓝[≠] 0] recipCoeff (valueChartTrace ω₀ f Φ) := by
  -- `‖ζ⁻¹‖ → ∞` as `ζ → 0` within `≠`, so eventually `ζ⁻¹` is outside the bounded finite set `br`.
  obtain ⟨R, hR⟩ := (br.finite_toSet).isBounded.subset_ball (0 : ℂ)
  have htend : Tendsto (fun ζ : ℂ => ‖ζ⁻¹‖) (𝓝[≠] 0) atTop := by
    simp only [norm_inv]
    exact (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp (tendsto_norm_nhdsNE_zero (E := ℂ))
  filter_upwards [htend.eventually_gt_atTop R] with ζ hζ
  have hζnotbr : ζ⁻¹ ∉ br := by
    intro hmem
    have : ζ⁻¹ ∈ ball (0 : ℂ) R := hR hmem
    rw [mem_ball, dist_zero_right] at this
    linarith
  show -(valueChartTracePatched ω₀ f Φ br (ζ⁻¹)) * ζ ^ (-2 : ℤ)
    = -(valueChartTrace ω₀ f Φ (ζ⁻¹)) * ζ ^ (-2 : ℤ)
  rw [valueChartTracePatched_of_not_mem ω₀ f Φ br hζnotbr]

/-! ### The branch-value boundedness crux from sheet sections (the §VIII.3 analytic port)

This is **the one genuinely-new analytic step** of the close: discharge the boundedness crux `hbnd`
`(z − b₀)·valueChartTrace z → 0` at a branch value `b₀` from the proven planar per-sheet ratio atom
`FormTraceBranchPlanarExtend.tendsto_zero_section_deriv`.

Near a branch value `b₀`, the geometric trace is, on a punctured neighbourhood, the **moving fibre sum**
`∑ j, chartIntegrand ω₀ g x_j (rinv_j z)·deriv (rinv_j) z` read along the chart pullbacks `rinv_j =
chart_{x_j} ∘ sec_j` of the cover sheets `sec_j : ℂ → X` through *all* the preimages `x_j` of `b₀`
(ramified **and** unramified — `sec_j` is a continuous section of `f.holoRepr`, its chart pullback a
right-inverse of `φ_j := f.holoRepr ∘ chart_{x_j}.symm`).  Each per-sheet term satisfies the bound:

* `(z − b₀)·deriv (rinv_j) z → 0` — the proven ratio atom `tendsto_zero_section_deriv`, with the section
  `s := rinv_j` and its analytic left-inverse `F := φ_j` (`φ_j (rinv_j z) = z` near `b₀`, `φ_j w₀ = b₀`,
  `φ_j` not eventually constant since `f` is nonconstant; the ramified-sheet derivative blow-up is killed
  by the `z − b₀` factor — *no* Puiseux/symmetric-function machinery, just `φ_j − b₀ = (w − w₀)^e·g`);
* `chartIntegrand ω₀ g x_j` is continuous at `rinv_j b₀ = w₀` (`α = ω₀·g` holomorphic at the non-pole
  `x_j` — the adapted cover separates poles from the branch locus).

Summed over the finite fibre (`tendsto_zero_fibreSum`/`tendsto_zero_perSheet`) and transported along the
moving-sum germ-equality, this gives `hbnd`.  This is the planar shadow of the proven bundle-side
`TraceForm.traceLocalCoeff_mul_sub_tendsto_zero_Y` — but the uniform-cardinality/finite-subcover
machinery is *replaced* by the explicit sheet enumeration `sec_j` supplied per branch value (the moving
selection's fibre data), and the per-sheet content is the same proven ratio atom. -/

/-- **The branch-value boundedness crux from sheet sections.**  Let `b₀ : ℂ` and `ι : Type*` finite.
Suppose the geometric trace germ-equals, on the *punctured* neighbourhood of `b₀`, the moving fibre sum
along chart pullbacks `rinv : ι → ℂ → ℂ` of sheet sections through preimages `x : ι → X` of `b₀`:

* `hgerm` — `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] fun z => ∑ j, chartIntegrand ω₀ g (x j) (rinv j z)·deriv
  (rinv j) z`;
* per sheet `j`: `rinv j b₀ = w₀ j := (chartAt ℂ (x j)) (x j)` (`hbase`); `rinv j` continuous at `b₀`
  (`hcont`); `φ_j := f.holoRepr ∘ chart_{x j}.symm` analytic at `w₀ j` (`hF_an`), with `φ_j (w₀ j) = b₀`
  (`hFw₀`) and `φ_j` not eventually constant near `w₀ j` (`hFnc`); `φ_j (rinv j z) = z` near `b₀`
  (`hsec`); the chain-rule identity `deriv (rinv j) z · deriv φ_j (rinv j z) = 1` near `b₀` (`hchain`);
  and `chartIntegrand ω₀ g (x j)` continuous at `w₀ j` (`hcoeff` — `α` holomorphic at the non-pole `x j`).

Then the boundedness crux `(z − b₀)·valueChartTrace ω₀ f Φ z → 0` holds.  *Proof.*  Each per-sheet term
`→ 0` by `tendsto_zero_perSheet` (the coeff continuous × the ratio atom `tendsto_zero_section_deriv`);
sum over the finite fibre (`tendsto_zero_fibreSum`); transport along `hgerm`. -/
theorem tendsto_zero_valueChartTrace_of_sections (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    {ι : Type*} [Fintype ι] (x : ι → X) (rinv : ι → ℂ → ℂ)
    (hgerm : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
      fun z => ∑ j, chartIntegrand ω₀ g (x j) (rinv j z) * deriv (rinv j) z)
    (hbase : ∀ j, rinv j b₀ = (chartAt ℂ (x j)) (x j))
    (hcont : ∀ j, ContinuousAt (rinv j) b₀)
    (hF_an : ∀ j, AnalyticAt ℂ (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w))
      ((chartAt ℂ (x j)) (x j)))
    (hFw₀ : ∀ j, f.holoRepr ((chartAt ℂ (x j)).symm ((chartAt ℂ (x j)) (x j))) = b₀)
    (hFnc : ∀ j, ¬ ∀ᶠ w in 𝓝 ((chartAt ℂ (x j)) (x j)),
      f.holoRepr ((chartAt ℂ (x j)).symm w) = b₀)
    (hsec : ∀ j, ∀ᶠ z in 𝓝[≠] b₀, f.holoRepr ((chartAt ℂ (x j)).symm (rinv j z)) = z)
    (hchain : ∀ j, ∀ᶠ z in 𝓝[≠] b₀,
      deriv (rinv j) z * deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) (rinv j z) = 1)
    (hcoeff : ∀ j, ContinuousAt (chartIntegrand ω₀ g (x j)) ((chartAt ℂ (x j)) (x j))) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0) := by
  -- The fibre-sum boundedness from per-sheet boundedness.
  have hsum : Tendsto (fun z => (z - b₀) *
      ∑ j, chartIntegrand ω₀ g (x j) (rinv j z) * deriv (rinv j) z) (𝓝[≠] b₀) (𝓝 0) := by
    refine tendsto_zero_fibreSum (ι := ι) (fun j => ?_)
    -- Per sheet: `(z − b₀)·coeff(rinv z)·deriv(rinv) z → 0`.
    refine tendsto_zero_perSheet ?_ (hcont j) ?_
    · -- `(z − b₀)·deriv (rinv j) z → 0` from the ratio atom on the left inverse `φ_j`.
      exact tendsto_zero_section_deriv (hcont j) (hbase j) (hF_an j) (hFw₀ j) (hFnc j)
        (hsec j) (hchain j)
    · -- `chartIntegrand` continuous at `rinv j b₀ = w₀ j`.
      rw [hbase j]; exact hcoeff j
  -- Transport along the germ-equality `hgerm`.
  refine hsum.congr' ?_
  filter_upwards [hgerm] with z hz
  show (z - b₀) * ∑ j, chartIntegrand ω₀ g (x j) (rinv j z) * deriv (rinv j) z
    = (z - b₀) * valueChartTrace ω₀ f Φ z
  rw [hz]

/-- **The branch-value boundedness crux from smooth sheet sections.**  The reduced interface for
`tendsto_zero_valueChartTrace_of_sections`: the per-sheet differentiability/right-inverse data is
*derived* from a family of smooth cover sheets `sec : ι → ℂ → X` through the preimages `x j := sec j b₀`
of `b₀`.  The caller supplies only the genuine geometric content:

* `hsmooth` — each `sec j` is `C^ω` at `b₀`;
* `hsec_sec` — each `sec j` is a section of `f.holoRepr` near `b₀` (`f.holoRepr (sec j b') = b'`);
* `hnp` — each `x j = sec j b₀` is a **non-pole** of `f` (`0 ≤ orderAtPoint`), so `φ_j := f.holoRepr ∘
  chart_{x j}.symm` is analytic at `chart_{x j}(x j)`;
* `hFnc` — `φ_j` is not eventually constant `≡ b₀` near `chart_{x j}(x j)` (the cover is nonconstant);
* `hcoeff` — `chartIntegrand ω₀ g (x j)` is continuous at `chart_{x j}(x j)` (`α` holomorphic at the
  non-pole `x j`);
* `hgerm` — the moving-sum germ-equality of `valueChartTrace` with the fibre sum along the chart pullbacks
  `chart_{x j} ∘ sec j` (the per-value monodromy content).

The right-inverse identity `hsec`, the base/continuity, the analytic left-inverse `hF_an`/`hFw₀`, and the
chain-rule identity `hchain` are all discharged from the section smoothness + non-poleness via
`chartPullback_section_rinv`, `analyticAt_holoRepr_chartPullback_of_orderNonneg`, and
`differentiableAt_chart_pullback_section`. -/
theorem tendsto_zero_valueChartTrace_of_sheetSections (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    {ι : Type*} [Fintype ι] (sec : ι → ℂ → X)
    (hsmooth : ∀ j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec j) b₀)
    (hsec_sec : ∀ j, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec j b') = b')
    (hnp : ∀ j, 0 ≤ f.orderAtPoint (sec j b₀))
    (hFnc : ∀ j, ¬ ∀ᶠ w in 𝓝 ((chartAt ℂ (sec j b₀)) (sec j b₀)),
      f.holoRepr ((chartAt ℂ (sec j b₀)).symm w) = b₀)
    (hcoeff : ∀ j, ContinuousAt (chartIntegrand ω₀ g (sec j b₀)) ((chartAt ℂ (sec j b₀)) (sec j b₀)))
    (hgerm : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀]
      fun z => ∑ j, chartIntegrand ω₀ g (sec j b₀)
        ((chartAt ℂ (sec j b₀)) (sec j z)) * deriv (fun w => (chartAt ℂ (sec j b₀)) (sec j w)) z) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0) := by
  classical
  -- Abbreviations: the fibre points `x j` and the chart pullbacks `rinv j`.
  set x : ι → X := fun j => sec j b₀ with hx
  set rinv : ι → ℂ → ℂ := fun j z => (chartAt ℂ (x j)) (sec j z) with hrinv
  -- The right-inverse data from `chartPullback_section_rinv` (on `𝓝 b₀`).
  have hrinv_props : ∀ j, rinv j b₀ = (chartAt ℂ (x j)) (x j) ∧
      ContinuousAt (rinv j) b₀ ∧
      ∀ᶠ b' in 𝓝 b₀, f.holoRepr ((chartAt ℂ (x j)).symm (rinv j b')) = b' :=
    fun j => chartPullback_section_rinv f (sec := sec j) (b₀ := b₀) (x := x j) rfl
      (hsmooth j).continuousAt (hsec_sec j)
  -- `φ_j := f.holoRepr ∘ chart_{x j}.symm` analytic at `chart_{x j}(x j)` (non-pole).
  have hF_an : ∀ j, AnalyticAt ℂ (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w))
      ((chartAt ℂ (x j)) (x j)) := fun j =>
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg (hnp j)
  -- `φ_j (chart_{x j}(x j)) = f.holoRepr (x j) = b₀` (from the section identity at `b₀`).
  have hFw₀ : ∀ j, f.holoRepr ((chartAt ℂ (x j)).symm ((chartAt ℂ (x j)) (x j))) = b₀ := by
    intro j
    -- The section identity at `b₀`: `f.holoRepr (chart⁻¹ (rinv j b₀)) = b₀`, with `rinv j b₀ = chart (x j)`.
    have h := ((hrinv_props j).2.2).self_of_nhds
    rwa [(hrinv_props j).1] at h
  -- `rinv j` differentiable on a neighbourhood of `b₀` (the chart pullback of a `C^ω` section).
  have hrinv_diff : ∀ j, ∀ᶠ z in 𝓝 b₀, DifferentiableAt ℂ (rinv j) z := by
    intro j
    have hsmooth_nhds : ∀ᶠ z in 𝓝 b₀, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec j) z :=
      (contMDiffAt_iff_contMDiffAt_nhds (by decide : (ω : WithTop ℕ∞) ≠ ∞)).mp (hsmooth j)
    -- At each `z` near `b₀`, `rinv j = chart_{x j} ∘ sec j` is differentiable — but the chart base is
    -- `x j = sec j b₀`, fixed.  Use that `chart_{x j}` is `C^ω` on its source, which contains `sec j z`
    -- for `z` near `b₀` (continuity), so `chart_{x j} ∘ sec j` is `C^ω` at `z`.
    have hmem : ∀ᶠ z in 𝓝 b₀, sec j z ∈ (chartAt ℂ (x j)).source :=
      (hsmooth j).continuousAt.eventually_mem
        ((chartAt ℂ (x j)).open_source.mem_nhds (mem_chart_source ℂ (x j)))
    filter_upwards [hsmooth_nhds, hmem] with z hz_smooth hz_mem
    have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (x j)) (sec j z) :=
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x j)) _ hz_mem).contMDiffAt
        ((chartAt ℂ (x j)).open_source.mem_nhds hz_mem)
    exact (contMDiffAt_iff_contDiffAt.1 (hchart.comp z hz_smooth)).differentiableAt (by decide)
  -- `φ_j` differentiable near `chart_{x j}(x j)` (analytic), pulled to `rinv j z` near `b₀`.
  have hF_diff_at : ∀ j, ∀ᶠ z in 𝓝 b₀,
      DifferentiableAt ℂ (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) (rinv j z) := by
    intro j
    have hcontinv : ContinuousAt (rinv j) b₀ := (hrinv_props j).2.1
    have hF_diff_nhds : ∀ᶠ w in 𝓝 ((chartAt ℂ (x j)) (x j)),
        DifferentiableAt ℂ (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) w :=
      (hF_an j).eventually_analyticAt.mono (fun _ h => h.differentiableAt)
    have hval : rinv j b₀ = (chartAt ℂ (x j)) (x j) := (hrinv_props j).1
    exact hcontinv.eventually_mem (hval ▸ hF_diff_nhds)
  -- The chain-rule identity (on `𝓝[≠] b₀`) from `φ_j ∘ rinv_j = id` (on `𝓝 b₀`) + differentiability.
  have hchain : ∀ j, ∀ᶠ z in 𝓝[≠] b₀,
      deriv (rinv j) z * deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) (rinv j z) = 1 := by
    intro j
    have hsec_nhds : ∀ᶠ z in 𝓝 b₀,
        (fun w => f.holoRepr ((chartAt ℂ (x j)).symm (rinv j w))) =ᶠ[𝓝 z] id := by
      filter_upwards [eventually_eventually_nhds.mpr (hrinv_props j).2.2] with z hz
      filter_upwards [hz] with w hw using hw
    have key : ∀ᶠ z in 𝓝 b₀,
        deriv (rinv j) z * deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) (rinv j z) = 1 := by
      filter_upwards [hrinv_diff j, hF_diff_at j, hsec_nhds] with z hrz hFz hsecz
      have hcomp : deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm (rinv j w))) z
          = deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm w)) (rinv j z) * deriv (rinv j) z :=
        deriv_comp z hFz hrz
      have hid : deriv (fun w => f.holoRepr ((chartAt ℂ (x j)).symm (rinv j w))) z = 1 := by
        rw [hsecz.deriv_eq]; simp
      rw [hid] at hcomp
      linear_combination -hcomp
    exact key.filter_mono nhdsWithin_le_nhds
  -- The right-inverse `hsec` on `𝓝[≠] b₀`.
  have hsec : ∀ j, ∀ᶠ z in 𝓝[≠] b₀, f.holoRepr ((chartAt ℂ (x j)).symm (rinv j z)) = z :=
    fun j => ((hrinv_props j).2.2).filter_mono nhdsWithin_le_nhds
  -- Apply the section-level boundedness lemma.
  exact tendsto_zero_valueChartTrace_of_sections ω₀ f Φ x rinv hgerm
    (fun j => (hrinv_props j).1) (fun j => (hrinv_props j).2.1) hF_an hFw₀ hFnc hsec hchain hcoeff

/-! ### Off-centre analyticity of the patched trace (`hT_off`)

`hT_off` for the patched trace dispatches each value off the pole-centres to either:
* a **regular value** (off `centres ∪ br`): there the patch is inert on a *full* neighbourhood (branch
  values isolated), so analyticity transfers from `valueChartTrace` (the moving-sheet coherence); or
* a **branch value** `b₀ ∈ br`: there `Tᵉˣᵗ` germ-equals the single-point removable extension
  `valueChartTrace_branchExtension ω₀ f Φ b₀`, which is `AnalyticAt b₀` by the proven planar engine
  `analyticAt_branchExtension_valueChartTrace` (needing punctured analyticity + the boundedness crux). -/

/-- **Analyticity of the patched trace at a regular value** (off `br`): the patch is inert on a full
neighbourhood of `z` (a small ball avoids the finite `br`), so analyticity transfers from
`valueChartTrace`. -/
theorem analyticAt_valueChartTracePatched_of_not_mem (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (br : Finset ℂ) {z : ℂ}
    (hz : z ∉ br) (han : AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z) :
    AnalyticAt ℂ (valueChartTracePatched ω₀ f Φ br) z := by
  -- `Tᵉˣᵗ =ᶠ[𝓝 z] valueChartTrace`: a ball around `z` avoids `br` (finite, `z ∉ br`).
  have hcompl : ((br : Set ℂ))ᶜ ∈ 𝓝 z := br.finite_toSet.isClosed.compl_mem_nhds (by simpa using hz)
  have heq : valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝 z] valueChartTrace ω₀ f Φ := by
    filter_upwards [hcompl] with z' hz'
    exact valueChartTracePatched_of_not_mem ω₀ f Φ br hz'
  exact han.congr heq.symm

/-- **Off-centre analyticity of the patched trace `Tᵉˣᵗ` (the `hT_off` ingredient).**  Let `centres
br : Finset ℂ` (pole-values, branch values).  Suppose:

* `hreg` — at every value `w` off `centres ∪ br`, `valueChartTrace ω₀ f Φ` is analytic (the moving-sheet
  coherence); and
* at every branch value `b₀ ∈ br` off the centres, the two inputs of the planar removable engine hold:
  `hpunct` (punctured analyticity of `valueChartTrace` at `b₀`) and `hbnd` (the boundedness crux).

Then `Tᵉˣᵗ` is analytic at **every** value off the centres.  Regular values transfer from `hreg`
(patch inert); branch values use the value-correct removable extension (no false continuity demand). -/
theorem analyticAt_valueChartTracePatched_off_centres (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (centres br : Finset ℂ)
    (hreg : ∀ w ∉ centres ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbranch : ∀ b₀ ∈ br, b₀ ∉ centres →
      (∀ᶠ z in 𝓝[≠] b₀, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z) ∧
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    {z : ℂ} (hz : z ∉ centres) :
    AnalyticAt ℂ (valueChartTracePatched ω₀ f Φ br) z := by
  by_cases hzbr : z ∈ br
  · -- Branch value: `Tᵉˣᵗ =ᶠ[𝓝 z] valueChartTrace_branchExtension`, which is analytic at `z`.
    obtain ⟨hpunct, hbnd⟩ := hbranch z hzbr hz
    have hext_an : AnalyticAt ℂ (valueChartTrace_branchExtension ω₀ f Φ z) z :=
      analyticAt_branchExtension_valueChartTrace ω₀ f Φ hpunct hbnd
    exact hext_an.congr (valueChartTracePatched_eq_branchExtension ω₀ f Φ br hzbr).symm
  · -- Regular value: patch inert, analyticity transfers from `hreg`.
    exact analyticAt_valueChartTracePatched_of_not_mem ω₀ f Φ br hzbr
      (hreg z (by simp [Finset.mem_union, hz, hzbr]))

/-! ### Punctured analyticity at a branch value from the regular-value coherence

The branch-value removable engine needs `valueChartTrace` analytic on a *punctured* neighbourhood of
each branch value `b₀`.  Branch (and pole) values are isolated, so a small punctured ball around `b₀`
avoids the finite set `(centres ∪ br) \ {b₀}` and lands in the regular-value regime, where `hreg`
gives analyticity.  This is the same isolation argument as `analyticAt_valueChartTrace_off_centres`,
extracted so the patched assembly can feed `hbranch`'s punctured-analyticity input from `hreg`. -/

/-- **Punctured analyticity at a branch value from the regular-value coherence.**  If
`valueChartTrace ω₀ f Φ` is analytic at every value off `centres ∪ br` (`hreg`), then at any
`b₀` it is analytic on the punctured neighbourhood `𝓝[≠] b₀` (a small punctured ball avoids the
finite `(centres ∪ br) \ {b₀}`).  Supplies the punctured-analyticity input of the branch-value
removable engine from the regular-value coherence — no branch-specific data. -/
theorem eventually_analyticAt_valueChartTrace_of_reg (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (centres br : Finset ℂ)
    (hreg : ∀ w ∉ centres ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w) (b₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] b₀, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) z := by
  have hfin : (((centres ∪ br : Finset ℂ) : Set ℂ) \ {b₀}).Finite := ((centres ∪ br).finite_toSet).diff
  have hcompl : ((((centres ∪ br : Finset ℂ) : Set ℂ) \ {b₀}))ᶜ ∈ 𝓝 b₀ :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with w hw_ne hw_compl
  refine hreg w ?_
  intro hw_mem
  exact hw_compl ⟨by simpa using hw_mem, fun hwz => hw_ne (by simpa using hwz)⟩

/-! ### The patched trace selection — the assembled Gate-A input

We bundle the genuine §VIII.3 geometry into one structure, feeding the value-correct **patched** trace
`Tᵉˣᵗ = valueChartTracePatched ω₀ f Φ br` to `residueSum_eq_zero_of_glue`.  Mirrors
`BranchAwareTraceSelection` for the finite/`∞` bookkeeping and the pole-value coherence, but:

* the off-exceptional content is split into a per-regular-value moving-sheet coherence datum `Creg`
  (no labeling, via the symmetric lever) **and**, at the finitely-many branch values, the genuine
  §VIII.3 **boundedness crux** `hbnd` (replacing the *false* `BranchAwareTraceSelection.hbranch`
  continuity — the raw trace value at a branch value is a partial sum, hence discontinuous);
* `hT_off` for `Tᵉˣᵗ` is then `analyticAt_valueChartTracePatched_off_centres`: regular values via the
  coherence (patch inert), branch values via the value-correct removable extension (whose analyticity
  rests on `hbnd`, never on continuity).

The finite glue / `∞`-glue / junk-freeness / kirovGenus-`0` for `Tᵉˣᵗ` are transported from `valueChartTrace`
along the germ-equalities (`valueChartTracePatched_eventuallyEq`,
`recipCoeff_valueChartTracePatched_eventuallyEq`) — `Tᵉˣᵗ` differs only at the finitely-many branch
values, so it shares every germ at the centres and at `∞`. -/

/-- **A patched-trace selection** for `α = ω₀·g` over `poles`, relative to an adapted cover `hac`.
The honest §VIII.3 Gate-A input feeding the value-correct **patched** trace to
`residueSum_eq_zero_of_glue`:

* `Φ`, `cs`/`ρ`/`hcenters_cs`, `Dinf`/`hxs_*` — the global selection + finite/`∞` enumeration;
* `Cfin i` (with `hCfin_D`) — the per-pole-value moving-sheet coherence datum (fixed fibre = the pole
  sub-fibre; *no labeling*);
* `br : Finset ℂ` — the finite branch values;
* `Creg z` (for `z ∉ cs ∪ br`) + `hCreg_g` — the per-regular-value moving-sheet coherence datum with
  `g`'s chart-pullback analytic at its fibre points (regular-value analyticity);
* `hbnd` — at each branch value off the centres, the §VIII.3 **boundedness crux** `(z − b₀)·valueChartTrace
  z → 0` (the genuine analytic content; reduced sheet-by-sheet to the proven ratio atom);
* `hglue_inf` / `hcont_int` / `R₀`+`hR₀_*` — the `∞`-glue, junk-freeness, kirovGenus-`0` `∞`-vanishing,
  all phrased for the **patched** trace `Tᵉˣᵗ` (= `valueChartTracePatched ω₀ f Φ br`).

Produces Gate A `∑Res = 0` via `residueSum_eq_zero_of_glue`. -/
structure PatchedTraceSelection (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The global fibre selection. -/
  Φ : (b : ℂ) → FibreRegularData g f b
  /-- The number of finite pole-values. -/
  m : ℕ
  /-- The finite pole-values (the `L`-centres). -/
  cs : Fin m → ℂ
  /-- A radius bounding the finite pole-values. -/
  ρ : ℝ
  /-- The finite pole-values lie inside `ball 0 ρ`. -/
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  /-- The finite pole-values are distinct. -/
  hcs_inj : Function.Injective cs
  /-- The finite pole-values, mapped to the sphere, are exactly the finite-value pole images. -/
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre regularity data. -/
  Dinf : InftyFibreData g f
  /-- The `∞`-fibre enumeration is injective. -/
  hxs_inj : Function.Injective Dinf.xs
  /-- Each `∞`-fibre point is a pole mapping to `∞`. -/
  hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- The `∞`-fibre enumeration is surjective onto the `∞` fibre. -/
  hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- **Per-pole-value moving-sheet coherence datum** (fixed fibre = the pole sub-fibre). -/
  Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i)
  /-- The per-pole datum's fixed fibre is the pole sub-fibre (the honest pole/regular separation). -/
  hCfin_D : ∀ i, (Cfin i).D = fibreReg hac (cs i)
  /-- **The finite branch values** of the cover (off the centres). -/
  br : Finset ℂ
  /-- **Per-regular-value moving-sheet coherence datum** off `cs ∪ br`. -/
  Creg : ∀ z, z ∉ Finset.univ.image cs ∪ br → MovingCoherenceDatum ω₀ g f Φ z
  /-- `g`'s chart-pullback is analytic at each fibre point of the regular datum. -/
  hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
    AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Creg z hz).D.xs i)).symm w))
      ((chartAt ℂ ((Creg z hz).D.xs i)) ((Creg z hz).D.xs i))
  /-- **Branch-value boundedness crux** (the genuine §VIII.3 analytic content; *replaces* the false
  `BranchAwareTraceSelection.hbranch` continuity): at each branch value off the centres,
  `(z − b₀)·valueChartTrace z → 0`. -/
  hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0)
  /-- **`∞` glue** for the patched trace.  Its reciprocal coefficient germ-equals the `∞`-fibre trace. -/
  hglue_inf : recipCoeff (valueChartTracePatched ω₀ f Φ br)
    =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff
  /-- **Junk-freeness** for the patched trace.  The remainder is continuous at each centre. -/
  hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
      (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
    ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p
  /-- The kirovGenus-`0` analytic continuation of the reciprocal remainder. -/
  R₀ : ℂ → ℂ
  /-- `R₀` is analytic at `0`. -/
  hR₀_an : AnalyticAt ℂ R₀ 0
  /-- **Genus-`0` `∞`-vanishing.** `R₀` vanishes at `0`. -/
  hR₀0 : R₀ 0 = 0
  /-- The reciprocal remainder germ-equals `R₀` off `0`. -/
  hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀

/-- **The finite glue of a patched-trace selection** (from the per-pole moving datum + pole sub-fibre,
transported to the patched trace).  `Tᵉˣᵗ =ᶠ[𝓝[≠] cs i] (fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff`:
the per-pole datum gives the glue for `valueChartTrace`, and `Tᵉˣᵗ` germ-equals `valueChartTrace` off `cs i`. -/
theorem PatchedTraceSelection.glue_fin {hac : AdaptedCover ω₀ g f poles}
    (S : PatchedTraceSelection ω₀ g f poles hac) (i : Fin S.m) :
    valueChartTracePatched ω₀ f S.Φ S.br
      =ᶠ[𝓝[≠] S.cs i] (fibreTrace ω₀ f (fibreReg hac (S.cs i))).traceCoeff := by
  have hglue : valueChartTrace ω₀ f S.Φ
      =ᶠ[𝓝[≠] S.cs i] (fibreTrace ω₀ f (fibreReg hac (S.cs i))).traceCoeff := by
    have h := (S.Cfin i).coherent_punctured
    rw [S.hCfin_D i] at h
    exact h
  exact (valueChartTracePatched_eventuallyEq ω₀ f S.Φ S.br (S.cs i)).trans hglue

/-- **The off-centre analyticity of a patched-trace selection** (the `hT_off` for `Tᵉˣᵗ`).  At every
value off the centres, the **patched** trace is analytic: regular values (off `cs ∪ br`) via the
moving-sheet coherence datum (`analyticAt_valueChartTrace_of_movingDatum`, patch inert there), branch
values `b₀ ∈ br` via the value-correct removable extension — punctured analyticity from the
regular-value coherence (`eventually_analyticAt_valueChartTrace_of_reg`), boundedness from `S.hbnd`.
*No* false continuity demand on the raw partial-sum trace. -/
theorem PatchedTraceSelection.hT_off {hac : AdaptedCover ω₀ g f poles}
    (S : PatchedTraceSelection ω₀ g f poles hac) {z : ℂ}
    (hz : z ∉ Finset.univ.image S.cs) :
    AnalyticAt ℂ (valueChartTracePatched ω₀ f S.Φ S.br) z := by
  have hreg : ∀ w ∉ Finset.univ.image S.cs ∪ S.br, AnalyticAt ℂ (valueChartTrace ω₀ f S.Φ) w :=
    fun w hw => analyticAt_valueChartTrace_of_movingDatum (S.Creg w hw) (S.hCreg_g w hw)
  refine analyticAt_valueChartTracePatched_off_centres ω₀ f S.Φ (Finset.univ.image S.cs) S.br
    hreg (fun b₀ hb₀br hb₀cs => ⟨?_, S.hbnd b₀ hb₀br hb₀cs⟩) hz
  exact eventually_analyticAt_valueChartTrace_of_reg ω₀ f S.Φ (Finset.univ.image S.cs) S.br hreg b₀

/-- **Gate A `∑Res = 0` from a patched-trace selection.**  Via `residueSum_eq_zero_of_glue` with
`T := valueChartTracePatched ω₀ f Φ br` (the value-correct patched trace): the finite glue from the
per-pole moving datum (transported to `Tᵉˣᵗ`), the off-centre analyticity from the regular-value
coherence ⊕ the value-correct branch extension (resting on the boundedness crux), and the
`∞`/junk/kirovGenus-`0` data.  This is the §VIII.3 reduction of Gate A **with the symmetric lever (no
labeling) and branch values via the value-correct removable patch** — no revived `hbranch`. -/
theorem residueSum_eq_zero_of_patchedTraceSelection (hac : AdaptedCover ω₀ g f poles)
    (S : PatchedTraceSelection ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_glue hac (valueChartTracePatched ω₀ f S.Φ S.br) S.cs S.ρ S.hcs_ball S.hcs_inj
    S.hcenters_cs S.Dinf S.hxs_inj S.hxs_mem S.hxs_surj S.glue_fin S.hglue_inf
    (fun _ hz => S.hT_off hz) S.hcont_int S.R₀ S.hR₀_an S.hR₀0 S.hR₀_eq

/-! ### Non-vacuity of the patched-trace selection (end-to-end soundness)

The `PatchedTraceSelection` obligation is *satisfiable*, not a disguised `False`: for the **empty pole
set** (`α = ω₀·g` globally holomorphic) the empty fibre selection assembles into one, with `br = ∅` (no
branch values, so `hbnd` is vacuous and the patch is inert: `valueChartTracePatched … ∅ = valueChartTrace
… ≡ 0`), the per-regular-value empty moving datum, the empty `∞`-trace, vacuous junk-freeness, and the
vanishing kirovGenus-`0` continuation.  Its `residueSum_eq_zero_of_patchedTraceSelection` yields `∑Res = 0`,
confirming the reduction is honest. -/

/-- With `br = ∅` the patch is inert: `valueChartTracePatched ω₀ f Φ ∅ = valueChartTrace ω₀ f Φ`
(no branch value to patch). -/
@[simp] theorem valueChartTracePatched_empty (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) :
    valueChartTracePatched ω₀ f Φ ∅ = valueChartTrace ω₀ f Φ := by
  funext z; rw [valueChartTracePatched, if_neg (Finset.notMem_empty z)]

/-- **The empty patched-trace selection.**  For the empty pole set, the empty fibre selection assembles
into a `PatchedTraceSelection`: `br = ∅` (the patch inert, `valueChartTrace ≡ 0`), per-regular-value
empty moving datum (`movingCoherenceDatum_empty`), vacuous finite/branch fields, and the vanishing
kirovGenus-`0` continuation.  The honest non-vacuity witness. -/
noncomputable def patchedTraceSelection_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    PatchedTraceSelection ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  Φ := fun p => emptyFibreRegularData g f p
  m := 0
  cs := Fin.elim0
  ρ := 0
  hcs_ball := fun i => i.elim0
  hcs_inj := fun i => i.elim0
  hcenters_cs := by simp
  Dinf := emptyInftyFibreData g f
  hxs_inj := fun i => i.elim
  hxs_mem := fun i => i.elim
  hxs_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)
  Cfin := fun i => i.elim0
  hCfin_D := fun i => i.elim0
  br := ∅
  Creg := fun z _ => movingCoherenceDatum_empty ω₀ g f z
  hCreg_g := fun z _ i => i.elim
  hbnd := fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀)
  hglue_inf := by
    rw [valueChartTracePatched_empty, valueChartTrace_emptySelection ω₀ f,
      inftyFibreTrace_emptyData_traceCoeff ω₀ f, recipCoeff_zero]
  hcont_int := by
    intro L hLa _ p hp
    rw [hLa, Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0))] at hp
    exact absurd hp (Finset.notMem_empty p)
  R₀ := fun _ => 0
  hR₀_an := analyticAt_const
  hR₀0 := rfl
  hR₀_eq := by
    intro L hLa
    rw [valueChartTracePatched_empty, valueChartTrace_emptySelection ω₀ f]
    have hLR0 : L.R = fun _ => (0 : ℂ) := by
      have hempty : (Finset.univ : Finset L.ι) = ∅ :=
        Finset.image_eq_empty.mp
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      funext z
      show (∑ p : L.ι, L.c p * (z - L.a p) ^ L.n p) = 0
      rw [hempty, Finset.sum_empty]
    rw [hLR0]
    filter_upwards with ζ
    show recipCoeff ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

/-- **Non-vacuity of the patched-trace Gate-A reduction.**  For the empty pole set the reduction
`residueSum_eq_zero_of_patchedTraceSelection` is satisfiable via the empty selection
(`patchedTraceSelection_empty`), yielding `∑Res = 0`.  Confirms the reduction is honest (not a disguised
`False`). -/
theorem residueSum_eq_zero_of_patchedTraceSelection_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_patchedTraceSelection (adaptedCover_empty ω₀ g f hdiv)
    (patchedTraceSelection_empty ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceGlobal
