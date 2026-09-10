/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ProjectiveLine
import KirovDolbeault.Degree
import KirovDolbeault.Abel
import KirovDolbeault.MeromorphicLiouville
import KirovDolbeault.GenusZeroOfSphere

/-!
# Degree-one ⟹ sphere endgame

Let `X` be a compact connected Riemann surface and `f : X → ℂ` a meromorphic
function with a **single simple pole** at `P` (`orderAtPoint P = -1` and
`0 ≤ orderAtPoint x` for `x ≠ P`).  Then `X` is homeomorphic to the Euclidean
`2`-sphere `S² ⊆ ℝ³`.

This is the classical "a degree-one map of compact Riemann surfaces is a
biholomorphism" run in the special case of `f : X → ℂℙ¹`, cashing in the
`ℂℙ¹`-shim built in `Jacobians.ProjectiveLine`:

1. **Build the map** `F : X → RiemannSphere` (`= OnePoint ℂ`): `F x = (f x : ℂℙ¹)`
   for `x ≠ P`, `F P = ∞`.  `F` is holomorphic (`ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`): off `P`
   it is `coe ∘ f`; at `P`, read in `chartInfty` it is `z ↦ 1/f`, which is
   holomorphic with value `0` because the pole is simple.
2. **Degree 1**: `F⁻¹(∞) = {P}`, and `∞` is a regular value with one preimage, so
   `degreeFiber F _ = 1`.
3. **Degree-1 ⟹ homeomorphism**: a non-constant degree-1 holomorphic map between
   compact connected Riemann surfaces is bijective and a local biholomorphism,
   hence a homeomorphism `X ≃ₜ RiemannSphere`.
4. **Compose** with `RiemannSphere.homeoSphere : RiemannSphere ≃ₜ S²`.

## References

* Forster, *Lectures on Riemann Surfaces*, §§4–5 (proper holomorphic maps, the
  degree, degree-one ⟹ biholomorphism).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The simple-pole predicate

`MeromorphicFunction.HasSingleSimplePole` is defined in `Jacobians.MeromorphicLiouville`
(it depends only on `orderAtPoint`), so that both this sphere endgame and the
Riemann–Roch reduction in `Jacobians.RiemannRoch` can refer to it without a cyclic
import. -/

/-! ### Step 1 — the map to the Riemann sphere -/

open Classical in
/-- The map `X → ℂℙ¹` associated with a meromorphic function `f` and a chosen
pole `P`: send finite points through the **limit-repair** `holoRepr` (composed
with `ℂ ↪ ℂℙ¹`) and `P` to `∞`.  (We send *only* `P` to `∞`; with a single
simple pole at `P` this is the honest "graph" of `f`.)

We use `f.holoRepr` rather than the raw `f.toFun` because `f.toFun` is pinned
only up to its meromorphic germ — at a removable singularity it may carry an
arbitrary junk value (see `Jacobians.MeromorphicLiouville`) — which would make
`coe ∘ f.toFun` discontinuous off `P` and `toSphere` *not* `ContMDiff`.  The
repair `holoRepr x = limUnder (𝓝[≠] x) f.toFun` discards that junk and is
analytic wherever the order of `f` is `≥ 0`. -/
def MeromorphicFunction.toSphere (f : MeromorphicFunction X) (P : X) :
    X → RiemannSphere :=
  fun x => if x = P then OnePoint.infty else ((f.holoRepr x : ℂ) : RiemannSphere)

@[simp] lemma MeromorphicFunction.toSphere_pole (f : MeromorphicFunction X) (P : X) :
    f.toSphere P P = OnePoint.infty := by
  simp [MeromorphicFunction.toSphere]

lemma MeromorphicFunction.toSphere_of_ne (f : MeromorphicFunction X) {P x : X}
    (hx : x ≠ P) :
    f.toSphere P x = ((f.holoRepr x : ℂ) : RiemannSphere) := by
  simp [MeromorphicFunction.toSphere, hx]

/-- Preimage of `∞` under `toSphere` is exactly `{P}` (since `coe` never hits `∞`
and we send only `P` to `∞`). -/
lemma MeromorphicFunction.toSphere_preimage_infty (f : MeromorphicFunction X) (P : X) :
    f.toSphere P ⁻¹' {OnePoint.infty} = {P} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    rw [f.toSphere_of_ne hne] at hx
    exact (OnePoint.coe_ne_infty _) hx
  · rintro rfl
    simp

set_option linter.unusedSectionVars false in
/-- **Converse chart bridge `AnalyticAt → ContMDiffAt … ω`.** For a map `F : X → Y`
between complex-analytic manifolds modelled on `ℂ`, if `F` is continuous at `x` and its
chart pullback `(chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm` is `AnalyticAt ℂ` at `(chartAt ℂ x) x`,
then `F` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `x`. (Reverse of `contMDiffAt_omega_analyticAt_chart_pullback`.) -/
theorem contMDiffAt_omega_of_analyticAt_chartPullback
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {F : X → Y} {x : X} (hcont : ContinuousAt F x)
    (hana : AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x := by
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  have hrange : Set.range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contDiffWithinAt_univ]
  have hbase : extChartAt 𝓘(ℂ) x x = (chartAt ℂ x) x := by simp
  have hfun : (extChartAt 𝓘(ℂ) (F x) ∘ F ∘ (extChartAt 𝓘(ℂ) x).symm)
      = ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) := by
    funext z; simp
  rw [hfun, hbase]
  exact hana.contDiffAt

/-- **Off `P`, `toSphere` is `ContMDiff … ω`.** For `x ≠ P` the order of `f` is `≥ 0`,
so `holoRepr` is analytic in the chart there; `toSphere = coe ∘ holoRepr` reads, in the
affine chart `chartCoe` at the finite value `coe (holoRepr x)`, as `holoRepr ∘ (chartAt x).symm`,
which is analytic (`analyticAt_holoRepr_chartPullback_of_orderNonneg`). -/
theorem MeromorphicFunction.contMDiffAt_toSphere_of_ne (f : MeromorphicFunction X) {P x : X}
    (hP : f.HasSingleSimplePole P) (hx : x ≠ P) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) x := by
  have hord : 0 ≤ f.orderAtPoint x := hP.2 x hx
  -- analyticity of the chart pullback of holoRepr
  have hana : AnalyticAt ℂ (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hord
  set φ := chartAt (H := ℂ) x with hφ
  -- holoRepr is continuous at x: pull the analytic chart-rep back through the chart.
  have hxsrc : x ∈ φ.source := mem_chart_source ℂ x
  have hReprContX : ContinuousAt f.holoRepr x := by
    have h1 : ContinuousAt (f.holoRepr ∘ φ.symm) (φ x) := hana.continuousAt
    have h2 : ContinuousAt φ x := φ.continuousAt hxsrc
    have hcomp : ContinuousAt ((f.holoRepr ∘ φ.symm) ∘ φ) x := h1.comp h2
    refine hcomp.congr ?_
    have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hxsrc
    filter_upwards [hev] with y hy
    simp [Function.comp, φ.left_inv hy]
  -- Away from P (an open condition, T2), `toSphere = coe ∘ holoRepr`.
  have hxne : ∀ᶠ y in 𝓝 x, y ≠ P := isOpen_compl_singleton.mem_nhds hx
  have hev : (f.toSphere P) =ᶠ[𝓝 x] (fun y => ((f.holoRepr y : ℂ) : RiemannSphere)) := by
    filter_upwards [hxne] with y hy using f.toSphere_of_ne hy
  -- `toSphere` near x is `coe ∘ holoRepr`, so it is continuous at x.
  have hFcont : ContinuousAt (f.toSphere P) x := by
    refine ContinuousAt.congr ?_ hev.symm
    exact (OnePoint.continuous_coe.continuousAt).comp hReprContX
  -- The value `F x = coe (holoRepr x)`, whose chart is the affine chart `chartCoe`.
  have hFval : f.toSphere P x = ((f.holoRepr x : ℂ) : RiemannSphere) := f.toSphere_of_ne hx
  refine contMDiffAt_omega_of_analyticAt_chartPullback hFcont ?_
  -- chart pullback equals `holoRepr ∘ φ.symm` near `φ x` (using `chartCoe ∘ coe = id` and y ≠ P).
  refine hana.congr ?_
  have hxne' : ∀ᶠ w in 𝓝 (φ x), φ.symm w ≠ P := by
    have : ∀ᶠ w in 𝓝 (φ x), φ.symm w ∈ ({P}ᶜ : Set X) := by
      have hcont : ContinuousAt φ.symm (φ x) :=
        φ.symm.continuousAt (by simpa using φ.map_source hxsrc)
      have hmem : φ.symm (φ x) ∈ ({P}ᶜ : Set X) := by rw [φ.left_inv hxsrc]; exact hx
      exact hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hmem)
    exact this
  -- `chartAt ℂ (coe c) = chartCoe` for any finite value.
  have hchartcoe : ∀ c : ℂ, chartAt ℂ ((c : ℂ) : RiemannSphere) = RiemannSphere.chartCoe := by
    intro c; rfl
  filter_upwards [hxne'] with w hw
  rw [hFval]
  simp only [Function.comp_apply]
  rw [show f.toSphere P (φ.symm w) = ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere) from
    f.toSphere_of_ne hw, hchartcoe, RiemannSphere.chartCoe_apply_coe]

open RiemannSphere in
/-- **At the simple pole `P`, `toSphere` is `ContMDiffAt … ω`.** Reading in the `∞`-chart
`chartInfty` at `toSphere P = ∞`, the chart pullback `G = chartInfty ∘ toSphere ∘ φ.symm`
(`φ = chartAt P`) equals, near `φ P`, the **inverse of the normal-form representative** `Nw⁻¹`
of the pullback `F = f.toFun ∘ φ.symm`.  Since `F` has `meromorphicOrderAt = -1` (the simple pole),
its normal form `N` has order `-1`, so `N⁻¹` (which `=` the chart pullback) is in normal form of
order `+1 ≥ 0`, hence **analytic at `φ P` with value `0`**. -/
theorem MeromorphicFunction.contMDiffAt_toSphere_at_pole (f : MeromorphicFunction X) {P : X}
    (hP : f.HasSingleSimplePole P) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) P := by
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  have hmeroF : MeromorphicAt F (φ P) := f.meromorphic P
  -- order of F at φP is -1.
  have hordF : meromorphicOrderAt F (φ P) = (-1 : ℤ) := by
    have h1 : f.orderAtPoint P = (meromorphicOrderAt F (φ P)).untop₀ := rfl
    rw [hP.1] at h1
    -- (-1 : ℤ) = (meromorphicOrderAt F (φP)).untop₀, and -1 ≠ 0 forces the value to be coe (-1).
    cases hv : meromorphicOrderAt F (φ P) with
    | top => rw [hv] at h1; simp at h1
    | coe n => rw [hv] at h1; simp only [WithTop.untop₀_coe] at h1; rw [← h1]
  -- Normal-form representative N of F.
  set N := toMeromorphicNFAt F (φ P) with hNdef
  have hNF : MeromorphicNFAt N (φ P) := meromorphicNFAt_toMeromorphicNFAt
  have hordN : meromorphicOrderAt N (φ P) = (-1 : ℤ) := by
    rw [hNdef, meromorphicOrderAt_congr hmeroF.eq_nhdsNE_toMeromorphicNFAt.symm, hordF]
  -- N⁻¹ (pointwise inverse) is in normal form, order +1, hence analytic with value 0.
  have hNFinv : MeromorphicNFAt (fun w => (N w)⁻¹) (φ P) := by
    have := hNF.inv
    simpa [Pi.inv_def] using this
  have hordNinv : meromorphicOrderAt (fun w => (N w)⁻¹) (φ P) = (1 : ℤ) := by
    have : meromorphicOrderAt (N⁻¹) (φ P) = -meromorphicOrderAt N (φ P) := meromorphicOrderAt_inv
    rw [hordN] at this
    simpa [Pi.inv_def] using this
  have hNinvAna : AnalyticAt ℂ (fun w => (N w)⁻¹) (φ P) := by
    refine hNFinv.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [hordNinv]; norm_num
  -- value 0: order +1 ≠ 0 forces vanishing at the center.
  have hNinvZero : (N (φ P))⁻¹ = 0 := by
    by_contra hne
    rw [hNFinv.meromorphicOrderAt_eq_zero_iff.2 hne] at hordNinv
    simp at hordNinv
  -- chart at ∞ is chartInfty; the chart pullback `G = chartInfty ∘ toSphere ∘ φ.symm`
  -- equals `fun w => (N w)⁻¹` near φP.
  set G : ℂ → ℂ := chartInfty ∘ (f.toSphere P) ∘ φ.symm with hGdef
  have hGeq : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] G := by
    -- Split `𝓝 φP = 𝓝[≠] φP ⊔ pure φP`.
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (φ P), Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · -- punctured part: off-center, both sides equal `(N w)⁻¹`.
      -- Off-center facts: φ.symm w ≠ P (injectivity), N w ≠ 0, holoRepr (φ.symm w) = N w.
      have htgt : ∀ᶠ w in 𝓝[≠] (φ P), w ∈ φ.target :=
        mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds (φ.map_source hxsrc))
      have hsymm_ne : ∀ᶠ w in 𝓝[≠] (φ P), φ.symm w ≠ P := by
        filter_upwards [self_mem_nhdsWithin, htgt] with w hw hwt
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        intro hcontra
        apply hw
        calc w = φ (φ.symm w) := (φ.right_inv hwt).symm
          _ = φ P := by rw [hcontra]
      -- N ≠ 0 off-center (order ≠ ⊤).
      have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
        rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt]
        rw [hordN]; exact WithTop.coe_ne_top
      -- holoRepr (φ.symm w) = N w off-center.
      have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
        f.holoRepr_chartPullback_eventuallyEq_NFAt P
      filter_upwards [hsymm_ne, hN_ne, hrepr, htgt] with w hwne hwN0 hwrepr hwt
      -- LHS = (N w)⁻¹.  RHS = chartInfty (toSphere P (φ.symm w)).
      show (N w)⁻¹ = chartInfty (f.toSphere P (φ.symm w))
      rw [f.toSphere_of_ne hwne]
      -- holoRepr (φ.symm w) = N w ≠ 0, so chartInfty (coe (N w)) = (N w)⁻¹.
      rw [show f.holoRepr (φ.symm w) = N w from hwrepr]
      rw [RiemannSphere.chartInfty_apply_coe hwN0]
    · -- center: `N⁻¹ φP = 0 = chartInfty ∞ = G φP`.
      simp only [Filter.eventually_pure]
      rw [hNinvZero]
      show (0 : ℂ) = chartInfty (f.toSphere P (φ.symm (φ P)))
      rw [φ.left_inv hxsrc, f.toSphere_pole P, RiemannSphere.chartInfty_apply_infty]
  -- `G` is analytic, hence continuous, at φP.
  have hGana : AnalyticAt ℂ G (φ P) := hNinvAna.congr hGeq
  have hGcont : ContinuousAt G (φ P) := hGana.continuousAt
  -- Continuity of `toSphere` at `P`: near P, `toSphere = chartInfty.symm ∘ G ∘ φ`.
  have hFcont : ContinuousAt (f.toSphere P) P := by
    -- `chartInfty.symm` is continuous at `G (φ P) = 0` (which lies in `chartInfty.target`).
    have hG0 : G (φ P) = 0 := by
      have := hGeq.eq_of_nhds; rw [hNinvZero] at this; exact this.symm
    have h0tgt : (0 : ℂ) ∈ chartInfty.target := by
      have : chartInfty OnePoint.infty = 0 := RiemannSphere.chartInfty_apply_infty
      rw [← this]
      exact chartInfty.map_source (by
        rw [RiemannSphere.chartInfty_source]
        simp [OnePoint.infty_ne_coe])
    have hsymm_cont : ContinuousAt chartInfty.symm (G (φ P)) := by
      rw [hG0]; exact chartInfty.symm.continuousAt (by simpa using h0tgt)
    have hφcont : ContinuousAt φ P := φ.continuousAt hxsrc
    have hGφ : ContinuousAt (G ∘ φ) P := hGcont.comp hφcont
    have hcomp : ContinuousAt (chartInfty.symm ∘ (G ∘ φ)) P :=
      ContinuousAt.comp (g := chartInfty.symm) (f := G ∘ φ) hsymm_cont hGφ
    refine hcomp.congr ?_
    -- near P, `φ.symm (φ y) = y`, and `toSphere P y ∈ chartInfty.source` (so `chartInfty` round-trips).
    have hev : ∀ᶠ y in 𝓝 P, y ∈ φ.source := φ.open_source.mem_nhds hxsrc
    -- source-membership of `toSphere P y` near P (center: `∞`; punctured: `holoRepr = N ≠ 0`).
    have hev3 : ∀ᶠ y in 𝓝 P, f.toSphere P y ∈ chartInfty.source := by
      rw [← nhdsNE_sup_pure P, Filter.eventually_sup]
      refine ⟨?_, ?_⟩
      · -- punctured: y ≠ P, `holoRepr y = N (φ y) ≠ 0`, so `coe (holoRepr y) ≠ coe 0`.
        -- transfer the ℂ-side punctured facts through `φ`.
        have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
          rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt, hordN]
          exact WithTop.coe_ne_top
        have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
          f.holoRepr_chartPullback_eventuallyEq_NFAt P
        -- pull `𝓝[≠] φP` facts back to `𝓝[≠] P` via `φ`.
        have htfwd : Filter.Tendsto φ (𝓝[≠] P) (𝓝[≠] (φ P)) := φ.tendsto_nhdsNE hxsrc
        filter_upwards [htfwd.eventually hN_ne, htfwd.eventually hrepr, self_mem_nhdsWithin,
          (φ.open_source.mem_nhds hxsrc |> mem_nhdsWithin_of_mem_nhds)] with y hyN hyr hyne hys
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
        rw [f.toSphere_of_ne hyne, RiemannSphere.chartInfty_source]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcontra
        -- `coe (holoRepr y) = coe 0 ⟹ holoRepr y = 0`, but `holoRepr y = N (φ y) ≠ 0`.
        have hz : f.holoRepr y = 0 := OnePoint.coe_injective hcontra
        have : f.holoRepr y = N (φ y) := by
          have := hyr; simpa [Function.comp, φ.left_inv hys] using this
        rw [this] at hz; exact hyN hz
      · -- center: `toSphere P P = ∞ ∈ source`.
        simp only [Filter.eventually_pure]
        rw [f.toSphere_pole P, RiemannSphere.chartInfty_source]
        simp [OnePoint.infty_ne_coe]
    filter_upwards [hev, hev3] with y hy hy3
    -- chartInfty.symm (G (φ y)) = chartInfty.symm (chartInfty (toSphere P y)) = toSphere P y
    show chartInfty.symm (G (φ y)) = f.toSphere P y
    have hGval : G (φ y) = chartInfty (f.toSphere P y) := by
      show chartInfty (f.toSphere P (φ.symm (φ y))) = chartInfty (f.toSphere P y)
      rw [φ.left_inv hy]
    rw [hGval, chartInfty.left_inv hy3]
  -- assemble via the converse bridge; `chartAt ℂ (toSphere P P) = chartInfty`.
  refine contMDiffAt_omega_of_analyticAt_chartPullback hFcont ?_
  have hchartInfty : chartAt ℂ (f.toSphere P P) = RiemannSphere.chartInfty := by
    rw [f.toSphere_pole P]; rfl
  rw [hchartInfty]
  exact hGana

/-- **Holomorphy of `toSphere`** (Step 1).  Off `P`, `toSphere = coe ∘ holoRepr`, which is
analytic where the order of `f` is `≥ 0` (`contMDiffAt_toSphere_of_ne`).  At `P`, reading in
`chartInfty`, `toSphere` is `z ↦ 1/f`, which is analytic with value `0` because the pole is simple
(`contMDiffAt_toSphere_at_pole`).  Together these give `ContMDiff … ω` everywhere. -/
theorem MeromorphicFunction.contMDiff_toSphere (f : MeromorphicFunction X) {P : X}
    (hP : f.HasSingleSimplePole P) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) := by
  intro x
  by_cases hx : x = P
  · subst hx; exact f.contMDiffAt_toSphere_at_pole hP
  · exact f.contMDiffAt_toSphere_of_ne hP hx

set_option linter.unusedSectionVars false in
/-- Every charted space over `ℂ` is nontrivial at each point: there is always a
second point.  Proof: the chart `e` at `P` is an open embedding into `ℂ`; its
target is a nonempty open set, which cannot be the singleton `{e P}` (singletons
are not open in `ℂ`), so it contains some `w ≠ e P`, whose preimage `e.symm w`
differs from `P`. -/
theorem exists_ne_of_chartedSpace_complex (P : X) : ∃ x : X, x ≠ P := by
  set e := chartAt ℂ P with he
  have hPsrc : P ∈ e.source := mem_chart_source ℂ P
  have hPtgt : e P ∈ e.target := e.map_source hPsrc
  have hne : e.target ≠ {e P} := by
    intro hsingle
    exact (not_isOpen_singleton (e P)) (hsingle ▸ e.open_target)
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ e.target, w ≠ e P := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (Set.eq_singleton_iff_unique_mem.mpr ⟨hPtgt, hcon⟩)
  refine ⟨e.symm w, fun hcontra => hwne ?_⟩
  have : e (e.symm w) = e P := by rw [hcontra]
  rwa [e.right_inv hw] at this

/-- `toSphere` is non-constant: it takes the value `∞` (at `P`) and a finite value
`coe (holoRepr x)` at any `x ≠ P` (such an `x` exists by
`exists_ne_of_chartedSpace_complex`), and `coe _ ≠ ∞`.  This uses the genuine
`IsConstantMap` predicate (`∃ c, ∀ x, f x = c`), which is non-vacuous since `X` is
nonempty. -/
theorem MeromorphicFunction.toSphere_not_isConstant (f : MeromorphicFunction X)
    {P : X} (_hP : f.HasSingleSimplePole P) :
    ¬ IsConstantMap (f.toSphere P) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx⟩ := exists_ne_of_chartedSpace_complex (X := X) P
  -- `f.toSphere P x = c` and `f.toSphere P P = c`, so `coe (f x) = ∞`, impossible.
  have hxv : f.toSphere P x = ((f.holoRepr x : ℂ) : RiemannSphere) := f.toSphere_of_ne hx
  have key : ((f.holoRepr x : ℂ) : RiemannSphere) = OnePoint.infty := by
    rw [← hxv, hc x, ← f.toSphere_pole P, hc P]
  exact (OnePoint.coe_ne_infty _) key

/-! ### Step 2 — degree one -/

open RiemannSphere in
/-- **The pole is a regular point of `F = toSphere f P`** (Step 2's analytic core,
and the genuine consumer of *simplicity*).  Reading `F` near `P` in the `∞`-chart,
`F` is `z ↦ 1/f` whose derivative at `P` is nonzero **precisely because the pole is
simple** (`orderAtPoint P = -1`): a double pole would give a vanishing derivative
here (chart-pullback `z ↦ z²`-shaped), so its fibre-degree would be `2`, not `1`.
This is the chart-pullback-derivative-nonzero certificate the regular-witness
bundle (`RegularValueWitnessReg.is_regular`) requires at the unique preimage `P` of
`∞`.

This is the same analytic local-normal-form content as `contMDiff_toSphere`, here
specialized to the first-derivative non-vanishing at the simple pole. -/
theorem MeromorphicFunction.toSphere_regular_at_pole (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P) :
    ∀ x ∈ (f.toSphere P) ⁻¹' {OnePoint.infty},
      deriv ((chartAt ℂ (OnePoint.infty : RiemannSphere)) ∘ (f.toSphere P) ∘
          (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
  -- The fibre `toSphere⁻¹{∞}` is `{P}`, so `x = P` and `chartAt x = chartAt P = φ`.
  intro x hx
  rw [f.toSphere_preimage_infty P] at hx
  simp only [Set.mem_singleton_iff] at hx
  obtain rfl : P = x := hx.symm
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  have hmeroF : MeromorphicAt F (φ P) := f.meromorphic P
  -- order of F at φP is -1.
  have hordF : meromorphicOrderAt F (φ P) = (-1 : ℤ) := by
    have h1 : f.orderAtPoint P = (meromorphicOrderAt F (φ P)).untop₀ := rfl
    rw [hP.1] at h1
    cases hv : meromorphicOrderAt F (φ P) with
    | top => rw [hv] at h1; simp at h1
    | coe n => rw [hv] at h1; simp only [WithTop.untop₀_coe] at h1; rw [← h1]
  set N := toMeromorphicNFAt F (φ P) with hNdef
  have hNF : MeromorphicNFAt N (φ P) := meromorphicNFAt_toMeromorphicNFAt
  have hordN : meromorphicOrderAt N (φ P) = (-1 : ℤ) := by
    rw [hNdef, meromorphicOrderAt_congr hmeroF.eq_nhdsNE_toMeromorphicNFAt.symm, hordF]
  have hNFinv : MeromorphicNFAt (fun w => (N w)⁻¹) (φ P) := by
    simpa [Pi.inv_def] using hNF.inv
  have hordNinv : meromorphicOrderAt (fun w => (N w)⁻¹) (φ P) = (1 : ℤ) := by
    have : meromorphicOrderAt (N⁻¹) (φ P) = -meromorphicOrderAt N (φ P) := meromorphicOrderAt_inv
    rw [hordN] at this; simpa [Pi.inv_def] using this
  have hNinvAna : AnalyticAt ℂ (fun w => (N w)⁻¹) (φ P) := by
    refine hNFinv.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_; rw [hordNinv]; norm_num
  -- `G = chartInfty ∘ toSphere ∘ φ.symm` agrees with `N⁻¹` near φP.
  set G : ℂ → ℂ := chartInfty ∘ (f.toSphere P) ∘ φ.symm with hGdef
  have hGeq : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] G := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (φ P), Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · have htgt : ∀ᶠ w in 𝓝[≠] (φ P), w ∈ φ.target :=
        mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds (φ.map_source hxsrc))
      have hsymm_ne : ∀ᶠ w in 𝓝[≠] (φ P), φ.symm w ≠ P := by
        filter_upwards [self_mem_nhdsWithin, htgt] with w hw hwt
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        intro hcontra
        apply hw
        calc w = φ (φ.symm w) := (φ.right_inv hwt).symm
          _ = φ P := by rw [hcontra]
      have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
        rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt, hordN]
        exact WithTop.coe_ne_top
      have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
        f.holoRepr_chartPullback_eventuallyEq_NFAt P
      filter_upwards [hsymm_ne, hN_ne, hrepr, htgt] with w hwne hwN0 hwrepr hwt
      show (N w)⁻¹ = chartInfty (f.toSphere P (φ.symm w))
      rw [f.toSphere_of_ne hwne, show f.holoRepr (φ.symm w) = N w from hwrepr,
        RiemannSphere.chartInfty_apply_coe hwN0]
    · simp only [Filter.eventually_pure]
      show (N (φ P))⁻¹ = chartInfty (f.toSphere P (φ.symm (φ P)))
      have hNinvZero : (N (φ P))⁻¹ = 0 := by
        by_contra hne; rw [hNFinv.meromorphicOrderAt_eq_zero_iff.2 hne] at hordNinv; simp at hordNinv
      rw [hNinvZero, φ.left_inv hxsrc, f.toSphere_pole P, RiemannSphere.chartInfty_apply_infty]
  -- `deriv G (φP) = deriv N⁻¹ (φP)`, and order = 1 forces it nonzero.
  have hderiv_eq : deriv G (φ P) = deriv (fun w => (N w)⁻¹) (φ P) :=
    (Filter.EventuallyEq.deriv_eq hGeq).symm
  -- chart-at-∞ and chart-at-P unfold to chartInfty, φ.
  show deriv ((chartAt ℂ (OnePoint.infty : RiemannSphere)) ∘ (f.toSphere P) ∘ φ.symm) (φ P) ≠ 0
  have hchart : (chartAt ℂ (OnePoint.infty : RiemannSphere)) = RiemannSphere.chartInfty := rfl
  rw [hchart, show (chartInfty ∘ (f.toSphere P) ∘ φ.symm) = G from rfl, hderiv_eq]
  -- order of `N⁻¹` (analytic) at φP is the natural number 1; factor `N⁻¹ = (·-φP) • g`, g(φP)≠0.
  have hordNat : analyticOrderAt (fun w => (N w)⁻¹) (φ P) = ((1 : ℕ) : ℕ∞) := by
    rw [hNinvAna.meromorphicOrderAt_eq] at hordNinv
    have : ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (fun w => (N w)⁻¹) (φ P))
        = ENat.map (Nat.cast : ℕ → ℤ) ((1 : ℕ) : ℕ∞) := by
      rw [hordNinv]; simp
    exact ENat.map_natCast_injective this
  obtain ⟨g, hg, hg0, hgeq⟩ := (hNinvAna.analyticOrderAt_eq_natCast (n := 1)).mp (by
    rw [hordNat])
  -- `deriv (N⁻¹) φP = g φP ≠ 0`.
  have hpow : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] (fun w => (w - φ P) ^ 1 • g w) := by
    filter_upwards [hgeq] with w hw using hw
  rw [hpow.deriv_eq]
  -- deriv of `(w - φP)^1 • g w` at φP = g φP.
  have hd : HasDerivAt (fun w => (w - φ P) ^ 1 • g w) (g (φ P)) (φ P) := by
    have h1 : HasDerivAt (fun w : ℂ => (w - φ P) ^ 1) (1 : ℂ) (φ P) := by
      simpa using ((hasDerivAt_id (φ P)).sub_const (φ P)).pow 1
    have h2 : HasDerivAt g (deriv g (φ P)) (φ P) := hg.differentiableAt.hasDerivAt
    have := h1.smul h2
    simpa using this
  rw [hd.deriv]
  exact hg0

/-- **Degree one** (Step 2).  `∞` is a regular value of `F = toSphere f P` with the
single preimage `P` (`toSphere_preimage_infty`), and `P` is a regular point
(`toSphere_regular_at_pole`, consuming pole simplicity).  Packaging this as a
`RegularValueWitnessReg` whose fibre `{P}` has cardinality `1`, witness-independence
of the fibre degree (`degreeFiber_eq_card_of_regularWitness`) gives
`degreeFiber F hF = 1`.

Note the genuine use of simplicity: the `RegularValueWitnessReg.is_regular`
certificate fed in here is `toSphere_regular_at_pole`, which *fails* for a higher-
order pole.  A double pole has the same singleton preimage `{P}` but is a critical
point, so it would not yield a regular witness — and indeed its topological degree
is `2`, not `1`. -/
theorem MeromorphicFunction.degreeFiber_toSphere_eq_one (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P)) :
    degreeFiber (f.toSphere P) hF = 1 := by
  classical
  -- The regular-value witness at `∞`, with fibre `{P}` and the simplicity certificate.
  set F := f.toSphere P with hFdef
  have hfib : F ⁻¹' {OnePoint.infty} = {P} := f.toSphere_preimage_infty P
  have hfin : (F ⁻¹' {OnePoint.infty}).Finite := by rw [hfib]; exact Set.finite_singleton P
  -- underlying cardinality-bearing witness
  let w₀ : RegularValueWitness F :=
    { value := OnePoint.infty, fiber_finite := hfin }
  -- promote to a regular witness using the simple-pole regularity certificate
  let w : RegularValueWitnessReg F :=
    w₀.toRegular (f.toSphere_regular_at_pole hP)
  -- non-constancy
  have hnc : ¬ IsConstantMap F := f.toSphere_not_isConstant hP
  -- witness independence pins the degree to this witness's card …
  have hdeg : degreeFiber F hF = w.card :=
    degreeFiber_eq_card_of_regularWitness F hF hnc w
  rw [hdeg]
  -- … and that card is `(F⁻¹{∞}).ncard = |{P}| = 1`.
  show (Jacobians.Discharge.ContMDiff.RegularValueWitnessReg.card w) = 1
  have hcard : w.card = (F ⁻¹' {OnePoint.infty}).ncard :=
    w₀.card_eq_ncard
  rw [show (Jacobians.Discharge.ContMDiff.RegularValueWitnessReg.card w) = w.card from rfl,
    hcard, hfib, Set.ncard_singleton]

/-! ### Step 3 — degree one ⟹ homeomorphism -/

/-- A nonempty open subset of a complex `1`-manifold `Y` is infinite: it is locally
homeomorphic to a nonempty open subset of `ℂ`, and those are infinite. -/
theorem infinite_of_isOpen_nonempty {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {W : Set Y} (hW : IsOpen W) (hne : W.Nonempty) : W.Infinite := by
  obtain ⟨y₀, hy₀⟩ := hne
  set c : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hc
  -- The open set `U := c.source ∩ W` contains `y₀`; its chart image is open in `ℂ`.
  set U : Set Y := c.source ∩ W with hU
  have hUopen : IsOpen U := c.open_source.inter hW
  have hy₀U : y₀ ∈ U := ⟨mem_chart_source ℂ y₀, hy₀⟩
  -- `c '' U` is open in `ℂ` and contains `c y₀`.
  have hcU_open : IsOpen (c '' U) := c.isOpen_image_of_subset_source hUopen Set.inter_subset_left
  have hcy₀ : c y₀ ∈ c '' U := ⟨y₀, hy₀U, rfl⟩
  -- Open sets in `ℂ` containing a point are infinite.
  haveI : Filter.NeBot (𝓝[≠] (c y₀)) := Module.punctured_nhds_neBot ℂ ℂ (c y₀)
  have hcU_inf : (c '' U).Infinite := infinite_of_mem_nhds (c y₀) (hcU_open.mem_nhds hcy₀)
  -- Pull back through `c.symm` (injective on the chart image), landing in `U ⊆ W`.
  have hsub : c '' U ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩; exact c.map_source hx.1
  have himg : (c.symm '' (c '' U)).Infinite := hcU_inf.image (c.symm.injOn.mono hsub)
  refine himg.mono ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [c.left_inv hx.1]; exact hx.2

/-- In a complex `1`-manifold, removing a finite set from a nonempty open set leaves a
nonempty set (open sets are infinite, finite sets removable). -/
theorem exists_mem_open_notMem_finite {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {W C : Set Y} (hW : IsOpen W) (hne : W.Nonempty) (hC : C.Finite) :
    ∃ y ∈ W, y ∉ C := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hWsub : W ⊆ C := fun y hy => h y hy
  exact (infinite_of_isOpen_nonempty hW hne) (hC.subset hWsub)

/-- **Degree-one ⟹ bijective** (Step 3's set-theoretic core, extracted from
`degreeOne_homeo` so the genus transport `KirovDolbeault.DegreeOneGenusTransport`
can consume the bijection together with the underlying holomorphic `F`).

Proof:
* **Surjective** — `surjective_of_nonconstant` (open + closed image, connected target).
* **Injective** — every regular value `y` (off the finite critical-value set) has a
  *singleton* fibre, because `degreeFiber F hF = (F⁻¹{y}).ncard = 1` by witness-
  independence of the degree. If `F a = F b = c` with `a ≠ b`, take disjoint opens
  `U ∋ a`, `V ∋ b` (Hausdorff); their open images `F '' U`, `F '' V` (open mapping)
  both contain `c`, so the open intersection contains a regular value `y`; then `y`
  has preimages in `U` and in `V`, contradicting the singleton fibre. -/
theorem degreeOne_bijective {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (F : X → Y) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hnc : ¬ IsConstantMap F)
    (hdeg : degreeFiber F hF = 1) :
    Function.Bijective F := by
  classical
  -- `¬ IsConstantMap F` unfolds to the form used by the open-mapping lemmas.
  have hnc' : ¬ ∃ y₀ : Y, ∀ x, F x = y₀ := hnc
  have hsurj : Function.Surjective F := surjective_of_nonconstant F hF hnc'
  have hopen : IsOpenMap F := isOpenMap_of_nonconstant F hF hnc'
  -- The finite critical-value set.
  set C : Set Y := Jacobians.Discharge.Manifold.criticalValuesGeneral F with hC
  have hCfin : C.Finite := Jacobians.Discharge.Manifold.criticalValues_finite_general F hF hnc
  -- Every value off `C` has a singleton fibre (degree = 1).
  have hsingleton : ∀ y ∉ C, ∃ p, F ⁻¹' {y} = {p} := by
    intro y hy
    obtain ⟨w, hwval⟩ :=
      Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq F hF hnc hy
    have hwcard : degreeFiber F hF = w.card :=
      degreeFiber_eq_card_of_regularWitness F hF hnc w
    have hcard1 : (F ⁻¹' {y}).ncard = 1 := by
      have hcardeq : w.card = (F ⁻¹' {w.toWitness.value}).ncard :=
        w.toWitness.card_eq_ncard
      rw [hwval] at hcardeq
      have : (F ⁻¹' {y}).ncard = w.card := hcardeq.symm
      rw [this, ← hwcard, hdeg]
    exact Set.ncard_eq_one.mp hcard1
  -- Injectivity.
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    -- Disjoint opens around `a` and `b`.
    obtain ⟨U, V, hUopen, hVopen, haU, hbV, hUV⟩ := t2_separation hne
    -- Their open images both contain `c := F a = F b`.
    have hcU : F a ∈ F '' U := ⟨a, haU, rfl⟩
    have hcV : F a ∈ F '' V := ⟨b, hbV, hab.symm⟩
    have hWopen : IsOpen (F '' U ∩ F '' V) := (hopen U hUopen).inter (hopen V hVopen)
    have hWne : (F '' U ∩ F '' V).Nonempty := ⟨F a, hcU, hcV⟩
    -- Pick a regular value `y` in the intersection.
    obtain ⟨y, ⟨⟨u, huU, hFu⟩, ⟨v, hvV, hFv⟩⟩, hyC⟩ :=
      exists_mem_open_notMem_finite hWopen hWne hCfin
    -- Its fibre is a singleton, but `u ∈ U`, `v ∈ V` are distinct preimages.
    obtain ⟨p, hp⟩ := hsingleton y hyC
    have hup : u = p := by
      have : u ∈ F ⁻¹' {y} := hFu
      rw [hp] at this; exact this
    have hvp : v = p := by
      have : v ∈ F ⁻¹' {y} := hFv
      rw [hp] at this; exact this
    have huv : u = v := hup.trans hvp.symm
    exact (hUV.ne_of_mem huU (huv ▸ hvV)) rfl
  exact ⟨hinj, hsurj⟩

/-- **Degree-one ⟹ homeomorphism** (Step 3, the crux).  A non-constant degree-one
holomorphic map `F : X → Y` between compact connected Riemann surfaces is
bijective (`degreeOne_bijective`) and open (open-mapping theorem), hence a
homeomorphism (`Equiv.toHomeomorphOfContinuousOpen`). -/
theorem degreeOne_homeo {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (F : X → Y) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hnc : ¬ IsConstantMap F)
    (hdeg : degreeFiber F hF = 1) :
    Nonempty (X ≃ₜ Y) := by
  have hbij : Function.Bijective F := degreeOne_bijective F hF hnc hdeg
  have hnc' : ¬ ∃ y₀ : Y, ∀ x, F x = y₀ := hnc
  have hopen : IsOpenMap F := isOpenMap_of_nonconstant F hF hnc'
  exact ⟨Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective F hbij)
    hF.continuous hopen⟩

/-! ### The endgame theorem -/

/-- **Degree-one ⟹ sphere.**  If a meromorphic function `f` on a compact
connected Riemann surface `X` has a single simple pole at some `P`, then `X` is
homeomorphic to the Euclidean `2`-sphere `S² ⊆ ℝ³`.

Proof: `F := f.toSphere P : X → ℂℙ¹` is holomorphic (Step 1), non-constant, and
has degree `1` because `F⁻¹(∞) = {P}` (Step 2).  A degree-one holomorphic map of
compact connected Riemann surfaces is a homeomorphism (Step 3), so `X ≃ₜ ℂℙ¹`,
and `ℂℙ¹ ≃ₜ S²` via `RiemannSphere.homeoSphere` (Step 4). -/
theorem nonempty_homeo_sphere_of_singleSimplePole
    (f : MeromorphicFunction X) {P : X} (hP : f.HasSingleSimplePole P) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  -- Step 1: the holomorphic map to ℂℙ¹.
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) := f.contMDiff_toSphere hP
  have hnc : ¬ IsConstantMap (f.toSphere P) := f.toSphere_not_isConstant hP
  -- Step 2: degree one.
  have hdeg : degreeFiber (f.toSphere P) hF = 1 :=
    f.degreeFiber_toSphere_eq_one hP hF
  -- Step 3: degree-one ⟹ homeomorphism X ≃ₜ ℂℙ¹.
  obtain ⟨e⟩ := degreeOne_homeo (f.toSphere P) hF hnc hdeg
  -- Step 4: compose with ℂℙ¹ ≃ₜ S².
  exact ⟨e.trans RiemannSphere.homeoSphere⟩

end Jacobians

/-! ### The challenge theorem `genus_eq_zero_iff_homeo`

Declared in the **root namespace** (matching `kirovGenus`, which lives in root namespace in `Genus.lean`),
so the challenge-conformance file resolves the bare name. Lives in this module — not `Genus.lean` —
because its forward direction needs the degree-one endgame, which sits downstream of `Genus` (via
`ProjectiveLine → Genus`); declaring it here breaks the import cycle. Both directions rest on isolated
analytic inputs (the unproved obligations below). `Nonempty X` is supplied for free by `[ConnectedSpace X]`
(`ConnectedSpace.toNonempty`), so the signature matches the spec exactly. -/

open scoped Manifold ContDiff in
/-- **[INPUT — the de Rham wall, the backward half].** A surface homeomorphic to `S²` has kirovGenus `0`.

`kirovGenus X = Module.finrank ℂ (HolomorphicOneForms X)` is **analytic**, while `X ≃ₜ S²` is purely
**topological**, so the bridge is the contrapositive route (`Jacobians.GenusSphereBackward`):
`X ≃ₜ S²` makes `X` simply connected, on which every holomorphic `1`-form has a global primitive,
hence (being constant on compact `X`, Liouville) vanishes, so `kirovGenus X = 0`.

Two of the route's three former walls have fallen and are discharged here completely:
* **`S²` simply connected** — unconditional (`Jacobians.VanKampen.twoOpenVanKampen_holds`); `X ≃ₜ S²`
  transports `SimplyConnectedSpace` to `X`.
* **Liouville / max-modulus** — `MDifferentiable.exists_eq_const_of_compactSpace` (Mathlib).

The *only* remaining input is the **holomorphic Poincaré lemma / monodromy theorem**
`Jacobians.HasHolomorphicPrimitives X` (every holomorphic `1`-form on a simply connected surface has
a global primitive); Mathlib has only the plane/ball version, the manifold de Rham globalisation is
the open gap. The whole route, *modulo that single input*, is assembled axiom-clean in
`Jacobians.genus_zero_of_nonempty_homeo_sphere_of_hasPrimitives`; the one remaining gap below is exactly
`HasHolomorphicPrimitives X`.

**Scope of the remaining sorry (E6 reroute, 2026-06-10).** This bare-homeomorphism statement
is now needed *only* for the backward half of the conformance headline `genus_eq_zero_iff_homeo`
(`KirovDolbeault.GenusSphereHeadline`). Wherever the homeomorphism arises from the degree-one
chain itself — i.e. from a single simple pole, as in the Abel-wall genus obstruction — the
genus-0 conclusion is available **without** this sorry via the biholomorphic genus transport
`Jacobians.genus_zero_of_singleSimplePole` (`KirovDolbeault.DegreeOneGenusTransport`,
axiom-clean, keystone- and de-Rham-free). The transport cannot replace THIS statement: a bare
`X ≃ₜ S²` carries no complex structure, so no holomorphic degree-1 map is available to pull
forms back along; closing this sorry as stated genuinely requires the de Rham input (or
uniformization). See `docs/planning/E6_BLOCKER.md` in the parent repository. -/
theorem genus_zero_of_nonempty_homeo_sphere {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    kirovGenus X = 0 :=
  Jacobians.genus_zero_of_nonempty_homeo_sphere_of_hasPrimitives
    (sorry : Jacobians.HasHolomorphicPrimitives X) h
