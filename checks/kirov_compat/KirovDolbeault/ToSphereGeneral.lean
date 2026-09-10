/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ProjectiveLine
import KirovDolbeault.Abel
import KirovDolbeault.MeromorphicLiouville
import KirovDolbeault.DegreeOneSphere

/-!
# The general holomorphic map `X → ℂℙ¹` of a meromorphic function

For an **arbitrary** meromorphic function `f` on a compact connected Riemann
surface `X`, the map sending each point to the value of `f` (and each pole to
`∞`) is a holomorphic map `X → ℂℙ¹ = RiemannSphere`.

This generalizes `MeromorphicFunction.toSphere` (in `Jacobians.DegreeOneSphere`),
which was restricted to a function with a **single simple pole** (`HasSingleSimplePole`).
Here we drop that hypothesis entirely: a point `x` is sent to `∞` precisely when
it is a genuine pole (`orderAtPoint x < 0`), and to the finite value
`coe (holoRepr x)` otherwise. The local analytic arguments are exactly those of
the single-pole template, pole by pole:

* **at a non-pole** `x` (`0 ≤ orderAtPoint x`): `toRiemannSphere = coe ∘ holoRepr` near `x`
  (poles are isolated, `orderAtPoint_isolated_at`), and `holoRepr` is analytic in
  the chart there (`analyticAt_holoRepr_chartPullback_of_orderNonneg`);
* **at a pole** `P` (`orderAtPoint P = n < 0`): reading in the `∞`-chart
  `chartInfty`, the chart pullback is the inverse `1/f` of the normal form `N`
  (order `n < 0`), hence `N⁻¹` is in normal form of order `-n ≥ 1 > 0`, analytic
  with value `0`. (For `n = -1` this is exactly the single-pole proof.)

This is the foundational "meromorphic function = holomorphic map to `ℂℙ¹`"
infrastructure underlying the branched cover, Riemann–Hurwitz, and the trace.

## References

* Forster, *Lectures on Riemann Surfaces*, §§1–2 (`ℂℙ¹`-valued meromorphic
  functions), §6 (order, isolation of poles).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The map to the Riemann sphere -/

open Classical in
/-- The holomorphic map `X → ℂℙ¹` associated with a meromorphic function `f`:
send a genuine pole (`orderAtPoint x < 0`) to `∞`, and every other point to the
**limit-repair** value `coe (holoRepr x)` (the junk-free meromorphic value, see
`Jacobians.MeromorphicLiouville`).

Generalizes `MeromorphicFunction.toSphere`, which fixed a single pole `P` and
sent only `P` to `∞`. -/
def MeromorphicFunction.toRiemannSphere (f : MeromorphicFunction X) :
    X → RiemannSphere :=
  fun x => if f.orderAtPoint x < 0 then OnePoint.infty
    else ((f.holoRepr x : ℂ) : RiemannSphere)

lemma MeromorphicFunction.toRiemannSphere_of_pole (f : MeromorphicFunction X) {x : X}
    (hx : f.orderAtPoint x < 0) : f.toRiemannSphere x = OnePoint.infty := by
  simp [MeromorphicFunction.toRiemannSphere, hx]

lemma MeromorphicFunction.toRiemannSphere_of_nonneg (f : MeromorphicFunction X) {x : X}
    (hx : 0 ≤ f.orderAtPoint x) :
    f.toRiemannSphere x = ((f.holoRepr x : ℂ) : RiemannSphere) := by
  simp only [MeromorphicFunction.toRiemannSphere]
  rw [if_neg (not_lt.mpr hx)]

/-- Preimage of `∞` is exactly the set of poles `{x | orderAtPoint x < 0}` (the
finite value `coe _` never equals `∞`, and we send a point to `∞` iff it is a pole). -/
lemma MeromorphicFunction.toRiemannSphere_preimage_infty (f : MeromorphicFunction X) :
    f.toRiemannSphere ⁻¹' {OnePoint.infty} = {x | f.orderAtPoint x < 0} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hne
    rw [f.toRiemannSphere_of_nonneg (not_lt.mp hne)] at hx
    exact (OnePoint.coe_ne_infty _) hx
  · intro hx
    exact f.toRiemannSphere_of_pole hx

/-- **Punctured chart pullback of `toRiemannSphere` is `coe ∘ holoRepr`.** For ANY
point `P` (in particular a pole), every point in a punctured neighborhood of `P` is
a non-pole (poles are isolated, `orderAtPoint_isolated_at`), so reading through the
chart `φ = chartAt P`, the pullback `toRiemannSphere ∘ φ.symm` agrees with
`coe ∘ holoRepr ∘ φ.symm` off the center `φ P`. This is the punctured-neighborhood
input the pole analysis consumes (the analogue, for `toRiemannSphere`, of
`holoRepr_chartPullback_eventuallyEq_NFAt`). -/
lemma MeromorphicFunction.toRiemannSphere_chartPullback_eventuallyEq_coe
    (f : MeromorphicFunction X) (P : X) :
    (fun w => f.toRiemannSphere ((chartAt (H := ℂ) P).symm w))
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) P) P)]
      (fun w => ((f.holoRepr ((chartAt (H := ℂ) P).symm w) : ℂ) : RiemannSphere)) := by
  set φ := chartAt (H := ℂ) P with hφ
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  obtain ⟨t, ht_nhds, ht⟩ := f.orderAtPoint_isolated_at P
  -- pull `t` and `φ.target` back to the punctured chart neighborhood, plus injectivity off-center.
  have htgt : ∀ᶠ w in 𝓝[≠] (φ P), w ∈ φ.target :=
    mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds (φ.map_source hxsrc))
  have htpull : ∀ᶠ w in 𝓝[≠] (φ P), φ.symm w ∈ t := by
    have hcont : ContinuousAt φ.symm (φ P) :=
      φ.symm.continuousAt (by simpa using φ.map_source hxsrc)
    have hmem : φ.symm (φ P) ∈ t := by rw [φ.left_inv hxsrc]; exact mem_of_mem_nhds ht_nhds
    exact mem_nhdsWithin_of_mem_nhds (hcont.preimage_mem_nhds (by rw [φ.left_inv hxsrc]; exact ht_nhds))
  have hsymm_ne : ∀ᶠ w in 𝓝[≠] (φ P), φ.symm w ≠ P := by
    filter_upwards [self_mem_nhdsWithin, htgt] with w hw hwt
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    intro hcontra
    apply hw
    calc w = φ (φ.symm w) := (φ.right_inv hwt).symm
      _ = φ P := by rw [hcontra]
  filter_upwards [htpull, hsymm_ne] with w hwt hwne
  -- `φ.symm w ∈ t`, `≠ P`, so it is a non-pole (order `0`), hence the `coe`-branch.
  exact f.toRiemannSphere_of_nonneg (le_of_eq (ht (φ.symm w) hwt hwne).symm)

/-! ### Holomorphy off the poles -/

/-- **Near a non-pole, `toRiemannSphere` agrees with `coe ∘ holoRepr`.** Since poles
are isolated (`orderAtPoint_isolated_at`), there is a neighborhood of a non-pole `x`
on which every point is also a non-pole (order `0` for `y ≠ x`, order `≥ 0` at `x`),
so the `if` in `toRiemannSphere` always takes the `coe`-branch. -/
lemma MeromorphicFunction.toRiemannSphere_eventuallyEq_coe_holoRepr
    (f : MeromorphicFunction X) {x : X} (hx : 0 ≤ f.orderAtPoint x) :
    f.toRiemannSphere =ᶠ[𝓝 x] (fun y => ((f.holoRepr y : ℂ) : RiemannSphere)) := by
  obtain ⟨t, ht_nhds, ht⟩ := f.orderAtPoint_isolated_at x
  filter_upwards [ht_nhds] with y hy
  by_cases hyx : y = x
  · subst hyx; exact f.toRiemannSphere_of_nonneg hx
  · exact f.toRiemannSphere_of_nonneg (le_of_eq (ht y hy hyx).symm)

/-- **Off the poles, `toRiemannSphere` is `ContMDiff … ω`.** Where the order of `f`
is `≥ 0`, near `x` the map is `coe ∘ holoRepr`
(`toRiemannSphere_eventuallyEq_coe_holoRepr`), and `holoRepr` is analytic in the
chart there (`analyticAt_holoRepr_chartPullback_of_orderNonneg`); reading in the
affine chart `chartCoe` at the finite value `coe (holoRepr x)`, the chart pullback
is `holoRepr ∘ (chartAt x).symm`, which is analytic. Mirrors
`contMDiffAt_toSphere_of_ne`. -/
theorem MeromorphicFunction.contMDiffAt_toRiemannSphere_of_nonneg (f : MeromorphicFunction X)
    {x : X} (hx : 0 ≤ f.orderAtPoint x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.toRiemannSphere) x := by
  -- analyticity of the chart pullback of holoRepr
  have hana : AnalyticAt ℂ (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hx
  set φ := chartAt (H := ℂ) x with hφ
  have hxsrc : x ∈ φ.source := mem_chart_source ℂ x
  -- holoRepr is continuous at x.
  have hReprContX : ContinuousAt f.holoRepr x := by
    have h1 : ContinuousAt (f.holoRepr ∘ φ.symm) (φ x) := hana.continuousAt
    have h2 : ContinuousAt φ x := φ.continuousAt hxsrc
    have hcomp : ContinuousAt ((f.holoRepr ∘ φ.symm) ∘ φ) x := h1.comp h2
    refine hcomp.congr ?_
    have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hxsrc
    filter_upwards [hev] with y hy
    simp [Function.comp, φ.left_inv hy]
  -- Near x, `toRiemannSphere = coe ∘ holoRepr`.
  have hev : (f.toRiemannSphere) =ᶠ[𝓝 x] (fun y => ((f.holoRepr y : ℂ) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_coe_holoRepr hx
  have hFcont : ContinuousAt (f.toRiemannSphere) x := by
    refine ContinuousAt.congr ?_ hev.symm
    exact (OnePoint.continuous_coe.continuousAt).comp hReprContX
  have hFval : f.toRiemannSphere x = ((f.holoRepr x : ℂ) : RiemannSphere) :=
    f.toRiemannSphere_of_nonneg hx
  refine contMDiffAt_omega_of_analyticAt_chartPullback hFcont ?_
  -- chart pullback equals `holoRepr ∘ φ.symm` near `φ x` (using `chartCoe ∘ coe = id`).
  refine hana.congr ?_
  -- near `φ x`, `φ.symm w` is a non-pole, so `toRiemannSphere (φ.symm w) = coe (holoRepr (φ.symm w))`.
  have hev_symm : ∀ᶠ w in 𝓝 (φ x), f.toRiemannSphere (φ.symm w) =
      ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere) := by
    have hcont : ContinuousAt φ.symm (φ x) :=
      φ.symm.continuousAt (by simpa using φ.map_source hxsrc)
    have hpt : φ.symm (φ x) = x := φ.left_inv hxsrc
    have := hcont.eventually (by rw [hpt]; exact hev)
    filter_upwards [this] with w hw using hw
  -- `chartAt ℂ (coe c) = chartCoe` for any finite value.
  have hchartcoe : ∀ c : ℂ, chartAt ℂ ((c : ℂ) : RiemannSphere) = RiemannSphere.chartCoe := by
    intro c; rfl
  filter_upwards [hev_symm] with w hw
  rw [hFval]
  simp only [Function.comp_apply]
  rw [hw, hchartcoe, RiemannSphere.chartCoe_apply_coe]

/-! ### Holomorphy at the poles -/

/-- The chart-level order is the negative integer `n` recorded by `orderAtPoint`.
At a pole (`orderAtPoint P < 0`) the order of the pullback `F = f.toFun ∘ φ.symm`
at `φ P` equals `(orderAtPoint P : ℤ)`, which is `< 0` (so in particular `F` has a
genuine pole — not a removable singularity — at `φ P`). -/
lemma MeromorphicFunction.meromorphicOrderAt_chartPullback_of_pole
    (f : MeromorphicFunction X) {P : X} (hP : f.orderAtPoint P < 0) :
    meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) P).symm) ((chartAt (H := ℂ) P) P)
      = (f.orderAtPoint P : ℤ) := by
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have h1 : f.orderAtPoint P = (meromorphicOrderAt F (φ P)).untop₀ := rfl
  cases hv : meromorphicOrderAt F (φ P) with
  | top =>
    -- order ⊤ ⟹ untop₀ = 0, contradicting `orderAtPoint P < 0`.
    rw [hv] at h1; simp only [WithTop.untop₀_top] at h1
    rw [h1] at hP; exact absurd hP (by norm_num)
  | coe n => rw [hv] at h1; simp only [WithTop.untop₀_coe] at h1; rw [h1]

open RiemannSphere in
/-- **At a pole `P`, `toRiemannSphere` is `ContMDiffAt … ω`.** Reading in the
`∞`-chart `chartInfty` at `toRiemannSphere P = ∞`, the chart pullback
`G = chartInfty ∘ toRiemannSphere ∘ φ.symm` (`φ = chartAt P`) equals, near `φ P`,
the **inverse of the normal-form representative** `Nw⁻¹` of the pullback
`F = f.toFun ∘ φ.symm`. Since `F` has `meromorphicOrderAt = n < 0` (the pole), its
normal form `N` has order `n`, so `N⁻¹` is in normal form of order `-n ≥ 1 > 0`,
hence **analytic at `φ P` with value `0`**. Mirrors
`contMDiffAt_toSphere_at_pole`, dropping the `orderAtPoint P = -1` restriction
(any `n < 0` works). -/
theorem MeromorphicFunction.contMDiffAt_toRiemannSphere_at_pole (f : MeromorphicFunction X)
    {P : X} (hP : f.orderAtPoint P < 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.toRiemannSphere) P := by
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  have hmeroF : MeromorphicAt F (φ P) := f.meromorphic P
  -- order of F at φP is `n := orderAtPoint P < 0`.
  set n : ℤ := f.orderAtPoint P with hn
  have hn_neg : n < 0 := hP
  have hordF : meromorphicOrderAt F (φ P) = (n : ℤ) :=
    f.meromorphicOrderAt_chartPullback_of_pole hP
  -- Normal-form representative N of F.
  set N := toMeromorphicNFAt F (φ P) with hNdef
  have hNF : MeromorphicNFAt N (φ P) := meromorphicNFAt_toMeromorphicNFAt
  have hordN : meromorphicOrderAt N (φ P) = (n : ℤ) := by
    rw [hNdef, meromorphicOrderAt_congr hmeroF.eq_nhdsNE_toMeromorphicNFAt.symm, hordF]
  -- N⁻¹ (pointwise inverse) is in normal form, order `-n ≥ 1 > 0`, hence analytic with value 0.
  have hNFinv : MeromorphicNFAt (fun w => (N w)⁻¹) (φ P) := by
    have := hNF.inv
    simpa [Pi.inv_def] using this
  have hordNinv : meromorphicOrderAt (fun w => (N w)⁻¹) (φ P) = ((-n : ℤ)) := by
    have : meromorphicOrderAt (N⁻¹) (φ P) = -meromorphicOrderAt N (φ P) := meromorphicOrderAt_inv
    rw [hordN] at this
    simpa [Pi.inv_def] using this
  have hnn_pos : (0 : ℤ) < -n := by omega
  have hNinvAna : AnalyticAt ℂ (fun w => (N w)⁻¹) (φ P) := by
    refine hNFinv.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [hordNinv]; exact_mod_cast le_of_lt hnn_pos
  -- value 0: order `-n ≠ 0` forces vanishing at the center.
  have hNinvZero : (N (φ P))⁻¹ = 0 := by
    by_contra hne
    rw [hNFinv.meromorphicOrderAt_eq_zero_iff.2 hne] at hordNinv
    rw [eq_comm, WithTop.coe_eq_zero] at hordNinv
    omega
  -- chart at ∞ is chartInfty; the chart pullback `G = chartInfty ∘ toRiemannSphere ∘ φ.symm`
  -- equals `fun w => (N w)⁻¹` near φP.
  set G : ℂ → ℂ := chartInfty ∘ (f.toRiemannSphere) ∘ φ.symm with hGdef
  have hGeq : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] G := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (φ P), Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · -- punctured part: off-center, both sides equal `(N w)⁻¹`.
      have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
        rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt]
        rw [hordN]; exact WithTop.coe_ne_top
      have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
        f.holoRepr_chartPullback_eventuallyEq_NFAt P
      -- punctured points near P are non-poles: `toRiemannSphere (φ.symm w) = coe (holoRepr (φ.symm w))`.
      have hcoe : (fun w => f.toRiemannSphere (φ.symm w)) =ᶠ[𝓝[≠] (φ P)]
          (fun w => ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere)) :=
        f.toRiemannSphere_chartPullback_eventuallyEq_coe P
      filter_upwards [hN_ne, hrepr, hcoe] with w hwN0 hwrepr hwcoe
      show (N w)⁻¹ = chartInfty (f.toRiemannSphere (φ.symm w))
      rw [hwcoe]
      -- holoRepr (φ.symm w) = N w ≠ 0, so chartInfty (coe (N w)) = (N w)⁻¹.
      rw [show f.holoRepr (φ.symm w) = N w from hwrepr]
      rw [RiemannSphere.chartInfty_apply_coe hwN0]
    · -- center: `N⁻¹ φP = 0 = chartInfty ∞ = G φP`.
      simp only [Filter.eventually_pure]
      rw [hNinvZero]
      show (0 : ℂ) = chartInfty (f.toRiemannSphere (φ.symm (φ P)))
      rw [φ.left_inv hxsrc, f.toRiemannSphere_of_pole hP, RiemannSphere.chartInfty_apply_infty]
  -- `G` is analytic, hence continuous, at φP.
  have hGana : AnalyticAt ℂ G (φ P) := hNinvAna.congr hGeq
  have hGcont : ContinuousAt G (φ P) := hGana.continuousAt
  -- Continuity of `toRiemannSphere` at `P`: near P, `toRiemannSphere = chartInfty.symm ∘ G ∘ φ`.
  have hFcont : ContinuousAt (f.toRiemannSphere) P := by
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
    have hev : ∀ᶠ y in 𝓝 P, y ∈ φ.source := φ.open_source.mem_nhds hxsrc
    -- source-membership of `toRiemannSphere P y` near P (center: `∞`; punctured: non-pole, `holoRepr = N ≠ 0`).
    have hev3 : ∀ᶠ y in 𝓝 P, f.toRiemannSphere y ∈ chartInfty.source := by
      rw [← nhdsNE_sup_pure P, Filter.eventually_sup]
      refine ⟨?_, ?_⟩
      · -- punctured: y a non-pole near P, `holoRepr y = N (φ y) ≠ 0`, so `coe (holoRepr y) ≠ coe 0`.
        have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
          rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt, hordN]
          exact WithTop.coe_ne_top
        have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
          f.holoRepr_chartPullback_eventuallyEq_NFAt P
        have hcoe : (fun w => f.toRiemannSphere (φ.symm w)) =ᶠ[𝓝[≠] (φ P)]
            (fun w => ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere)) :=
          f.toRiemannSphere_chartPullback_eventuallyEq_coe P
        have htfwd : Filter.Tendsto φ (𝓝[≠] P) (𝓝[≠] (φ P)) := φ.tendsto_nhdsNE hxsrc
        filter_upwards [htfwd.eventually hN_ne, htfwd.eventually hrepr, htfwd.eventually hcoe,
          (φ.open_source.mem_nhds hxsrc |> mem_nhdsWithin_of_mem_nhds)] with y hyN hyr hycoe hys
        -- `toRiemannSphere y = coe (holoRepr y) = coe (N (φ y)) ≠ coe 0`.
        have hycoe' : f.toRiemannSphere y = ((f.holoRepr y : ℂ) : RiemannSphere) := by
          have := hycoe; simpa [φ.left_inv hys] using this
        rw [hycoe', RiemannSphere.chartInfty_source]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcontra
        have hz : f.holoRepr y = 0 := OnePoint.coe_injective hcontra
        have : f.holoRepr y = N (φ y) := by
          have := hyr; simpa [Function.comp, φ.left_inv hys] using this
        rw [this] at hz; exact hyN hz
      · -- center: `toRiemannSphere P = ∞ ∈ source`.
        simp only [Filter.eventually_pure]
        rw [f.toRiemannSphere_of_pole hP, RiemannSphere.chartInfty_source]
        simp [OnePoint.infty_ne_coe]
    filter_upwards [hev, hev3] with y hy hy3
    show chartInfty.symm (G (φ y)) = f.toRiemannSphere y
    have hGval : G (φ y) = chartInfty (f.toRiemannSphere y) := by
      show chartInfty (f.toRiemannSphere (φ.symm (φ y))) = chartInfty (f.toRiemannSphere y)
      rw [φ.left_inv hy]
    rw [hGval, chartInfty.left_inv hy3]
  -- assemble via the converse bridge; `chartAt ℂ (toRiemannSphere P) = chartInfty`.
  refine contMDiffAt_omega_of_analyticAt_chartPullback hFcont ?_
  have hchartInfty : chartAt ℂ (f.toRiemannSphere P) = RiemannSphere.chartInfty := by
    rw [f.toRiemannSphere_of_pole hP]; rfl
  rw [hchartInfty]
  exact hGana

/-! ### Global holomorphy -/

/-- **Holomorphy of `toRiemannSphere`.** Off the poles, `toRiemannSphere = coe ∘ holoRepr`
is analytic where the order is `≥ 0` (`contMDiffAt_toRiemannSphere_of_nonneg`). At a pole,
reading in `chartInfty`, `toRiemannSphere` is `z ↦ 1/f`, analytic with value `0`
(`contMDiffAt_toRiemannSphere_at_pole`). Together: `ContMDiff … ω` everywhere — the general
"meromorphic function = holomorphic map to `ℂℙ¹`". -/
theorem MeromorphicFunction.contMDiff_toRiemannSphere (f : MeromorphicFunction X) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toRiemannSphere) := by
  intro x
  by_cases hx : 0 ≤ f.orderAtPoint x
  · exact f.contMDiffAt_toRiemannSphere_of_nonneg hx
  · exact f.contMDiffAt_toRiemannSphere_at_pole (not_le.mp hx)

/-- `toRiemannSphere` is continuous (it is holomorphic). -/
theorem MeromorphicFunction.continuous_toRiemannSphere (f : MeromorphicFunction X) :
    Continuous (f.toRiemannSphere) :=
  f.contMDiff_toRiemannSphere.continuous

/-- **`toRiemannSphere` is a proper map.** `X` is compact and `RiemannSphere` is Hausdorff,
so the continuous map `toRiemannSphere` is automatically proper (preimages of compacts are
closed subsets of the compact `X`, hence compact). -/
theorem MeromorphicFunction.isProperMap_toRiemannSphere (f : MeromorphicFunction X) :
    IsProperMap (f.toRiemannSphere) :=
  f.continuous_toRiemannSphere.isProperMap

/-! ### The zero fibre -/

/-- The chart-level order at a zero is the positive integer `orderAtPoint x`. At a genuine
zero (`0 < orderAtPoint x`), the order of the pullback `F = f.toFun ∘ φ.symm` at `φ x`
equals `(orderAtPoint x : ℤ) > 0` (it is not `⊤`, since `untop₀ ⊤ = 0`). -/
lemma MeromorphicFunction.meromorphicOrderAt_chartPullback_of_zero
    (f : MeromorphicFunction X) {x : X} (hx : 0 < f.orderAtPoint x) :
    meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
      = (f.orderAtPoint x : ℤ) := by
  set φ := chartAt (H := ℂ) x with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have h1 : f.orderAtPoint x = (meromorphicOrderAt F (φ x)).untop₀ := rfl
  cases hv : meromorphicOrderAt F (φ x) with
  | top =>
    rw [hv] at h1; simp only [WithTop.untop₀_top] at h1
    rw [h1] at hx; exact absurd hx (by norm_num)
  | coe n => rw [hv] at h1; simp only [WithTop.untop₀_coe] at h1; rw [h1]

/-- **At a genuine zero (`0 < orderAtPoint x`), the limit-repair value is `0`.** The pullback
`F` tends to `0` along the punctured chart neighborhood (`tendsto_zero_of_meromorphicOrderAt_pos`,
since the chart order is positive); transferring through `φ.symm` gives `f.toFun → 0` along
`𝓝[≠] x`, so `holoRepr x = limUnder (𝓝[≠] x) f.toFun = 0`. -/
lemma MeromorphicFunction.holoRepr_eq_zero_of_orderPos
    (f : MeromorphicFunction X) {x : X} (hx : 0 < f.orderAtPoint x) :
    f.holoRepr x = 0 := by
  set φ := chartAt (H := ℂ) x with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : x ∈ φ.source := mem_chart_source ℂ x
  -- chart order is positive.
  have hordF : meromorphicOrderAt F (φ x) = (f.orderAtPoint x : ℤ) :=
    f.meromorphicOrderAt_chartPullback_of_zero hx
  have hordpos : 0 < meromorphicOrderAt F (φ x) := by
    rw [hordF]; exact_mod_cast hx
  -- F → 0 along 𝓝[≠] (φ x).
  have hFlim : Filter.Tendsto F (𝓝[≠] (φ x)) (𝓝 0) :=
    tendsto_zero_of_meromorphicOrderAt_pos hordpos
  -- transfer to f.toFun along 𝓝[≠] x.
  show Filter.limUnder (𝓝[≠] x) f.toFun = 0
  have htsymm : Filter.Tendsto φ.symm (𝓝[≠] (φ x)) (𝓝[≠] x) := by
    have := φ.symm.tendsto_nhdsNE (x := φ x) (by simpa using φ.map_source hxsrc)
    simpa [φ.left_inv hxsrc] using this
  have hfwd : Filter.Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x)) := φ.tendsto_nhdsNE hxsrc
  haveI : (𝓝[≠] x).NeBot := htsymm.neBot
  apply Filter.Tendsto.limUnder_eq
  -- f.toFun = F ∘ φ near x (punctured), and F ∘ φ → 0.
  have hcomp : Filter.Tendsto (F ∘ φ) (𝓝[≠] x) (𝓝 0) := hFlim.comp hfwd
  refine hcomp.congr' ?_
  have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hxsrc
  filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
  simp [hFdef, Function.comp, φ.left_inv hy]

/-- **The zeros of `f` lie in the `0`-fibre.** A genuine zero (`0 < orderAtPoint x`) is a
non-pole, where `toRiemannSphere x = coe (holoRepr x) = coe 0 = 0`. (Inclusion, not equality:
the affine value `coe 0` could also be attained where the order is `0` but the value happens
to vanish, e.g. for a junk-free removable point.) -/
lemma MeromorphicFunction.zeros_subset_toRiemannSphere_preimage_zero (f : MeromorphicFunction X) :
    {x | 0 < f.orderAtPoint x} ⊆ f.toRiemannSphere ⁻¹' {((0 : ℂ) : RiemannSphere)} := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [f.toRiemannSphere_of_nonneg (le_of_lt hx), f.holoRepr_eq_zero_of_orderPos hx]

/-! ### Non-constancy -/

/-- The set of poles `{x | orderAtPoint x < 0}` is **finite**: it is contained in the support
`{x | orderAtPoint x ≠ 0}` of the locally-finite order function, which is finite on the compact
`X` (`orderLocallyFinsupp.finiteSupport`). -/
lemma MeromorphicFunction.finite_poles (f : MeromorphicFunction X) :
    {x | f.orderAtPoint x < 0}.Finite := by
  have hsupp : (Function.support f.orderAtPoint).Finite :=
    f.orderLocallyFinsupp.finiteSupport isCompact_univ
  refine hsupp.subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  exact ne_of_lt hx

/-- **`toRiemannSphere` is non-constant when `f` has a pole.** At a pole `P`,
`toRiemannSphere P = ∞`. Poles are finite (`finite_poles`) while `X` is infinite (a nonempty
open subset of a complex `1`-manifold, `infinite_of_isOpen_nonempty`), so there is a non-pole
`x₀`, where `toRiemannSphere x₀ = coe (holoRepr x₀) ≠ ∞`. Uses the genuine `IsConstantMap`
predicate. -/
theorem MeromorphicFunction.toRiemannSphere_not_isConstant_of_exists_pole
    (f : MeromorphicFunction X) (hpole : ∃ P, f.orderAtPoint P < 0) :
    ¬ IsConstantMap (f.toRiemannSphere) := by
  rintro ⟨c, hc⟩
  obtain ⟨P, hP⟩ := hpole
  -- A non-pole point exists: poles are finite, `X` is infinite.
  obtain ⟨x₀, _, hx₀⟩ : ∃ x ∈ (Set.univ : Set X), x ∉ {x | f.orderAtPoint x < 0} :=
    exists_mem_open_notMem_finite isOpen_univ Set.univ_nonempty f.finite_poles
  simp only [Set.mem_setOf_eq, not_lt] at hx₀
  -- `toRiemannSphere x₀ = coe (holoRepr x₀) = c` and `toRiemannSphere P = ∞ = c`.
  have hx₀v : f.toRiemannSphere x₀ = ((f.holoRepr x₀ : ℂ) : RiemannSphere) :=
    f.toRiemannSphere_of_nonneg hx₀
  have key : ((f.holoRepr x₀ : ℂ) : RiemannSphere) = OnePoint.infty := by
    rw [← hx₀v, hc x₀, ← f.toRiemannSphere_of_pole hP, hc P]
  exact (OnePoint.coe_ne_infty _) key

/-- **`toRiemannSphere` is non-constant for a non-constant meromorphic `f`.** A meromorphic
function with some nonzero order (`∃ x, orderAtPoint x ≠ 0` — i.e. genuinely non-constant) has
a pole on the compact connected `X` (`exists_pole_of_nonconstant`, the compact-Liouville
corollary), so `toRiemannSphere` is non-constant
(`toRiemannSphere_not_isConstant_of_exists_pole`). -/
theorem MeromorphicFunction.toRiemannSphere_not_isConstant (f : MeromorphicFunction X)
    (hf : ∃ x, f.orderAtPoint x ≠ 0) :
    ¬ IsConstantMap (f.toRiemannSphere) :=
  f.toRiemannSphere_not_isConstant_of_exists_pole (f.exists_pole_of_nonconstant hf)

end Jacobians
