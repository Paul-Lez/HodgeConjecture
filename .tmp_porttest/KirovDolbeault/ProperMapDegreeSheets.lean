/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.MultiplicityPatchingConstruct

/-!
# The local multiplicity sheets — discharging `exists_properMapDegree`

This file supplies the last input to the conservation-of-number / argument-principle wall:
the *pointwise* local-conservation data `∀ w₀, LocalMultiplicitySheets f w₀` (the irreducible
§17.9 content), from which `MultiplicityPatchingConstruct.exists_properMapDegree_of_localSheets`
delivers the proper-map-degree existential `∃ d, zerosCount f = d = polesCount f`, hence the
residue theorem `deg (div f) = 0`.

Everything *downstream* of `∀ w₀, LocalMultiplicitySheets f w₀` is already proved complete
(the connectedness globalization of `N f`, the special-fibre identities, the `ofDisjointSheets`
assembly). The content here is the per-value local construction:

* `w₀ ∉ range F`: the empty fibre — `LocalMultiplicitySheets.ofNotMemRange` (proven upstream).
* `w₀ = coe c` (a finite value): around each fibre point `x` (a solution of `f = c`), the planar
  normal form `Planar.orderSum_eq_of_analyticOrder` applied to `g = f ∘ chart.symm` gives a
  value-neighbourhood on which the multiplicity sum is the local order; transported to `localDeg`
  via `localDeg_coe_eq_chartPullback_order`.
* `w₀ = ∞` (the pole fibre): around each pole `x`, the same engine applied to `1/g` at `0`
  (a zero of order = the pole order), with the order-matching `ord(g − c') = ord(1/g − 1/c')`
  for `g(z) = c'` finite nonzero.

This is a true, non-vacuous obligation (the empty-fibre witness certifies satisfiability).

References: Forster §4 (the degree, Cor. 4.24–4.25), Miranda II.4 (argument principle).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint Filter

namespace Jacobians.ProperMapDegreeSheets

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.MultiplicityPatchingConstruct Jacobians.MultiplicityPatching

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The `holoRepr`/`toFun` reconciliation toolkit

`localDeg f (coe c) y` is the order of `f.toFun ∘ chart.symm − c`, while the *value* fibre
`F⁻¹(coe c)` (= `f.toRiemannSphere ⁻¹' {coe c}`) is cut out by the limit-repair `holoRepr` (the
geometric value of `F`).  The planar normal form is most cleanly applied to the analytic
`g = holoRepr ∘ chart.symm` (whose value matches `F` and whose order matches `localDeg`).  The
three lemmas below bridge the two representatives:

* `meromorphicAt_toFun_chartPullback`: the raw pullback is meromorphic at *any* chart-target point.
* `holoRepr_pullback_eventuallyEq_toFun`: off-center, `holoRepr ∘ chart.symm` agrees with
  `f.toFun ∘ chart.symm` (the junk-repair only changes the value *at* removable singularities,
  which are isolated).
* `meromorphicOrderAt_holoRepr_sub_eq`: hence the chart-pullback order of `f.toFun − c` is the
  order of `holoRepr − c` — the order is `𝓝[≠]`-determined. -/

/-- **The chart pullback `f.toFun ∘ (chartAt x).symm` is meromorphic at any target point `z`.**
At `y₀ := (chartAt x).symm z` the function is meromorphic at the centre of its own chart
(`f.meromorphic y₀`); the chart transition `(chartAt y₀) ∘ (chartAt x).symm` is analytic at `z`
(maximal-atlas coordinate change, `ω`), and `MeromorphicAt.comp_analyticAt` transports the order
across the (locally invertible) transition. -/
theorem meromorphicAt_toFun_chartPullback (f : MeromorphicFunction X) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) z := by
  set e := chartAt (H := ℂ) x with he
  set y₀ := e.symm z with hy₀
  have hy₀src : y₀ ∈ e.source := e.map_target hz
  have hez : e y₀ = z := e.right_inv hz
  have hmero0 : MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) y₀) :=
    f.meromorphic y₀
  have hchg_an : AnalyticAt ℂ ((chartAt (H := ℂ) y₀) ∘ e.symm) z := by
    have he_max : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)
    have hy0_max : chartAt (H := ℂ) y₀ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.chart_mem_maximalAtlas y₀
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange'
      he_max hy0_max hy₀src (mem_chart_source ℂ y₀)
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
    have hpt : (e.extend 𝓘(ℂ)) y₀ = z := by simp [hez, mfld_simps]
    rw [hpt] at h
    exact h.analyticAt
  have hzval : ((chartAt (H := ℂ) y₀) ∘ e.symm) z = (chartAt (H := ℂ) y₀) y₀ := by
    show (chartAt (H := ℂ) y₀) (e.symm z) = (chartAt (H := ℂ) y₀) y₀
    rw [← hy₀]
  have hcomp : MeromorphicAt ((f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ∘
      ((chartAt (H := ℂ) y₀) ∘ e.symm)) z :=
    MeromorphicAt.comp_analyticAt (by rw [hzval]; exact hmero0) hchg_an
  apply hcomp.congr
  have hsrc : ∀ᶠ w in 𝓝 z, e.symm w ∈ (chartAt (H := ℂ) y₀).source := by
    have hcont : ContinuousAt e.symm z := e.continuousAt_symm hz
    have : e.symm ⁻¹' (chartAt (H := ℂ) y₀).source ∈ 𝓝 z := by
      apply hcont.preimage_mem_nhds
      rw [← hy₀]
      exact (chartAt (H := ℂ) y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
    exact this
  filter_upwards [mem_nhdsWithin_of_mem_nhds hsrc] with w hw
  show (f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) (e.symm w)) =
    f.toFun (e.symm w)
  simp only [Function.comp_apply]
  rw [(chartAt (H := ℂ) y₀).left_inv hw]

/-- **The chart pullback `holoRepr ∘ (chartAt x).symm` is analytic at a target point of a non-pole.**
The analytic analogue of `meromorphicAt_toFun_chartPullback`: at `y₀ := (chartAt x).symm z`, where
`f` has nonnegative order, `holoRepr ∘ (chartAt y₀).symm` is analytic at its own chart centre
(`analyticAt_holoRepr_chartPullback_of_orderNonneg`); the chart transition
`(chartAt y₀) ∘ (chartAt x).symm` is analytic at `z` (maximal-atlas coordinate change, `ω`), so
`AnalyticAt.comp` transports the analyticity across.  This supplies the `AnalyticAt ℂ G z`
hypothesis the reciprocal keystone `meromorphicOrderAt_inv_sub_eq` consumes at each fibre point. -/
theorem analyticAt_holoRepr_chartPullback_target (f : MeromorphicFunction X) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target)
    (hnp : 0 ≤ f.orderAtPoint ((chartAt (H := ℂ) x).symm z)) :
    AnalyticAt ℂ (fun w => f.holoRepr ((chartAt (H := ℂ) x).symm w)) z := by
  set e := chartAt (H := ℂ) x with he
  set y₀ := e.symm z with hy₀
  have hy₀src : y₀ ∈ e.source := e.map_target hz
  have hez : e y₀ = z := e.right_inv hz
  have hana0 : AnalyticAt ℂ (f.holoRepr ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) y₀) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  have hchg_an : AnalyticAt ℂ ((chartAt (H := ℂ) y₀) ∘ e.symm) z := by
    have he_max : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)
    have hy0_max : chartAt (H := ℂ) y₀ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.chart_mem_maximalAtlas y₀
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange'
      he_max hy0_max hy₀src (mem_chart_source ℂ y₀)
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
    have hpt : (e.extend 𝓘(ℂ)) y₀ = z := by simp [hez, mfld_simps]
    rw [hpt] at h
    exact h.analyticAt
  have hzval : ((chartAt (H := ℂ) y₀) ∘ e.symm) z = (chartAt (H := ℂ) y₀) y₀ := by
    show (chartAt (H := ℂ) y₀) (e.symm z) = (chartAt (H := ℂ) y₀) y₀; rw [← hy₀]
  have hcomp : AnalyticAt ℂ ((f.holoRepr ∘ (chartAt (H := ℂ) y₀).symm) ∘
      ((chartAt (H := ℂ) y₀) ∘ e.symm)) z :=
    AnalyticAt.comp (g := f.holoRepr ∘ (chartAt (H := ℂ) y₀).symm) (by rw [hzval]; exact hana0)
      hchg_an
  apply hcomp.congr
  have hsrc : ∀ᶠ w in 𝓝 z, e.symm w ∈ (chartAt (H := ℂ) y₀).source := by
    have hcont : ContinuousAt e.symm z := e.continuousAt_symm hz
    apply hcont.preimage_mem_nhds
    rw [← hy₀]
    exact (chartAt (H := ℂ) y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
  filter_upwards [hsrc] with w hw
  show (f.holoRepr ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) (e.symm w)) =
    f.holoRepr (e.symm w)
  simp only [Function.comp_apply]
  rw [(chartAt (H := ℂ) y₀).left_inv hw]

/-- **Off-center, `holoRepr ∘ (chartAt x).symm` agrees with `f.toFun ∘ (chartAt x).symm`.**
At any target point `z`, the raw pullback is analytic on the *punctured* neighbourhood (it is
meromorphic there, `meromorphicAt_toFun_chartPullback`), so `f.toFun` carries no junk and its
punctured limit `holoRepr` equals the analytic value.  This generalises
`holoRepr_chartPullback_eventuallyEq_NFAt` from the chart centre to any target point. -/
theorem holoRepr_pullback_eventuallyEq_toFun (f : MeromorphicFunction X) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    f.holoRepr ∘ (chartAt (H := ℂ) x).symm =ᶠ[𝓝[≠] z]
      f.toFun ∘ (chartAt (H := ℂ) x).symm := by
  set φ := chartAt (H := ℂ) x with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hmero : MeromorphicAt F z := meromorphicAt_toFun_chartPullback f x hz
  have hana : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ F w := hmero.eventually_analyticAt
  have htgt : ∀ᶠ w in 𝓝[≠] z, w ∈ φ.target :=
    mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds hz)
  filter_upwards [hana, htgt] with w hwana hwtgt
  show f.holoRepr (φ.symm w) = F w
  show limUnder (𝓝[≠] (φ.symm w)) f.toFun = F w
  have hys : φ.symm w ∈ φ.source := φ.map_target hwtgt
  have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
    have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hwtgt)
    simpa using this
  haveI : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
  apply Filter.Tendsto.limUnder_eq
  have hFlim : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
    hwana.continuousAt.continuousWithinAt.tendsto
  have hwr : φ (φ.symm w) = w := φ.right_inv hwtgt
  have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] w) := by
    have := φ.tendsto_nhdsNE hys; rwa [hwr] at this
  have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 (F w)) := hFlim.comp hfwd
  refine hcomp.congr' ?_
  have hev : ∀ᶠ y in 𝓝 (φ.symm w), y ∈ φ.source := φ.open_source.mem_nhds hys
  filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
  simp [hFdef, Function.comp, φ.left_inv hy]

/-- **The chart-pullback order of `localDeg` can be read with `holoRepr` instead of `f.toFun`.**
Since `holoRepr ∘ chart.symm` and `f.toFun ∘ chart.symm` agree on `𝓝[≠] z`
(`holoRepr_pullback_eventuallyEq_toFun`) and `meromorphicOrderAt` is `𝓝[≠]`-determined. -/
theorem meromorphicOrderAt_holoRepr_sub_eq (f : MeromorphicFunction X) (x : X) (c : ℂ)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    meromorphicOrderAt (fun w => f.holoRepr ((chartAt (H := ℂ) x).symm w) - c) z =
      meromorphicOrderAt (fun w => f.toFun ((chartAt (H := ℂ) x).symm w) - c) z := by
  apply meromorphicOrderAt_congr
  filter_upwards [holoRepr_pullback_eventuallyEq_toFun f x hz] with w hw
  show f.holoRepr ((chartAt (H := ℂ) x).symm w) - c = f.toFun ((chartAt (H := ℂ) x).symm w) - c
  rw [show f.holoRepr ((chartAt (H := ℂ) x).symm w) = f.toFun ((chartAt (H := ℂ) x).symm w) from hw]

/-- **Non-constancy bridge.** A meromorphic `f` with nontrivial divisor (`f.div ≠ 0`) has
`toRiemannSphere` non-constant: `f.div ≠ 0` means some point has nonzero order, and a function
with a nonzero order somewhere is non-constant on the sphere (`toRiemannSphere_not_isConstant`,
the compact-Liouville corollary). -/
theorem toRiemannSphere_not_isConstant_of_div_ne_zero (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) :
    ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere := by
  apply f.toRiemannSphere_not_isConstant
  by_contra h
  apply hnc
  ext x
  simp only [Finsupp.coe_zero, Pi.zero_apply, div_apply]
  exact not_not.mp fun hx => h ⟨x, hx⟩

/-- **All fibres of `F = toRiemannSphere` are finite** for a non-constant `f` (`f.div ≠ 0`).
Direct from the unconditional finite-fibres theorem (`fibres_finite_statement_unconditional`)
applied to the ContMDiff sphere map (`contMDiff_toRiemannSphere`), using the non-constancy bridge. -/
theorem fibre_finite_of_div_ne_zero (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) (w : RiemannSphere) :
    (f.toRiemannSphere ⁻¹' {w}).Finite :=
  Jacobians.Discharge.ContMDiff.Degree.fibres_finite_statement_unconditional
    f.toRiemannSphere f.contMDiff_toRiemannSphere
    (toRiemannSphere_not_isConstant_of_div_ne_zero f hnc) w

/-! ### The radius-bounded planar engine

To make the sheets `U x` pairwise disjoint we must control their radius: choose disjoint open
neighbourhoods `V x` of the (finite) fibre *first* (T2 separation), then apply the planar normal
form with an outer radius small enough that `chart.symm '' (ball ε) ⊆ V x`.  The proven engine
`Planar.orderSum_eq_of_analyticOrder` fixes `ε` internally; this radius-bounded restatement threads
an external bound `R_ext` (the underlying `kFold_count_radiusBounded` already supports a prescribed
radius), giving `ε ≤ R_ext` while keeping the conservation conclusion. -/

namespace Planar

open Metric Jacobians.Discharge.Manifold

/-- **Radius-bounded planar conservation of number.** Identical to
`Planar.orderSum_eq_of_analyticOrder` but with the counting radius `ε` bounded by a prescribed
`R_ext > 0` — the freedom we need to fit each sheet inside a pre-chosen disjoint neighbourhood.
The proof copies the engine, threading `R ≤ R_ext` through the deriv-nonzero radius choice. -/
theorem orderSum_eq_of_analyticOrder_radiusBounded
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {m : ℕ} {R_ext : ℝ} (hR_ext : 0 < R_ext)
    (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g x₀) (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (m : ℕ∞)) :
    ∃ ε > (0 : ℝ), ε ≤ R_ext ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ ball w₀ δ, w ≠ w₀ →
        (∑ᶠ z ∈ {z ∈ ball x₀ ε | g z = w}, (meromorphicOrderAt (fun ζ => g ζ - w) z).untop₀)
          = (m : ℤ) := by
  classical
  obtain ⟨R₀, hR₀_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hm hg h_w₀ hord
  have hsub : KthRootSubstitution g x₀ w₀ m :=
    kthRootSubstitution_of_localFactorization hR₀_pos hm hu_an hu_x₀ hfact
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  obtain ⟨R_g, hR_g_pos, hg_anBall⟩ :
      ∃ r > (0 : ℝ), AnalyticOnNhd ℂ g (closedBall x₀ r) := by
    obtain ⟨s, hs_mem, hs_an⟩ := hg.exists_mem_nhds_analyticOnNhd
    rw [Metric.mem_nhds_iff] at hs_mem
    obtain ⟨r, hr_pos, hr_sub⟩ := hs_mem
    exact ⟨r / 2, by linarith, fun z hz => hs_an z (hr_sub (by
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith))⟩
  obtain ⟨R, hR_pos, hR_le_ρ, hR_le_Rg, hR_le_ext, hdv_ball⟩ :
      ∃ R > (0 : ℝ), R ≤ ρ ∧ R ≤ R_g ∧ R ≤ R_ext ∧ ∀ z ∈ ball x₀ R, deriv v z ≠ 0 := by
    have hderiv_an : AnalyticOnNhd ℂ (deriv v) (closedBall x₀ ρ) := hv_an.deriv
    have hcont : ContinuousAt (deriv v) x₀ :=
      (hderiv_an x₀ (mem_closedBall_self hρ_pos.le)).continuousAt
    have hpre : (deriv v) ⁻¹' {z : ℂ | z ≠ 0} ∈ 𝓝 x₀ :=
      hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hv_d)
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨r, hr_pos, hr_sub⟩ := hpre
    refine ⟨min r (min ρ (min R_g R_ext)),
      lt_min hr_pos (lt_min hρ_pos (lt_min hR_g_pos hR_ext)),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),
      fun z hz => hr_sub (ball_subset_ball (min_le_left _ _) hz)⟩
  have hg_anNhd : AnalyticOnNhd ℂ g (closedBall x₀ R) :=
    hg_anBall.mono (closedBall_subset_closedBall hR_le_Rg)
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, hcount⟩ :=
    Jacobians.Discharge.MMeromorphicAt.kFold_count_radiusBounded hR_pos hm hg h_w₀ hord
  refine ⟨ε, hε_pos, hε_le_R.trans hR_le_ext, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw_ball' : w ∈ ball (g x₀) δ := by rw [h_w₀]; exact hw_ball
  have hw_ne' : w ≠ g x₀ := by rw [h_w₀]; exact hw_ne
  have hncard : ({z ∈ ball x₀ ε | g z = w} : Set ℂ).ncard = m := hcount w hw_ball' hw_ne'
  set S : Set ℂ := {z ∈ ball x₀ ε | g z = w} with hS_def
  have hS_fin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hncard]; omega)
  have hroot1 : ∀ z ∈ S, (meromorphicOrderAt (fun ζ => g ζ - w) z).untop₀ = 1 := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_R : z ∈ ball x₀ R := ball_subset_ball hε_le_R hz_ball
    exact Jacobians.MultiplicityPatching.Planar.orderAt_root_eq_one
      (g := g) (v := v) (x₀ := x₀) (w₀ := w₀) (ρ := ρ) (m := m)
      hm hR_le_ρ hv_an hg_anNhd hdv_ball hv_pow hz_R hz_g hw_ne
  rw [finsum_mem_eq_finite_toFinset_sum _ hS_fin,
    Finset.sum_congr rfl (fun z hz => hroot1 z (by rwa [hS_fin.mem_toFinset] at hz)),
    Finset.sum_const]
  have hc : hS_fin.toFinset.card = m := by rw [← Set.ncard_eq_toFinset_card S hS_fin, hncard]
  rw [hc]; simp

end Planar

/-! ### The per-sheet datum and the per-point construction

For each fibre point `x` we package the local-conservation output: an open sheet `U` (inside a
pre-chosen disjoint neighbourhood `V`), a value-neighbourhood `W` of `w₀`, the weight `m`, and the
per-sheet multiplicity conservation on `W`.  `SheetDatum` bundles exactly the per-point fields of
`LocalMultiplicitySheets`; the assembly `choose`s one per fibre point. -/

/-- **Per-sheet local-conservation output** at a fibre point, parametrised by the ambient value
`w₀` and a containing open set `V` (a disjoint-separating neighbourhood).  Bundles the open sheet
`U ⊆ V` containing `x`, an open value-neighbourhood `W ∋ w₀`, the integer weight `m`, and the
per-sheet multiplicity conservation `∑_{y ∈ U ∩ F⁻¹(w)} localDeg = m` for `w ∈ W`. -/
structure SheetDatum (f : MeromorphicFunction X) (w₀ : RiemannSphere) (x : X) (V : Set X) where
  /-- The sheet. -/
  U : Set X
  /-- The sheet is open. -/
  U_open : IsOpen U
  /-- The fibre point lies in its sheet. -/
  mem_U_self : x ∈ U
  /-- The sheet fits inside the separating neighbourhood. -/
  U_subset : U ⊆ V
  /-- The integer weight. -/
  m : ℤ
  /-- The value-neighbourhood. -/
  W : Set RiemannSphere
  /-- The value-neighbourhood is open. -/
  W_open : IsOpen W
  /-- `w₀` lies in the value-neighbourhood. -/
  w₀_mem_W : w₀ ∈ W
  /-- **Per-sheet multiplicity conservation.** -/
  sheetMult_eq : ∀ w ∈ W, (∑ᶠ y ∈ U ∩ f.toRiemannSphere ⁻¹' {w}, localDeg f w y) = m

open Metric in
/-- **The per-point construction at a finite value `coe c`.**  At a fibre point `x` of `F⁻¹(coe c)`
(so `holoRepr x = c`, `x` a non-pole), with a clean separating neighbourhood `V` (open, containing
`x`, inside the chart source and the non-pole locus), the radius-bounded planar normal form applied
to `g = holoRepr ∘ chart.symm` produces a sheet `U ⊆ V` and a value-disc `W = coe '' ball c δ` on
which the per-sheet multiplicity sum is the local order `m = localDeg f (coe c) x`.  The generic
rows (`w = coe c'`, `c' ≠ c`) come from the engine; the central row (`w = coe c`) holds because the
`c`-fibre in `U` is the single isolated point `x`. -/
theorem exists_sheetDatum_coe (f : MeromorphicFunction X) (hnc : (f.div : Divisor X) ≠ 0)
    (c : ℂ) {x : X} (hx_fib : f.toRiemannSphere x = ((c : ℂ) : RiemannSphere))
    {V : Set X} (hV_open : IsOpen V) (hxV : x ∈ V)
    (hV_np : V ⊆ {y | 0 ≤ f.orderAtPoint y}) :
    Nonempty (SheetDatum f ((c : ℂ) : RiemannSphere) x V) := by
  classical
  set e := chartAt (H := ℂ) x with he
  have hfib_fin := fibre_finite_of_div_ne_zero f hnc (((c : ℂ) : RiemannSphere))
  -- Non-pole at `x`, `holoRepr x = c`, and the analytic chart pullback `g = holoRepr ∘ e.symm`.
  have hnonpole : 0 ≤ f.orderAtPoint x := hV_np hxV
  have hrepr : f.holoRepr x = c := by
    have := f.toRiemannSphere_of_nonneg hnonpole; rw [this] at hx_fib
    exact OnePoint.coe_injective hx_fib
  set g := f.holoRepr ∘ e.symm with hg
  have hg_an : AnalyticAt ℂ g (e x) := f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnonpole
  have hg_val : g (e x) = c := by
    show f.holoRepr (e.symm (e x)) = c; rw [e.left_inv (mem_chart_source ℂ x), hrepr]
  have hgc_an : AnalyticAt ℂ (fun z => g z - c) (e x) := hg_an.sub analyticAt_const
  -- The analytic order of `g − c` at `e x` is a natural `m ≥ 1` (value `0`, finite by finite fibre).
  have hval0 : (fun z => g z - c) (e x) = 0 := by show g (e x) - c = 0; rw [hg_val]; ring
  have hne_zero : analyticOrderAt (fun z => g z - c) (e x) ≠ 0 :=
    (hgc_an.analyticOrderAt_ne_zero).mpr hval0
  have hne_top : analyticOrderAt (fun z => g z - c) (e x) ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    -- `g = c` on a nbhd ⟹ `holoRepr = c` ⟹ `F = coe c` on a nbhd ⟹ fibre infinite, contradiction.
    have hge : ∀ᶠ y in 𝓝 x, f.holoRepr y = c := by
      have hpre : e ⁻¹' {z | g z - c = 0} ∈ 𝓝 x :=
        (e.continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds htop
      have hsrc : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds (mem_chart_source ℂ x)
      filter_upwards [hpre, hsrc] with y hy hysrc
      simp only [Set.mem_preimage, Set.mem_setOf_eq, sub_eq_zero] at hy
      show f.holoRepr y = c
      rw [show f.holoRepr y = g (e y) from
        (by show _ = f.holoRepr (e.symm (e y)); rw [e.left_inv hysrc]), hy]
    have hFe : ∀ᶠ y in 𝓝 x, f.toRiemannSphere y = ((c : ℂ) : RiemannSphere) := by
      filter_upwards [f.toRiemannSphere_eventuallyEq_coe_holoRepr hnonpole, hge] with y hy1 hy2
      rw [hy1]; show ((f.holoRepr y : ℂ) : RiemannSphere) = _; rw [hy2]
    rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hFe
    obtain ⟨U0, hU0sub, hU0open, hxU0⟩ := hFe
    exact (Jacobians.infinite_of_isOpen_nonempty hU0open ⟨x, hxU0⟩)
      (hfib_fin.subset (fun y hy => hU0sub hy))
  set m : ℕ := (analyticOrderAt (fun z => g z - c) (e x)).toNat with hm_def
  have hm_eq : analyticOrderAt (fun z => g z - c) (e x) = (m : ℕ∞) := (ENat.coe_toNat hne_top).symm
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero]; intro h0; apply hne_zero; rw [hm_eq, h0]; rfl
  -- `localDeg f (coe c) x = m`.
  have hlocalDeg_x : localDeg f ((c : ℂ) : RiemannSphere) x = (m : ℤ) := by
    rw [localDeg_coe_eq_chartPullback_order f c e (chart_mem_atlas ℂ x) (mem_chart_source ℂ x),
      ← meromorphicOrderAt_holoRepr_sub_eq f x c (e.map_source (mem_chart_source ℂ x)),
      show (fun w => f.holoRepr (e.symm w) - c) = (fun w => g w - c) from rfl,
      hgc_an.meromorphicOrderAt_eq, hm_eq]
    simp
  -- Choose the outer radius `R`: ball inside `e.target`, `e.symm '' ball ⊆ V`, and the `c`-zero
  -- is isolated in it.
  have htgt_nhds : e.target ∈ 𝓝 (e x) :=
    e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x))
  have hsymmV : e.symm ⁻¹' V ∈ 𝓝 (e x) := by
    apply (e.continuousAt_symm (e.map_source (mem_chart_source ℂ x))).preimage_mem_nhds
    rw [e.left_inv (mem_chart_source ℂ x)]; exact hV_open.mem_nhds hxV
  have hiso : ∀ᶠ z in 𝓝[≠] (e x), g z ≠ c := by
    rcases hgc_an.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso; apply hne_top; rw [analyticOrderAt_eq_top]; exact h
    · filter_upwards [h] with z hz; intro hzc; apply hz; rw [hzc]; ring
  rw [eventually_nhdsWithin_iff] at hiso
  have hiso' : ∀ᶠ z in 𝓝 (e x), z ≠ e x → g z ≠ c := by
    filter_upwards [hiso] with z hz hzne; exact hz hzne
  have hall : (e.target ∩ e.symm ⁻¹' V) ∩ {z | z ≠ e x → g z ≠ c} ∈ 𝓝 (e x) :=
    Filter.inter_mem (Filter.inter_mem htgt_nhds hsymmV) hiso'
  rw [Metric.mem_nhds_iff] at hall
  obtain ⟨R, hR_pos, hR_sub⟩ := hall
  have hcond_a : ball (e x) R ⊆ e.target := fun z hz => (hR_sub hz).1.1
  have hcond_c : ∀ z ∈ ball (e x) R, z ≠ e x → g z ≠ c := fun z hz => (hR_sub hz).2
  have hcond_b : e.symm '' (ball (e x) R ∩ e.target) ⊆ V := by
    rintro y ⟨z, ⟨hz_ball, _⟩, rfl⟩; exact (hR_sub hz_ball).1.2
  -- Apply the radius-bounded planar engine.
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, hcount⟩ :=
    Planar.orderSum_eq_of_analyticOrder_radiusBounded (w₀ := c) hR_pos hm1 hg_an hg_val hm_eq
  -- Shrunk-radius facts (`ε ≤ R`).
  have hε_tgt : ball (e x) ε ⊆ e.target := (ball_subset_ball hε_le_R).trans hcond_a
  have hε_V : e.symm '' (ball (e x) ε ∩ e.target) ⊆ V := by
    rintro y ⟨z, ⟨hz_ball, _⟩, rfl⟩
    exact hcond_b ⟨z, ⟨ball_subset_ball hε_le_R hz_ball, hcond_a (ball_subset_ball hε_le_R hz_ball)⟩,
      rfl⟩
  have hε_c : ∀ z ∈ ball (e x) ε, z ≠ e x → g z ≠ c :=
    fun z hz => hcond_c z (ball_subset_ball hε_le_R hz)
  -- Non-pole on the sheet (`U ⊆ V ⊆ nonpoles`).
  have hε_np : ∀ z ∈ ball (e x) ε, 0 ≤ f.orderAtPoint (e.symm z) := by
    intro z hz
    exact hV_np (hε_V ⟨z, ⟨hz, hε_tgt hz⟩, rfl⟩)
  have hxball : e x ∈ ball (e x) ε := mem_ball_self hε_pos
  -- The order-equation transfer (holoRepr ↔ toFun) for the reindexing.
  have horder_eq : ∀ w' : ℂ, ∀ z ∈ e.target,
      meromorphicOrderAt (fun w => f.holoRepr (e.symm w) - w') z =
        meromorphicOrderAt (fun w => f.toFun (e.symm w) - w') z :=
    fun w' z hz => meromorphicOrderAt_holoRepr_sub_eq f x w' hz
  -- Assemble the datum.
  refine ⟨{
    U := e.symm '' (ball (e x) ε ∩ e.target)
    U_open := e.symm.isOpen_image_of_subset_source (isOpen_ball.inter e.open_target)
      (by rw [e.symm_source]; exact Set.inter_subset_right)
    mem_U_self := ⟨e x, ⟨hxball, hε_tgt hxball⟩, e.left_inv (mem_chart_source ℂ x)⟩
    U_subset := hε_V
    m := (m : ℤ)
    W := (fun z : ℂ => (z : RiemannSphere)) '' (ball c δ)
    W_open := OnePoint.isOpenMap_coe _ isOpen_ball
    w₀_mem_W := ⟨c, mem_ball_self hδ_pos, rfl⟩
    sheetMult_eq := ?_ }⟩
  -- The per-sheet conservation.
  rintro w ⟨w', hw'_ball, rfl⟩
  by_cases hw'c : w' = c
  · -- Central row `w' = c`: the `c`-fibre in `U` is the single isolated point `x`.
    subst hw'c
    have hset_central : (e.symm '' (ball (e x) ε ∩ e.target)
        ∩ f.toRiemannSphere ⁻¹' {((w' : ℂ) : RiemannSphere)}) = {x} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, ⟨hz_ball, hz_tgt⟩, rfl⟩, hFy⟩
        have hrep : f.holoRepr (e.symm z) = w' := by
          have := hFy; rw [f.toRiemannSphere_of_nonneg (hε_np z hz_ball)] at this
          exact OnePoint.coe_injective this
        by_cases hze : z = e x
        · rw [hze, e.left_inv (mem_chart_source ℂ x)]
        · exact absurd hrep (hε_c z hz_ball hze)
      · intro hyx
        rw [hyx]
        exact ⟨⟨e x, ⟨hxball, hε_tgt hxball⟩, e.left_inv (mem_chart_source ℂ x)⟩, hx_fib⟩
    rw [hset_central, finsum_mem_singleton, hlocalDeg_x]
  · -- Generic row `w' ≠ c`: reindex the planar engine count.
    set S' := (e.symm '' (ball (e x) ε ∩ e.target)
      ∩ f.toRiemannSphere ⁻¹' {((w' : ℂ) : RiemannSphere)}) with hS'
    have hset : {z ∈ ball (e x) ε | g z = w'} = e '' S' := by
      ext z
      simp only [hS', Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz_ball, hz_g⟩
        have hz_tgt : z ∈ e.target := hε_tgt hz_ball
        exact ⟨e.symm z, ⟨⟨z, ⟨hz_ball, hz_tgt⟩, rfl⟩, by
          rw [f.toRiemannSphere_of_nonneg (hε_np z hz_ball),
            show f.holoRepr (e.symm z) = w' from hz_g]⟩, e.right_inv hz_tgt⟩
      · rintro ⟨y, ⟨⟨z', ⟨hz'_ball, hz'_tgt⟩, hz'y⟩, hFy⟩, hyz⟩
        have hz'_eq : e (e.symm z') = z' := e.right_inv hz'_tgt
        subst hyz; subst hz'y; rw [hz'_eq]
        refine ⟨hz'_ball, ?_⟩
        have hF := hFy
        rw [f.toRiemannSphere_of_nonneg (hε_np z' hz'_ball)] at hF
        exact OnePoint.coe_injective hF
    have hInj : Set.InjOn e S' := by
      intro a ha b hb hab
      obtain ⟨za, hza, rfl⟩ := ha.1
      obtain ⟨zb, hzb, rfl⟩ := hb.1
      rw [e.right_inv hza.2, e.right_inv hzb.2] at hab; rw [hab]
    have hcount' := hcount _ hw'_ball hw'c
    rw [hset, finsum_mem_image hInj] at hcount'
    rw [← hcount']
    apply finsum_mem_congr rfl
    intro y hy
    obtain ⟨za, hza, rfl⟩ := hy.1
    have hy_src : e.symm za ∈ e.source := e.map_target hza.2
    rw [localDeg_coe_eq_chartPullback_order f w' e (chart_mem_atlas ℂ x) hy_src,
      e.right_inv hza.2]
    show (meromorphicOrderAt (fun z => f.toFun (e.symm z) - w') za).untop₀
      = (meromorphicOrderAt (fun ζ => f.holoRepr (e.symm ζ) - w') za).untop₀
    rw [horder_eq w' za hza.2]

/-- **The reciprocal order-matching identity** (the keystone for the `∞` case).  At a point `z`
where `G` is analytic with finite nonzero value `G z = c'`, the order of `1/G − 1/c'` equals the
order of `G − c'`: writing `1/G − 1/c' = −(c'·G)⁻¹ · (G − c')` with `−(c'·G)⁻¹` analytic and nonzero
at `z` (`meromorphicOrderAt_mul_of_ne_zero`).  This is what lets the planar engine applied to the
reciprocal `1/G` (a zero of order `= the pole order` at the pole) re-deliver the finite-value local
degrees `localDeg f (coe c')` in the pole fibre's `∞`-neighbourhood. -/
theorem meromorphicOrderAt_inv_sub_eq (G : ℂ → ℂ) {z c' : ℂ} (hc' : c' ≠ 0) (hGz : G z = c')
    (hGanal : AnalyticAt ℂ G z) :
    meromorphicOrderAt (fun ζ => (G ζ)⁻¹ - c'⁻¹) z = meromorphicOrderAt (fun ζ => G ζ - c') z := by
  have hfac_anal : AnalyticAt ℂ (fun ζ => -(c' * G ζ)⁻¹) z :=
    ((analyticAt_const.mul hGanal).inv (by simp [hGz, hc'])).neg
  have hfac_ne : (fun ζ => -(c' * G ζ)⁻¹) z ≠ 0 := by simp [hGz, hc']
  have heq : (fun ζ => (G ζ)⁻¹ - c'⁻¹)
      =ᶠ[𝓝[≠] z] (fun ζ => -(c' * G ζ)⁻¹) * (fun ζ => G ζ - c') := by
    have hGne : ∀ᶠ ζ in 𝓝[≠] z, G ζ ≠ 0 :=
      (hGanal.continuousAt.eventually_ne (by rw [hGz]; exact hc')).filter_mono nhdsWithin_le_nhds
    filter_upwards [hGne] with ζ hζ
    simp only [Pi.mul_apply]; field_simp; ring
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul_of_ne_zero hfac_anal hfac_ne]

/-- **The chart-pullback order of `f.toFun` at the chart centre equals `orderAtPoint`** (as a
`WithTop ℤ`, *finite*).  At a pole (`orderAtPoint x < 0`) the order is not `⊤` (else `orderAtPoint`
would be the junk `0`), so `meromorphicOrderAt (f.toFun ∘ e.symm) (e x) = (orderAtPoint x : ℤ)`.
This pins the negative order `−m` of the pullback `G`, whose reciprocal `1/G` then has the positive
order `m` that drives the reciprocal normal form. -/
theorem meromorphicOrderAt_chartPullback_eq_orderAtPoint (f : MeromorphicFunction X) {x : X}
    (hx_pole : f.orderAtPoint x < 0) :
    meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) x).symm z)) ((chartAt (H := ℂ) x) x)
      = (f.orderAtPoint x : WithTop ℤ) := by
  set e := chartAt (H := ℂ) x with he
  have hord : f.orderAtPoint x = (meromorphicOrderAt (f.toFun ∘ e.symm) (e x)).untop₀ := rfl
  have hne_top : meromorphicOrderAt (f.toFun ∘ e.symm) (e x) ≠ ⊤ := by
    intro htop; rw [hord, htop] at hx_pole; simp at hx_pole
  rw [show (fun z => f.toFun (e.symm z)) = (f.toFun ∘ e.symm) from rfl, hord]
  exact (WithTop.coe_untop₀_of_ne_top hne_top).symm

/-- **The repaired reciprocal at a pole.**  At a pole `x` (`orderAtPoint x < 0`), with
`g = f.holoRepr ∘ (chartAt x).symm` the *junk-free* chart pullback (meromorphic, order `−m`; equal
to `f.toFun ∘ (chartAt x).symm` off the centre, so it cuts the geometric value fibre `F⁻¹(coe ·)`),
the normal-form representative `h := toMeromorphicNFAt g⁻¹ (e x)` of the reciprocal `1/g` is
**analytic** at `e x`, agrees with `(g ·)⁻¹` on the punctured neighbourhood `𝓝[≠] (e x)`, vanishes
at `e x` (`h (e x) = 0`), and has analytic order exactly `m = (orderAtPoint x).natAbs ≥ 1`
(`meromorphicOrderAt g⁻¹ = −meromorphicOrderAt g = m`, transported through the normal form, with
`AnalyticAt.meromorphicOrderAt_eq` converting the meromorphic order to the analytic order).  This is
the analytic input the planar engine consumes at `w₀ = 0`. -/
theorem exists_reciprocal_NF (f : MeromorphicFunction X) {x : X} (hx_pole : f.orderAtPoint x < 0) :
    ∃ (h : ℂ → ℂ) (m : ℕ), 1 ≤ m ∧ (m : ℤ) = -f.orderAtPoint x ∧
      AnalyticAt ℂ h ((chartAt (H := ℂ) x) x) ∧
      ((fun z => (f.holoRepr ((chartAt (H := ℂ) x).symm z))⁻¹) =ᶠ[𝓝[≠] ((chartAt (H := ℂ) x) x)] h) ∧
      h ((chartAt (H := ℂ) x) x) = 0 ∧
      analyticOrderAt h ((chartAt (H := ℂ) x) x) = (m : ℕ∞) := by
  set e := chartAt (H := ℂ) x with he
  set G : ℂ → ℂ := fun z => f.holoRepr (e.symm z) with hG
  have htgt : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
  -- `G = holoRepr ∘ e.symm` agrees with `toFun ∘ e.symm` off the centre (the junk-repair toolkit).
  have hGtF : G =ᶠ[𝓝[≠] (e x)] (fun z => f.toFun (e.symm z)) :=
    holoRepr_pullback_eventuallyEq_toFun f x htgt
  have hmeroG : MeromorphicAt G (e x) :=
    (meromorphicAt_toFun_chartPullback f x htgt).congr hGtF.symm
  have hordG : meromorphicOrderAt G (e x) = (f.orderAtPoint x : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr hGtF]
    exact meromorphicOrderAt_chartPullback_eq_orderAtPoint f hx_pole
  -- `G⁻¹` meromorphic, order `−orderAtPoint x = m > 0`.
  have hmeroInv : MeromorphicAt G⁻¹ (e x) := hmeroG.inv
  have hordInv : meromorphicOrderAt G⁻¹ (e x) = -(f.orderAtPoint x : WithTop ℤ) := by
    rw [meromorphicOrderAt_inv, hordG]
  set h : ℂ → ℂ := toMeromorphicNFAt G⁻¹ (e x) with hh
  have hheq : G⁻¹ =ᶠ[𝓝[≠] (e x)] h := hmeroInv.eq_nhdsNE_toMeromorphicNFAt
  have hNF : MeromorphicNFAt h (e x) := meromorphicNFAt_toMeromorphicNFAt
  have hordh : meromorphicOrderAt h (e x) = -(f.orderAtPoint x : WithTop ℤ) := by
    rw [← hordInv]; exact (meromorphicOrderAt_congr hheq).symm
  -- `m := (−orderAtPoint x).toNat ≥ 1`.
  set m : ℕ := (-f.orderAtPoint x).toNat with hm_def
  have hm_eq : (m : ℤ) = -f.orderAtPoint x := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  have hordh' : meromorphicOrderAt h (e x) = (m : WithTop ℤ) := by
    rw [hordh]
    have : ((m : ℤ) : WithTop ℤ) = ((-f.orderAtPoint x : ℤ) : WithTop ℤ) := by rw [hm_eq]
    push_cast at this ⊢; rw [this]
  have hnonneg : 0 ≤ meromorphicOrderAt h (e x) := by rw [hordh']; exact_mod_cast (Nat.zero_le m)
  have hana : AnalyticAt ℂ h (e x) := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hnonneg
  -- `analyticOrderAt h (e x) = m`, and `h (e x) = 0`.
  have hbridge : meromorphicOrderAt h (e x) = ENat.map Nat.cast (analyticOrderAt h (e x)) :=
    hana.meromorphicOrderAt_eq
  rw [hordh'] at hbridge
  have hAO : analyticOrderAt h (e x) = (m : ℕ∞) := by
    cases hAO' : analyticOrderAt h (e x) with
    | top => rw [hAO'] at hbridge; simp at hbridge
    | coe n =>
      rw [hAO'] at hbridge; simp only [ENat.map_coe] at hbridge; norm_cast at hbridge ⊢; omega
  have hval0 : h (e x) = 0 := by
    have hne0 : analyticOrderAt h (e x) ≠ 0 := by rw [hAO]; exact_mod_cast (by omega : m ≠ 0)
    rwa [hana.analyticOrderAt_ne_zero] at hne0
  refine ⟨h, m, hm1, hm_eq, hana, ?_, hval0, hAO⟩
  -- `(fun z => (f.holoRepr (e.symm z))⁻¹) = G⁻¹` (definitionally `Pi.inv G`).
  have hpi : (fun z => (f.holoRepr (e.symm z))⁻¹) = G⁻¹ := rfl
  rw [hpi]; exact hheq

open Metric in
/-- **The per-point construction at `∞` (the pole fibre).**  At a pole `x` (`orderAtPoint x < 0`,
so `F x = ∞`), with a clean separating neighbourhood `V`, the same conservation-of-number content
holds via the reciprocal normal form `1/g` (a zero of order `= the pole order` at `e x`): a sheet
`U ⊆ V` and an `∞`-neighbourhood `W` on which the per-sheet multiplicity sum is the pole order
`m = localDeg f ∞ x = −orderAtPoint x`.

PROOF (mirrors `exists_sheetDatum_coe`; the keystone `meromorphicOrderAt_inv_sub_eq` and the
reciprocal extraction `exists_reciprocal_NF` are proven, and the radius-bounded engine +
`finsum_mem_image` reindexing are reusable):

* `exists_reciprocal_NF` gives the *repaired reciprocal* `h : ℂ → ℂ` analytic at `e x` with
  `h =ᶠ[𝓝[≠] (e x)] (G ·)⁻¹` (`G = f.toFun ∘ e.symm`), `h (e x) = 0`, `analyticOrderAt h (e x) = m`.
* `Planar.orderSum_eq_of_analyticOrder_radiusBounded` applied to `h` at `w₀ = 0`, order `m`.
* Value-neighbourhood `W := invMap ⁻¹' ((↑) '' ball 0 δ)` (open, `∞ ∈ W` since `invMap ∞ = coe 0`).
* Generic rows (`w = coe c'`, `c' ≠ 0`): the engine count `{z ∈ ball ε | h z = w'}` (`w' = c'⁻¹`)
  reindexes to `U ∩ F⁻¹(coe c')` via `h z = w' ↔ G z = c'` off the centre, and the summand
  `localDeg f (coe c') (e.symm z) = (meromorphicOrderAt (h − w') z).untop₀` matches by
  `meromorphicOrderAt_inv_sub_eq` plus the `holoRepr`/`toFun` reconciliation toolkit.
* Central row (`w = ∞`): the pole fibre in `U` is the isolated point `x`, with
  `localDeg f ∞ x = −orderAtPoint x = m`. -/
theorem exists_sheetDatum_infty (f : MeromorphicFunction X) (_hnc : (f.div : Divisor X) ≠ 0)
    {x : X} (hx_pole : f.orderAtPoint x < 0)
    {V : Set X} (hV_open : IsOpen V) (hxV : x ∈ V)
    (_hV_src : V ⊆ (chartAt (H := ℂ) x).source) :
    Nonempty (SheetDatum f OnePoint.infty x V) := by
  classical
  set e := chartAt (H := ℂ) x with he
  -- `G = holoRepr ∘ e.symm` is the *junk-free* pullback: it cuts the geometric value fibre and
  -- agrees with `f.toFun ∘ e.symm` off the centre (so orders transport to `localDeg`).
  set G : ℂ → ℂ := fun z => f.holoRepr (e.symm z) with hG
  -- The repaired reciprocal `h` (analytic, order `m`, `=ᶠ (G ·)⁻¹` on `𝓝[≠] (e x)`).
  obtain ⟨h, m, hm1, hm_eq, hana, hheq, hval0, hAO⟩ := exists_reciprocal_NF f hx_pole
  -- `localDeg f ∞ x = m` (the central-row weight).
  have hlocalDeg_x : localDeg f OnePoint.infty x = (m : ℤ) := by
    rw [localDeg_infty, hm_eq]
  -- The punctured reciprocal identity `h = (G ·)⁻¹` off `e x`, as an eventual statement.
  have hheq' : ∀ᶠ z in 𝓝[≠] (e x), (G z)⁻¹ = h z := hheq
  rw [eventually_nhdsWithin_iff] at hheq'
  have hrecip' : ∀ᶠ z in 𝓝 (e x), z ≠ e x → h z = (G z)⁻¹ := by
    filter_upwards [hheq'] with z hz hzne; exact (hz hzne).symm
  have htgt_nhds : e.target ∈ 𝓝 (e x) :=
    e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x))
  -- Pole isolation: `e.symm z` is a non-pole (order `0`) for `z ≠ e x` near `e x`.
  obtain ⟨t, ht_nhds, ht⟩ := f.orderAtPoint_isolated_at x
  have hiso' : ∀ᶠ z in 𝓝 (e x), z ≠ e x → f.orderAtPoint (e.symm z) = 0 := by
    have hsymm_t : e.symm ⁻¹' t ∈ 𝓝 (e x) := by
      apply (e.continuousAt_symm (e.map_source (mem_chart_source ℂ x))).preimage_mem_nhds
      rw [e.left_inv (mem_chart_source ℂ x)]; exact ht_nhds
    have hsymm_ne : ∀ᶠ z in 𝓝 (e x), z ≠ e x → e.symm z ≠ x := by
      filter_upwards [htgt_nhds] with z hzt hzne hcontra
      apply hzne
      calc z = e (e.symm z) := (e.right_inv hzt).symm
        _ = e x := by rw [hcontra]
    filter_upwards [hsymm_t, hsymm_ne] with z hzt hzne hne
    exact ht (e.symm z) hzt (hzne hne)
  -- Choose the outer radius `R`: ball inside `e.target`, `e.symm '' ball ⊆ V`, `h = (G ·)⁻¹` off the
  -- centre, and no other pole of `f` (order `0` off the centre) throughout it.
  have hsymmV : e.symm ⁻¹' V ∈ 𝓝 (e x) := by
    apply (e.continuousAt_symm (e.map_source (mem_chart_source ℂ x))).preimage_mem_nhds
    rw [e.left_inv (mem_chart_source ℂ x)]; exact hV_open.mem_nhds hxV
  have hall : ((e.target ∩ e.symm ⁻¹' V) ∩ {z | z ≠ e x → h z = (G z)⁻¹})
      ∩ {z | z ≠ e x → f.orderAtPoint (e.symm z) = 0} ∈ 𝓝 (e x) :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem htgt_nhds hsymmV) hrecip') hiso'
  rw [Metric.mem_nhds_iff] at hall
  obtain ⟨R, hR_pos, hR_sub⟩ := hall
  have hcond_a : ball (e x) R ⊆ e.target := fun z hz => (hR_sub hz).1.1.1
  have hcond_recip : ∀ z ∈ ball (e x) R, z ≠ e x → h z = (G z)⁻¹ := fun z hz => (hR_sub hz).1.2
  have hcond_np : ∀ z ∈ ball (e x) R, z ≠ e x → f.orderAtPoint (e.symm z) = 0 :=
    fun z hz => (hR_sub hz).2
  have hcond_b : e.symm '' (ball (e x) R ∩ e.target) ⊆ V := by
    rintro y ⟨z, ⟨hz_ball, _⟩, rfl⟩; exact (hR_sub hz_ball).1.1.2
  -- Apply the radius-bounded planar engine to `h` at `w₀ = 0`, order `m`.
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, hcount⟩ :=
    Planar.orderSum_eq_of_analyticOrder_radiusBounded (g := h) (w₀ := 0) (m := m) hR_pos hm1 hana
      hval0 (by simp only [sub_zero]; exact hAO)
  -- Shrunk-radius facts (`ε ≤ R`).
  have hε_tgt : ball (e x) ε ⊆ e.target := (ball_subset_ball hε_le_R).trans hcond_a
  have hε_V : e.symm '' (ball (e x) ε ∩ e.target) ⊆ V := by
    rintro y ⟨z, ⟨hz_ball, _⟩, rfl⟩
    exact hcond_b ⟨z, ⟨ball_subset_ball hε_le_R hz_ball, hcond_a (ball_subset_ball hε_le_R hz_ball)⟩,
      rfl⟩
  have hε_recip : ∀ z ∈ ball (e x) ε, z ≠ e x → h z = (G z)⁻¹ :=
    fun z hz => hcond_recip z (ball_subset_ball hε_le_R hz)
  have hε_np : ∀ z ∈ ball (e x) ε, z ≠ e x → f.orderAtPoint (e.symm z) = 0 :=
    fun z hz => hcond_np z (ball_subset_ball hε_le_R hz)
  have hxball : e x ∈ ball (e x) ε := mem_ball_self hε_pos
  -- The pole fibre point `x` lies in the sheet and `F x = ∞`.
  have hFx : f.toRiemannSphere x = OnePoint.infty := f.toRiemannSphere_of_pole hx_pole
  -- Assemble the datum.
  refine ⟨{
    U := e.symm '' (ball (e x) ε ∩ e.target)
    U_open := e.symm.isOpen_image_of_subset_source (isOpen_ball.inter e.open_target)
      (by rw [e.symm_source]; exact Set.inter_subset_right)
    mem_U_self := ⟨e x, ⟨hxball, hε_tgt hxball⟩, e.left_inv (mem_chart_source ℂ x)⟩
    U_subset := hε_V
    m := (m : ℤ)
    W := RiemannSphere.invMap ⁻¹' ((fun z : ℂ => (z : RiemannSphere)) '' (ball 0 δ))
    W_open := (OnePoint.isOpenMap_coe _ isOpen_ball).preimage RiemannSphere.continuous_invMap
    w₀_mem_W := by
      simp only [Set.mem_preimage, RiemannSphere.invMap_infty, Set.mem_image]
      exact ⟨0, mem_ball_self hδ_pos, rfl⟩
    sheetMult_eq := ?_ }⟩
  -- The per-sheet conservation.  `w ∈ W` means `invMap w ∈ coe '' ball 0 δ`.
  rintro w hwW
  induction w using OnePoint.rec with
  | infty =>
    -- Central row `w = ∞`: the pole fibre in `U` is the single point `x`.
    have hset_central : (e.symm '' (ball (e x) ε ∩ e.target)
        ∩ f.toRiemannSphere ⁻¹' {OnePoint.infty}) = {x} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, ⟨hz_ball, hz_tgt⟩, rfl⟩, hFy⟩
        by_cases hze : z = e x
        · rw [hze, e.left_inv (mem_chart_source ℂ x)]
        · exfalso
          have hnp : 0 ≤ f.orderAtPoint (e.symm z) := le_of_eq (hε_np z hz_ball hze).symm
          rw [f.toRiemannSphere_of_nonneg hnp] at hFy
          exact (OnePoint.coe_ne_infty _) hFy
      · intro hyx
        rw [hyx]
        exact ⟨⟨e x, ⟨hxball, hε_tgt hxball⟩, e.left_inv (mem_chart_source ℂ x)⟩, hFx⟩
    rw [hset_central, finsum_mem_singleton, hlocalDeg_x]
  | coe c' =>
    -- Generic row `w = coe c'`.  Membership in `W` forces `c' ≠ 0` and `c'⁻¹ ∈ ball 0 δ`.
    have hc'_ne : c' ≠ 0 := by
      rintro rfl
      simp only [Set.mem_preimage, RiemannSphere.invMap_coe_zero, Set.mem_image] at hwW
      obtain ⟨d, _, hd⟩ := hwW
      exact (OnePoint.coe_ne_infty d) hd
    have hw'_ne : c'⁻¹ ≠ 0 := inv_ne_zero hc'_ne
    have hw'_ball : c'⁻¹ ∈ ball (0 : ℂ) δ := by
      simp only [Set.mem_preimage, RiemannSphere.invMap_coe_of_ne hc'_ne, Set.mem_image] at hwW
      obtain ⟨d, hd_ball, hd⟩ := hwW
      rwa [show c'⁻¹ = d from (OnePoint.coe_injective hd).symm]
    -- For `z` off the centre in the ball: `G z = c' ↔ h z = c'⁻¹` (via `h = (G ·)⁻¹` and `inv_inv`).
    have hGc_iff : ∀ z ∈ ball (e x) ε, z ≠ e x → (h z = c'⁻¹ ↔ G z = c') := by
      intro z hz_ball hzne
      rw [hε_recip z hz_ball hzne]
      constructor
      · intro hG; rw [← inv_inv (G z), hG, inv_inv]
      · intro hG; rw [hG]
    -- `F (e.symm z) = coe c'` (at a non-pole) ↔ `G z = c'` (`G = holoRepr ∘ e.symm`).
    have hFib_iff : ∀ z ∈ ball (e x) ε, z ≠ e x →
        (f.toRiemannSphere (e.symm z) = ((c' : ℂ) : RiemannSphere) ↔ G z = c') := by
      intro z hz_ball hzne
      have hnp : 0 ≤ f.orderAtPoint (e.symm z) := le_of_eq (hε_np z hz_ball hzne).symm
      rw [f.toRiemannSphere_of_nonneg hnp]
      exact ⟨fun hh => OnePoint.coe_injective hh, fun hh => by rw [show f.holoRepr (e.symm z) = G z
        from rfl, hh]⟩
    -- Reindex the engine count `{z ∈ ball ε | h z = c'⁻¹}` to `U ∩ F⁻¹(coe c')`.
    set S' := (e.symm '' (ball (e x) ε ∩ e.target)
      ∩ f.toRiemannSphere ⁻¹' {((c' : ℂ) : RiemannSphere)}) with hS'
    have hset : {z ∈ ball (e x) ε | h z = c'⁻¹} = e '' S' := by
      ext z
      simp only [hS', Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz_ball, hz_h⟩
        have hz_tgt : z ∈ e.target := hε_tgt hz_ball
        have hzne : z ≠ e x := by rintro rfl; rw [hval0] at hz_h; exact hw'_ne hz_h.symm
        refine ⟨e.symm z, ⟨⟨z, ⟨hz_ball, hz_tgt⟩, rfl⟩, ?_⟩, e.right_inv hz_tgt⟩
        rw [(hFib_iff z hz_ball hzne), ← (hGc_iff z hz_ball hzne)]; exact hz_h
      · rintro ⟨y, ⟨⟨z', ⟨hz'_ball, hz'_tgt⟩, hz'y⟩, hFy⟩, hyz⟩
        have hz'_eq : e (e.symm z') = z' := e.right_inv hz'_tgt
        subst hyz; subst hz'y; rw [hz'_eq]
        have hzne : z' ≠ e x := by
          rintro rfl
          rw [e.left_inv (mem_chart_source ℂ x)] at hFy
          rw [hFx] at hFy; exact (OnePoint.coe_ne_infty c') hFy.symm
        exact ⟨hz'_ball, (hGc_iff z' hz'_ball hzne).mpr ((hFib_iff z' hz'_ball hzne).mp hFy)⟩
    have hInj : Set.InjOn e S' := by
      intro a ha b hb hab
      obtain ⟨za, hza, rfl⟩ := ha.1
      obtain ⟨zb, hzb, rfl⟩ := hb.1
      rw [e.right_inv hza.2, e.right_inv hzb.2] at hab; rw [hab]
    have hcount' := hcount c'⁻¹ hw'_ball hw'_ne
    rw [hset, finsum_mem_image hInj] at hcount'
    rw [← hcount']
    apply finsum_mem_congr rfl
    intro y hy
    obtain ⟨za, hza, rfl⟩ := hy.1
    -- Match the summand `localDeg f (coe c') (e.symm za) = (meromorphicOrderAt (h − c'⁻¹) za).untop₀`.
    have hy_src : e.symm za ∈ e.source := e.map_target hza.2
    have hza_tgt : za ∈ e.target := hza.2
    have hza_ball : za ∈ ball (e x) ε := hza.1
    have hFy := hy.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hFy
    have hzne : za ≠ e x := by
      rintro rfl
      rw [e.left_inv (mem_chart_source ℂ x)] at hFy
      rw [hFx] at hFy; exact (OnePoint.coe_ne_infty c') hFy.symm
    have hGza : G za = c' := (hFib_iff za hza_ball hzne).mp hFy
    -- `h = (G ·)⁻¹` on a full neighbourhood of `za` (interior, off the centre); `G` analytic at `za`.
    have heq_nhds : (fun ζ => (G ζ)⁻¹) =ᶠ[𝓝 za] h := by
      have hopen : IsOpen (ball (e x) ε \ {e x}) := isOpen_ball.sdiff isClosed_singleton
      have hza_mem : za ∈ ball (e x) ε \ {e x} := ⟨hza_ball, by simp [hzne]⟩
      filter_upwards [hopen.mem_nhds hza_mem] with ζ hζ
      exact (hε_recip ζ hζ.1 (by simpa using hζ.2)).symm
    have hnp_za : 0 ≤ f.orderAtPoint (e.symm za) := le_of_eq (hε_np za hza_ball hzne).symm
    have hGana : AnalyticAt ℂ G za := analyticAt_holoRepr_chartPullback_target f x hza_tgt hnp_za
    -- The order computation: `localDeg = order(toFun − c') = order(holoRepr − c') = order(h − c'⁻¹)`.
    rw [localDeg_coe_eq_chartPullback_order f c' e (chart_mem_atlas ℂ x) hy_src,
      e.right_inv hza.2, ← meromorphicOrderAt_holoRepr_sub_eq f x c' hza_tgt]
    congr 1
    -- `meromorphicOrderAt (h − c'⁻¹) za = meromorphicOrderAt (holoRepr(e.symm·) − c') za`.
    have hstep : meromorphicOrderAt (fun ζ => h ζ - c'⁻¹) za
        = meromorphicOrderAt (fun ζ => (G ζ)⁻¹ - c'⁻¹) za := by
      apply meromorphicOrderAt_congr
      filter_upwards [mem_nhdsWithin_of_mem_nhds heq_nhds] with ζ hζ; rw [hζ]
    rw [hstep, meromorphicOrderAt_inv_sub_eq G hc'_ne hGza hGana]

/-- **Assembling `LocalMultiplicitySheets` from the per-sheet data.**  Given the finite fibre `xs`,
pairwise-disjoint separating neighbourhoods `V0 ⊇ V`, and a per-point `SheetDatum` at each fibre
point (in its sheet `V x`), this packages the full local conservation structure.  The total
per-point fields are read off as `⋃ (h : x ∈ xs), (D x h).U` (= the datum on the fibre, `∅` off it),
and disjointness descends from `U ⊆ V ⊆ V0` with `V0` pairwise disjoint. -/
def ofSheetData (f : MeromorphicFunction X) (w₀ : RiemannSphere) (xs : Finset X)
    (hxs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {w₀})
    (V0 : X → Set X) (hV0disj : (f.toRiemannSphere ⁻¹' {w₀}).PairwiseDisjoint V0)
    (V : X → Set X) (hV_sub : ∀ x, V x ⊆ V0 x)
    (hfin : ∀ w : RiemannSphere, (f.toRiemannSphere ⁻¹' {w}).Finite)
    (hdatum : ∀ x ∈ xs, Nonempty (SheetDatum f w₀ x (V x))) :
    LocalMultiplicitySheets f w₀ := by
  classical
  have D : ∀ x, x ∈ xs → SheetDatum f w₀ x (V x) := fun x hx => (hdatum x hx).some
  -- The total per-point fields collapse to the chosen datum by proof irrelevance on `x ∈ xs`.
  have hUif : ∀ x (hx : x ∈ xs), (⋃ (h : x ∈ xs), (D x h).U) = (D x hx).U := by
    intro x hx; ext z; simp only [Set.mem_iUnion]
    exact ⟨fun ⟨h, hz⟩ => by rwa [Subsingleton.elim h hx] at hz, fun hz => ⟨hx, hz⟩⟩
  have hWif : ∀ x (hx : x ∈ xs), (⋃ (h : x ∈ xs), (D x h).W) = (D x hx).W := by
    intro x hx; ext z; simp only [Set.mem_iUnion]
    exact ⟨fun ⟨h, hz⟩ => by rwa [Subsingleton.elim h hx] at hz, fun hz => ⟨hx, hz⟩⟩
  refine {
    xs := xs
    xs_coe := hxs_coe
    U := fun x => ⋃ (h : x ∈ xs), (D x h).U
    U_open := fun x hx => by rw [hUif x hx]; exact (D x hx).U_open
    mem_U_self := fun x hx => by rw [hUif x hx]; exact (D x hx).mem_U_self
    U_pairwiseDisjoint := ?_
    m := fun x => if h : x ∈ xs then (D x h).m else 0
    Wsheet := fun x => ⋃ (h : x ∈ xs), (D x h).W
    Wsheet_open := fun x hx => by rw [hWif x hx]; exact (D x hx).W_open
    w₀_mem_Wsheet := fun x hx => by rw [hWif x hx]; exact (D x hx).w₀_mem_W
    sheetMult_eq := ?_
    Wfin := Set.univ, Wfin_open := isOpen_univ, w₀_mem_Wfin := Set.mem_univ _
    fibre_finite_Wfin := fun w _ => hfin w }
  · intro x hx x' hx' hne
    rw [hUif x hx, hUif x' hx']
    exact Set.disjoint_of_subset ((D x hx).U_subset.trans (hV_sub x))
      ((D x' hx').U_subset.trans (hV_sub x'))
      (hV0disj (hxs_coe ▸ Finset.mem_coe.mpr hx) (hxs_coe ▸ Finset.mem_coe.mpr hx') hne)
  · intro x hx w hw
    rw [hWif x hx] at hw
    rw [hUif x hx, dif_pos hx]
    exact (D x hx).sheetMult_eq w hw

/-- **The local conservation data at a value in the range** (`w₀ ∈ range F`), for a *non-constant*
`f` (`f.div ≠ 0`, ensuring finite fibres): the genuine §17.9 content, built per fibre point from the
planar normal form.  The finite fibre is enumerated by `xs`; pairwise-disjoint clean sheets are
chosen by T2 separation (`Set.Finite.t2_separation`) intersected with the chart source and the
non-pole locus, then the per-point datum (`exists_sheetDatum_coe` at a finite value,
`exists_sheetDatum_infty` at `∞`) supplies each sheet's conservation. -/
def localMultiplicitySheets_of_mem_range (f : MeromorphicFunction X) (hnc : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (hmem : w₀ ∈ Set.range f.toRiemannSphere) :
    LocalMultiplicitySheets f w₀ := by
  classical
  -- The non-pole locus is open (complement of the finite pole set, T1 ⟹ closed).
  have hnp_open : IsOpen {y : X | 0 ≤ f.orderAtPoint y} := by
    have : {y : X | 0 ≤ f.orderAtPoint y} = {y | f.orderAtPoint y < 0}ᶜ := by ext y; simp [not_lt]
    rw [this]; exact (f.finite_poles.isClosed).isOpen_compl
  -- Case on the value (the per-point datum and clean-sheet shape differ at `∞` vs a finite value).
  -- We case *first* so the data-valued construction never eliminates the `Exists` of T2 separation.
  cases w₀ with
  | none =>
    -- The pole fibre (`w₀ = ∞`): enumerate, separate, build sheets via the reciprocal normal form.
    have hfib_fin : (f.toRiemannSphere ⁻¹' {OnePoint.infty}).Finite :=
      fibre_finite_of_div_ne_zero f hnc OnePoint.infty
    set xs : Finset X := hfib_fin.toFinset with hxs_def
    have hxs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {OnePoint.infty} := hfib_fin.coe_toFinset
    set V0 : X → Set X := hfib_fin.t2_separation.choose with hV0_def
    have hV0 : ∀ x, x ∈ V0 x ∧ IsOpen (V0 x) := hfib_fin.t2_separation.choose_spec.1
    have hV0disj : (f.toRiemannSphere ⁻¹' {OnePoint.infty}).PairwiseDisjoint V0 :=
      hfib_fin.t2_separation.choose_spec.2
    have hfib_pole : ∀ x ∈ xs, f.orderAtPoint x < 0 := by
      intro x hx
      rw [hxs_def, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
      have hxin : x ∈ {y | f.orderAtPoint y < 0} := by
        rw [← f.toRiemannSphere_preimage_infty]; exact hx
      exact hxin
    refine ofSheetData f OnePoint.infty xs hxs_coe V0 hV0disj
      (fun x => V0 x ∩ (chartAt (H := ℂ) x).source) (fun x => Set.inter_subset_left)
      (fun w => fibre_finite_of_div_ne_zero f hnc w) (fun x hx => ?_)
    exact exists_sheetDatum_infty f hnc (hfib_pole x hx)
      ((hV0 x).2.inter (chartAt (H := ℂ) x).open_source) ⟨(hV0 x).1, mem_chart_source ℂ x⟩
      Set.inter_subset_right
  | some c =>
    -- A finite value `w₀ = coe c`: enumerate and separate the fibre, build sheets via the engine.
    have hfib_fin : (f.toRiemannSphere ⁻¹' {((c : ℂ) : RiemannSphere)}).Finite :=
      fibre_finite_of_div_ne_zero f hnc _
    set xs : Finset X := hfib_fin.toFinset with hxs_def
    have hxs_coe : (xs : Set X) = f.toRiemannSphere ⁻¹' {((c : ℂ) : RiemannSphere)} :=
      hfib_fin.coe_toFinset
    set V0 : X → Set X := hfib_fin.t2_separation.choose with hV0_def
    have hV0 : ∀ x, x ∈ V0 x ∧ IsOpen (V0 x) := hfib_fin.t2_separation.choose_spec.1
    have hV0disj : (f.toRiemannSphere ⁻¹' {((c : ℂ) : RiemannSphere)}).PairwiseDisjoint V0 :=
      hfib_fin.t2_separation.choose_spec.2
    have hfib_val : ∀ x ∈ xs, f.toRiemannSphere x = ((c : ℂ) : RiemannSphere) := by
      intro x hx; rw [hxs_def, Set.Finite.mem_toFinset] at hx; exact hx
    refine ofSheetData f ((c : ℂ) : RiemannSphere) xs hxs_coe V0 hV0disj
      (fun x => V0 x ∩ (chartAt (H := ℂ) x).source ∩ {y | 0 ≤ f.orderAtPoint y})
      (fun x => Set.inter_subset_left.trans Set.inter_subset_left)
      (fun w => fibre_finite_of_div_ne_zero f hnc w) (fun x hx => ?_)
    have hxV : x ∈ V0 x ∩ (chartAt (H := ℂ) x).source ∩ {y | 0 ≤ f.orderAtPoint y} := by
      refine ⟨⟨(hV0 x).1, mem_chart_source ℂ x⟩, ?_⟩
      show 0 ≤ f.orderAtPoint x
      by_contra h
      have := hfib_val x hx; rw [f.toRiemannSphere_of_pole (not_le.mp h)] at this
      exact (OnePoint.coe_ne_infty c) this.symm
    exact exists_sheetDatum_coe f hnc c (hfib_val x hx)
      (((hV0 x).2.inter (chartAt (H := ℂ) x).open_source).inter hnp_open) hxV
      Set.inter_subset_right

/-- **Pointwise local-conservation supply for non-constant `f`.** For every value `w₀ : ℂℙ¹` there
is a `LocalMultiplicitySheets f w₀`: the empty-fibre witness off the range, and the §17.9
construction on it. (Needs `f.div ≠ 0`: for a constant `f` the fibre over the constant value is all
of `X`, which is infinite, so no finite `xs` enumerates it — that case is handled separately by
`exists_properMapDegree_of_div_eq_zero`.) -/
def localMultiplicitySheets_of_nonconstant (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) (w₀ : RiemannSphere) :
    LocalMultiplicitySheets f w₀ := by
  by_cases hmem : w₀ ∈ Set.range f.toRiemannSphere
  · exact localMultiplicitySheets_of_mem_range f hnc hmem
  · exact LocalMultiplicitySheets.ofNotMemRange f hmem

/-- **`exists_properMapDegree`, PROVEN.** The proper-map-degree existential — `∃ d : ℕ` with
`zerosCount f = d = polesCount f`. For the trivial divisor (`f.div = 0`, the constant/germ-zero
case) both counts vanish (`exists_properMapDegree_of_div_eq_zero`); otherwise it is discharged from
the pointwise local-conservation supply via the proven connectedness globalization. This is the
exact shape of the upstream named input `Jacobians.exists_properMapDegree`; closing the residue
theorem `deg (div f) = 0`. -/
theorem exists_properMapDegree_proven (f : MeromorphicFunction X) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  by_cases h : (f.div : Divisor X) = 0
  · exact exists_properMapDegree_of_div_eq_zero f h
  · exact exists_properMapDegree_of_localSheets f (localMultiplicitySheets_of_nonconstant f h)

end Jacobians.ProperMapDegreeSheets

end
