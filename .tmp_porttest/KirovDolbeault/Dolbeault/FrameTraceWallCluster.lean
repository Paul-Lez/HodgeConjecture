/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FrameTraceWallEngine
import KirovDolbeault.Dolbeault.FrameTraceWallDescent
import KirovDolbeault.Dolbeault.ResidueAtom

/-!
# The cluster descent of the plain value trace (T lane)

The per-fibre-point **cluster lemma** for the `ω₀ = df` value trace and its per-centre
assembly — the `hmero`/`hres` fields of the residual wall `exists_frameTraceFunctionData_df`
at every finite centre, ramified clusters included:

* `cluster_descent` — at a fibre point `r` over the finite centre `c` of local degree `m`, the
  per-sheet slice sum of `F.holoRepr` descends through the §5 normal form
  (`exists_clusterSplit_at_fibrePoint`: `f̂ = c + ηᵐ`, local inverse `s`) and the unweighted
  symmetric descent (`meromorphicAt_plainSymSum_descent`) to a function `H` meromorphic at `c`
  with `Res_c H = frameRes data F r` — the residue identification chains the contour ↔ planar
  bridge, the PROVEN `residueChangeOfVariables` along `η`, and the branch normalization
  `planarCoeff_neg_one_branch` (`Res = m·a_{−m}`) against the descent's own
  `planarCoeff (−1) H c = m·a_{−m}(Q)`.
* `valueTrace_meromorphic_data` — the per-centre assembly over the patching engine: near any
  finite centre `c` the value trace germ-agrees with the finite sum of the cluster descents,
  hence is meromorphic at `c` with residue the full-fibre `frameRes` sum.

This covers unramified centres uniformly (`m = 1` is just a one-sheet cluster); the engine's
section route (`analyticAt_valueTrace_of_sections`) is still needed for the `hoff` field
(analyticity is stronger than meromorphy).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3 (steps 1–2, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §§4–5.
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FrameTraceWall

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatching
  Jacobians.MultiplicityPatchingConstruct Jacobians.MeromorphicTrace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The per-cluster descent -/

/-- **The cluster descent at a fibre point** (Miranda §VIII.3 step 1 + Lemma 3.2, one cluster).
At a fibre point `r` of the cover over the finite centre `c`, the per-sheet slice sum of the
plain value trace descends to a function `H` meromorphic at `c`, germ-equal to the slice sum
off the centre, with residue exactly the atom's frame residue `frameRes data F r` of the
`ω₀ = df` datum. -/
theorem cluster_descent (data : CanonicalForm17Data X) (F f : MeromorphicFunction X)
    (hω : data.ω₀ = differentialForm f) (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere))) {r : X} (hr : r ∈ P.xs) :
    ∃ H : ℂ → ℂ, MeromorphicAt H c ∧
      (∀ᶠ z in 𝓝[≠] c, (∑ y ∈ slice hdiv P r z, F.holoRepr y) = H z) ∧
      resAt H c = frameRes data F r := by
  classical
  -- the fibre point and its multiplicity
  have hfib : f.toRiemannSphere r = (((c : ℂ) : RiemannSphere)) := by
    have : r ∈ (P.xs : Set X) := hr
    rwa [P.xs_coe] at this
  have hnp := nonpole_of_fibre_coe hfib
  obtain ⟨hm1, _, hld⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv hfib hnp
  set m : ℕ := (localDeg f (((c : ℂ) : RiemannSphere)) r).toNat with hm_def
  have hm0 : m ≠ 0 := by omega
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  set ζ : ℂ := Complex.exp (2 * π * Complex.I / m) with hζ_def
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  -- the §5 normal form `f̂ = c + ηᵐ` with local inverse `s`
  obtain ⟨η, s, hη_an, hη0, hη', hNF, hs_an, hs0, hs', hηs, _⟩ :=
    exists_clusterSplit_at_fibrePoint f hdiv hfib hnp hζ
  set pre : ℂ := (chartAt (H := ℂ) r) r with hpre_def
  have hpre_tgt : pre ∈ (chartAt (H := ℂ) r).target :=
    (chartAt (H := ℂ) r).map_source (mem_chart_source ℂ r)
  -- the straightened value read `Q = F.holoRepr ∘ chart⁻¹ ∘ s`, meromorphic at `0`
  have hFh_mero : MeromorphicAt (F.holoRepr ∘ (chartAt (H := ℂ) r).symm) pre :=
    (F.meromorphic r).congr (holoRepr_pullback_eventuallyEq_toFun F r hpre_tgt).symm
  set Q : ℂ → ℂ := fun a => F.holoRepr ((chartAt (H := ℂ) r).symm (s a)) with hQ_def
  have hQ_mero : MeromorphicAt Q 0 := by
    have h0 : MeromorphicAt (F.holoRepr ∘ (chartAt (H := ℂ) r).symm) (s 0) := by
      rw [hs0]; exact hFh_mero
    exact h0.comp_analyticAt hs_an
  -- the descent
  obtain ⟨H, hH_mero, hH_eq, hH_res⟩ := meromorphicAt_plainSymSum_descent c hQ_mero hmpos hζ
  refine ⟨H, hH_mero, ?_, ?_⟩
  · -- THE GERM IDENTITY ------------------------------------------------------
    -- gather the per-`u` eventual facts
    have hζj_ne : ∀ j : ℕ, (ζ : ℂ) ^ j ≠ 0 := fun j =>
      pow_ne_zero j (hζ.ne_zero hm0)
    -- (b) η inverts `s` along each rotated ray
    have hb : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ), η (s (ζ ^ j * u)) = ζ ^ j * u := by
      intro j _
      have hcont : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
      exact hcont.eventually hηs
    -- the moving sheet point map and its continuity at `0`
    set yy : ℕ → ℂ → X := fun j u => (chartAt (H := ℂ) r).symm (s (ζ ^ j * u)) with hyy_def
    have hy_cont : ∀ j, ContinuousAt (yy j) 0 := by
      intro j
      have h1 : Tendsto (fun u : ℂ => s (ζ ^ j * u)) (𝓝 0) (𝓝 pre) := by
        have hmul : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
        have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
          have := hs_an.continuousAt.tendsto
          rwa [hs0] at this
        exact hs_t.comp hmul
      have h2 : Tendsto (chartAt (H := ℂ) r).symm (𝓝 pre)
          (𝓝 ((chartAt (H := ℂ) r).symm pre)) :=
        ((chartAt (H := ℂ) r).continuousAt_symm hpre_tgt).tendsto
      have hcomp := h2.comp h1
      have hval : (chartAt (H := ℂ) r).symm pre = yy j 0 := by
        show _ = (chartAt (H := ℂ) r).symm (s (ζ ^ j * 0))
        rw [show s (ζ ^ j * 0) = pre by simpa using hs0]
      rw [hval] at hcomp
      exact hcomp
    have hy0 : ∀ j, yy j 0 = r := by
      intro j
      show (chartAt (H := ℂ) r).symm (s (ζ ^ j * 0)) = r
      have : s (ζ ^ j * 0) = pre := by simpa using hs0
      rw [this, hpre_def, (chartAt (H := ℂ) r).left_inv (mem_chart_source ℂ r)]
    -- (c) the normal form along each sheet
    have hc : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ),
        f.holoRepr ((chartAt (H := ℂ) r).symm (s (ζ ^ j * u)))
          = c + η (s (ζ ^ j * u)) ^ m := by
      intro j _
      have hcont : Tendsto (fun u : ℂ => s (ζ ^ j * u)) (𝓝 0) (𝓝 pre) := by
        have hmul : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
        have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
          have := hs_an.continuousAt.tendsto
          rwa [hs0] at this
        exact hs_t.comp hmul
      exact hcont.eventually hNF
    -- (d) the moving point is in the sheet and a non-pole
    have hdU : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ),
        yy j u ∈ P.U r ∧ 0 ≤ f.orderAtPoint (yy j u) := by
      intro j _
      have hU : ∀ᶠ u in 𝓝 (0 : ℂ), yy j u ∈ P.U r := by
        have : P.U r ∈ 𝓝 (yy j 0) := by
          rw [hy0 j]
          exact (P.U_open r hr).mem_nhds (P.mem_U_self r hr)
        exact hy_cont j this
      have hnpu : ∀ᶠ u in 𝓝 (0 : ℂ), 0 ≤ f.orderAtPoint (yy j u) := by
        have : {y : X | 0 ≤ f.orderAtPoint y} ∈ 𝓝 (yy j 0) := by
          rw [hy0 j]
          exact (isOpen_nonpole f).mem_nhds hnp
        exact hy_cont j this
      filter_upwards [hU, hnpu] with u h1 h2
      exact ⟨h1, h2⟩
    -- (e) the `s` values stay in the chart target (for injectivity of `chart⁻¹`)
    have he : ∀ j ∈ Finset.range m, ∀ᶠ u in 𝓝 (0 : ℂ),
        s (ζ ^ j * u) ∈ (chartAt (H := ℂ) r).target := by
      intro j _
      have hcont : Tendsto (fun u : ℂ => s (ζ ^ j * u)) (𝓝 0) (𝓝 pre) := by
        have hmul : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_const.mul continuous_id).tendsto (0 : ℂ)
        have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
          have := hs_an.continuousAt.tendsto
          rwa [hs0] at this
        exact hs_t.comp hmul
      exact hcont.eventually ((chartAt (H := ℂ) r).open_target.mem_nhds hpre_tgt)
    -- the combined eventual fact on the punctured `u`-disc
    have hall : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ((∑ j ∈ Finset.range m, Q (ζ ^ j * u)) = H (c + u ^ m)) ∧
        (∀ j ∈ Finset.range m, η (s (ζ ^ j * u)) = ζ ^ j * u) ∧
        (∀ j ∈ Finset.range m,
          f.holoRepr ((chartAt (H := ℂ) r).symm (s (ζ ^ j * u))) = c + η (s (ζ ^ j * u)) ^ m) ∧
        (∀ j ∈ Finset.range m, yy j u ∈ P.U r ∧ 0 ≤ f.orderAtPoint (yy j u)) ∧
        (∀ j ∈ Finset.range m, s (ζ ^ j * u) ∈ (chartAt (H := ℂ) r).target) := by
      have h1 := hH_eq
      have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m, η (s (ζ ^ j * u)) = ζ ^ j * u :=
        (eventually_all_finset _).mpr hb
      have h3 : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m,
          f.holoRepr ((chartAt (H := ℂ) r).symm (s (ζ ^ j * u)))
            = c + η (s (ζ ^ j * u)) ^ m :=
        (eventually_all_finset _).mpr hc
      have h4 : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m,
          yy j u ∈ P.U r ∧ 0 ≤ f.orderAtPoint (yy j u) :=
        (eventually_all_finset _).mpr hdU
      have h5 : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m,
          s (ζ ^ j * u) ∈ (chartAt (H := ℂ) r).target :=
        (eventually_all_finset _).mpr he
      filter_upwards [h1, h2.filter_mono nhdsWithin_le_nhds,
        h3.filter_mono nhdsWithin_le_nhds, h4.filter_mono nhdsWithin_le_nhds,
        h5.filter_mono nhdsWithin_le_nhds] with u u1 u2 u3 u4 u5
      exact ⟨u1, u2, u3, u4, u5⟩
    -- extract a punctured-disc radius
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hall
    obtain ⟨δ, hδ0, hδ⟩ := hall
    -- the conclusion, on the punctured disc of radius `δ^m` inside the patching neighbourhood
    have hWev : ∀ᶠ z in 𝓝 c, (((z : ℂ) : RiemannSphere)) ∈ P.W :=
      (OnePoint.continuous_coe.continuousAt) (P.W_open.mem_nhds P.w₀_mem_W)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c (pow_pos hδ0 m)),
      mem_nhdsWithin_of_mem_nhds hWev, self_mem_nhdsWithin] with z hzball hWz hzc'
    have hzc : z ≠ c := hzc'
    have hzd : dist z c < δ ^ m := Metric.mem_ball.mp hzball
    -- pick an `m`-th root `u` of `z − c`
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (z - c) hmpos
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow hm0] at hu
      exact hzc (sub_eq_zero.mp hu.symm)
    have hud : dist u 0 < δ := by
      rw [dist_zero_right]
      have h1 : ‖u‖ ^ m < δ ^ m := by
        rw [← norm_pow, hu]
        simpa [dist_eq_norm] using hzd
      exact lt_of_pow_lt_pow_left₀ m hδ0.le h1
    have hΨ := hδ hud (Set.mem_compl_singleton_iff.mpr hu0)
    obtain ⟨hΨ1, hΨ2, hΨ3, hΨ4, hΨ5⟩ := hΨ
    -- the `m` distinct sheet points exhaust the slice
    have hyfib : ∀ j ∈ Finset.range m,
        f.toRiemannSphere (yy j u) = ((z : ℂ) : RiemannSphere) := by
      intro j hj
      have hval : f.holoRepr (yy j u) = z := by
        show f.holoRepr ((chartAt (H := ℂ) r).symm (s (ζ ^ j * u))) = z
        rw [hΨ3 j hj, hΨ2 j hj, mul_pow, ← pow_mul, mul_comm j m, pow_mul,
          hζ.pow_eq_one, one_pow, one_mul, hu]
        ring
      rw [f.toRiemannSphere_of_nonneg (hΨ4 j hj).2, hval]
    have hy_inj : Set.InjOn (fun j => yy j u) (Finset.range m : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have hi' : i ∈ Finset.range m := Finset.mem_range.mpr hi
      have hj' : j ∈ Finset.range m := Finset.mem_range.mpr hj
      -- undo the chart, then `η`, then the primitive-root powers
      have hs_eq : s (ζ ^ i * u) = s (ζ ^ j * u) := by
        have h1 := congrArg (chartAt (H := ℂ) r) hij
        have h2 : (chartAt (H := ℂ) r) ((chartAt (H := ℂ) r).symm (s (ζ ^ i * u)))
            = s (ζ ^ i * u) := (chartAt (H := ℂ) r).right_inv (hΨ5 i hi')
        have h3 : (chartAt (H := ℂ) r) ((chartAt (H := ℂ) r).symm (s (ζ ^ j * u)))
            = s (ζ ^ j * u) := (chartAt (H := ℂ) r).right_inv (hΨ5 j hj')
        rwa [h2, h3] at h1
      have hζu : ζ ^ i * u = ζ ^ j * u := by
        rw [← hΨ2 i hi', ← hΨ2 j hj', hs_eq]
      have hζij : (ζ : ℂ) ^ i = ζ ^ j := mul_right_cancel₀ hu0 hζu
      exact hζ.pow_inj hi hj hζij
    set cand : Finset X := (Finset.range m).image (fun j => yy j u) with hcand_def
    have hcand_card : cand.card = m := by
      rw [hcand_def, Finset.card_image_of_injOn hy_inj, Finset.card_range]
    have hcand_sub : cand ⊆ slice hdiv P r z := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact mem_slice.mpr ⟨hyfib j hj, (hΨ4 j hj).1⟩
    have hmP : P.m r = (m : ℤ) := by
      rw [patch_m_eq_localDeg hdiv P hr, hld]
    have hslice : slice hdiv P r z = cand :=
      slice_eq_of_exhibited hdiv P hr hWz cand hcand_sub (by rw [hmP, hcand_card])
    -- assemble
    rw [hslice, hcand_def, Finset.sum_image (fun i hi j hj h => hy_inj hi hj h)]
    have hsum : ∑ j ∈ Finset.range m, F.holoRepr (yy j u)
        = ∑ j ∈ Finset.range m, Q (ζ ^ j * u) := rfl
    rw [hsum, hΨ1, hu]
    show H (c + (z - c)) = H z
    congr 1
    ring
  · -- THE RESIDUE IDENTIFICATION ---------------------------------------------
    -- the straightened branch integrand `A(u) = Q(u)·m·u^{m−1}`
    set A : ℂ → ℂ := fun a => Q a * ((m : ℂ) * (a - 0) ^ ((m : ℤ) - 1)) with hA_def
    have hA_mero : MeromorphicAt A 0 :=
      hQ_mero.mul ((MeromorphicAt.const _ 0).mul (meromorphicAt_zpow_self 0 ((m : ℤ) - 1)))
    -- the local left inverse of `η` certifies `s ∘ η = id` near `pre`
    have hsd : HasStrictDerivAt η (deriv η pre) pre := hη_an.hasStrictDerivAt
    have hlinv : ∀ᶠ ζ' in 𝓝 pre, hsd.localInverse η (deriv η pre) pre hη' (η ζ') = ζ' :=
      hsd.eventually_left_inverse hη'
    obtain ⟨V, hV_mem, hV⟩ := Filter.eventually_iff_exists_mem.mp hlinv
    have hsη : ∀ᶠ ζ' in 𝓝 pre, s (η ζ') = ζ' := by
      -- `η (s (η ζ')) = η ζ'` (right inverse along `η ζ' → 0`), then apply the left inverse
      have h1 : ∀ᶠ ζ' in 𝓝 pre, η (s (η ζ')) = η ζ' := by
        have hηt : Tendsto η (𝓝 pre) (𝓝 0) := by
          have := hη_an.continuousAt.tendsto
          rwa [hη0] at this
        exact hηt.eventually hηs
      have h2 : ∀ᶠ ζ' in 𝓝 pre, s (η ζ') ∈ V := by
        have hst : Tendsto (fun ζ' => s (η ζ')) (𝓝 pre) (𝓝 pre) := by
          have hηt : Tendsto η (𝓝 pre) (𝓝 0) := by
            have := hη_an.continuousAt.tendsto
            rwa [hη0] at this
          have hs_t : Tendsto s (𝓝 0) (𝓝 pre) := by
            have := hs_an.continuousAt.tendsto
            rwa [hs0] at this
          exact hs_t.comp hηt
        exact hst.eventually hV_mem
      filter_upwards [h1, h2, hlinv] with ζ' h1' h2' h3'
      have ha := hV _ h2'
      rw [h1'] at ha
      rw [← ha]
      exact h3'
    -- the integrand chain: `(F·df)`-read = `A(η ζ')·η'(ζ')` off the centre
    have hev : (fun ζ' => F.toFun ((chartAt (H := ℂ) r).symm ζ')
          * deriv (f.toFun ∘ (chartAt (H := ℂ) r).symm) ζ')
        =ᶠ[𝓝[≠] pre] (fun ζ' => A (η ζ') * deriv η ζ') := by
      -- (R1) junk-free `F` read
      have hR1 : (fun ζ' => F.toFun ((chartAt (H := ℂ) r).symm ζ'))
          =ᶠ[𝓝[≠] pre] (fun ζ' => F.holoRepr ((chartAt (H := ℂ) r).symm ζ')) :=
        (holoRepr_pullback_eventuallyEq_toFun F r hpre_tgt).symm
      -- (R2) junk-free `f`-derivative read
      have hR2 : deriv (f.toFun ∘ (chartAt (H := ℂ) r).symm)
          =ᶠ[𝓝[≠] pre] deriv (f.holoRepr ∘ (chartAt (H := ℂ) r).symm) :=
        Jacobians.Dolbeault.deriv_eventuallyEq_punctured
          (holoRepr_pullback_eventuallyEq_toFun f r hpre_tgt).symm
      -- (R3) the normal-form derivative
      have hR3 : deriv (f.holoRepr ∘ (chartAt (H := ℂ) r).symm)
          =ᶠ[𝓝 pre] (fun ζ' => (m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ') := by
        have hNF' : (f.holoRepr ∘ (chartAt (H := ℂ) r).symm)
            =ᶠ[𝓝 pre] (fun w => c + η w ^ m) := hNF
        have hd := hNF'.deriv
        have hcalc : ∀ᶠ ζ' in 𝓝 pre,
            deriv (fun w => c + η w ^ m) ζ' = (m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ' := by
          filter_upwards [hη_an.eventually_analyticAt] with ζ' hζ'an
          have hpow : HasDerivAt (fun w => c + η w ^ m)
              ((m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ') ζ' := by
            have h := (hζ'an.differentiableAt.hasDerivAt.pow m).const_add c
            simpa using h
          exact hpow.deriv
        filter_upwards [hd, hcalc] with ζ' h1 h2
        rw [h1, h2]
      -- (R4) `F.holoRepr` read through the straightening
      have hR4 : (fun ζ' => F.holoRepr ((chartAt (H := ℂ) r).symm ζ'))
          =ᶠ[𝓝 pre] (fun ζ' => Q (η ζ')) := by
        filter_upwards [hsη] with ζ' h
        show F.holoRepr ((chartAt (H := ℂ) r).symm ζ')
          = F.holoRepr ((chartAt (H := ℂ) r).symm (s (η ζ')))
        rw [h]
      filter_upwards [hR1, hR2, hR3.filter_mono nhdsWithin_le_nhds,
        hR4.filter_mono nhdsWithin_le_nhds] with ζ' h1 h2 h3 h4
      show F.toFun ((chartAt (H := ℂ) r).symm ζ')
          * deriv (f.toFun ∘ (chartAt (H := ℂ) r).symm) ζ' = A (η ζ') * deriv η ζ'
      rw [show F.toFun ((chartAt (H := ℂ) r).symm ζ')
          = F.holoRepr ((chartAt (H := ℂ) r).symm ζ') from h1, h2, h3, h4]
      show Q (η ζ') * ((m : ℂ) * η ζ' ^ (m - 1) * deriv η ζ')
          = Q (η ζ') * ((m : ℂ) * (η ζ' - 0) ^ ((m : ℤ) - 1)) * deriv η ζ'
      have hzp : (η ζ' - 0) ^ ((m : ℤ) - 1) = η ζ' ^ (m - 1) := by
        rw [sub_zero, show ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      rw [hzp]
      ring
    -- chain the bridges
    have hint_mero : MeromorphicAt
        (fun ζ' => F.toFun ((chartAt (H := ℂ) r).symm ζ')
          * deriv (f.toFun ∘ (chartAt (H := ℂ) r).symm) ζ') pre :=
      (F.meromorphic r).mul (f.meromorphic r).deriv
    have hAη_mero : MeromorphicAt (fun ζ' => A (η ζ') * deriv η ζ') pre := by
      have h1 : MeromorphicAt (A ∘ η) pre := by
        have hA0 : MeromorphicAt A (η pre) := by rw [hη0]; exact hA_mero
        exact hA0.comp_analyticAt hη_an
      exact h1.mul hη_an.deriv.meromorphicAt
    have hCoV : resAt (fun ζ' => A (η ζ') * deriv η ζ') pre = resAt A (η pre) :=
      Jacobians.MeromorphicTrace.residueChangeOfVariables η A pre hη_an hη'
        (by rw [hη0]; exact hA_mero)
    have hbranch : planarCoeff (-1) A 0 = (m : ℂ) * planarCoeff (-(m : ℤ)) Q 0 :=
      planarCoeff_neg_one_branch hQ_mero m
    -- assemble: `Res_c H = m·a₋ₘ(Q) = Res(A at 0) = Res(integrand) = frameRes`
    rw [resAt_eq_planarCoeff_neg_one hH_mero, hH_res]
    rw [frameRes_df_read data f F hω r]
    rw [planarCoeff_congr hev (-1)]
    rw [← resAt_eq_planarCoeff_neg_one hAη_mero, hCoV, hη0,
      resAt_eq_planarCoeff_neg_one hA_mero, hbranch]

/-! ## The per-centre assembly -/

/-- **The per-centre meromorphy + residue data of the value trace** (Miranda §VIII.3 step 1 +
Lemma 3.2 at one finite centre, full fibre).  Near any finite centre `c`, the value trace
germ-agrees with the finite sum of the per-cluster descents; hence it is meromorphic at `c`
with residue the full-fibre `frameRes` sum. -/
theorem valueTrace_meromorphicAt_and_resAt (data : CanonicalForm17Data X)
    (F f : MeromorphicFunction X) (hω : data.ω₀ = differentialForm f)
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ) :
    MeromorphicAt (valueTrace F f) c ∧
      resAt (valueTrace F f) c
        = ∑ y ∈ fibreFinset f hdiv (((c : ℂ) : RiemannSphere)), frameRes data F y := by
  classical
  set P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere)) :=
    patchAt f hdiv (((c : ℂ) : RiemannSphere)) with hP_def
  -- choose the per-cluster descents
  have hex : ∀ r ∈ P.xs, ∃ H : ℂ → ℂ, MeromorphicAt H c ∧
      (∀ᶠ z in 𝓝[≠] c, (∑ y ∈ slice hdiv P r z, F.holoRepr y) = H z) ∧
      resAt H c = frameRes data F r :=
    fun r hr => cluster_descent data F f hω hdiv P hr
  choose! Hf hH_mero hH_germ hH_res using hex
  -- the fibre `Finset` at the centre is the patching enumeration
  have hfibP : fibreFinset f hdiv (((c : ℂ) : RiemannSphere)) = P.xs := by
    apply Finset.coe_injective
    rw [coe_fibreFinset, P.xs_coe]
  -- the trace germ-agrees with the cluster sum
  have hgerm : valueTrace F f =ᶠ[𝓝[≠] c] fun z => ∑ r ∈ P.xs, Hf r z := by
    have hW : ∀ᶠ z in 𝓝[≠] c, (((z : ℂ) : RiemannSphere)) ∈ P.W := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      exact (OnePoint.continuous_coe.continuousAt) (P.W_open.mem_nhds P.w₀_mem_W)
    have hclusters : ∀ᶠ z in 𝓝[≠] c, ∀ r ∈ P.xs,
        (∑ y ∈ slice hdiv P r z, F.holoRepr y) = Hf r z :=
      (eventually_all_finset _).mpr (fun r hr => hH_germ r hr)
    filter_upwards [hW, hclusters] with z hzW hzc
    rw [valueTrace_eq_sum_slices F f hdiv P hzW]
    exact Finset.sum_congr rfl hzc
  have hsum_mero : MeromorphicAt (fun z => ∑ r ∈ P.xs, Hf r z) c :=
    MeromorphicAt.fun_sum (fun r hr => hH_mero r hr)
  constructor
  · exact hsum_mero.congr hgerm.symm
  · rw [resAt_congr hgerm,
      Jacobians.TraceResidue.LaurentForm.resAt_finsum P.xs Hf (fun r hr => hH_mero r hr), hfibP]
    exact Finset.sum_congr rfl fun r hr => hH_res r hr

end Jacobians.Dolbeault.FrameTraceWall

end
