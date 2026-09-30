/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Geometry.Manifold.ChartDifferential
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Maps.Basic

/-!
# A uniform reach estimate for a compact immersed submanifold

Let `e : M → E` be a smooth immersion of a manifold into a real inner product space. The two
results of this file are the two ingredients of the nearest-point construction of a tubular
neighbourhood.

* `inner_mfderiv_eq_zero_of_isMinOn`: if `q` minimizes `q' ↦ ‖x - e q'‖`, then `x - e q` is
  orthogonal to the image of the differential of `e` at `q` (the first-order condition).
* `exists_global_normal_estimate`: if `M` is compact and `e` is a closed embedding, there is a
  constant `C > 0` such that for all `q q' : M` and every `n : E` orthogonal to the image of the
  differential of `e` at `q`,
  `|⟪e q' - e q, n⟫| ≤ C * ‖e q' - e q‖ ^ 2 * ‖n‖`.
  This is a quantitative form of "the submanifold has positive reach": `1 / (2 * C)` is a lower
  bound for its reach.

Together these give uniqueness of nearest points at distance less than `1 / (2 * C)`, which is
what `Other.Geometry.Manifold.TubularNeighbourhood` uses.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Set Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **First-order condition.** If `q` minimizes the distance from `x` to the image of `e`, then
`x - e q` is orthogonal to the image of the differential of `e` at `q`. -/
theorem inner_mfderiv_eq_zero_of_isMinOn {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e) {x : E}
    {q : M} (hq : ∀ q' : M, ‖x - e q‖ ≤ ‖x - e q'‖) (v : F) :
    ⟪mfderivNormed I e q v, x - e q⟫ = 0 := by
  set φ := extChartAt I q with hφdef
  have hT : IsOpen φ.target := isOpen_extChartAt_target (I := I) q
  have hy₀T : φ q ∈ φ.target := mem_extChartAt_target (I := I) q
  set G : F → E := e ∘ φ.symm with hGdef
  have hGd : ContDiffOn ℝ ∞ G φ.target := contDiffOn_comp_extChartAt_symm he q
  have hsymm : φ.symm (φ q) = q := φ.left_inv (mem_extChartAt_source (I := I) q)
  have hGy₀ : G (φ q) = e q := by simp [hGdef, hsymm]
  have hGdiff : HasFDerivAt G (fderiv ℝ G (φ q)) (φ q) :=
    ((hGd.contDiffAt (hT.mem_nhds hy₀T)).differentiableAt (by simp)).hasFDerivAt
  -- the squared distance to `x`, read in the chart, has a global minimum at `φ q`
  have hmin : IsLocalMin (fun z : F => ‖x - G z‖ ^ 2) (φ q) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have h := hq (φ.symm z)
    have : ‖x - G (φ q)‖ ≤ ‖x - G z‖ := by rw [hGy₀]; exact h
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hderiv := (hGdiff.const_sub x).norm_sq
  have hzero := hmin.hasFDerivAt_eq_zero hderiv
  have hkey : ∀ u : F, ⟪x - e q, (fderiv ℝ G (φ q)) u⟫ = 0 := by
    intro u
    have h := DFunLike.congr_fun hzero u
    simp only [hGy₀] at h
    simp only [smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
      map_neg, zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
    rw [innerSL_apply_apply] at h
    linarith
  obtain ⟨u, hu⟩ := exists_preimage_fderiv_comp_extChartAt_symm he q hy₀T v
  rw [hsymm] at hu
  rw [← hu, real_inner_comm]
  exact hkey u

/-- **Local reach estimate.** Near a point `p` at which the differential of `e` is injective,
the inner product of a displacement `e q' - e q` with a vector `n` normal to the submanifold at
`q` is quadratically small in `‖e q' - e q‖`. -/
theorem exists_local_normal_estimate [FiniteDimensional ℝ F] {e : M → E}
    (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (p : M)
    (hde : Function.Injective (mfderivNormed I e p)) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ C : ℝ, 0 < C ∧
      ∀ q ∈ U, ∀ q' ∈ U, ∀ n : E, (∀ v : F, ⟪mfderivNormed I e q v, n⟫ = 0) →
        |⟪e q' - e q, n⟫| ≤ C * ‖e q' - e q‖ ^ 2 * ‖n‖ := by
  classical
  set φ := extChartAt I p with hφdef
  have hT : IsOpen φ.target := isOpen_extChartAt_target (I := I) p
  set y₀ := φ p with hy₀def
  have hy₀T : y₀ ∈ φ.target := mem_extChartAt_target (I := I) p
  set G : F → E := e ∘ φ.symm with hGdef
  have hGd : ContDiffOn ℝ ∞ G φ.target := contDiffOn_comp_extChartAt_symm he p
  have hGdiff : ∀ y ∈ φ.target, HasFDerivAt G (fderiv ℝ G y) y := fun y hy =>
    ((hGd.contDiffAt (hT.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨L, t, ht, hLip⟩ :=
    ((hGd.fderiv_of_isOpen hT (by decide)).contDiffAt (hT.mem_nhds hy₀T)).exists_lipschitzOnWith
  obtain ⟨r₁, hr₁pos, hball₁⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem ht (hT.mem_nhds hy₀T))
  have hsymm : φ.symm y₀ = p := φ.left_inv (mem_extChartAt_source (I := I) p)
  have hinj : Function.Injective (fderiv ℝ G y₀) :=
    injective_fderiv_comp_extChartAt_symm he p hy₀T (by rw [hsymm]; exact hde)
  obtain ⟨K, hKpos, hanti⟩ :=
    (fderiv ℝ G y₀ : F →ₗ[ℝ] E).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
  set κ : ℝ := (K : ℝ) with hκdef
  set lam : ℝ := (L : ℝ) with hlamdef
  have hκpos : 0 < κ := hKpos
  have hlam : 0 ≤ lam := L.coe_nonneg
  have hlow : ∀ u : F, ‖u‖ ≤ κ * ‖fderiv ℝ G y₀ u‖ := by
    intro u
    have h := hanti.le_mul_dist u 0
    simpa [dist_eq_norm] using h
  set r : ℝ := min r₁ (1 / (6 * κ * (lam + 1))) with hrdef
  have hden : 0 < 6 * κ * (lam + 1) := by positivity
  have hrpos : 0 < r := lt_min hr₁pos (by positivity)
  have hrr : 3 * κ * lam * r ≤ 1 / 2 := by
    have h : r ≤ 1 / (6 * κ * (lam + 1)) := min_le_right _ _
    rw [le_div_iff₀ hden] at h
    nlinarith [hrpos.le, hκpos.le, hlam]
  have hballsub : Metric.ball y₀ r ⊆ t ∩ φ.target :=
    fun y hy => hball₁ (Metric.ball_subset_ball (min_le_left _ _) hy)
  have hnormball : ∀ y ∈ Metric.ball y₀ r, ‖y - y₀‖ < r := by
    intro y hy
    rwa [Metric.mem_ball, dist_eq_norm] at hy
  -- Lipschitz estimate for the derivative
  have hdlip : ∀ y ∈ Metric.ball y₀ r, ∀ z ∈ Metric.ball y₀ r,
      ‖fderiv ℝ G y - fderiv ℝ G z‖ ≤ lam * ‖y - z‖ := by
    intro y hy z hz
    have h := hLip.dist_le_mul y (hballsub hy).1 z (hballsub hz).1
    simpa [dist_eq_norm] using h
  -- second-order Taylor estimate
  have htaylor : ∀ y ∈ Metric.ball y₀ r, ∀ y' ∈ Metric.ball y₀ r,
      ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖ ≤ lam * ‖y' - y‖ * ‖y' - y‖ := by
    intro y hy y' hy'
    have hseg : segment ℝ y y' ⊆ Metric.ball y₀ r := (convex_ball y₀ r).segment_subset hy hy'
    have hnorm : ∀ z ∈ segment ℝ y y', ‖z - y‖ ≤ ‖y' - y‖ := by
      intro z hz
      rw [segment_eq_image'] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      nlinarith [norm_nonneg (y' - y), hθ.1, hθ.2]
    refine (convex_segment y y').norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f' := fun z => fderiv ℝ G z)
      (fun z hz => (hGdiff z (hballsub (hseg hz)).2).hasFDerivWithinAt)
      (fun z hz => ?_) (left_mem_segment ℝ y y') (right_mem_segment ℝ y y')
    calc ‖fderiv ℝ G z - fderiv ℝ G y‖ ≤ lam * ‖z - y‖ := hdlip z (hseg hz) y hy
      _ ≤ lam * ‖y' - y‖ := by gcongr; exact hnorm z hz
  -- lower bound: `G` is bi-Lipschitz from below on the ball
  have hlower : ∀ y ∈ Metric.ball y₀ r, ∀ y' ∈ Metric.ball y₀ r,
      ‖y' - y‖ ≤ 2 * κ * ‖G y' - G y‖ := by
    intro y hy y' hy'
    have ha : (0 : ℝ) ≤ ‖y' - y‖ := norm_nonneg _
    have hasmall : ‖y' - y‖ ≤ 2 * r := by
      have hrw : y' - y = (y' - y₀) - (y - y₀) := by abel
      have h1 := hnormball y' hy'
      have h2 := hnormball y hy
      have h3 := norm_sub_le (y' - y₀) (y - y₀)
      rw [← hrw] at h3
      linarith
    have h1 : ‖y' - y‖ ≤ κ * ‖(fderiv ℝ G y₀) (y' - y)‖ := hlow _
    have h2 : ‖(fderiv ℝ G y) (y' - y) - (fderiv ℝ G y₀) (y' - y)‖ ≤ lam * r * ‖y' - y‖ := by
      have hb : ‖fderiv ℝ G y - fderiv ℝ G y₀‖ ≤ lam * r := by
        refine (hdlip y hy y₀ (Metric.mem_ball_self hrpos)).trans ?_
        have := (hnormball y hy).le
        gcongr
      calc ‖(fderiv ℝ G y) (y' - y) - (fderiv ℝ G y₀) (y' - y)‖
          = ‖(fderiv ℝ G y - fderiv ℝ G y₀) (y' - y)‖ := by simp
        _ ≤ ‖fderiv ℝ G y - fderiv ℝ G y₀‖ * ‖y' - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ lam * r * ‖y' - y‖ := by gcongr
    have h3 : ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖ ≤ lam * (2 * r) * ‖y' - y‖ := by
      refine (htaylor y hy y' hy').trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hasmall (mul_nonneg hlam ha)]
    have h4 : ‖(fderiv ℝ G y₀) (y' - y)‖ ≤ ‖G y' - G y‖ + 3 * lam * r * ‖y' - y‖ := by
      have hrw : (fderiv ℝ G y₀) (y' - y)
          = (G y' - G y) + ((fderiv ℝ G y₀) (y' - y) - (fderiv ℝ G y) (y' - y))
            + ((fderiv ℝ G y) (y' - y) - (G y' - G y)) := by abel
      have e1 : ‖(fderiv ℝ G y₀) (y' - y) - (fderiv ℝ G y) (y' - y)‖ ≤ lam * r * ‖y' - y‖ := by
        rw [norm_sub_rev]; exact h2
      have e2 : ‖(fderiv ℝ G y) (y' - y) - (G y' - G y)‖ ≤ lam * (2 * r) * ‖y' - y‖ := by
        rw [norm_sub_rev]; exact h3
      calc ‖(fderiv ℝ G y₀) (y' - y)‖
          = ‖(G y' - G y) + ((fderiv ℝ G y₀) (y' - y) - (fderiv ℝ G y) (y' - y))
              + ((fderiv ℝ G y) (y' - y) - (G y' - G y))‖ := by rw [← hrw]
        _ ≤ ‖G y' - G y‖ + ‖(fderiv ℝ G y₀) (y' - y) - (fderiv ℝ G y) (y' - y)‖
              + ‖(fderiv ℝ G y) (y' - y) - (G y' - G y)‖ := norm_add₃_le
        _ ≤ ‖G y' - G y‖ + lam * r * ‖y' - y‖ + lam * (2 * r) * ‖y' - y‖ := by gcongr
        _ = ‖G y' - G y‖ + 3 * lam * r * ‖y' - y‖ := by ring
    have hstep : 3 * κ * lam * r * ‖y' - y‖ ≤ 1 / 2 * ‖y' - y‖ :=
      mul_le_mul_of_nonneg_right hrr ha
    have hcomb : κ * ‖(fderiv ℝ G y₀) (y' - y)‖
        ≤ κ * (‖G y' - G y‖ + 3 * lam * r * ‖y' - y‖) :=
      mul_le_mul_of_nonneg_left h4 hκpos.le
    nlinarith [h1, hcomb, hstep]
  -- assemble
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball y₀ r,
    (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) p) Metric.isOpen_ball,
    ⟨mem_extChartAt_source (I := I) p, by
      simp only [mem_preimage, ← hy₀def]; exact Metric.mem_ball_self hrpos⟩,
    4 * lam * κ ^ 2 + 1, by positivity, ?_⟩
  rintro q ⟨hqs, hqb⟩ q' ⟨hq's, hq'b⟩ n hn
  set y := φ q with hydef
  set y' := φ q' with hy'def
  have hyb : y ∈ Metric.ball y₀ r := hqb
  have hy'b : y' ∈ Metric.ball y₀ r := hq'b
  have hyT : y ∈ φ.target := φ.map_source hqs
  have hqy : φ.symm y = q := φ.left_inv hqs
  have hq'y : φ.symm y' = q' := φ.left_inv hq's
  have hGy : G y = e q := by simp [hGdef, hqy]
  have hGy' : G y' = e q' := by simp [hGdef, hq'y]
  have hzero : ⟪(fderiv ℝ G y) (y' - y), n⟫ = 0 := by
    rw [fderiv_comp_extChartAt_symm_apply he p hyT, hqy]
    exact hn _
  have hkey : ⟪G y' - G y - (fderiv ℝ G y) (y' - y), n⟫ = ⟪e q' - e q, n⟫ := by
    rw [inner_sub_left, hzero, sub_zero, hGy, hGy']
  rw [← hkey]
  have hb1 : |⟪G y' - G y - (fderiv ℝ G y) (y' - y), n⟫|
      ≤ ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖ * ‖n‖ := abs_real_inner_le_norm _ _
  have hb2 : ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖ ≤ lam * ‖y' - y‖ * ‖y' - y‖ :=
    htaylor y hyb y' hy'b
  have hb3 : ‖y' - y‖ ≤ 2 * κ * ‖G y' - G y‖ := hlower y hyb y' hy'b
  have hGs : ‖G y' - G y‖ = ‖e q' - e q‖ := by rw [hGy, hGy']
  rw [hGs] at hb3
  have hnn : 0 ≤ ‖n‖ := norm_nonneg _
  have hGnn : 0 ≤ ‖e q' - e q‖ := norm_nonneg _
  have hyy : (0 : ℝ) ≤ ‖y' - y‖ := norm_nonneg _
  have hsq : ‖y' - y‖ * ‖y' - y‖
      ≤ (2 * κ * ‖e q' - e q‖) * (2 * κ * ‖e q' - e q‖) :=
    mul_le_mul hb3 hb3 hyy (by positivity)
  have hD : ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖
      ≤ (4 * lam * κ ^ 2) * ‖e q' - e q‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq hlam
    nlinarith [hb2, h]
  have hpos : 0 ≤ ‖e q' - e q‖ ^ 2 * ‖n‖ := by positivity
  calc |⟪G y' - G y - (fderiv ℝ G y) (y' - y), n⟫|
      ≤ ‖G y' - G y - (fderiv ℝ G y) (y' - y)‖ * ‖n‖ := hb1
    _ ≤ (4 * lam * κ ^ 2) * ‖e q' - e q‖ ^ 2 * ‖n‖ := mul_le_mul_of_nonneg_right hD hnn
    _ ≤ (4 * lam * κ ^ 2 + 1) * ‖e q' - e q‖ ^ 2 * ‖n‖ := by nlinarith [hpos]

/-- **Global reach estimate.** For a compact submanifold embedded in `E` there is a uniform
constant `C > 0` such that every displacement `e q' - e q` is orthogonal to the normal space at
`q` up to an error quadratic in `‖e q' - e q‖`. Equivalently, the reach of `range e` is at least
`1 / (2 * C)`. -/
theorem exists_global_normal_estimate [FiniteDimensional ℝ F] [CompactSpace M] {e : M → E}
    (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (hemb : IsClosedEmbedding e)
    (hde : ∀ q : M, Function.Injective (mfderivNormed I e q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q q' : M, ∀ n : E, (∀ v : F, ⟪mfderivNormed I e q v, n⟫ = 0) →
      |⟪e q' - e q, n⟫| ≤ C * ‖e q' - e q‖ ^ 2 * ‖n‖ := by
  classical
  choose U hUopen hUmem C hCpos hCest using fun p : M => exists_local_normal_estimate he p (hde p)
  have hVex : ∀ p : M, ∃ V : Set E, IsOpen V ∧ e ⁻¹' V = U p := fun p =>
    hemb.isInducing.isOpen_iff.mp (hUopen p)
  choose V hVopen hVpre using hVex
  have hcompact : IsCompact (Set.range e) := isCompact_range he.continuous
  have hcov : Set.range e ⊆ ⋃ p, V p := by
    rintro _ ⟨p, rfl⟩
    refine mem_iUnion.2 ⟨p, ?_⟩
    have h := hUmem p
    rw [← hVpre p] at h
    exact h
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover V hVopen hcov
  have hcov' : Set.range e ⊆ ⋃ i : {p : M // p ∈ s}, V i := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric hcompact (fun i : {p : M // p ∈ s} => hVopen i) hcov'
  have hsum : 0 ≤ ∑ p ∈ s, C p := Finset.sum_nonneg fun p _ => (hCpos p).le
  have hinvpos : 0 < 1 / δ := by positivity
  refine ⟨1 / δ + ∑ p ∈ s, C p, by linarith, ?_⟩
  set Ctot : ℝ := 1 / δ + ∑ p ∈ s, C p with hCtot
  have hCtotpos : 0 < Ctot := by rw [hCtot]; linarith
  intro q q' n hn
  by_cases hcase : ‖e q' - e q‖ < δ
  · obtain ⟨i, hi⟩ := hδ (e q) ⟨q, rfl⟩
    have hq : q ∈ U i := by
      rw [← hVpre]; exact hi (Metric.mem_ball_self hδpos)
    have hq' : q' ∈ U i := by
      refine (hVpre (i : M)) ▸ hi ?_
      rw [Metric.mem_ball, dist_eq_norm]
      exact hcase
    refine (hCest (i : M) q hq q' hq' n hn).trans ?_
    have hCle : C (i : M) ≤ Ctot := by
      have := Finset.single_le_sum (f := C) (fun p _ => (hCpos p).le) i.2
      rw [hCtot]; linarith
    gcongr
  · replace hcase : δ ≤ ‖e q' - e q‖ := not_lt.mp hcase
    have h1 : |⟪e q' - e q, n⟫| ≤ ‖e q' - e q‖ * ‖n‖ := abs_real_inner_le_norm _ _
    have hδC : 1 / δ ≤ Ctot := by rw [hCtot]; linarith
    have hone : 1 ≤ Ctot * ‖e q' - e q‖ := by
      have h2 : 1 / δ * δ ≤ Ctot * ‖e q' - e q‖ :=
        mul_le_mul hδC hcase hδpos.le hCtotpos.le
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hδpos)] at h2
    nlinarith [h1, hone, mul_nonneg (norm_nonneg (e q' - e q)) (norm_nonneg n),
      norm_nonneg (e q' - e q), norm_nonneg n]
