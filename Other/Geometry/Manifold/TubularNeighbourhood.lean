/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Geometry.Manifold.NormalReach
public import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Neighbourhood retraction of a compact embedded submanifold

Let `M` be a compact smooth manifold, modelled on a finite-dimensional real vector space `F` with
a boundaryless model with corners, and let `e : M → E` be a smooth closed embedding into a real
inner product space whose differential is injective at every point (an embedding in the strong
sense, i.e. exactly the output of Mathlib's `exists_embedding_euclidean_of_compact`). Then
`range e` has an open neighbourhood `W ⊆ E` which retracts continuously onto `M`:

* `exists_retraction_of_compact_embedding`;
* `exists_euclidean_retraction_of_compact`, the same statement with the embedding produced by the
  Whitney embedding theorem.

The retraction is the nearest-point projection. The two inputs are in
`Other.Geometry.Manifold.NormalReach`: the first-order condition at a nearest point and the
uniform reach estimate. `NormalReach.reach_key_inequality` below turns them into the inequality

`‖x - e q‖ ^ 2 + ‖e q' - e q‖ ^ 2 * (1 - 2 * C * ‖x - e q‖) ≤ ‖x - e q'‖ ^ 2`

valid for every nearest point `q` of `x` and every `q' : M`. Taking `q'` to be another nearest
point gives uniqueness of the nearest point once `2 * C * ‖x - e q‖ < 1`, and comparing the
nearest points of two nearby points `x`, `x'` gives the quantitative continuity estimate

`‖e (r x') - e (r x)‖ ^ 2 ≤ 8 * ‖x - x'‖ ^ 2 + 8 * ρ * ‖x - x'‖`

for the retraction `r`, from which its continuity follows since `e` is an embedding.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Set Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The basic inequality satisfied by a nearest point `q` of `x` on `range e`, given a reach
constant `C` for `e`. -/
theorem reach_key_inequality {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e) {C : ℝ}
    (hest : ∀ q q' : M, ∀ n : E, (∀ v : F, ⟪mfderivNormed I e q v, n⟫ = 0) →
      |⟪e q' - e q, n⟫| ≤ C * ‖e q' - e q‖ ^ 2 * ‖n‖)
    {x : E} {q : M} (hq : ∀ p : M, ‖x - e q‖ ≤ ‖x - e p‖) (q' : M) :
    ‖x - e q‖ ^ 2 + ‖e q' - e q‖ ^ 2 * (1 - 2 * C * ‖x - e q‖) ≤ ‖x - e q'‖ ^ 2 := by
  have hn : ∀ v : F, ⟪mfderivNormed I e q v, x - e q⟫ = 0 :=
    fun v => inner_mfderiv_eq_zero_of_isMinOn he hq v
  have hbound := hest q q' (x - e q) hn
  have hrw : x - e q' = (x - e q) - (e q' - e q) := by abel
  have hexp : ‖x - e q'‖ ^ 2
      = ‖x - e q‖ ^ 2 - 2 * ⟪x - e q, e q' - e q⟫ + ‖e q' - e q‖ ^ 2 := by
    rw [hrw, norm_sub_sq_real]
  have hcomm : ⟪x - e q, e q' - e q⟫ = ⟪e q' - e q, x - e q⟫ := real_inner_comm _ _
  have habs : ⟪e q' - e q, x - e q⟫ ≤ C * ‖e q' - e q‖ ^ 2 * ‖x - e q‖ :=
    (le_abs_self _).trans hbound
  rw [hexp, hcomm]
  nlinarith [habs]

/-- **Nearest points are unique in a tube of radius `1 / (2 * C)`.** -/
theorem eq_of_nearest_of_nearest {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e)
    (hinj : Function.Injective e) {C : ℝ}
    (hest : ∀ q q' : M, ∀ n : E, (∀ v : F, ⟪mfderivNormed I e q v, n⟫ = 0) →
      |⟪e q' - e q, n⟫| ≤ C * ‖e q' - e q‖ ^ 2 * ‖n‖)
    {x : E} {q q' : M} (hq : ∀ p : M, ‖x - e q‖ ≤ ‖x - e p‖)
    (hq' : ‖x - e q'‖ ≤ ‖x - e q‖) (hd : 2 * C * ‖x - e q‖ < 1) : q' = q := by
  have hkey := reach_key_inequality he hest hq q'
  have hsq : ‖x - e q'‖ ^ 2 ≤ ‖x - e q‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hq' 2
  have hnn : (0 : ℝ) ≤ ‖e q' - e q‖ ^ 2 := sq_nonneg _
  have hzero : ‖e q' - e q‖ ^ 2 = 0 := by nlinarith [hkey, hsq, hnn, hd]
  have hsub : e q' - e q = 0 := by
    have h := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    exact norm_eq_zero.mp h
  exact hinj (sub_eq_zero.mp hsub)

/-- **Neighbourhood retraction.** A compact manifold smoothly and closedly embedded in a real
inner product space with everywhere injective differential is a retract of an open neighbourhood
of its image; the retraction is the nearest-point projection. -/
theorem exists_retraction_of_compact_embedding [FiniteDimensional ℝ F] [CompactSpace M]
    {e : M → E} (he : ContMDiff I 𝓘(ℝ, E) ∞ e) (hemb : IsClosedEmbedding e)
    (hde : ∀ x : M, Function.Injective (mfderiv I 𝓘(ℝ, E) e x)) :
    ∃ W : Set E, IsOpen W ∧ ∃ hW : Set.range e ⊆ W, ∃ r : W → M, Continuous r ∧
      ∀ x : M, r ⟨e x, hW (Set.mem_range_self x)⟩ = x := by
  classical
  obtain ⟨C, hCpos, hest⟩ := exists_global_normal_estimate he hemb hde
  set ρ : ℝ := 1 / (4 * C) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hρC : 2 * C * ρ = 1 / 2 := by
    rw [hρdef]
    field_simp
    ring
  set W : Set E := ⋃ q : M, Metric.ball (e q) ρ with hWdef
  have hWopen : IsOpen W := isOpen_iUnion fun q => Metric.isOpen_ball
  have hWsub : Set.range e ⊆ W := by
    rintro _ ⟨q, rfl⟩
    exact mem_iUnion.2 ⟨q, Metric.mem_ball_self hρpos⟩
  -- existence of nearest points, with the distance bound
  have hex : ∀ x : W, ∃ q : M, (∀ p : M, ‖(x : E) - e q‖ ≤ ‖(x : E) - e p‖) ∧
      ‖(x : E) - e q‖ < ρ := by
    rintro ⟨x, hx⟩
    obtain ⟨q₀, hq₀⟩ := mem_iUnion.mp hx
    have hne : (Set.univ : Set M).Nonempty := ⟨q₀, trivial⟩
    obtain ⟨q, -, hqmin⟩ := isCompact_univ.exists_isMinOn (α := ℝ) hne
      (f := fun p : M => ‖x - e p‖)
      ((continuous_const.sub he.continuous).norm).continuousOn
    have hmin : ∀ p : M, ‖x - e q‖ ≤ ‖x - e p‖ := fun p => hqmin (mem_univ p)
    refine ⟨q, hmin, lt_of_le_of_lt (hmin q₀) ?_⟩
    rw [← dist_eq_norm]
    exact hq₀
  choose r hrmin hrρ using hex
  have hd : ∀ x : W, 2 * C * ‖(x : E) - e (r x)‖ < 1 := by
    intro x
    have h := hrρ x
    nlinarith [hCpos, h, norm_nonneg ((x : E) - e (r x)), hρC]
  -- uniqueness of the nearest point
  have huniq : ∀ (x : W) (q' : M), ‖(x : E) - e q'‖ ≤ ‖(x : E) - e (r x)‖ → q' = r x :=
    fun x q' h => eq_of_nearest_of_nearest he hemb.injective hest (hrmin x) h (hd x)
  -- the quantitative continuity estimate
  have hcont : ∀ x x' : W,
      ‖e (r x') - e (r x)‖ ^ 2 ≤ 8 * ‖(x : E) - (x' : E)‖ ^ 2 + 8 * ρ * ‖(x : E) - (x' : E)‖ := by
    intro x x'
    have hkey := reach_key_inequality he hest (hrmin x) (r x')
    have hhalf : (1 : ℝ) - 2 * C * ‖(x : E) - e (r x)‖ ≥ 1 / 2 := by
      nlinarith [hrρ x, hCpos, hρC, norm_nonneg ((x : E) - e (r x))]
    have htri : ‖(x : E) - e (r x')‖ ≤ 2 * ‖(x : E) - (x' : E)‖ + ‖(x : E) - e (r x)‖ := by
      have h1 : ‖(x : E) - e (r x')‖ ≤ ‖(x : E) - (x' : E)‖ + ‖(x' : E) - e (r x')‖ := by
        have : (x : E) - e (r x') = ((x : E) - (x' : E)) + ((x' : E) - e (r x')) := by abel
        rw [this]; exact norm_add_le _ _
      have h2 : ‖(x' : E) - e (r x')‖ ≤ ‖(x' : E) - e (r x)‖ := hrmin x' (r x)
      have h3 : ‖(x' : E) - e (r x)‖ ≤ ‖(x' : E) - (x : E)‖ + ‖(x : E) - e (r x)‖ := by
        have : (x' : E) - e (r x) = ((x' : E) - (x : E)) + ((x : E) - e (r x)) := by abel
        rw [this]; exact norm_add_le _ _
      have h4 : ‖(x' : E) - (x : E)‖ = ‖(x : E) - (x' : E)‖ := norm_sub_rev _ _
      linarith
    have hnn : (0 : ℝ) ≤ ‖(x : E) - e (r x)‖ := norm_nonneg _
    have htt : (0 : ℝ) ≤ ‖(x : E) - (x' : E)‖ := norm_nonneg _
    have hsq : ‖(x : E) - e (r x')‖ ^ 2
        ≤ (2 * ‖(x : E) - (x' : E)‖ + ‖(x : E) - e (r x)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hbound : ‖(x : E) - e (r x)‖ ≤ ρ := (hrρ x).le
    nlinarith [hkey, hsq, hhalf, hnn, htt, hbound, sq_nonneg ‖e (r x') - e (r x)‖]
  -- continuity of `e ∘ r`, hence of `r`
  have her : Continuous (e ∘ r) := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨min 1 (ε ^ 2 / (8 + 8 * ρ)), lt_min one_pos (by positivity), ?_⟩
    intro x' hx'
    have ht : ‖(x' : E) - (x : E)‖ < min 1 (ε ^ 2 / (8 + 8 * ρ)) := by
      rwa [← dist_eq_norm, ← Subtype.dist_eq]
    have ht1 : ‖(x' : E) - (x : E)‖ < 1 := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : ‖(x' : E) - (x : E)‖ < ε ^ 2 / (8 + 8 * ρ) :=
      lt_of_lt_of_le ht (min_le_right _ _)
    have htt : (0 : ℝ) ≤ ‖(x' : E) - (x : E)‖ := norm_nonneg _
    have hmain := hcont x' x
    have hlt : ‖e (r x) - e (r x')‖ ^ 2 < ε ^ 2 := by
      have hden : (0 : ℝ) < 8 + 8 * ρ := by positivity
      have h2 : ‖(x' : E) - (x : E)‖ * (8 + 8 * ρ) < ε ^ 2 := by
        rw [← lt_div_iff₀ hden]; exact ht2
      nlinarith [hmain, ht1, htt, h2]
    have : ‖e (r x) - e (r x')‖ < ε :=
      lt_of_pow_lt_pow_left₀ 2 hε.le hlt
    rw [dist_eq_norm]
    simpa [Function.comp, norm_sub_rev] using this
  have hr : Continuous r := hemb.isEmbedding.continuous_iff.mpr her
  refine ⟨W, hWopen, hWsub, r, hr, fun x => ?_⟩
  refine (huniq ⟨e x, hWsub (Set.mem_range_self x)⟩ x ?_).symm
  simp only
  have : ‖e x - e x‖ = 0 := by simp
  rw [this]
  exact norm_nonneg _

/-- **Neighbourhood retraction, Euclidean form.** A compact smooth manifold embeds in some
Euclidean space as a retract of an open neighbourhood of its image. -/
theorem exists_euclidean_retraction_of_compact [FiniteDimensional ℝ F] [CompactSpace M]
    [T2Space M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)) (W : Set (EuclideanSpace ℝ (Fin n))),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧ IsClosedEmbedding e ∧ IsOpen W ∧
        ∃ hW : Set.range e ⊆ W, ∃ r : W → M, Continuous r ∧
          ∀ x : M, r ⟨e x, hW (Set.mem_range_self x)⟩ = x := by
  obtain ⟨n, e, hsmooth, hemb, hdiff⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨W, hWopen, hWsub, r, hr, hrr⟩ :=
    exists_retraction_of_compact_embedding hsmooth hemb hdiff
  exact ⟨n, e, W, hsmooth, hemb, hWopen, hWsub, r, hr, hrr⟩
