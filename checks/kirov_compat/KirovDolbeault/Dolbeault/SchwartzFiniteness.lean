/-
  The abstract Schwartz / Riesz–Schauder finiteness lemma (Forster *Lectures on Riemann Surfaces*
  Lemma 14.8) — the functional-analysis core of the `H¹(X, 𝒪_D)` finiteness theorem (14.9).

  Standalone (Banach-space functional analysis; no manifold / Čech dependency). Mathlib has the
  spectral Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) and Riesz's
  lemma but NOT this packaged "compact perturbation of a surjection has finite-codimensional image".
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Jacobians.SchwartzFiniteness

open Metric Filter Topology Finset

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Successive-approximation surjectivity.** If a continuous linear map `g : E →L[ℂ] G` between
Banach spaces admits, for every target `y`, an *approximate* preimage `x` within distance
`(1/2)‖y‖` and with norm `≤ C‖y‖`, then `g` is (exactly) surjective. This is the iterative second
half of the Banach open mapping theorem (`ContinuousLinearMap.exists_preimage_norm_le`), abstracted
so it can be applied to a small perturbation of a surjection. -/
theorem surjective_of_approx {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (g : E →L[ℂ] G) {C : ℝ}
    (h : ∀ y : G, ∃ x : E, dist (g x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Function.Surjective g := by
  choose f hdist hnorm using h
  intro y
  set r : G → G := fun y => y - g (f y) with hr
  have hrle : ∀ z, ‖r z‖ ≤ 1 / 2 * ‖z‖ := by
    intro z
    show ‖z - g (f z)‖ ≤ 1 / 2 * ‖z‖
    rw [← dist_eq_norm, dist_comm]
    exact hdist z
  have hrnle : ∀ n : ℕ, ‖r^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Function.iterate_succ']
      calc ‖r (r^[n] y)‖ ≤ 1 / 2 * ‖r^[n] y‖ := hrle _
        _ ≤ 1 / 2 * ((1 / 2) ^ n * ‖y‖) := by gcongr
        _ = (1 / 2) ^ (n + 1) * ‖y‖ := by ring
  set u : ℕ → E := fun n => f (r^[n] y) with hu
  have hunorm : ∀ n, ‖u n‖ ≤ (|C| * ‖y‖) * (1 / 2) ^ n := by
    intro n
    calc ‖u n‖ ≤ C * ‖r^[n] y‖ := hnorm _
      _ ≤ |C| * ‖r^[n] y‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ |C| * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hrnle n
      _ = (|C| * ‖y‖) * (1 / 2) ^ n := by ring
  have hcauchy : CauchySeq (fun n => ∑ k ∈ range (n + 1), u k) :=
    NormedAddCommGroup.cauchy_series_of_le_geometric' (by norm_num : (1:ℝ)/2 < 1) hunorm
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ?_⟩
  have hgu : ∀ k, g (u k) = r^[k] y - r^[k + 1] y := by
    intro k
    show g (f (r^[k] y)) = r^[k] y - r^[k + 1] y
    rw [Function.iterate_succ']
    show g (f (r^[k] y)) = r^[k] y - (r^[k] y - g (f (r^[k] y)))
    abel
  have hpartial : ∀ n, g (∑ k ∈ range (n + 1), u k) = y - r^[n + 1] y := by
    intro n
    rw [map_sum, Finset.sum_congr rfl (fun k _ => hgu k)]
    rw [Finset.sum_range_sub' (fun k => r^[k] y) (n + 1)]
    simp
  have hlim1 : Tendsto (fun n => g (∑ k ∈ range (n + 1), u k)) atTop (𝓝 (g x)) :=
    (g.continuous.tendsto x).comp hx
  have hr0 : Tendsto (fun n => r^[n + 1] y) atTop (𝓝 0) := by
    have htend : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ‖y‖) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1:ℝ)/2 < 1)).comp (tendsto_add_atTop_nat 1)
      simpa using this.mul_const ‖y‖
    exact squeeze_zero_norm (fun n => hrnle (n + 1)) htend
  have hlim2 : Tendsto (fun n => y - r^[n + 1] y) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub hr0
  rw [sub_zero] at hlim2
  apply tendsto_nhds_unique hlim1
  simpa only [hpartial] using hlim2

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Finite-dimensional `δ`-net for a compact operator.** A compact operator `K` admits a
finite-dimensional subspace `S ≤ F` that `δ`-approximates the image of the unit ball: every `K x`
with `‖x‖ ≤ 1` lies within distance `δ` of `S`. The subspace is the span of a finite `δ`-net of the
(relatively compact) image of the closed unit ball. -/
theorem exists_finiteDim_approx
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Submodule ℂ F, FiniteDimensional ℂ S ∧
      ∀ x : E, ‖x‖ ≤ 1 → infDist (K x) (S : Set F) ≤ δ := by
  have hcompact : IsCompact (closure (K '' closedBall 0 1)) :=
    hK.isCompact_closure_image_closedBall 1
  obtain ⟨t, _ht_sub, ht_fin, ht_cover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hcompact hδ
  refine ⟨Submodule.span ℂ t, FiniteDimensional.span_of_finite ℂ ht_fin, ?_⟩
  intro x hx
  have hKx : K x ∈ K '' closedBall 0 1 := ⟨x, by simpa using hx, rfl⟩
  obtain ⟨y, hy_mem, hy_dist⟩ := Set.mem_iUnion₂.mp (ht_cover hKx)
  calc infDist (K x) (Submodule.span ℂ t : Set F)
      ≤ dist (K x) y := infDist_le_dist_of_mem (Submodule.subset_span hy_mem)
    _ ≤ δ := (mem_ball.mp hy_dist).le

/-- **Schwartz finiteness (Forster 14.8).** A compact perturbation of a surjection between Banach
spaces has finite-codimensional image: if `A : E →L[ℂ] F` is surjective and `K : E →L[ℂ] F` is a
compact operator, then `F ⧸ range (A + K)` is finite-dimensional. (`K = 0` ⟹ codim 0; `A = id` ⟹
Riesz–Schauder for `1 + K`.) This is the functional-analysis core of Forster 14.9. -/
theorem finiteDimensional_quotient_range_add_compact
    (A : E →L[ℂ] F) (hA : Function.Surjective A)
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (F ⧸ LinearMap.range (A + K).toLinearMap) := by
  -- `A` is quantitatively surjective (Banach open mapping theorem): preimages with `‖x‖ ≤ C‖y‖`.
  obtain ⟨C, hCpos, hAC⟩ := ContinuousLinearMap.exists_preimage_norm_le A hA
  -- Choose `δ` so that, after the `2×` lift through the quotient, `q ∘ K` shrinks by a factor `1/2`.
  set δ : ℝ := 1 / (4 * C) with hδdef
  have hδpos : 0 < δ := by positivity
  -- A finite-dimensional `S` whose `δ`-neighbourhood absorbs `K` of the unit ball.
  obtain ⟨S, hSfin, hSnet⟩ := exists_finiteDim_approx K hK hδpos
  haveI : FiniteDimensional ℂ S := hSfin
  haveI hSclosed : IsClosed (S : Set F) := S.closed_of_finiteDimensional
  -- The continuous quotient map `q : F →L[ℂ] F ⧸ S` (well-defined since `S` is closed).
  set q : F →L[ℂ] (F ⧸ S) := S.mkQ.mkContinuous 1 (fun w => by
    simpa using (Submodule.Quotient.norm_mk_le S w)) with hqdef
  have hqmk : ∀ z : F, q z = Submodule.Quotient.mk z := fun _ => rfl
  have hqnorm : ∀ z : F, ‖q z‖ = infDist z (S : Set F) := fun z =>
    QuotientAddGroup.norm_mk (S := S.toAddSubgroup) z
  -- `q ∘ K` has operator norm `≤ δ`, hence `‖q (K x)‖ ≤ δ‖x‖` pointwise.
  have hqKbound : ∀ x : E, ‖q (K x)‖ ≤ δ * ‖x‖ := by
    set qK : E →L[ℂ] (F ⧸ S) := q.comp K with hqKdef
    have hqKnorm : ‖qK‖ ≤ δ := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hδpos.le
      intro x hx
      rw [show ‖qK x‖ = infDist (K x) (S : Set F) from hqnorm (K x)]
      exact hSnet x hx.le
    intro x
    simpa [hqKdef] using qK.le_of_opNorm_le hqKnorm x
  -- `q ∘ (A + K)` is surjective: a `< δ`-perturbation of the `δ`-open surjection `q ∘ A`.
  have hsurj : Function.Surjective (q.comp (A + K)) := by
    refine surjective_of_approx (C := 2 * C) (q.comp (A + K)) ?_
    intro w
    rcases eq_or_ne w 0 with hzero | hne
    · exact ⟨0, by simp [hzero], by simp [hzero]⟩
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
      obtain ⟨y, hy_mk, hy_norm⟩ := Submodule.Quotient.norm_mk_lt w hwpos
      have hqy : q y = w := by rw [hqmk]; exact hy_mk
      have hy_norm' : ‖y‖ < 2 * ‖w‖ := by linarith
      obtain ⟨x, hAx, hx_norm⟩ := hAC y
      refine ⟨x, ?_, ?_⟩
      · have hcompute : (q.comp (A + K)) x = w + q (K x) := by
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
          rw [map_add, hAx, hqy]
        rw [hcompute, dist_eq_norm, show w + q (K x) - w = q (K x) from by abel]
        calc ‖q (K x)‖ ≤ δ * ‖x‖ := hqKbound x
          _ ≤ δ * (C * ‖y‖) := by
              apply mul_le_mul_of_nonneg_left hx_norm; rw [hδdef]; positivity
          _ ≤ δ * (C * (2 * ‖w‖)) := by
              apply mul_le_mul_of_nonneg_left _ (by rw [hδdef]; positivity)
              exact mul_le_mul_of_nonneg_left hy_norm'.le hCpos.le
          _ = 1 / 2 * ‖w‖ := by rw [hδdef]; field_simp; ring
      · calc ‖x‖ ≤ C * ‖y‖ := hx_norm
          _ ≤ C * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hy_norm'.le hCpos.le
          _ = 2 * C * ‖w‖ := by ring
  -- Surjectivity of `q ∘ (A + K)` means `range (A + K) ⊔ S = ⊤`; then the quotient `F ⧸ range`
  -- is the surjective image of the finite-dimensional `S`, hence finite-dimensional.
  set T := (A + K).toLinearMap with hT
  have hrange_top : LinearMap.range (S.mkQ.comp T) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨x, hx⟩ := hsurj w
    refine ⟨x, ?_⟩
    rw [LinearMap.comp_apply, show S.mkQ (T x) = q (T x) from (hqmk (T x)).symm]
    exact hx
  have hmap : Submodule.map S.mkQ (LinearMap.range T) = ⊤ := by
    rw [← LinearMap.range_comp]; exact hrange_top
  have hsup : S ⊔ LinearMap.range T = ⊤ := (Submodule.map_mkQ_eq_top S _).mp hmap
  have hsup' : LinearMap.range T ⊔ S = ⊤ := by rw [sup_comm]; exact hsup
  have hrange2 : LinearMap.range ((LinearMap.range T).mkQ.comp S.subtype) = ⊤ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact (Submodule.map_mkQ_eq_top _ _).mpr hsup'
  exact FiniteDimensional.of_surjective ((LinearMap.range T).mkQ.comp S.subtype)
    (LinearMap.range_eq_top.mp hrange2)

end Jacobians.SchwartzFiniteness
