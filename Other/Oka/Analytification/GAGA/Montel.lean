/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.MittagLeffler
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Montel's theorem in several variables

Let `E` be a finite-dimensional complex normed space and `U ⊆ E` open. A family of holomorphic
functions on `U` which is uniformly bounded on every compact subset of `U` is relatively compact
for the topology of uniform convergence on compact subsets of `U`.

The proof is the classical one: a bound `M` on a ball `B(z, R)` gives, by the Schwarz lemma
applied on the complex line through `z` and `y`, the Lipschitz estimate
`‖f y - f z‖ ≤ 2M/R ‖y - z‖`, so the family is equicontinuous, and the Arzelà–Ascoli theorem
applies. Limits are holomorphic by Weierstrass' theorem
(`differentiableOn_of_tendstoLocallyUniformlyOn`).

## Main results

- `norm_sub_le_of_differentiableOn_ball`: the Cauchy-type estimate above.
- `equicontinuous_restrict_of_differentiableOn`: a locally uniformly bounded family of
  holomorphic functions on `U` is equicontinuous on `U`.
- `isCompact_closure_of_differentiableOn`: **Montel's theorem**, compactness form: such a family
  has compact closure in `C(U, ℂ)` (compact-open topology).
- `exists_subseq_tendstoLocallyUniformlyOn`: **Montel's theorem**, sequential form: a locally
  uniformly bounded sequence of holomorphic functions on `U` has a subsequence converging locally
  uniformly on `U` to a holomorphic function.
-/

@[expose] public section

open Metric Set Filter Topology

/-- The restriction to `U` of a function continuous on `U`, as a continuous map on `U`. -/
def ContinuousOn.toContinuousMapOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {f : X → Y} (hf : ContinuousOn f U) : C(U, Y) :=
  ⟨U.restrict f, hf.restrict⟩

@[simp]
lemma ContinuousOn.toContinuousMapOn_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {U : Set X} {f : X → Y} (hf : ContinuousOn f U) (x : U) :
    hf.toContinuousMapOn x = f x :=
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function holomorphic on `B(z, R)` and bounded by `M` there satisfies
`‖f y - f z‖ ≤ 2M/R ‖y - z‖` on `B(z, R)`. -/
theorem norm_sub_le_of_differentiableOn_ball {f : E → ℂ} {z y : E} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball z R)) (hM : ∀ w ∈ ball z R, ‖f w‖ ≤ M)
    (hy : y ∈ ball z R) :
    ‖f y - f z‖ ≤ 2 * M / R * ‖y - z‖ := by
  have hR : 0 < R := pos_of_mem_ball hy
  rcases eq_or_ne y z with rfl | hyz
  · simp
  set v := y - z
  have hv : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 hyz)
  have hvR : ‖v‖ < R := by simpa [v, dist_eq_norm] using hy
  set g : ℂ → ℂ := fun t ↦ f (z + t • v)
  have hmaps : MapsTo (fun t : ℂ ↦ z + t • v) (ball 0 (R / ‖v‖)) (ball z R) := by
    intro t ht
    rw [mem_ball_zero_iff, lt_div_iff₀ hv] at ht
    simpa [dist_eq_norm, norm_smul] using ht
  have hg : DifferentiableOn ℂ g (ball 0 (R / ‖v‖)) :=
    hf.comp ((differentiable_const _).add (differentiable_id.smul_const v)).differentiableOn hmaps
  have hg' : MapsTo g (ball 0 (R / ‖v‖)) (closedBall (g 0) (2 * M)) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hM _ (hmaps ht)
    have h2 := hM z (mem_ball_self hR)
    calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add h1 (by simpa [g] using h2)
      _ = 2 * M := by ring
  have h1 : (1 : ℂ) ∈ ball 0 (R / ‖v‖) := by
    rw [mem_ball_zero_iff, norm_one, one_lt_div hv]; exact hvR
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hg' h1
  simp only [g, one_smul, zero_smul, add_zero, dist_eq_norm, sub_zero, norm_one, mul_one] at this
  simp only [v, div_div_eq_mul_div, add_sub_cancel] at this
  calc ‖f y - f z‖ ≤ 2 * M * ‖y - z‖ / R := this
    _ = 2 * M / R * ‖y - z‖ := by ring

variable [FiniteDimensional ℂ E] {ι : Type*}


/-- A family of holomorphic functions on `U` which is uniformly bounded on compact subsets of `U`
is equicontinuous on `U`. -/
theorem equicontinuous_restrict_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : ι → E → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C, ∀ i, ∀ x ∈ K, ‖F i x‖ ≤ C) :
    Equicontinuous fun i ↦ U.restrict (F i) := by
  intro x₀
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds x₀.2)
  obtain ⟨C, hC⟩ := hb _ hRU (isCompact_closedBall _ _)
  refine Metric.equicontinuousAt_of_continuity_modulus (fun x : U ↦ 2 * C / R * dist x x₀)
    ?_ _ ?_
  · have : Tendsto (fun x : U ↦ dist x x₀) (𝓝 x₀) (𝓝 0) := by
      simpa using (continuous_id.dist (continuous_const (y := x₀))).tendsto x₀
    simpa using this.const_mul (2 * C / R)
  · filter_upwards [Metric.ball_mem_nhds x₀ hR] with x hx i
    rw [dist_comm, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact norm_sub_le_of_differentiableOn_ball ((hF i).mono (ball_subset_closedBall.trans hRU))
      (fun w hw ↦ hC i w (ball_subset_closedBall hw)) (by rw [mem_ball]; exact hx)

/-- **Montel's theorem**: a family of holomorphic functions on `U` which is uniformly bounded on
compact subsets of `U` has compact closure in `C(U, ℂ)` (topology of compact convergence). -/
theorem isCompact_closure_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : ι → E → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C, ∀ i, ∀ x ∈ K, ‖F i x‖ ≤ C) :
    IsCompact (closure (range fun i ↦ (hF i).continuousOn.toContinuousMapOn)) := by
  haveI := hU.locallyCompactSpace
  set s := range fun i ↦ (hF i).continuousOn.toContinuousMapOn
  have hclemb : IsClosedEmbedding (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
      ((⇑) : C(U, ℂ) → U → ℂ)) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (range ContinuousMap.toUniformOnFunIsCompact)
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK ↦ hK) hclemb
    (fun K _ ↦ ?_) (fun K _ x _ ↦ ?_)
  · choose j hj using fun f : s ↦ f.2
    have := equicontinuous_restrict_of_differentiableOn hU (fun f : s ↦ hF (j f))
      (fun K hKU hK ↦ (hb K hKU hK).imp fun C hC f ↦ hC (j f))
    have heq : ((⇑) ∘ ((↑) : s → C(U, ℂ))) = fun f ↦ U.restrict (F (j f)) :=
      funext fun f ↦ by simp only [Function.comp_apply, ← hj f]; rfl
    rw [heq]
    exact this.equicontinuousOn K
  · obtain ⟨C, hC⟩ := hb {x.1} (by simp) isCompact_singleton
    refine ⟨closedBall 0 C, isCompact_closedBall _ _, ?_⟩
    rintro _ ⟨i, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hC i x rfl

/-- **Montel's theorem**, sequential form: a sequence of holomorphic functions on `U` which is
uniformly bounded on compact subsets of `U` has a subsequence converging locally uniformly on `U`
to a holomorphic function. -/
theorem exists_subseq_tendstoLocallyUniformlyOn {U : Set E} (hU : IsOpen U) {F : ℕ → E → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C, ∀ n, ∀ x ∈ K, ‖F n x‖ ≤ C) :
    ∃ G : E → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ DifferentiableOn ℂ G U ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) G atTop U := by
  haveI := hU.locallyCompactSpace
  obtain ⟨g, -, φ, hφ, hlim⟩ := (isCompact_closure_of_differentiableOn hU hF hb).tendsto_subseq
    (x := fun n ↦ (hF n).continuousOn.toContinuousMapOn) fun n ↦ subset_closure ⟨n, rfl⟩
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly] at hlim
  classical
  set G : E → ℂ := fun x ↦ if h : x ∈ U then g ⟨x, h⟩ else 0
  have hG : TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) G atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    convert hlim using 1
    · rfl
    · funext x
      simp [G, x.2]
  exact ⟨G, φ, hφ, differentiableOn_of_tendstoLocallyUniformlyOn hU (fun n ↦ hF _) hG, hG⟩

end
