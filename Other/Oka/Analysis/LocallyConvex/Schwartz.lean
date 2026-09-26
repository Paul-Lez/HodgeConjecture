/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Bases
public import Other.Oka.Topology.Algebra.Module.OpenMapping
public import Other.Oka.Topology.Algebra.Module.Schwartz.Basic

/-!
# Schwartz's finiteness theorem for Fréchet spaces

**Theorem (L. Schwartz).** Let `E`, `F` be Fréchet spaces over `𝕜 = ℝ` or `ℂ`,
`u : E →L[𝕜] F` surjective and `v : E →L[𝕜] F` compact. Then the range of `u + v` is closed and
of finite codimension.

Here "Fréchet" is spelled out as: complete, first countable (i.e. metrizable) topological vector
space over `𝕜`, Hausdorff for `F`; local convexity (`LocallyConvexSpace ℝ E`) is only needed for
`E`, and not at all for `F`.

## Main results

* `IsCompactOperator.exists_range_add_sup_eq_top_of_locallyConvex`: there is a finite
  dimensional `G ⊆ F` with `range (u + v) ⊔ G = ⊤`.
* `IsCompactOperator.finiteDimensional_quotient_range_add_of_locallyConvex`: the cokernel
  `F ⧸ range (u + v)` is finite dimensional.
* `IsCompactOperator.isClosed_range_add_of_locallyConvex`: `range (u + v)` is closed.

## Proof

Let `U` be a balanced neighbourhood of `0` with `K = v(U)` relatively compact. By the open
mapping theorem (`ContinuousLinearMap.image_mem_nhds_zero_of_surjective`), `K` has a totally
bounded, hence bounded, lift `ℓ` along `u` with `ℓ(k) ∈ Φ + ½ U` for a finite set `Φ`
(`exists_lift_of_totallyBounded`). With `G = span v(Φ)` this gives
`v(ℓ k) ∈ G + ½ K`, and the iteration `ContinuousLinearMap.range_add_sup_eq_top_of_step` applies:
the series `∑ 2⁻ⁿ ℓₙ` with `ℓₙ` in the bounded set `ℓ(K)` converge by local convexity
(`Bornology.IsVonNBounded.summable_real_smul`).
-/

@[expose] public section

open Filter Topology Set Pointwise Bornology

section Convex

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- A convex set containing `0` contains all sums `∑ wᵢ • zᵢ` with `zᵢ` in the set, `wᵢ ≥ 0` and
`∑ wᵢ ≤ 1`. -/
theorem Convex.sum_smul_mem_of_sum_le_one {s : Set E} (hs : Convex ℝ s) (h0 : (0 : E) ∈ s)
    {t : Finset ι} {w : ι → ℝ} {z : ι → E} (hw0 : ∀ i ∈ t, 0 ≤ w i)
    (hw1 : ∑ i ∈ t, w i ≤ 1) (hz : ∀ i ∈ t, z i ∈ s) : ∑ i ∈ t, w i • z i ∈ s := by
  set R := ∑ i ∈ t, w i
  rcases (Finset.sum_nonneg hw0).eq_or_lt with hR | hR
  · have hw : ∀ i ∈ t, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw0).1 hR.symm
    rw [Finset.sum_eq_zero fun i hi ↦ by rw [hw i hi, zero_smul]]
    exact h0
  · have hsum : ∑ i ∈ t, w i • z i = R • ∑ i ∈ t, (w i / R) • z i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, mul_div_cancel₀ _ hR.ne']
    rw [hsum]
    refine hs.smul_mem_of_zero_mem h0 (hs.sum_mem (fun i hi ↦ div_nonneg (hw0 i hi) hR.le)
      ?_ hz) ⟨hR.le, hw1⟩
    rw [← Finset.sum_div, div_self hR.ne']

end Convex

section Summable

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [UniformSpace E]
  [IsUniformAddGroup E] [CompleteSpace E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- In a complete locally convex space, `∑ rₙ • ℓₙ` converges for `ℓₙ` in a bounded set and
`rₙ ≥ 0` summable. -/
theorem Bornology.IsVonNBounded.summable_real_smul {L : Set E} (hL : IsVonNBounded 𝕜 L)
    {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n) (hr : Summable r) {ℓ : ℕ → E} (hℓ : ∀ n, ℓ n ∈ L) :
    Summable fun n ↦ r n • ℓ n := by
  rw [summable_iff_vanishing]
  intro U hU
  obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hU
  obtain ⟨ρ, hρ0, hρ⟩ := (hL hV).exists_pos
  have hLV : L ⊆ ((ρ : ℝ) : 𝕜) • V := hρ _ (by simp [abs_of_pos hρ0])
  obtain ⟨s, hs⟩ := summable_iff_vanishing.1 hr (Iio ρ⁻¹) (Iio_mem_nhds (inv_pos.2 hρ0))
  refine ⟨s, fun t ht ↦ hVU ?_⟩
  have hts : ∑ i ∈ t, r i < ρ⁻¹ := hs t ht
  choose y hy hyℓ using fun n ↦ hLV (hℓ n)
  have : ∑ i ∈ t, r i • ℓ i = ∑ i ∈ t, (r i * ρ) • y i := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hyℓ i]
    change r i • ((ρ : 𝕜) • y i) = _
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜) ρ (y i), smul_smul]
  rw [this]
  refine hVc.sum_smul_mem_of_sum_le_one (mem_of_mem_nhds hV)
    (fun i _ ↦ mul_nonneg (hr0 i) hρ0.le) ?_ fun i _ ↦ hy i
  rw [← Finset.sum_mul]
  calc (∑ i ∈ t, r i) * ρ ≤ ρ⁻¹ * ρ := by gcongr
    _ = 1 := inv_mul_cancel₀ hρ0.ne'

end Summable

namespace IsCompactOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [FirstCountableTopology E] [CompleteSpace E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [LocallyConvexSpace ℝ E]
  [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
  [FirstCountableTopology F] [CompleteSpace F] [T2Space F]

/-- **Schwartz's theorem** (Fréchet spaces): for `u` surjective and `v` compact there is a
finite dimensional subspace `G` with `range (u + v) ⊔ G = ⊤`. -/
theorem exists_range_add_sup_eq_top_of_locallyConvex {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    ∃ G : Submodule 𝕜 F, FiniteDimensional 𝕜 G ∧
      LinearMap.range (u + v).toLinearMap ⊔ G = ⊤ := by
  obtain ⟨K₀, hK₀, hK₀nhds⟩ := hv
  set U := balancedCore 𝕜 (v ⁻¹' K₀)
  have hU : U ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hK₀nhds
  have hUb : Balanced 𝕜 U := balancedCore_balanced _
  set K := v '' U
  have hKtb : TotallyBounded K :=
    hK₀.totallyBounded.subset (image_subset_iff.2 (balancedCore_subset _))
  set c : 𝕜 := ((2⁻¹ : ℝ) : 𝕜)
  have hc0 : c ≠ 0 := by simp [c]
  have hc1 : ‖c‖ < 1 := by
    simp only [c, RCLike.norm_ofReal]
    rw [abs_of_pos (by norm_num)]
    norm_num
  have hW : c • U ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hc0).2 hU
  obtain ⟨Φ, hΦ, ℓ, hℓu, hℓtb, hℓW⟩ := exists_lift_of_totallyBounded u u.continuous hu
    (fun W hW ↦ u.image_mem_nhds_zero_of_surjective hu hW) hKtb hW
  let G := Submodule.span 𝕜 (v '' Φ)
  haveI : FiniteDimensional 𝕜 G := FiniteDimensional.span_of_finite 𝕜 (hΦ.image v)
  refine ⟨G, this, ContinuousLinearMap.range_add_sup_eq_top_of_step (K := K) (L := ℓ '' K)
    G.closed_of_finiteDimensional hc1 (hKtb.isVonNBounded 𝕜) ?_ ?_ hu ?_⟩
  · intro ℓs hℓs
    have hsum := (hℓtb.isVonNBounded 𝕜).summable_real_smul (fun n ↦ by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num : (2⁻¹ : ℝ) < 1)) hℓs
    refine ⟨_, (hsum.congr fun n ↦ ?_).hasSum⟩
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [c]
  · rintro k hk
    obtain ⟨φ, hφ, _, ⟨x', hx', rfl⟩, hsum⟩ := hℓW k hk
    refine ⟨ℓ k, mem_image_of_mem ℓ hk, v (-x'), mem_image_of_mem v (hUb.neg_mem_iff.2 hx'),
      hℓu k hk, ?_⟩
    rw [← hsum]
    simp only [map_add, map_smul, map_neg, smul_neg, add_neg_cancel_right]
    exact Submodule.subset_span (mem_image_of_mem v hφ)
  · intro x
    obtain ⟨t, ht⟩ := (absorbent_nhds_zero (𝕜 := 𝕜) hU x).exists
    obtain ⟨x', hx', rfl⟩ := ht (mem_singleton x)
    exact ⟨t, v x', mem_image_of_mem v hx', map_smul v t x'⟩

/-- **Schwartz's theorem** (Fréchet spaces): for `u` surjective and `v` compact, the cokernel
`F ⧸ range (u + v)` is finite dimensional. -/
theorem finiteDimensional_quotient_range_add_of_locallyConvex {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u + v).toLinearMap) := by
  obtain ⟨G, hG, h⟩ := hv.exists_range_add_sup_eq_top_of_locallyConvex hu
  exact Submodule.finiteDimensional_quotient_of_sup_eq_top h

/-- **Schwartz's theorem** (Fréchet spaces): for `u` surjective and `v` compact, the range of
`u + v` is closed. -/
theorem isClosed_range_add_of_locallyConvex {u v : E →L[𝕜] F}
    (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    IsClosed (LinearMap.range (u + v).toLinearMap : Set F) := by
  obtain ⟨G, hG, h⟩ := hv.exists_range_add_sup_eq_top_of_locallyConvex hu
  haveI : IsUniformAddGroup G := G.toAddSubgroup.isUniformAddGroup
  haveI : FirstCountableTopology G :=
    TopologicalSpace.firstCountableTopology_induced _ F ((↑) : G → F)
  haveI : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  refine ContinuousLinearMap.isClosed_range_of_isOpenMap_coprod h
    (ContinuousLinearMap.isOpenMap_of_surjective _ fun y ↦ ?_)
  obtain ⟨r, ⟨x, rfl⟩, g, hg, rfl⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : y ∈ _)
  exact ⟨(x, ⟨g, hg⟩), rfl⟩

end IsCompactOperator

end
