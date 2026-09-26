/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Other.Oka.Topology.Algebra.IsUniformGroup.LiftTotallyBounded

/-!
# The open mapping theorem for complete metrizable topological vector spaces

Let `E`, `F` be complete, first countable (i.e. metrizable) topological vector spaces over a
nontrivially normed field, `F` Hausdorff (no local convexity is needed). A surjective continuous
linear map `u : E →L[𝕜] F` is open (`ContinuousLinearMap.isOpenMap_of_surjective`). This covers
Fréchet spaces, where Mathlib only has the Banach space version `ContinuousLinearMap.isOpenMap`.

The proof is the classical one: by Baire's theorem the closure of the image of every
neighbourhood of `0` is a neighbourhood of `0`
(`ContinuousLinearMap.closure_image_mem_nhds_zero_of_surjective`), and completeness of `E`
removes the closure (`ContinuousLinearMap.image_mem_nhds_zero_of_surjective`) by a successive
approximation along a halving sequence of neighbourhoods.
-/

@[expose] public section

open Filter Topology Set Pointwise

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
  [FirstCountableTopology F] [CompleteSpace F]

/-- Baire step of the open mapping theorem: for `u` surjective onto a complete metrizable `F`,
the closure of the image of a neighbourhood of `0` is a neighbourhood of `0`. -/
theorem closure_image_mem_nhds_zero_of_surjective (u : E →L[𝕜] F) (hu : Function.Surjective u)
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) : closure (u '' W) ∈ 𝓝 (0 : F) := by
  haveI : (uniformity F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨W', hW', hW'W⟩ : ∃ W' ∈ 𝓝 (0 : E), ∀ x ∈ W', ∀ y ∈ W', x - y ∈ W := by
    obtain ⟨A, hA, hAW⟩ := exists_nhds_zero_half hW
    refine ⟨A ∩ -A, inter_mem hA (neg_mem_nhds_zero E hA), fun a ha b hb ↦ ?_⟩
    rw [sub_eq_add_neg]
    exact hAW a ha.1 (-b) hb.2
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  have ha0 : a ≠ 0 := norm_pos_iff.1 (one_pos.trans ha)
  set S := closure (u '' W')
  have hcov : ⋃ n : ℕ, a ^ n • S = univ := by
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hu y
    have htend : Tendsto (fun n : ℕ ↦ a ^ n) atTop (Bornology.cobounded 𝕜) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_pow_atTop_atTop_of_one_lt ha
    obtain ⟨n, hn⟩ := (htend.eventually (absorbent_nhds_zero hW' x)).exists
    obtain ⟨x', hx', hxx'⟩ := hn (mem_singleton x)
    refine mem_iUnion.2 ⟨n, u x', subset_closure ⟨x', hx', rfl⟩, ?_⟩
    simp [← hxx']
  obtain ⟨n, y₀, hy₀⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n ↦ isClosed_closure.smul_of_ne_zero (pow_ne_zero n ha0)) hcov
  rw [interior_smul₀ (pow_ne_zero n ha0)] at hy₀
  obtain ⟨y₁, hy₁, rfl⟩ := hy₀
  have hS : S ∈ 𝓝 y₁ := mem_interior_iff_mem_nhds.1 hy₁
  have hT : (fun z ↦ y₁ + z) ⁻¹' S ∈ 𝓝 (0 : F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hS)
  refine mem_of_superset hT fun z hz ↦ ?_
  have hsub : (fun p : F × F ↦ p.1 - p.2) '' (S ×ˢ S) ⊆ closure (u '' W) := by
    rw [← closure_prod_eq]
    refine (image_closure_subset_closure_image (by fun_prop)).trans (closure_mono ?_)
    rintro _ ⟨⟨_, _⟩, ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, rfl⟩⟩, rfl⟩
    exact ⟨x₁ - x₂, hW'W x₁ hx₁ x₂ hx₂, by simp⟩
  exact hsub ⟨(y₁ + z, y₁), ⟨hz, interior_subset hy₁⟩, by simp⟩

variable [FirstCountableTopology E] [CompleteSpace E] [T2Space F]

/-- **Open mapping theorem** (complete metrizable TVS, neighbourhoods of `0`): a surjective
continuous linear map maps neighbourhoods of `0` to neighbourhoods of `0`. -/
theorem image_mem_nhds_zero_of_surjective (u : E →L[𝕜] F) (hu : Function.Surjective u)
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) : u '' W ∈ 𝓝 (0 : F) := by
  obtain ⟨N, hNnhds, hN, hNW, hNbasis, hanti⟩ := exists_add_subset_basis_nhds_zero hW
  have h0 : ∀ n, (0 : E) ∈ N n := fun n ↦ mem_of_mem_nhds (hNnhds n)
  set C : ℕ → Set F := fun n ↦ closure (u '' N n)
  have hC : ∀ n, C n ∈ 𝓝 (0 : F) := fun n ↦
    closure_image_mem_nhds_zero_of_surjective u hu (hNnhds n)
  have hCsmall : ∀ Y ∈ 𝓝 (0 : F), ∀ᶠ m in atTop, C m ⊆ Y := by
    intro Y hY
    obtain ⟨Y', ⟨hY', hY'c⟩, hY'Y⟩ := (closed_nhds_basis (0 : F)).mem_iff.1 hY
    have : (u : E → F) ⁻¹' Y' ∈ 𝓝 (0 : E) :=
      u.continuous.continuousAt.preimage_mem_nhds (by simpa using hY')
    obtain ⟨n, hn⟩ := hNbasis _ this
    filter_upwards [eventually_ge_atTop n] with m hm
    refine (closure_minimal ?_ hY'c).trans hY'Y
    rintro _ ⟨x, hx, rfl⟩
    exact hn (hanti hm hx)
  have hstep : ∀ n (z : F), ∃ x : E, z ∈ C n → x ∈ N n ∧ z - u x ∈ C (n + 1) := by
    intro n z
    by_cases hz : z ∈ C n
    · have hnhds : (fun w ↦ z - w) ⁻¹' C (n + 1) ∈ 𝓝 z :=
        (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using hC (n + 1))
      obtain ⟨_, hw, ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hz _ hnhds
      exact ⟨x, fun _ ↦ ⟨hx, hw⟩⟩
    · exact ⟨0, fun h ↦ absurd h hz⟩
  choose X hX using hstep
  refine mem_of_superset (hC 2) fun y hy ↦ ?_
  let zs : ℕ → F := fun k ↦ Nat.rec y (fun k z ↦ z - u (X (k + 2) z)) k
  have hzs : ∀ k, zs k ∈ C (k + 2) := by
    intro k
    induction k with
    | zero => exact hy
    | succ k ih => exact (hX (k + 2) (zs k) ih).2
  let xs : ℕ → E := fun k ↦ X (k + 2) (zs k)
  have hxs : ∀ k, xs k ∈ N (k + 2) := fun k ↦ (hX (k + 2) (zs k) (hzs k)).1
  have hpartial : ∀ m, u (∑ k ∈ Finset.range m, xs k) = y - zs m := by
    intro m
    induction m with
    | zero => simp [zs]
    | succ m ih =>
      rw [Finset.sum_range_succ, map_add, ih]
      change y - zs m + u (xs m) = y - (zs m - u (xs m))
      abel
  have hsum : Summable xs :=
    summable_of_add_subset h0 hN hNbasis fun k ↦ hanti (by omega) (hxs k)
  refine ⟨∑' k, xs k, hNW ?_, ?_⟩
  · have hcl := hsum.hasSum.mem_closure_of_add_subset (N := fun n ↦ N (n + 1)) (fun n ↦ h0 _)
      (fun n ↦ hN (n + 1)) hxs
    exact (closure_subset_add_self_of_mem_nhds_zero (hNnhds 1)).trans (hN 0) hcl
  · have h1 := (hsum.hasSum.map u u.continuous).tendsto_sum_nat
    have h2 : Tendsto (fun m ↦ u (∑ k ∈ Finset.range m, xs k)) atTop (𝓝 (y - 0)) := by
      simp_rw [hpartial]
      refine tendsto_const_nhds.sub (tendsto_def.2 fun Y hY ↦ ?_)
      filter_upwards [hCsmall Y hY] with m hm
      exact hm (closure_mono (image_mono (hanti (by omega))) (hzs m))
    simp_rw [map_sum] at h2
    simpa using tendsto_nhds_unique h1 h2

/-- **Open mapping theorem** for complete metrizable topological vector spaces (e.g. Fréchet
spaces): a surjective continuous linear map is open. -/
theorem isOpenMap_of_surjective (u : E →L[𝕜] F) (hu : Function.Surjective u) : IsOpenMap u := by
  refine IsOpenMap.of_nhds_le fun a t ht ↦ ?_
  rw [mem_map] at ht
  have hW : (fun w ↦ a + w) ⁻¹' (u ⁻¹' t) ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht)
  have h := image_mem_nhds_zero_of_surjective u hu hW
  rw [← map_add_left_nhds_zero (u a)]
  refine mem_map.2 (mem_of_superset h ?_)
  rintro _ ⟨w, hw, rfl⟩
  simpa using hw

end ContinuousLinearMap

end
