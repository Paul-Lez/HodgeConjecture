/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The iteration behind Schwartz's finiteness theorem

Let `u v : E →L[𝕜] F` be continuous linear maps between topological vector spaces and put
`w = u + v`. Suppose there are a bounded set `K ⊆ F`, a set `L ⊆ E`, a closed subspace `G ⊆ F`
and a scalar `c` with `‖c‖ < 1` such that

* every `k ∈ K` is `u x` for some `x ∈ L` with `v x + c • k' ∈ G` for some `k' ∈ K`;
* every series `∑ cⁿ • ℓₙ` with all `ℓₙ ∈ L` converges.

Then `K ⊆ range w ⊔ G` (`ContinuousLinearMap.mem_range_add_sup_of_step`): starting from
`r₀ = k`, the residuals `rₙ = cⁿ • kₙ` are corrected by `xₙ = cⁿ • ℓₙ` up to an element of `G`,
and `rₙ → 0` because `K` is bounded. If moreover `u` is surjective and `K` absorbs `v(E)`, then
`range w ⊔ G = ⊤` (`ContinuousLinearMap.range_add_sup_eq_top_of_step`), so `F ⧸ range w` is
finite dimensional when `G` is.

This is the common core of Schwartz's theorem for Banach spaces
(`Other/Oka/Analysis/Normed/Operator/Compact/Schwartz.lean`) and for Fréchet spaces.
-/

@[expose] public section

open Filter Topology Bornology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- The Schwartz iteration: under the hypotheses in the module docstring, every element of `K`
lies in `range (u + v) ⊔ G`. -/
theorem mem_range_add_sup_of_step {u v : E →L[𝕜] F} {K : Set F} {L : Set E}
    {G : Submodule 𝕜 F} (hG : IsClosed (G : Set F)) {c : 𝕜} (hc : ‖c‖ < 1)
    (hK : IsVonNBounded 𝕜 K)
    (hL : ∀ ℓ : ℕ → E, (∀ n, ℓ n ∈ L) → ∃ x, HasSum (fun n ↦ c ^ n • ℓ n) x)
    (hstep : ∀ k ∈ K, ∃ x ∈ L, ∃ k' ∈ K, u x = k ∧ v x + c • k' ∈ G) {k : F} (hk : k ∈ K) :
    k ∈ LinearMap.range (u + v).toLinearMap ⊔ G := by
  choose X hXL K' hK'K hXu hXv using hstep
  -- the sequence of normalised residuals `kₙ ∈ K`
  let seq : ℕ → K := fun n ↦ Nat.rec ⟨k, hk⟩ (fun _ p ↦ ⟨K' p.1 p.2, hK'K p.1 p.2⟩) n
  have seq_succ (n : ℕ) : (seq (n + 1)).1 = K' (seq n).1 (seq n).2 := rfl
  let ℓ : ℕ → E := fun n ↦ X (seq n).1 (seq n).2
  obtain ⟨x, hx⟩ := hL ℓ (fun n ↦ hXL _ _)
  set w : E →L[𝕜] F := u + v
  have key (N : ℕ) : w (∑ n ∈ Finset.range N, c ^ n • ℓ n) - k + c ^ N • (seq N).1 ∈ G := by
    induction N with
    | zero => simp [seq]
    | succ N ih =>
      have hu : u (ℓ N) = (seq N).1 := hXu (seq N).1 (seq N).2
      have h : w (∑ n ∈ Finset.range (N + 1), c ^ n • ℓ n) - k + c ^ (N + 1) • (seq (N + 1)).1
          = (w (∑ n ∈ Finset.range N, c ^ n • ℓ n) - k + c ^ N • (seq N).1) +
            c ^ N • (v (ℓ N) + c • (seq (N + 1)).1) := by
        simp only [Finset.sum_range_succ, map_add, map_smul, w, add_apply, hu, smul_add,
          smul_smul, pow_succ]
        abel
      rw [h]
      exact G.add_mem ih (G.smul_mem _ (by rw [seq_succ]; exact hXv _ _))
  have hlim : Tendsto (fun N ↦ w (∑ n ∈ Finset.range N, c ^ n • ℓ n) - k + c ^ N • (seq N).1)
      atTop (𝓝 (w x - k + 0)) := by
    refine ((w.continuous.tendsto x).comp hx.tendsto_sum_nat |>.sub_const k).add ?_
    exact hK.smul_tendsto_zero (Eventually.of_forall fun n ↦ (seq n).2)
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc)
  have hmem : w x - k ∈ G := by
    simpa using hG.mem_of_tendsto hlim (Eventually.of_forall key)
  have : k = w x + -(w x - k) := by abel
  rw [this]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (G.neg_mem hmem)

/-- Schwartz's iteration, global form: if moreover `u` is surjective and every `v x` is a
multiple of an element of `K`, then `range (u + v) ⊔ G = ⊤`. -/
theorem range_add_sup_eq_top_of_step {u v : E →L[𝕜] F} {K : Set F} {L : Set E}
    {G : Submodule 𝕜 F} (hG : IsClosed (G : Set F)) {c : 𝕜} (hc : ‖c‖ < 1)
    (hK : IsVonNBounded 𝕜 K)
    (hL : ∀ ℓ : ℕ → E, (∀ n, ℓ n ∈ L) → ∃ x, HasSum (fun n ↦ c ^ n • ℓ n) x)
    (hstep : ∀ k ∈ K, ∃ x ∈ L, ∃ k' ∈ K, u x = k ∧ v x + c • k' ∈ G)
    (hu : Function.Surjective u) (habs : ∀ x, ∃ t : 𝕜, ∃ k ∈ K, v x = t • k) :
    LinearMap.range (u + v).toLinearMap ⊔ G = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨x, rfl⟩ := hu y
  obtain ⟨t, k, hk, hvx⟩ := habs x
  have hmem := mem_range_add_sup_of_step hG hc hK hL hstep hk
  have : u x = (u + v) x + -(t • k) := by rw [add_apply, hvx]; abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
    (Submodule.neg_mem _ (Submodule.smul_mem _ t hmem))

end ContinuousLinearMap

namespace Submodule

variable {𝕜 F : Type*} [Field 𝕜] [AddCommGroup F] [Module 𝕜 F]

/-- If `R ⊔ G = ⊤` with `G` finite dimensional, then `F ⧸ R` is finite dimensional. -/
theorem finiteDimensional_quotient_of_sup_eq_top {R G : Submodule 𝕜 F} [FiniteDimensional 𝕜 G]
    (h : R ⊔ G = ⊤) : FiniteDimensional 𝕜 (F ⧸ R) := by
  refine Module.Finite.of_surjective (R.mkQ.comp G.subtype) fun y ↦ ?_
  obtain ⟨y, rfl⟩ := R.mkQ_surjective y
  obtain ⟨r, hr, g, hg, rfl⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : y ∈ R ⊔ G)
  refine ⟨⟨g, hg⟩, ?_⟩
  simp [(Submodule.Quotient.mk_eq_zero R).2 hr]

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F]

/-- If `range w ⊔ G = ⊤` for a finite dimensional `G` and `(x, g) ↦ w x + g` is an open map
(e.g. by an open mapping theorem), then `range w` is closed. -/
theorem isClosed_range_of_isOpenMap_coprod {w : E →L[𝕜] F} {G : Submodule 𝕜 F}
    [FiniteDimensional 𝕜 G] (h : LinearMap.range w.toLinearMap ⊔ G = ⊤)
    (hopen : IsOpenMap (w.coprod G.subtypeL)) :
    IsClosed (LinearMap.range w.toLinearMap : Set F) := by
  set R := LinearMap.range w.toLinearMap
  have hS : IsClosed ((R.comap G.subtype : Submodule 𝕜 G) : Set G) :=
    Submodule.closed_of_finiteDimensional _
  rw [← isOpen_compl_iff]
  have : (R : Set F)ᶜ = w.coprod G.subtypeL '' (Set.univ ×ˢ
      ((R.comap G.subtype : Submodule 𝕜 G) : Set G)ᶜ) := by
    ext y
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_image, Set.mem_prod, Set.mem_univ,
      true_and, Prod.exists, coprod_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      Submodule.mem_comap]
    constructor
    · intro hy
      obtain ⟨r, ⟨x, rfl⟩, g, hg, rfl⟩ :=
        Submodule.mem_sup.1 (h ▸ Submodule.mem_top : y ∈ R ⊔ G)
      refine ⟨x, ⟨g, hg⟩, fun hgR ↦ hy (R.add_mem (LinearMap.mem_range_self _ _) hgR), rfl⟩
    · rintro ⟨x, g, hg, rfl⟩ hy
      exact hg (by simpa using R.sub_mem hy (LinearMap.mem_range_self w.toLinearMap x))
  rw [this]
  exact hopen _ (isOpen_univ.prod hS.isOpen_compl)

end ContinuousLinearMap

end
