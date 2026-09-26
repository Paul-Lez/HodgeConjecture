/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Lifting totally bounded sets along open surjections of complete metrizable groups

Let `u : E → F` be a continuous surjective homomorphism of commutative topological groups which
maps neighbourhoods of `0` to neighbourhoods of `0`, with `E` complete and first countable and `F`
Hausdorff. Then every totally bounded `K ⊆ F` has a totally bounded lift: there is `ℓ : F → E`
with `u (ℓ k) = k` for `k ∈ K` and `ℓ '' K` totally bounded
(`exists_lift_of_totallyBounded`). Moreover, for a given neighbourhood `W` of `0` the lift can be
chosen in `Φ + W` for a finite set `Φ`.

The proof writes `k = τ₀ k + ∑ₙ (τₙ₊₁ k - τₙ k)` where `τₙ k` is chosen in a finite `Vₙ`-net of
`K` and lifts the finitely many possible differences into a sequence of neighbourhoods
`Nₙ` with `Nₙ₊₁ + Nₙ₊₁ ⊆ Nₙ`, which makes the lifted series converge.

We also record the elementary facts about series with terms in such a "halving" sequence of
neighbourhoods (`Finset.sum_mem_of_add_subset`, `summable_of_add_subset`,
`HasSum.mem_closure_of_add_subset`), which are used for the open mapping theorem as well.
-/

@[expose] public section

open Filter Topology Set Pointwise

section Halving

variable {G : Type*} [AddCommMonoid G]

/-- If `N (n + 1) + N (n + 1) ⊆ N n` and `e n ∈ N (n + 1)`, every finite sum of terms `e i`
with `i ≥ m` lies in `N m`. -/
theorem Finset.sum_mem_of_add_subset {N : ℕ → Set G} (h0 : ∀ n, (0 : G) ∈ N n)
    (hN : ∀ n, N (n + 1) + N (n + 1) ⊆ N n) {e : ℕ → G} (he : ∀ n, e n ∈ N (n + 1))
    {t : Finset ℕ} {m : ℕ} (ht : ∀ i ∈ t, m ≤ i) : ∑ i ∈ t, e i ∈ N m := by
  have hanti : Antitone N :=
    antitone_nat_of_succ_le fun n x hx ↦ hN n (by simpa using Set.add_mem_add hx (h0 (n + 1)))
  induction t using Finset.induction_on_min generalizing m with
  | empty => simpa using h0 m
  | insert a s ha ih =>
    rw [Finset.sum_insert fun h ↦ lt_irrefl a (ha a h)]
    exact hanti (ht a (Finset.mem_insert_self a s))
      (hN a (Set.add_mem_add (he a) (ih fun i hi ↦ ha i hi)))

variable [TopologicalSpace G]

/-- If `N (n + 1) + N (n + 1) ⊆ N n`, `0 ∈ N n` and `e n ∈ N (n + 1)`, then any sum of `e`
lies in the closure of `N 0`. -/
theorem HasSum.mem_closure_of_add_subset {N : ℕ → Set G} (h0 : ∀ n, (0 : G) ∈ N n)
    (hN : ∀ n, N (n + 1) + N (n + 1) ⊆ N n) {e : ℕ → G} (he : ∀ n, e n ∈ N (n + 1)) {x : G}
    (hx : HasSum e x) : x ∈ closure (N 0) :=
  mem_closure_of_tendsto hx (Eventually.of_forall fun _ ↦
    Finset.sum_mem_of_add_subset h0 hN he fun _ _ ↦ Nat.zero_le _)

end Halving

section Summable

variable {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]

/-- In a complete group, a series with `e n ∈ N (n + 1)` converges, where `N` is a halving
sequence of sets which is cofinal in the neighbourhoods of `0`. -/
theorem summable_of_add_subset {N : ℕ → Set G} (h0 : ∀ n, (0 : G) ∈ N n)
    (hN : ∀ n, N (n + 1) + N (n + 1) ⊆ N n) (hbasis : ∀ V ∈ 𝓝 (0 : G), ∃ n, N n ⊆ V)
    {e : ℕ → G} (he : ∀ n, e n ∈ N (n + 1)) : Summable e := by
  rw [summable_iff_vanishing]
  intro V hV
  obtain ⟨n, hn⟩ := hbasis V hV
  refine ⟨Finset.range n, fun t ht ↦ hn (Finset.sum_mem_of_add_subset h0 hN he fun i hi ↦ ?_)⟩
  by_contra h
  exact Finset.disjoint_left.1 ht hi (Finset.mem_range.2 (not_le.1 h))

end Summable

section Lift

variable {E F : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [FirstCountableTopology E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T2Space F]

/-- A halving sequence of neighbourhoods of `0`, cofinal in `𝓝 0`, starting inside `W`. -/
theorem exists_add_subset_basis_nhds_zero {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ N : ℕ → Set E, (∀ n, N n ∈ 𝓝 (0 : E)) ∧ (∀ n, N (n + 1) + N (n + 1) ⊆ N n) ∧
      N 0 ⊆ W ∧ (∀ V ∈ 𝓝 (0 : E), ∃ n, N n ⊆ V) ∧ Antitone N := by
  obtain ⟨N₀, hN₀basis, hN₀⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero E
  obtain ⟨m₀, -, hm₀⟩ := hN₀basis.1.mem_iff.1 hW
  refine ⟨fun n ↦ N₀ (n + m₀), fun n ↦ hN₀basis.1.mem_of_mem trivial, fun n ↦ ?_,
    by simpa using hm₀, fun V hV ↦ ?_, fun a b hab ↦ hN₀basis.2 (by omega)⟩
  · simpa only [Nat.add_right_comm n 1 m₀] using hN₀ (n + m₀)
  · obtain ⟨i, -, hi⟩ := hN₀basis.1.mem_iff.1 hV
    exact ⟨i, (hN₀basis.2 (by omega : i ≤ i + m₀)).trans hi⟩

/-- **Lifting totally bounded sets.** Let `u : E → F` be a continuous surjective additive map
between commutative topological groups which maps neighbourhoods of `0` to neighbourhoods of `0`,
with `E` complete and first countable and `F` Hausdorff. Then every totally bounded `K ⊆ F`
admits a lift `ℓ` with `ℓ '' K` totally bounded, and, for any neighbourhood `W` of `0` in `E`,
with values in `Φ + W` for some finite `Φ`. -/
theorem exists_lift_of_totallyBounded {M : Type*} [FunLike M E F] [AddMonoidHomClass M E F]
    [CompleteSpace E] (u : M) (hu : Continuous u) (hsurj : Function.Surjective u)
    (hopen : ∀ W ∈ 𝓝 (0 : E), u '' W ∈ 𝓝 (0 : F)) {K : Set F} (hK : TotallyBounded K)
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ Φ : Set E, Φ.Finite ∧ ∃ ℓ : F → E, (∀ k ∈ K, u (ℓ k) = k) ∧ TotallyBounded (ℓ '' K) ∧
      ∀ k ∈ K, ℓ k ∈ Φ + W := by
  obtain ⟨N, hNnhds, hN, hNW, hNbasis, hanti⟩ := exists_add_subset_basis_nhds_zero hW
  have h0 : ∀ n, (0 : E) ∈ N n := fun n ↦ mem_of_mem_nhds (hNnhds n)
  -- the neighbourhoods `V n` of `0` in `F` into which lifting is controlled
  let V : ℕ → Set F := fun n ↦ u '' N (n + 2)
  have hV : ∀ n, V n ∈ 𝓝 (0 : F) := fun n ↦ hopen _ (hNnhds _)
  have hVsmall : ∀ Y ∈ 𝓝 (0 : F), ∀ᶠ n in atTop, V n ⊆ Y := by
    intro Y hY
    have : (u : E → F) ⁻¹' Y ∈ 𝓝 (0 : E) :=
      hu.continuousAt.preimage_mem_nhds (by simpa using hY)
    obtain ⟨n, hn⟩ := hNbasis _ this
    filter_upwards [eventually_ge_atTop n] with m hm
    rintro _ ⟨x, hx, rfl⟩
    exact hn (hanti (by omega : n ≤ m + 2) hx)
  have hA : ∀ n, ∃ A ∈ 𝓝 (0 : F), ∀ a ∈ A, ∀ b ∈ A, a - b ∈ V n := by
    intro n
    obtain ⟨A, hA, hAV⟩ := exists_nhds_zero_half (hV n)
    refine ⟨A ∩ -A, inter_mem hA (neg_mem_nhds_zero F hA), fun a ha b hb ↦ ?_⟩
    rw [sub_eq_add_neg]
    exact hAV a ha.1 (-b) hb.2
  choose A hA hAV using hA
  have hAV' : ∀ n, A n ⊆ V n := fun n a ha ↦ by
    simpa using hAV n a ha 0 (mem_of_mem_nhds (hA n))
  let B : ℕ → Set F := fun n ↦ A n ∩ A (n - 1)
  have hcov := fun n ↦ (totallyBounded_iff_subset_finite_iUnion_nhds_zero.1 hK) (B n)
    (inter_mem (hA n) (hA (n - 1)))
  choose T hTfin hTcov using hcov
  have hτ : ∀ n k, ∃ τ, k ∈ K → τ ∈ T n ∧ k - τ ∈ B n := by
    intro n k
    by_cases hk : k ∈ K
    · obtain ⟨y, hy, hky⟩ := mem_iUnion₂.1 (hTcov n hk)
      obtain ⟨b, hb, rfl⟩ := mem_vadd_set.1 hky
      exact ⟨y, fun _ ↦ ⟨hy, by simpa using hb⟩⟩
    · exact ⟨0, fun h ↦ absurd h hk⟩
  choose τ hτ using hτ
  have hlift : ∀ n (d : F), ∃ e : E, d ∈ V n → e ∈ N (n + 2) ∧ u e = d := by
    intro n d
    by_cases hd : d ∈ V n
    · obtain ⟨e, he, rfl⟩ := hd
      exact ⟨e, fun _ ↦ ⟨he, rfl⟩⟩
    · exact ⟨0, fun h ↦ absurd h hd⟩
  choose lift hlift using hlift
  choose lift0 hlift0 using hsurj
  let e : F → ℕ → E := fun k n ↦ lift n (τ (n + 1) k - τ n k)
  have hd : ∀ k ∈ K, ∀ n, τ (n + 1) k - τ n k ∈ V n := by
    intro k hk n
    have h1 := (hτ n k hk).2
    have h2 := (hτ (n + 1) k hk).2
    simpa [sub_sub_sub_cancel_left] using hAV n _ h1.1 _ h2.2
  have he_mem : ∀ k ∈ K, ∀ n, e k n ∈ N (n + 2) := fun k hk n ↦ (hlift n _ (hd k hk n)).1
  have he_u : ∀ k ∈ K, ∀ n, u (e k n) = τ (n + 1) k - τ n k :=
    fun k hk n ↦ (hlift n _ (hd k hk n)).2
  have hsum : ∀ k ∈ K, Summable (e k) := fun k hk ↦
    summable_of_add_subset h0 hN hNbasis fun n ↦ hanti (by omega) (he_mem k hk n)
  -- the tail of the lifted series from index `m` lies in `N m`
  have htail : ∀ k ∈ K, ∀ m, (∑' n, e k n) - ∑ n ∈ Finset.range m, e k n ∈ N m := by
    intro k hk m
    have hs : HasSum (fun n ↦ e k (n + m)) ((∑' n, e k n) - ∑ n ∈ Finset.range m, e k n) :=
      (hasSum_nat_add_iff' m).2 (hsum k hk).hasSum
    have hcl := hs.mem_closure_of_add_subset (N := fun n ↦ N (n + m + 1))
      (fun n ↦ h0 _) (fun n ↦ by
        simpa only [show n + 1 + m + 1 = n + m + 1 + 1 by omega] using hN (n + m + 1))
      (fun n ↦ by simpa only [show n + 1 + m + 1 = n + m + 2 by omega] using he_mem k hk (n + m))
    exact (closure_subset_add_self_of_mem_nhds_zero (hNnhds _)).trans (hN m) (by simpa using hcl)
  have hτlim : ∀ k ∈ K, Tendsto (fun m ↦ τ m k) atTop (𝓝 k) := by
    intro k hk
    have : Tendsto (fun m ↦ k - τ m k) atTop (𝓝 0) := by
      refine tendsto_def.2 fun Y hY ↦ ?_
      filter_upwards [hVsmall Y hY] with m hm
      exact hm (hAV' m (hτ m k hk).2.1)
    simpa using (tendsto_const_nhds (x := k)).sub this
  let ℓ : F → E := fun k ↦ lift0 (τ 0 k) + ∑' n, e k n
  refine ⟨lift0 '' T 0, (hTfin 0).image _, ℓ, fun k hk ↦ ?_, ?_, fun k hk ↦ ?_⟩
  · have h1 : HasSum (fun n ↦ u (e k n)) (u (∑' n, e k n)) := (hsum k hk).hasSum.map u hu
    have h2 : Tendsto (fun m ↦ ∑ n ∈ Finset.range m, u (e k n)) atTop (𝓝 (k - τ 0 k)) := by
      simp_rw [he_u k hk, Finset.sum_range_sub (fun n ↦ τ n k)]
      exact (hτlim k hk).sub_const _
    have := tendsto_nhds_unique h1.tendsto_sum_nat h2
    simp [ℓ, map_add, hlift0, this]
  · rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
    intro U hU
    obtain ⟨m, hm⟩ := hNbasis U hU
    let P : ℕ → F → E := fun m k ↦ lift0 (τ 0 k) + ∑ n ∈ Finset.range m, e k n
    have hPfin : ∀ m, (P m '' K).Finite := by
      intro m
      induction m with
      | zero =>
        refine ((hTfin 0).image lift0).subset ?_
        rintro _ ⟨k, hk, rfl⟩
        exact ⟨τ 0 k, (hτ 0 k hk).1, by simp [P]⟩
      | succ m ih =>
        refine (Set.Finite.add ih
          (((hTfin (m + 1)).sub (hTfin m)).image (lift m))).subset ?_
        rintro _ ⟨k, hk, rfl⟩
        have : P (m + 1) k = P m k + lift m (τ (m + 1) k - τ m k) := by
          simp [P, e, Finset.sum_range_succ, add_assoc]
        rw [this]
        exact Set.add_mem_add ⟨k, hk, rfl⟩ ⟨τ (m + 1) k - τ m k,
          Set.sub_mem_sub (hτ (m + 1) k hk).1 (hτ m k hk).1, rfl⟩
    refine ⟨P m '' K, hPfin m, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    refine mem_iUnion₂.2 ⟨P m k, ⟨k, hk, rfl⟩, mem_vadd_set.2 ⟨_, hm (htail k hk m), ?_⟩⟩
    simp only [vadd_eq_add, P, ℓ]
    abel
  · refine Set.add_mem_add ⟨τ 0 k, (hτ 0 k hk).1, rfl⟩ (hNW ?_)
    simpa using htail k hk 0

end Lift

end
