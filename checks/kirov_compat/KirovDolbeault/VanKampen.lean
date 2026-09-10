/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.SphereSimplyConnected
import Mathlib.Topology.Subpath
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Two-open Seifert–van Kampen for `π₁`, and `S²` simply connected (unconditional)

This file discharges the single remaining hypothesis of `Jacobians/SphereSimplyConnected.lean`:
the abstract **two-open van Kampen** statement `TwoOpenVanKampen`.  Combined with the (already
proven, complete) side-conditions there it yields the **unconditional**

```
instance : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
```

so every downstream consumer of `#1b` picks it up with no remaining input.

## The statement

`TwoOpenVanKampen` says: a path-connected space `Z` covered by two open simply-connected sets
`U`, `V` with path-connected intersection `U ∩ V` is simply connected.  Mathlib has no
Seifert–van Kampen for `π₁`, so this is built here from scratch.

## The proof

By `simply_connected_iff_loops_nullhomotopic` it suffices, given `PathConnectedSpace Z`, to
nullhomotope an arbitrary loop `γ : Path x x`.

1. **Lebesgue subdivision.**  `{γ⁻¹ U, γ⁻¹ V}` is an open cover of the compact interval `I`; the
   Lebesgue number lemma gives `n` so that each subinterval `[k/(n+1), (k+1)/(n+1)]` maps into
   `U` or into `V`.  Writing `tᵢ = i/(n+1)`, the subpaths `γₖ := γ.subpath (t k) (t (k+1))` each
   lie in one chart, and `Path.Homotopic.concat_subpath` identifies their concatenation with `γ`.

2. **Spokes through the overlap.**  Pick a basepoint `o ∈ U ∩ V`.  For each junction `qₖ = γ(tₖ)`,
   path-connectivity of the relevant chart provides a spoke `cₖ` from `o` to `qₖ` lying in that
   chart; we arrange `cₖ` to lie in `U ∩ V` whenever `qₖ` is an *interior* junction (so that the
   adjacent conjugated loops stay inside their charts).

3. **Per-arc nullhomotopy.**  Each conjugated loop `Lₖ := cₖ · γₖ · c_{k+1}⁻¹` lies entirely in a
   single chart (`U` or `V`), hence is nullhomotopic there; transported to `Z` it is nullhomotopic
   (`isSimplyConnected_iff_exists_homotopy_refl_forall_mem`).

4. **Telescoping.**  In the fundamental groupoid quotient the product
   `L₀ ≫ L₁ ≫ ⋯ ≫ Lₙ` telescopes (the `c_{k}⁻¹ ≫ c_{k}` cancel) to `c₀ ≫ ⟦γ⟧ ≫ c_{n}⁻¹`; with
   `c₀` and `c_{last}` the identity and each `Lₖ` the identity, this collapses `⟦γ⟧` to the
   identity.

## References

* tom Dieck, *Algebraic Topology*, §2.7–2.8 (Seifert–van Kampen; the two-open corollary).
* Forster, *Lectures on Riemann Surfaces*, §1.
-/

noncomputable section

open Set unitInterval Path Topology Fin

namespace Jacobians.RiemannSphere.VanKampen

universe u

variable {Z : Type u} [TopologicalSpace Z]

/-! ### The telescoping core (fundamental-groupoid quotient algebra)

Everything here is pure algebra in `Path.Homotopic.Quotient`: spokes `c` from a base point to the
junctions `q`, arcs `F` between consecutive junctions, and the hypothesis that every conjugated
loop is nullhomotopic.  The conclusion is that the (quotient class of the) concatenation of arcs,
conjugated by the two end spokes, is the identity. -/

/-- Local abbreviation for the fundamental-groupoid quotient (homotopy classes of paths). -/
local notation "Q" => Path.Homotopic.Quotient

open Path.Homotopic.Quotient (mk symm trans refl) in
/-- **Telescoping.**  Given junctions `q`, spokes `c k : ⟦o ⤳ q k⟧`, arcs `F`, and the hypothesis
that each conjugated loop `c kᵢ · F k · c kᵢ₊₁⁻¹` is the identity at `o`, the concatenation of the
arcs, conjugated by the two end spokes, is the identity at `o`.  Proved by induction on the number
of arcs, cancelling the inner `c⁻¹ · c` pairs. -/
theorem telescope {o : Z} :
    ∀ {n : ℕ} (q : Fin (n + 1) → Z) (c : (k : Fin (n + 1)) → Q o (q k))
      (F : (k : Fin n) → Path (q k.castSucc) (q k.succ)),
      (∀ k : Fin n,
        trans (c k.castSucc) (trans (mk (F k)) (symm (c k.succ))) = Path.Homotopic.Quotient.refl o) →
      trans (c 0) (trans (mk (Path.concat q F)) (symm (c (last n)))) = Path.Homotopic.Quotient.refl o := by
  intro n
  induction n with
  | zero =>
    intro q c F _
    -- `concat` of zero arcs is `refl (q 0)`; `last 0 = 0`, so the goal is `c 0 · c 0⁻¹ = refl`.
    show trans (c 0) (trans (mk (Path.concat q F)) (symm (c (last 0)))) =
      Path.Homotopic.Quotient.refl o
    rw [Path.concat_zero]
    show trans (c 0) (trans (mk (Path.refl (q 0))) (symm (c 0))) =
      Path.Homotopic.Quotient.refl o
    rw [Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_symm]
  | succ n ih =>
    intro q c F hloop
    -- Peel the last arc.
    rw [Path.concat_succ]
    -- Inner data: junctions/spokes/arcs of the first `n` arcs.
    set q' : Fin (n + 1) → Z := q ∘ Fin.castSucc with hq'
    set c' : (k : Fin (n + 1)) → Q o (q' k) := fun k => c k.castSucc with hc'
    set F' : (k : Fin n) → Path (q' k.castSucc) (q' k.succ) := fun k => F k.castSucc with hF'
    -- IH on the inner data; `c' (last n) = c (last n).castSucc` definitionally.
    have IH : trans (c 0) (trans (mk (Path.concat q' F'))
        (symm (c (last n).castSucc))) = Path.Homotopic.Quotient.refl o :=
      ih q' c' F' (fun k => hloop k.castSucc)
    -- `hloop` at the last arc; `last (n+1) = (last n).succ` definitionally.
    have last_eq := hloop (last n)
    -- Reassociate and cancel the inner `c (last n).castSucc⁻¹ · c (last n).castSucc`, exhibiting
    -- the concatenation as the product of `IH`'s loop and `last_eq`'s loop.
    have key : trans (c 0) (trans (trans (mk (Path.concat q' F')) (mk (F (last n))))
          (symm (c (last n).succ))) =
        trans (trans (c 0) (trans (mk (Path.concat q' F')) (symm (c (last n).castSucc))))
          (trans (c (last n).castSucc)
            (trans (mk (F (last n))) (symm (c (last n).succ)))) := by
      -- Fully right-associate, then `grind` cancels the inner `c⁻¹ · c`.
      simp only [Path.Homotopic.Quotient.trans_assoc]
      grind
    -- `last (n+1) = (last n).succ` and `mk (A.trans B) = trans (mk A) (mk B)` are both `rfl`,
    -- so this `show` is definitionally the goal.
    show trans (c 0) (trans (trans (mk (Path.concat q' F')) (mk (F (last n))))
      (symm (c (last n).succ))) = Path.Homotopic.Quotient.refl o
    rw [key, IH, last_eq, Path.Homotopic.Quotient.refl_trans]

open Path.Homotopic.Quotient (mk symm trans refl) in
/-- Groupoid cancellation: from `a · (x · b⁻¹) = id` conclude `x = a⁻¹ · b`.  (Conjugation by the
end spokes is undone.) -/
theorem cancel_conj {o p r : Z} (a : Q o p) (x : Q p r) (b : Q o r)
    (h : trans a (trans x (symm b)) = Path.Homotopic.Quotient.refl o) :
    x = trans (symm a) b := by
  have h2 : trans (trans a (trans x (symm b))) b = trans (Path.Homotopic.Quotient.refl o) b := by
    rw [h]
  -- LHS of `h2` simplifies to `a · x`; RHS to `b`.  Hence `a · x = b`, so `x = a⁻¹ · b`.
  rw [Path.Homotopic.Quotient.refl_trans] at h2
  have h3 : trans a x = b := by
    rw [← h2]; grind
  rw [← h3, ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

open Path.Homotopic.Quotient (mk symm trans refl) in
/-- **Loop-chain nullhomotopy** (Path level).  A loop presented as the concatenation of arcs `F`
with junctions `q` (both ends at `o`, via `h0`, `hl`), equipped with spokes `spoke j : o ⤳ q j`
whose two ends are the constant path (retyped) and for which every conjugated loop
`spoke kᵢ · F k · spoke kᵢ₊₁⁻¹` is nullhomotopic, is itself nullhomotopic.  This re-expresses
`telescope` via `mk`, isolating the homotopy-theory input (`hloop`) from the groupoid algebra. -/
theorem concat_nullhomotopic {o : Z} {n : ℕ} (q : Fin (n + 1) → Z)
    (F : (k : Fin n) → Path (q k.castSucc) (q k.succ)) (h0 : q 0 = o) (hl : q (last n) = o)
    (spoke : (j : Fin (n + 1)) → Path o (q j))
    (hs0 : spoke 0 = (Path.refl o).cast rfl h0)
    (hsl : spoke (last n) = (Path.refl o).cast rfl hl)
    (hloop : ∀ k : Fin n,
      Path.Homotopic ((spoke k.castSucc).trans ((F k).trans (spoke k.succ).symm))
        (Path.refl o)) :
    Path.Homotopic (Path.concat q F) ((Path.refl o).cast h0 hl) := by
  -- Per-arc hypothesis, lifted to the quotient.
  have hper : ∀ k : Fin n,
      trans (mk (spoke k.castSucc)) (trans (mk (F k)) (symm (mk (spoke k.succ)))) =
        Path.Homotopic.Quotient.refl o := by
    intro k
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.eq]
    exact hloop k
  -- `telescope` gives `(mk s₀) · (mk concat · (mk sₗ)⁻¹) = id`; cancel the conjugation.
  have hT := telescope q (fun j => mk (spoke j)) F hper
  have hcancel := cancel_conj (mk (spoke 0)) (mk (Path.concat q F)) (mk (spoke (last n))) hT
  -- The end spokes are the constant path (retyped), so `s₀⁻¹ · sₗ` is the constant path.
  have hAeq : (spoke 0).symm = (Path.refl o).cast h0 rfl := by
    rw [hs0, ← Path.cast_symm, Path.refl_symm]
  have hABeq : ((spoke 0).symm).trans (spoke (last n)) = (Path.refl o).cast h0 hl := by
    rw [hAeq, hsl, ← Path.cast_trans, refl_trans_refl]
  -- Assemble: `mk concat = (mk s₀)⁻¹ · mk sₗ = mk (s₀⁻¹ · sₗ) = mk ((refl o).cast h0 hl)`.
  rw [← Path.Homotopic.Quotient.eq, hcancel, ← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_trans, hABeq]

/-! ### Topological inputs: per-arc nullhomotopy and spokes -/

/-- A loop lying entirely in a simply-connected set `W` is nullhomotopic in the ambient space. -/
theorem nullhomotopic_of_mem_isSimplyConnected {W : Set Z} (hW : IsSimplyConnected W) {o : Z}
    (L : Path o o) (hL : ∀ t, L t ∈ W) : Path.Homotopic L (Path.refl o) := by
  obtain ⟨_, hforall⟩ := isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hW
  obtain ⟨F, _⟩ := hforall o L hL
  exact ⟨F⟩

/-- **Lebesgue subdivision of a loop.**  For a continuous `γ : I → Z` and an open cover `{U, V}`
of `Z`, there is a uniform subdivision `t k = k/(n+1)` of `[0,1]` (so `t 0 = 0`, `t (last n) = 1`)
such that each closed piece `γ '' [t kᵢ, t kᵢ₊₁]` lies entirely in `U` or in `V`. -/
theorem exists_lebesgue_subdivision {γ : I → Z} (hγ : Continuous γ) {U V : Set Z}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (last n) = 1 ∧
      ∀ k : Fin n, (γ '' (Set.uIcc (t k.castSucc) (t k.succ)) ⊆ U) ∨
        (γ '' (Set.uIcc (t k.castSucc) (t k.succ)) ⊆ V) := by
  -- The two preimages form an open cover of the compact interval `I`.
  set c : Bool → Set I := fun b => if b then γ ⁻¹' U else γ ⁻¹' V with hc
  have hcopen : ∀ b, IsOpen (c b) := by
    intro b; cases b <;> simp [hc, hU.preimage hγ, hV.preimage hγ]
  have hccov : (Set.univ : Set I) ⊆ ⋃ b, c b := by
    intro s _
    have : γ s ∈ U ∪ V := hcov ▸ Set.mem_univ _
    rcases this with h | h
    · exact Set.mem_iUnion.2 ⟨true, by simp [hc, h]⟩
    · exact Set.mem_iUnion.2 ⟨false, by simp [hc, h]⟩
  -- Lebesgue number `δ`.
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hcopen hccov
  -- Choose `N = m+1` arcs with width `1/(m+1) < δ`.
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, fun k => projIcc 0 1 zero_le_one ((k : ℝ) / (m + 1)), ?_, ?_, ?_⟩
  · -- `t 0 = projIcc … (0/(m+1)) = 0`.
    simp
  · -- `t (last (m+1)) = projIcc … ((m+1)/(m+1)) = 1`.
    have hval : (((last (m + 1) : Fin (m + 2)) : ℕ) : ℝ) / (m + 1) = 1 := by
      rw [Fin.val_last]; push_cast; field_simp
    simp only
    rw [hval, Set.projIcc_right]; rfl
  · -- Per-arc: the closed piece lies in a single chart.
    intro k
    set N : ℝ := (m : ℝ) + 1 with hN
    have hNpos : 0 < N := by positivity
    -- General value formula for the subdivision points when the argument is in `[0,1]`.
    have hval_of : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        ((projIcc (0 : ℝ) 1 zero_le_one x : ℝ)) = x := by
      intro x h1 h2
      rw [Set.coe_projIcc, min_eq_right h2, max_eq_right h1]
    -- Numerator inequalities as naturals: `k ≤ k+1 ≤ m+1`.
    have hk_succ : ((k.castSucc : Fin (m + 2)) : ℕ) ≤ ((k.succ : Fin (m + 2)) : ℕ) := by
      rw [Fin.val_castSucc, Fin.val_succ]; omega
    have hk_top : ((k.succ : Fin (m + 2)) : ℕ) ≤ m + 1 := by
      rw [Fin.val_succ]; have := k.isLt; omega
    -- Endpoint reals and their bounds.
    have hcs0 : (0 : ℝ) ≤ (k.castSucc : ℝ) / N := by positivity
    have hsucc1 : (k.succ : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos, hN]; exact_mod_cast hk_top
    have hkle : (k.castSucc : ℝ) / N ≤ (k.succ : ℝ) / N := by gcongr
    have hcs1 : (k.castSucc : ℝ) / N ≤ 1 := le_trans hkle hsucc1
    have hsucc0 : (0 : ℝ) ≤ (k.succ : ℝ) / N := by positivity
    -- The two subdivision points and their order.
    set a : I := projIcc (0 : ℝ) 1 zero_le_one ((k.castSucc : ℝ) / N) with ha
    set b : I := projIcc (0 : ℝ) 1 zero_le_one ((k.succ : ℝ) / N) with hb
    have hab : a ≤ b := by
      rw [ha, hb, ← Subtype.coe_le_coe, hval_of _ hcs0 hcs1, hval_of _ hsucc0 hsucc1]; exact hkle
    -- `uIcc a b = Icc a b`.
    have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
    -- Lebesgue ball around `a` lands in one chart `c i`.
    obtain ⟨i, hi⟩ := hball a (Set.mem_univ a)
    -- Every `s ∈ Icc a b` is within `δ` of `a`, hence in `c i`.
    have hsub : Set.Icc a b ⊆ c i := by
      intro s hs
      apply hi
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by
        rw [sub_nonneg]; exact_mod_cast hs.1)]
      have hsb : (s : ℝ) ≤ (b : ℝ) := by exact_mod_cast hs.2
      have : (b : ℝ) - (a : ℝ) = 1 / N := by
        rw [hval_of _ hcs0 hcs1, hval_of _ hsucc0 hsucc1, div_sub_div_same]
        congr 1; push_cast [Fin.val_castSucc, Fin.val_succ]; ring
      calc (s : ℝ) - (a : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
        _ = 1 / N := this
        _ < δ := by rw [hN] at hm ⊢; exact hm
    -- Translate `Icc a b ⊆ γ⁻¹' (chart)` into `γ '' Icc a b ⊆ chart`.
    rw [huIcc]
    cases i with
    | true =>
      refine Or.inl ?_
      rintro _ ⟨s, hs, rfl⟩
      have := hsub hs; simp only [hc, if_true] at this; exact this
    | false =>
      refine Or.inr ?_
      rintro _ ⟨s, hs, rfl⟩
      have := hsub hs; simp only [hc] at this; exact this

/-! ### The base-point loop nullhomotopy and the abstract corollary -/

open Path.Homotopic.Quotient (mk symm trans refl) in
/-- **Loops at a basepoint in the overlap are nullhomotopic.**  If `Z` is covered by two open
simply-connected sets `U`, `V` with path-connected intersection `U ∩ V`, then every loop based at a
point `o ∈ U ∩ V` is nullhomotopic.  This is the analytic heart: Lebesgue-subdivide the loop into
arcs each inside one chart, connect the junctions to `o` through the appropriate chart (the
*spokes*), nullhomotope each conjugated arc inside its chart, and telescope. -/
theorem loop_at_overlap_nullhomotopic {U V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hUsc : IsSimplyConnected U) (hVsc : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) {o : Z} (hoUV : o ∈ U ∩ V) (γ : Path o o) :
    Path.Homotopic γ (Path.refl o) := by
  -- Lebesgue subdivision into `n` arcs.
  obtain ⟨n, t, ht0, htl, hchart⟩ :=
    exists_lebesgue_subdivision γ.continuous hU hV hcov
  set q : Fin (n + 1) → Z := fun j => γ (t j) with hq
  set F : (k : Fin n) → Path (q k.castSucc) (q k.succ) :=
    fun k => γ.subpath (t k.castSucc) (t k.succ) with hF
  -- Endpoints of the loop.
  have h0 : q 0 = o := by simp [hq, ht0]
  have hl : q (last n) = o := by simp [hq, htl]
  -- `U` and `V` are path-connected (from simply connected); `o` lies in both.
  have hUpc : IsPathConnected U := hUsc.isPathConnected
  have hVpc : IsPathConnected V := hVsc.isPathConnected
  have hoU : o ∈ U := hoUV.1
  have hoV : o ∈ V := hoUV.2
  -- For every junction there is a spoke from `o` to `q j` staying in whichever chart(s) contain
  -- the endpoint `q j`.
  have hspoke_exists : ∀ j : Fin (n + 1), ∃ p : Path o (q j),
      ∀ s, (q j ∈ U → p s ∈ U) ∧ (q j ∈ V → p s ∈ V) := by
    intro j
    have hjcov : q j ∈ U ∪ V := hcov ▸ Set.mem_univ _
    by_cases hjU : q j ∈ U <;> by_cases hjV : q j ∈ V
    · -- `q j ∈ U ∩ V`: route through the overlap.
      obtain ⟨p, hp⟩ := (hUV.joinedIn o hoUV (q j) ⟨hjU, hjV⟩)
      exact ⟨p, fun s => ⟨fun _ => (hp s).1, fun _ => (hp s).2⟩⟩
    · -- `q j ∈ U \ V`: route through `U`.
      obtain ⟨p, hp⟩ := hUpc.joinedIn o hoU (q j) hjU
      exact ⟨p, fun s => ⟨fun _ => hp s, fun h => absurd h hjV⟩⟩
    · -- `q j ∈ V \ U`: route through `V`.
      obtain ⟨p, hp⟩ := hVpc.joinedIn o hoV (q j) hjV
      exact ⟨p, fun s => ⟨fun h => absurd h hjU, fun _ => hp s⟩⟩
    · exact absurd hjcov (by simp [hjU, hjV])
  -- Choose the spokes, overriding the two ends with the constant path.
  classical
  set spoke : (j : Fin (n + 1)) → Path o (q j) := fun j =>
    if hj0 : (j : ℕ) = 0 then (Path.refl o).cast rfl (by
      have : j = 0 := Fin.ext hj0; rw [this]; exact h0)
    else if hjl : (j : ℕ) = n then (Path.refl o).cast rfl (by
      have : j = last n := Fin.ext (by rw [hjl, Fin.val_last]); rw [this]; exact hl)
    else (hspoke_exists j).choose with hspoke
  -- The two ends are the constant path.
  have hs0 : spoke 0 = (Path.refl o).cast rfl h0 := by
    simp only [hspoke, Fin.val_zero, dif_pos]
  have hsl : spoke (last n) = (Path.refl o).cast rfl hl := by
    by_cases hn0 : n = 0
    · -- Degenerate: `last 0 = 0`, so this is the same as `hs0`.
      subst hn0; simp only [hspoke, Fin.val_last, dif_pos]
    · have h1 : ((last n : Fin (n + 1)) : ℕ) ≠ 0 := by rw [Fin.val_last]; omega
      have h2 : ((last n : Fin (n + 1)) : ℕ) = n := Fin.val_last n
      simp only [hspoke, dif_neg h1, dif_pos h2]
  -- The spoke-membership certificate, for all junctions.
  have hcert : ∀ j : Fin (n + 1), ∀ s,
      (q j ∈ U → spoke j s ∈ U) ∧ (q j ∈ V → spoke j s ∈ V) := by
    intro j s
    simp only [hspoke]
    split_ifs with hj0 hjl
    · refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
        · rw [Path.cast_coe, Path.refl_apply]; assumption
    · refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
        · rw [Path.cast_coe, Path.refl_apply]; assumption
    · exact (hspoke_exists j).choose_spec s
  -- Each chart `W k` (`= U` or `V`), with the arc and both spokes inside it.
  have harc : ∀ k : Fin n,
      Path.Homotopic ((spoke k.castSucc).trans ((F k).trans (spoke k.succ).symm))
        (Path.refl o) := by
    intro k
    have hrange : range (F k) = γ '' Set.uIcc (t k.castSucc) (t k.succ) := by
      rw [hF, Path.range_subpath]
    -- A uniform sub-proof given the chart `W` (either `U` or `V`) containing arc `k`.
    have main : ∀ W : Set Z, IsSimplyConnected W → range (F k) ⊆ W →
        (q k.castSucc ∈ W) → (q k.succ ∈ W) →
        (∀ j, q j ∈ W → ∀ s, spoke j s ∈ W) →
        Path.Homotopic ((spoke k.castSucc).trans ((F k).trans (spoke k.succ).symm))
          (Path.refl o) := by
      intro W hWsc hFW hcsW hscW hspokeW
      apply nullhomotopic_of_mem_isSimplyConnected hWsc
      -- The whole conjugated loop lies in `W`.
      have hsub : range ((spoke k.castSucc).trans ((F k).trans (spoke k.succ).symm)) ⊆ W := by
        rw [Path.trans_range, Path.trans_range, Path.symm_range]
        refine Set.union_subset ?_ (Set.union_subset hFW ?_)
        · exact fun x hx => by
            obtain ⟨s, rfl⟩ := hx; exact hspokeW _ hcsW s
        · exact fun x hx => by
            obtain ⟨s, rfl⟩ := hx; exact hspokeW _ hscW s
      exact fun s => hsub (Set.mem_range_self s)
    rcases hchart k with hk | hk
    · exact main U hUsc (hrange ▸ hk) ((hrange ▸ hk) (F k).source_mem_range)
        ((hrange ▸ hk) (F k).target_mem_range) (fun j hj s => (hcert j s).1 hj)
    · exact main V hVsc (hrange ▸ hk) ((hrange ▸ hk) (F k).source_mem_range)
        ((hrange ▸ hk) (F k).target_mem_range) (fun j hj s => (hcert j s).2 hj)
  -- Assemble via `concat_nullhomotopic`: `concat q F ≃ (refl o).cast h0 hl`.
  have hconcat := concat_nullhomotopic q F h0 hl spoke hs0 hsl harc
  -- Relate the concatenation to `γ` via `concat_subpath` (`concat (γ∘t) subpaths = concat q F`).
  have hcs : Path.Homotopic (Path.concat q F) (γ.subpath (t 0) (t (last n))) :=
    Path.Homotopic.concat_subpath γ t
  -- `γ.subpath (t 0) (t last)`, retyped to `Path o o`, is exactly `γ`.
  have hsubγ : (γ.subpath (t 0) (t (last n))).cast h0.symm hl.symm = γ := by
    ext s
    rw [Path.cast_coe]
    show (γ ∘ Icc.convexComb (t 0) (t (last n))) s = γ s
    rw [Function.comp_apply, ht0, htl, Icc.convexComb_zero_one]
  -- The doubly-cast constant path is the constant path.
  have hcastrefl : ((Path.refl o).cast h0 hl).cast h0.symm hl.symm = Path.refl o := by
    ext s; rw [Path.cast_coe, Path.cast_coe]
  -- Combine: `γ.subpath (t 0)(t last) ≃ (refl o).cast h0 hl`; strip casts to get `γ ≃ refl o`.
  have hcombined : Path.Homotopic (γ.subpath (t 0) (t (last n))) ((Path.refl o).cast h0 hl) :=
    hcs.symm.trans hconcat
  have hstripped := hcombined.pathCast h0.symm hl.symm
  rwa [hsubγ, hcastrefl] at hstripped

open Path.Homotopic.Quotient (mk symm trans refl) in
/-- **Two-open van Kampen.**  A path-connected space that is the union of two open simply-connected
sets with path-connected intersection is simply connected.  (This is exactly the abstract engine
`Jacobians.RiemannSphere.TwoOpenVanKampen`.) -/
theorem twoOpenVanKampen_holds : Jacobians.RiemannSphere.TwoOpenVanKampen := by
  intro Z _ _ U V hU hV hcov hUsc hVsc hUV
  -- It suffices that every loop is nullhomotopic.
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  -- Base point in the overlap.
  obtain ⟨o, hoUV⟩ := hUV.nonempty
  -- Connect `o` to the loop's base point `x` (path-connected space).
  obtain ⟨δ⟩ : Joined o x := PathConnectedSpace.joined o x
  -- The conjugate `δ · γ · δ⁻¹` is a loop at `o`, hence nullhomotopic.
  have hconj : Path.Homotopic (δ.trans (γ.trans δ.symm)) (Path.refl o) :=
    loop_at_overlap_nullhomotopic hU hV hcov hUsc hVsc hUV hoUV _
  -- Rewrite as a quotient identity and expand into `mk δ · (mk γ · (mk δ)⁻¹) = refl o`.
  rw [← Path.Homotopic.Quotient.eq] at hconj
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_refl] at hconj
  -- Undo the conjugation: `mk γ = (mk δ)⁻¹ · mk δ = refl x`.
  have key := cancel_conj (mk δ) (mk γ) (mk δ) hconj
  rw [Path.Homotopic.Quotient.symm_trans] at key
  rw [← Path.Homotopic.Quotient.eq]
  exact key

/-- **The Euclidean `2`-sphere `S² ⊆ ℝ³` is simply connected** — unconditionally.  Discharges the
last hypothesis of `Jacobians.RiemannSphere.simplyConnectedSpace_sphere_of_vanKampen`. -/
instance : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  Jacobians.RiemannSphere.simplyConnectedSpace_sphere_of_vanKampen twoOpenVanKampen_holds
