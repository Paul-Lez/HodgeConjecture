/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailRR1
import KirovDolbeault.Dolbeault.TailGenusTarget
import KirovDolbeault.Dolbeault.FormRemovableSingularity
import KirovDolbeault.RiemannRochDegree

/-!
# The tail residue pairing and the injectivity half of tail Serre duality (tail tower T5)

Over the T1–T4 substrate (route: `docs/planning/TAILRR_ROUTE.md`): the residue pairing of
`L(K−D)` against the tail `H¹(D)`, in pure full-Laurent-coefficient algebra.

* Part A (planar): `planarCoeff` — the planar mirror of `coeffAt` (full Laurent coefficient,
  honest at every order), with linearity, the order laws, the monomial shift
  (`planarCoeff_monomial_mul`), the strip representation (`stripFun_eq_sub_sum`), and the
  **window product law** `resCoeff_mul_window`:
  `c₋₁(A·B) = ∑_{k ∈ [lo,hi)} c_k(A)·c₋₁₋ₖ(B)` whenever `ord B ≥ −hi` — the single
  computation behind both the well-definedness and the recovery identities of the pairing.
* Part B: `TailPairFrame` — the pair frame: a `CanonicalForm17Data` `(ω₀, K)`, a per-point
  slot family (the chart reads of `ω₀`, of exact order `K p`), and the **pair-frame residue
  theorem** `∑Res(F·ω₀) = 0` (the ONE analytic atom of the tower; everything else here is
  finite Laurent algebra).
* Part C: the pairing `pairingL : L(K−D)/junk →ₗ Dual(H¹(D))` — descends to the quotient by
  `resSum` (well-definedness = the window product law + the atom).
* Part D: **the injectivity half** (`pairingL_injective`, Miranda VI.3.6 flavour):
  `l(K−D) ≤ h¹_t(D)` (`lDim_le_h1TailDim`).

The surjectivity half (recovery + pigeonhole, Miranda VI.3.10) is the remaining
mathematical content — `docs/planning/TAILRR_BLOCKER.md`.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI §3.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians

namespace Dolbeault

/-! ## Part A — the planar full coefficient `planarCoeff` -/

variable {F G A B : ℂ → ℂ} {c : ℂ} {lo hi : ℤ}

/-- **The planar full Laurent coefficient** (the planar mirror of
`MeromorphicFunction.coeffAt`): honest at every order. -/
def planarCoeff (k : ℤ) (F : ℂ → ℂ) (c : ℂ) : ℂ :=
  if meromorphicOrderAt F c = ⊤ then 0
  else fullCoeffFrom F c (min ((meromorphicOrderAt F c).untop₀) k)
    (k - min ((meromorphicOrderAt F c).untop₀) k).toNat

/-- `fullCoeffFrom` at offset `0` is the raw bottom-level read. -/
theorem fullCoeffFrom_offset_zero' (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) :
    fullCoeffFrom F c lo 0 = laurentCoeff lo F c := by
  rw [fullCoeffFrom, stripFun_zero_iter]
  norm_num

/-- A germ-zero function has all planar coefficients `0`. -/
theorem planarCoeff_of_order_eq_top (h : meromorphicOrderAt F c = ⊤) (k : ℤ) :
    planarCoeff k F c = 0 := by
  rw [planarCoeff, if_pos h]

/-- **The level-free bridge** (mirror of `coeffAt_eq_fullCoeffFrom`). -/
theorem planarCoeff_eq_fullCoeffFrom (hF : MeromorphicAt F c) {k lo : ℤ}
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) (hlk : lo ≤ k) :
    planarCoeff k F c = fullCoeffFrom F c lo (k - lo).toNat := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · rw [planarCoeff, if_pos htop]
    have hev : F =ᶠ[𝓝[≠] c] (fun _ => (0 : ℂ)) := meromorphicOrderAt_eq_top_iff.mp htop
    rw [fullCoeffFrom_congr hev lo, fullCoeffFrom_zero_fun]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [planarCoeff, if_neg hne]
    have hun : (meromorphicOrderAt F c).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
    rw [hun]
    refine fullCoeffFrom_level_irrel hF ?_ hlo (min_le_right _ _) hlk
    rw [← hn]
    exact_mod_cast min_le_left n k

/-- `planarCoeff` depends only on the germ. -/
theorem planarCoeff_congr (h : F =ᶠ[𝓝[≠] c] G) (k : ℤ) :
    planarCoeff k F c = planarCoeff k G c := by
  have hord : meromorphicOrderAt F c = meromorphicOrderAt G c := meromorphicOrderAt_congr h
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · rw [planarCoeff, if_pos htop, planarCoeff, if_pos (hord ▸ htop)]
  · rw [planarCoeff, if_neg hne, planarCoeff, if_neg (hord ▸ hne), ← hord,
      fullCoeffFrom_congr h]

@[simp] theorem planarCoeff_zero_fun (k : ℤ) (c : ℂ) :
    planarCoeff k (fun _ => (0 : ℂ)) c = 0 := by
  refine planarCoeff_of_order_eq_top ?_ k
  refine meromorphicOrderAt_eq_top_iff.mpr ?_
  filter_upwards with z
  rfl

/-- **Additivity** — no order hypotheses (mirror of `coeffAt_add`). -/
theorem planarCoeff_add (hF : MeromorphicAt F c) (hG : MeromorphicAt G c) (k : ℤ) :
    planarCoeff k (F + G) c = planarCoeff k F c + planarCoeff k G c := by
  classical
  set lo : ℤ := min (min ((meromorphicOrderAt F c).untop₀)
    ((meromorphicOrderAt G c).untop₀)) k with hlo
  have hlk : lo ≤ k := min_le_right _ _
  have hloF : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c := by
    rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hn]
      have h1 : (meromorphicOrderAt F c).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
      have : lo ≤ n := by
        have := min_le_left (min ((meromorphicOrderAt F c).untop₀)
          ((meromorphicOrderAt G c).untop₀)) k
        omega
      exact_mod_cast this
  have hloG : (lo : WithTop ℤ) ≤ meromorphicOrderAt G c := by
    rcases eq_or_ne (meromorphicOrderAt G c) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hn]
      have h1 : (meromorphicOrderAt G c).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
      have : lo ≤ n := by
        have := min_le_left (min ((meromorphicOrderAt F c).untop₀)
          ((meromorphicOrderAt G c).untop₀)) k
        omega
      exact_mod_cast this
  have hloFG : (lo : WithTop ℤ) ≤ meromorphicOrderAt (F + G) c :=
    le_trans (le_min hloF hloG) (meromorphicOrderAt_add hF hG)
  rw [planarCoeff_eq_fullCoeffFrom hF hloF hlk, planarCoeff_eq_fullCoeffFrom hG hloG hlk,
    planarCoeff_eq_fullCoeffFrom (hF.add hG) hloFG hlk]
  exact fullCoeffFrom_add hF hG hloF hloG _

/-- **ℂ-homogeneity** — no order hypotheses (mirror of `coeffAt_smul`). -/
theorem planarCoeff_smul (s : ℂ) (hF : MeromorphicAt F c) (k : ℤ) :
    planarCoeff k (s • F) c = s * planarCoeff k F c := by
  rcases eq_or_ne s 0 with hs | hs
  · rw [hs, zero_smul, zero_mul]
    rw [show ((0 : ℂ → ℂ)) = (fun _ => (0 : ℂ)) from rfl]
    exact planarCoeff_zero_fun k c
  · set lo : ℤ := min ((meromorphicOrderAt F c).untop₀) k with hlo
    have hlk : lo ≤ k := min_le_right _ _
    have hloF : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c := by
      rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
      · rw [htop]; exact le_top
      · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hn]
        have h1 : (meromorphicOrderAt F c).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
        have : lo ≤ n := by
          have := min_le_left ((meromorphicOrderAt F c).untop₀) k
          omega
        exact_mod_cast this
    have hords : meromorphicOrderAt (s • F) c = meromorphicOrderAt F c :=
      meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hs)
    have hlosF : (lo : WithTop ℤ) ≤ meromorphicOrderAt (s • F) c := by
      rw [hords]; exact hloF
    have hsF : MeromorphicAt (s • F) c := by
      have h1 : MeromorphicAt ((fun _ => s) • F) c :=
        (MeromorphicAt.const s c).smul hF
      exact h1
    rw [planarCoeff_eq_fullCoeffFrom hF hloF hlk,
      planarCoeff_eq_fullCoeffFrom hsF hlosF hlk]
    exact fullCoeffFrom_smul s hF hloF _

/-- Planar coefficients vanish strictly below the order. -/
theorem planarCoeff_eq_zero_of_lt_order {k : ℤ}
    (h : (k : WithTop ℤ) < meromorphicOrderAt F c) (hF : MeromorphicAt F c) :
    planarCoeff k F c = 0 := by
  rw [planarCoeff_eq_fullCoeffFrom hF (le_of_lt h) le_rfl, sub_self, Int.toNat_zero,
    fullCoeffFrom_offset_zero']
  exact (laurentCoeff_eq_zero_iff hF (le_of_lt h)).mpr h

/-- The leading planar coefficient is nonzero at finite order. -/
theorem planarCoeff_leading_ne_zero {n : ℤ} (hF : MeromorphicAt F c)
    (hn : meromorphicOrderAt F c = (n : WithTop ℤ)) :
    planarCoeff n F c ≠ 0 := by
  rw [planarCoeff_eq_fullCoeffFrom hF (le_of_eq hn.symm) le_rfl, sub_self, Int.toNat_zero,
    fullCoeffFrom_offset_zero']
  intro h0
  have := (laurentCoeff_eq_zero_iff hF (le_of_eq hn.symm)).mp h0
  rw [hn] at this
  exact lt_irrefl _ this

/-- **The order law (iff form)**, planar (mirror of `orderW_ge_iff_coeffAt_vanish`). -/
theorem order_ge_iff_planarCoeff_vanish (hF : MeromorphicAt F c) (m : ℤ) :
    ((m : WithTop ℤ) ≤ meromorphicOrderAt F c) ↔ ∀ k : ℤ, k < m → planarCoeff k F c = 0 := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · constructor
    · intro _ k _
      exact planarCoeff_of_order_eq_top htop k
    · intro _
      rw [htop]
      exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    constructor
    · intro hord k hk
      refine planarCoeff_eq_zero_of_lt_order ?_ hF
      refine lt_of_lt_of_le ?_ hord
      exact_mod_cast hk
    · intro hvan
      by_contra hcon
      have hnm : n < m := by
        rw [← hn] at hcon
        by_contra hge
        exact hcon (by exact_mod_cast (by omega : m ≤ n))
      exact planarCoeff_leading_ne_zero hF hn.symm (hvan n hnm)

/-- All planar coefficients vanish iff the germ is zero. -/
theorem order_eq_top_of_planarCoeff_vanish (hF : MeromorphicAt F c)
    (hvan : ∀ k : ℤ, planarCoeff k F c = 0) :
    meromorphicOrderAt F c = ⊤ := by
  by_contra hne
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  exact planarCoeff_leading_ne_zero hF hn.symm (hvan n)

/-! ### The monomial shift and the strip representation -/

/-- Raw-level monomial shift: `c_k((z−c)^m·F) = c_{k−m}(F)` (de-poles agree off `c`). -/
theorem laurentCoeff_monomial_mul (m k : ℤ) (F : ℂ → ℂ) (c : ℂ) :
    laurentCoeff k (fun z => (z - c) ^ m * F z) c = laurentCoeff (k - m) F c := by
  have heq : dePole k (fun z => (z - c) ^ m * F z) c =ᶠ[𝓝[≠] c] dePole (k - m) F c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    simp only [dePole]
    rw [← mul_assoc, ← zpow_add₀ hzc, show -k + m = -(k - m) from by ring]
  rw [laurentCoeff, laurentCoeff, limUnder, limUnder, Filter.map_congr heq]

/-- Strips commute with monomial multiplication (as germs at `c`). -/
theorem stripFun_monomial_mul (m : ℤ) (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) :
    ∀ j : ℕ, stripFun (fun z => (z - c) ^ m * F z) c (lo + m) j
      =ᶠ[𝓝[≠] c] fun z => (z - c) ^ m * stripFun F c lo j z
  | 0 => by
    filter_upwards with z
    rfl
  | j + 1 => by
    have ih := stripFun_monomial_mul m F c lo j
    have hco : laurentCoeff (lo + m + j) (stripFun (fun z => (z - c) ^ m * F z) c (lo + m) j) c
        = laurentCoeff (lo + j) (stripFun F c lo j) c := by
      rw [laurentCoeff_congr ih, laurentCoeff_monomial_mul,
        show (lo + m + (j : ℤ)) - m = lo + j from by ring]
    filter_upwards [ih, self_mem_nhdsWithin] with z hz hzne
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
    rw [stripFun_succ, stripFun_succ]
    show stripFun (fun z => (z - c) ^ m * F z) c (lo + m) j z
        - _ * (z - c) ^ (lo + m + j)
      = (z - c) ^ m * (stripFun F c lo j z - _ * (z - c) ^ (lo + j))
    rw [hz, hco, show (lo + m + (j : ℤ)) = m + (lo + j) from by ring, zpow_add₀ hzc]
    ring

/-- **The planar monomial shift**: `c_k((z−c)^m·F) = c_{k−m}(F)` at full-coefficient level. -/
theorem planarCoeff_monomial_mul (m k : ℤ) (hF : MeromorphicAt F c) :
    planarCoeff k (fun z => (z - c) ^ m * F z) c = planarCoeff (k - m) F c := by
  have hmono : MeromorphicAt (fun z => (z - c) ^ m) c := meromorphicAt_zpow_self c m
  have hprod : MeromorphicAt (fun z => (z - c) ^ m * F z) c := by
    have := hmono.mul hF
    exact this
  have hordp : meromorphicOrderAt (fun z => (z - c) ^ m * F z) c
      = (m : WithTop ℤ) + meromorphicOrderAt F c := by
    rw [show (fun z => (z - c) ^ m * F z) = (fun z => (z - c) ^ m) * F from rfl,
      meromorphicOrderAt_mul hmono hF, meromorphicOrderAt_zpow_self]
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · rw [planarCoeff_of_order_eq_top (by rw [hordp, htop]; rfl) k,
      planarCoeff_of_order_eq_top htop (k - m)]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    set lo : ℤ := min n (k - m) with hlodef
    have hloF : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
      rw [← hn]
      exact_mod_cast min_le_left n (k - m)
    have hlop : ((lo + m : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (fun z => (z - c) ^ m * F z) c := by
      rw [hordp, ← hn]
      have : lo + m ≤ m + n := by omega
      exact_mod_cast this
    rw [planarCoeff_eq_fullCoeffFrom hF hloF (by omega : lo ≤ k - m),
      planarCoeff_eq_fullCoeffFrom hprod hlop (by omega : lo + m ≤ k)]
    have hsh : fullCoeffFrom (fun z => (z - c) ^ m * F z) c (lo + m) ((k - m) - lo).toNat
        = fullCoeffFrom F c lo ((k - m) - lo).toNat := by
      rw [fullCoeffFrom, fullCoeffFrom, laurentCoeff_congr
        (stripFun_monomial_mul m F c lo ((k - m) - lo).toNat),
        laurentCoeff_monomial_mul]
      congr 1
      ring
    rw [show (k - (lo + m)) = (k - m) - lo from by ring, hsh]

/-- **The strip representation**: the strip is `F` minus its initial Laurent monomials. -/
theorem stripFun_eq_sub_sum (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) :
    ∀ j : ℕ, stripFun F c lo j
      = fun z => F z - ∑ i ∈ Finset.range j, fullCoeffFrom F c lo i * (z - c) ^ (lo + i)
  | 0 => by
    funext z
    simp
  | j + 1 => by
    have ih := stripFun_eq_sub_sum F c lo j
    funext z
    have ihz := congrFun ih z
    have hstep : stripFun F c lo (j + 1) z
        = stripFun F c lo j z
          - laurentCoeff (lo + j) (stripFun F c lo j) c * (z - c) ^ (lo + j) := rfl
    rw [hstep, ihz, Finset.sum_range_succ,
      show laurentCoeff (lo + j) (stripFun F c lo j) c = fullCoeffFrom F c lo j from rfl]
    ring

/-- Finite-sum additivity of a planar coefficient (each summand meromorphic). -/
theorem planarCoeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (k : ℤ) (c : ℂ)
    (hf : ∀ i ∈ s, MeromorphicAt (f i) c) :
    planarCoeff k (fun z => ∑ i ∈ s, f i z) c = ∑ i ∈ s, planarCoeff k (f i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hfa : MeromorphicAt (f a) c := hf a (Finset.mem_insert_self a t)
    have hft : MeromorphicAt (fun z => ∑ i ∈ t, f i z) c :=
      MeromorphicAt.fun_sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsplit : (fun z => ∑ i ∈ insert a t, f i z)
        = f a + fun z => ∑ i ∈ t, f i z := by
      funext z
      simp [Finset.sum_insert ha]
    rw [hsplit, planarCoeff_add hfa hft k, Finset.sum_insert ha,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- **The window product law**: the residue coefficient of a product reads off the window
coefficients of `A` against the shifted coefficients of `B`, provided `B`'s order clears the
window top (`ord B ≥ −hi`).  The single computation behind the pairing's well-definedness. -/
theorem resCoeff_mul_window (hA : MeromorphicAt A c) (hB : MeromorphicAt B c)
    {lo hi : ℤ} (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt A c) (hlohi : lo ≤ hi)
    (hBord : ((-hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B c) :
    planarCoeff (-1) (fun z => A z * B z) c
      = ∑ k ∈ Finset.Ico lo hi, planarCoeff k A c * planarCoeff (-1 - k) B c := by
  classical
  set n : ℕ := (hi - lo).toNat with hndef
  have hrep := stripFun_eq_sub_sum A c lo n
  have hRmero : MeromorphicAt (stripFun A c lo n) c := stripFun_meromorphicAt hA n
  have hRord : ((hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (stripFun A c lo n) c := by
    have := stripFun_order hA hlo n
    have hcast : (lo + (n : ℤ) : ℤ) = hi := by omega
    rwa [hcast] at this
  -- the polynomial part
  set polyB : ℂ → ℂ := fun z =>
    ∑ i ∈ Finset.range n, fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z) with hpolyB
  have hterm_mero : ∀ i ∈ Finset.range n,
      MeromorphicAt (fun z => fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z)) c := by
    intro i _
    have h1 : MeromorphicAt (fun z => (z - c) ^ (lo + i) * B z) c :=
      (meromorphicAt_zpow_self c (lo + i)).mul hB
    have h2 : MeromorphicAt ((fun _ => fullCoeffFrom A c lo i) • fun z =>
        (z - c) ^ (lo + i) * B z) c := (MeromorphicAt.const _ c).smul h1
    exact h2
  have hpolyB_mero : MeromorphicAt polyB c := MeromorphicAt.fun_sum hterm_mero
  have hRB_mero : MeromorphicAt (fun z => stripFun A c lo n z * B z) c := hRmero.mul hB
  -- the split
  have hsplit : (fun z => A z * B z)
      = polyB + fun z => stripFun A c lo n z * B z := by
    funext z
    have hz := congrFun hrep z
    have hS : (∑ i ∈ Finset.range n, fullCoeffFrom A c lo i * (z - c) ^ (lo + i)) * B z
        = ∑ i ∈ Finset.range n, fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    show A z * B z
      = (∑ i ∈ Finset.range n, fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z))
        + stripFun A c lo n z * B z
    rw [hz, ← hS]
    ring
  rw [hsplit, planarCoeff_add hpolyB_mero hRB_mero]
  -- the remainder term vanishes: order `≥ hi + (−hi) = 0 > −1`
  have hRB_zero : planarCoeff (-1) (fun z => stripFun A c lo n z * B z) c = 0 := by
    refine planarCoeff_eq_zero_of_lt_order ?_ hRB_mero
    have hord : meromorphicOrderAt (fun z => stripFun A c lo n z * B z) c
        = meromorphicOrderAt (stripFun A c lo n) c + meromorphicOrderAt B c := by
      rw [show (fun z => stripFun A c lo n z * B z) = stripFun A c lo n * B from rfl,
        meromorphicOrderAt_mul hRmero hB]
    rw [hord]
    have hsum : ((0 : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (stripFun A c lo n) c + meromorphicOrderAt B c := by
      have := add_le_add hRord hBord
      rwa [show ((hi : ℤ) : WithTop ℤ) + ((-hi : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ)
        from by exact_mod_cast (by ring : (hi : ℤ) + (-hi) = 0)] at this
    refine lt_of_lt_of_le ?_ hsum
    exact_mod_cast (by omega : (-1 : ℤ) < 0)
  rw [hRB_zero, add_zero, hpolyB]
  -- the polynomial part: termwise shift
  rw [planarCoeff_finset_sum _ _ _ _ hterm_mero]
  have hterm : ∀ i ∈ Finset.range n,
      planarCoeff (-1) (fun z => fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z)) c
        = planarCoeff (lo + i) A c * planarCoeff (-1 - (lo + i)) B c := by
    intro i hi'
    have h1 : MeromorphicAt (fun z => (z - c) ^ (lo + i) * B z) c :=
      (meromorphicAt_zpow_self c (lo + i)).mul hB
    have hsmul : (fun z => fullCoeffFrom A c lo i * ((z - c) ^ (lo + i) * B z))
        = (fullCoeffFrom A c lo i) • fun z => (z - c) ^ (lo + i) * B z := rfl
    rw [hsmul, planarCoeff_smul _ h1, planarCoeff_monomial_mul _ _ hB]
    congr 1
    have hin : (i : ℤ) < hi - lo := by
      have := Finset.mem_range.mp hi'
      omega
    rw [planarCoeff_eq_fullCoeffFrom hA hlo (by omega : lo ≤ lo + i)]
    congr 1
    omega
  rw [Finset.sum_congr rfl hterm]
  -- reindex `range n ↔ Ico lo hi`
  refine Finset.sum_nbij' (fun i => lo + (i : ℤ)) (fun k => (k - lo).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi'
    have hmem := Finset.mem_range.mp hi'
    have hmem' : (i : ℤ) < hi - lo := by omega
    show lo + (i : ℤ) ∈ Finset.Ico lo hi
    refine Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk
    have := Finset.mem_Ico.mp hk
    show (k - lo).toNat ∈ Finset.range n
    refine Finset.mem_range.mpr ?_
    omega
  · intro i hi'
    have := Finset.mem_range.mp hi'
    show ((lo + (i : ℤ)) - lo).toNat = i
    omega
  · intro k hk
    have := Finset.mem_Ico.mp hk
    show lo + (((k - lo).toNat : ℕ) : ℤ) = k
    omega
  · intro i _
    rfl

/-! ## Part B — the pair frame -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The tail pair frame** (Miranda Ch. VI pair calculus): a canonical-divisor frame
`(ω₀, K)` (`CanonicalForm17Data`), its per-point chart slot family (the local `dz`-reads of
`ω₀`, meromorphic of exact order `K p`), and the **pair-frame residue theorem**
`∑ₚ Res_p(F·ω₀) = 0` — the ONE analytic atom of the tail tower
(`docs/planning/TAILRR_ROUTE.md`).  Everything downstream is finite Laurent algebra. -/
structure TailPairFrame (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The canonical-divisor frame `(ω₀, K = div ω₀)` (Forster §17.4, proven substrate). -/
  data : CanonicalForm17Data X
  /-- The chart read of `ω₀`'s `dz`-coefficient at `p`, in the ambient chart at `p`. -/
  slot : (p : X) → ℂ → ℂ
  /-- Each slot is meromorphic at its chart centre. -/
  slot_mero : ∀ p : X, MeromorphicAt (slot p) ((chartAt (H := ℂ) p) p)
  /-- Each slot has exact order `K p` (the canonical divisor reads the slot orders). -/
  slot_order : ∀ p : X, meromorphicOrderAt (slot p) ((chartAt (H := ℂ) p) p)
    = ((data.K p : ℤ) : WithTop ℤ)
  /-- **The pair-frame residue theorem** `∑ₚ Res_p(F·ω₀) = 0` (Miranda Ch. VI; classically
  by Stokes / the trace to `ℙ¹`).  The single analytic input of the tail tower. -/
  resSum : ∀ F : MeromorphicFunction X,
    ∑ p ∈ F.div.support ∪ data.K.support,
      planarCoeff (-1)
        (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * slot p ζ)
        ((chartAt (H := ℂ) p) p) = 0

namespace TailPairFrame

variable (P : TailPairFrame X)

/-- The per-point residue `Res_p(F·ω₀)`. -/
def resAt (p : X) (F : MeromorphicFunction X) : ℂ :=
  planarCoeff (-1)
    (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
    ((chartAt (H := ℂ) p) p)

/-- The product read is meromorphic at the chart centre. -/
theorem prodRead_mero (p : X) (F : MeromorphicFunction X) :
    MeromorphicAt (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ((chartAt (H := ℂ) p) p) :=
  (F.meromorphic p).mul (P.slot_mero p)

/-- The product-read order: `ord_p(F·ω₀) = ord_p F + K p`. -/
theorem prodRead_order (p : X) (F : MeromorphicFunction X) :
    meromorphicOrderAt (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ((chartAt (H := ℂ) p) p) = F.orderW p + ((P.data.K p : ℤ) : WithTop ℤ) := by
  rw [show (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      = (F.toFun ∘ (chartAt (H := ℂ) p).symm) * P.slot p from rfl,
    meromorphicOrderAt_mul (F.meromorphic p) (P.slot_mero p), P.slot_order p]
  rfl

/-- Off the poles of `F` and the canonical support, the residue vanishes. -/
theorem resAt_eq_zero_of_notMem {p : X} {F : MeromorphicFunction X}
    (hp : p ∉ F.div.support ∪ P.data.K.support) : P.resAt p F = 0 := by
  rw [Finset.mem_union, not_or] at hp
  refine planarCoeff_eq_zero_of_lt_order ?_ (P.prodRead_mero p F)
  rw [P.prodRead_order p F]
  have hK0 : P.data.K p = 0 := Finsupp.notMem_support_iff.mp hp.2
  have hF0 : (0 : WithTop ℤ) ≤ F.orderW p :=
    MeromorphicFunction.orderW_nonneg_of_not_mem_div_support hp.1
  rw [hK0]
  calc ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (-1:ℤ) < 0)
    _ ≤ F.orderW p + (((0 : ℤ) : ℤ) : WithTop ℤ) := by
        rw [show (((0 : ℤ) : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) from rfl, add_zero]
        exact hF0

/-- **The extended residue theorem**: the residue sum vanishes over any finite superset. -/
theorem resSum_ext (F : MeromorphicFunction X) {S : Finset X}
    (hS : F.div.support ∪ P.data.K.support ⊆ S) :
    ∑ p ∈ S, P.resAt p F = 0 := by
  classical
  rw [← Finset.sum_subset hS (fun p _ hp => P.resAt_eq_zero_of_notMem hp)]
  exact P.resSum F

/-! ## Part C — the pairing and its descent to `H¹(D)` -/

/-- **The single-slot pairing** `⟨h, z^k at p⟩ = Res_p(h·z^k·ω₀)` — the `(−1−k)`-th full
coefficient of the slot product. -/
def pairSlot (h : MeromorphicFunction X) (p : X) (k : ℤ) : ℂ :=
  planarCoeff (-1 - k)
    (fun ζ => h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
    ((chartAt (H := ℂ) p) p)

/-- **The pairing functional on ambient tails**: `t ↦ ∑ t_{p,k}·⟨h, z^k at p⟩`. -/
def pairFun (h : MeromorphicFunction X) : GlobalTails X →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun q => LinearMap.toSpanSingleton ℂ ℂ (P.pairSlot h q.1 q.2)

@[simp] theorem pairFun_single (h : MeromorphicFunction X) (q : X × ℤ) (a : ℂ) :
    P.pairFun h (Finsupp.single q a) = a * P.pairSlot h q.1 q.2 := by
  rw [pairFun, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_eq_mul]

theorem pairFun_apply (h : MeromorphicFunction X) (t : GlobalTails X) :
    P.pairFun h t = t.sum fun q a => a * P.pairSlot h q.1 q.2 := by
  rw [pairFun, Finsupp.lsum_apply]
  refine Finsupp.sum_congr fun q _ => ?_
  rw [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The slot-product order bound for `h ∈ L(K−D)`: `ord_p(h·ω₀) ≥ D p`. -/
theorem prodRead_order_ge {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) (p : X) :
    ((D p : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ((chartAt (H := ℂ) p) p) := by
  rw [P.prodRead_order p h]
  have h1 := hh p
  have e1 : (-((P.data.K - D : Divisor X) p) : WithTop ℤ)
      = ((-((P.data.K - D : Divisor X) p) : ℤ) : WithTop ℤ) := rfl
  rw [e1, show (-((P.data.K - D : Divisor X) p) : ℤ) = D p - P.data.K p from by
    rw [Finsupp.sub_apply]; ring] at h1
  cases hord : h.orderW p with
  | top => simp
  | coe n =>
    rw [hord] at h1
    have hn : D p - P.data.K p ≤ n := by exact_mod_cast h1
    have : ((D p : ℤ) : WithTop ℤ) ≤ ((n + P.data.K p : ℤ) : WithTop ℤ) := by
      exact_mod_cast (by omega : D p ≤ n + P.data.K p)
    refine le_trans this (le_of_eq ?_)
    exact_mod_cast rfl

/-- Slots at or above the cut pair to `0` against `L(K−D)`. -/
theorem pairSlot_eq_zero_of_le {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) {p : X} {k : ℤ} (hk : -(D p) ≤ k) :
    P.pairSlot h p k = 0 := by
  refine planarCoeff_eq_zero_of_lt_order ?_ (P.prodRead_mero p h)
  refine lt_of_lt_of_le ?_ (P.prodRead_order_ge hh p)
  exact_mod_cast (by omega : (-1 : ℤ) - k < D p)

/-- **W1**: the pairing kills the upper space. -/
theorem pairFun_eq_zero_of_mem_upperSpace {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) {u : GlobalTails X}
    (hu : u ∈ upperSpace D) :
    P.pairFun h u = 0 := by
  rw [P.pairFun_apply h u, Finsupp.sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hcut : -(D q.1) ≤ q.2 := by
    have := hu hq
    simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq, not_lt] at this
    omega
  rw [P.pairSlot_eq_zero_of_le hh hcut, mul_zero]

/-- The level-`min` helper: the window bottom is a valid level under any order. -/
private theorem coe_min_untop₀_le (o : WithTop ℤ) (m : ℤ) :
    ((min o.untop₀ m : ℤ) : WithTop ℤ) ≤ o ⊔ ((m : ℤ) : WithTop ℤ) := by
  cases o with
  | top => simp
  | coe n =>
    rw [WithTop.untop₀_coe]
    rcases le_total n m with h | h
    · exact le_sup_of_le_left (by exact_mod_cast min_le_left n m)
    · exact le_sup_of_le_right (by exact_mod_cast min_le_right n m)

/-- **W2, per point** (the window product law in pairing form): the windowed tail
coefficients of `f` paired against `h·ω₀` assemble the residue of `f·h·ω₀`. -/
theorem window_pairing_eq_resAt {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) (f : MeromorphicFunction X) (p : X) :
    ∑ k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p)),
      f.coeffAt p k * P.pairSlot h p k
      = P.resAt p (f * h) := by
  classical
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set A : ℂ → ℂ := f.toFun ∘ (chartAt (H := ℂ) p).symm with hA
  set B : ℂ → ℂ := fun ζ => h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ with hB
  have hAm : MeromorphicAt A c := f.meromorphic p
  have hBm : MeromorphicAt B c := P.prodRead_mero p h
  have hlo : ((min ((f.orderW p).untop₀) (-(D p)) : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt A c := by
    cases hord : f.orderW p with
    | top =>
      have : meromorphicOrderAt A c = ⊤ := hord
      rw [this]
      exact le_top
    | coe n =>
      have hAc : meromorphicOrderAt A c = (n : WithTop ℤ) := hord
      rw [hAc, WithTop.untop₀_coe]
      exact_mod_cast min_le_left n (-(D p))
  have hBord : ((-(-(D p)) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B c := by
    rw [neg_neg]
    exact P.prodRead_order_ge hh p
  have hlaw := resCoeff_mul_window hAm hBm hlo (min_le_right _ _) hBord
  -- identify the RHS of the law with the pairing sum
  have hsum : ∑ k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p)),
      planarCoeff k A c * planarCoeff (-1 - k) B c
      = ∑ k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p)),
        f.coeffAt p k * P.pairSlot h p k := rfl
  rw [hsum] at hlaw
  rw [← hlaw]
  -- identify `A·B` with the `(f·h)·ω₀` read
  show planarCoeff (-1) (fun z => A z * B z) c = planarCoeff (-1)
    (fun ζ => (f * h).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ) c
  refine planarCoeff_congr ?_ (-1)
  filter_upwards with ζ
  show A ζ * B ζ = (f * h).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ
  have hmul : (f * h).toFun ((chartAt (H := ℂ) p).symm ζ)
      = f.toFun ((chartAt (H := ℂ) p).symm ζ) * h.toFun ((chartAt (H := ℂ) p).symm ζ) := rfl
  rw [hmul]
  show f.toFun ((chartAt (H := ℂ) p).symm ζ)
      * (h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ) = _
  ring

/-- Off `D` and the poles of `f`, the windowed residue of `f·h·ω₀` vanishes. -/
theorem resAt_mul_eq_zero_of_notMem {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) (f : MeromorphicFunction X) {p : X}
    (hp : p ∉ D.support ∪ f.div.support) :
    P.resAt p (f * h) = 0 := by
  classical
  have hwin := P.window_pairing_eq_resAt hh f p
  rw [Finset.mem_union, not_or] at hp
  have hD0 : D p = 0 := Finsupp.notMem_support_iff.mp hp.1
  have hord : (0 : WithTop ℤ) ≤ f.orderW p :=
    MeromorphicFunction.orderW_nonneg_of_not_mem_div_support hp.2
  have huntop : 0 ≤ (f.orderW p).untop₀ := by
    cases hcase : f.orderW p with
    | top =>
      rw [WithTop.untop₀_top]
    | coe n =>
      rw [WithTop.untop₀_coe]
      rw [hcase] at hord
      exact_mod_cast hord
  have hempty : Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p)) = ∅ := by
    rw [hD0]
    simp only [neg_zero]
    rw [Finset.Ico_eq_empty_iff]
    omega
  rw [hempty, Finset.sum_empty] at hwin
  exact hwin.symm

/-- **W2**: the pairing kills the tail-map image (well-definedness — the residue theorem). -/
theorem pairFun_tailMap_eq_zero {D : Divisor X} {h : MeromorphicFunction X}
    (hh : h ∈ linearSystem (X := X) (P.data.K - D)) (f : MeromorphicFunction X) :
    P.pairFun h (tailMap D f) = 0 := by
  classical
  -- expand the tail map into its windowed singles and apply the per-point law
  have hexp : P.pairFun h (tailMap D f)
      = ∑ p ∈ D.support ∪ f.div.support, P.resAt p (f * h) := by
    rw [show tailMap D f = tailMapFun D f from rfl, tailMapFun, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    rw [Finset.sum_congr rfl fun k _ => P.pairFun_single h (p, k) (f.coeffAt p k)]
    exact P.window_pairing_eq_resAt hh f p
  rw [hexp]
  -- extend to the residue-theorem support and conclude
  set S : Finset X := (D.support ∪ f.div.support)
    ∪ ((f * h).div.support ∪ P.data.K.support) with hS
  rw [Finset.sum_subset (Finset.subset_union_left)
    (fun p _ hp => P.resAt_mul_eq_zero_of_notMem hh f hp)]
  exact P.resSum_ext (f * h) Finset.subset_union_right

/-- **The pairing functional on `H¹(D)`** (descends by W1 + W2). -/
def pairingFunctional {D : Divisor X} (h : ↥(linearSystem (X := X) (P.data.K - D))) :
    H1Tail (X := X) D →ₗ[ℂ] ℂ := by
  refine Submodule.liftQ _ (P.pairFun (h : MeromorphicFunction X)) (sup_le ?_ ?_)
  · rintro - ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    exact P.pairFun_tailMap_eq_zero h.2 f
  · intro u hu
    rw [LinearMap.mem_ker]
    exact P.pairFun_eq_zero_of_mem_upperSpace h.2 hu

@[simp] theorem pairingFunctional_mk {D : Divisor X}
    (h : ↥(linearSystem (X := X) (P.data.K - D))) (t : GlobalTails X) :
    P.pairingFunctional h (Submodule.Quotient.mk t)
      = P.pairFun (h : MeromorphicFunction X) t := rfl

/-! ## Part D — linearity in `h`, junk-invariance, and the injectivity half -/

theorem pairSlot_add (h₁ h₂ : MeromorphicFunction X) (p : X) (k : ℤ) :
    P.pairSlot (h₁ + h₂) p k = P.pairSlot h₁ p k + P.pairSlot h₂ p k := by
  rw [pairSlot, pairSlot, pairSlot,
    show (fun ζ => (h₁ + h₂).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      = (fun ζ => h₁.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
        + (fun ζ => h₂.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ) from by
      funext ζ
      show (h₁.toFun ((chartAt (H := ℂ) p).symm ζ)
          + h₂.toFun ((chartAt (H := ℂ) p).symm ζ)) * P.slot p ζ
        = h₁.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ
          + h₂.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ
      ring]
  exact planarCoeff_add (P.prodRead_mero p h₁) (P.prodRead_mero p h₂) _

theorem pairSlot_smul (a : ℂ) (h : MeromorphicFunction X) (p : X) (k : ℤ) :
    P.pairSlot (a • h) p k = a * P.pairSlot h p k := by
  rw [pairSlot, pairSlot,
    show (fun ζ => (a • h).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      = a • (fun ζ => h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ) from by
      funext ζ
      show (a * h.toFun ((chartAt (H := ℂ) p).symm ζ)) * P.slot p ζ
        = a * (h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ring]
  exact planarCoeff_smul a (P.prodRead_mero p h) _

theorem pairSlot_eq_zero_of_germZero {h : MeromorphicFunction X}
    (hj : h ∈ germZeroSubmodule (X := X)) (p : X) (k : ℤ) :
    P.pairSlot h p k = 0 := by
  have htop : meromorphicOrderAt (h.toFun ∘ (chartAt (H := ℂ) p).symm)
      ((chartAt (H := ℂ) p) p) = ⊤ := hj p
  have hev : (h.toFun ∘ (chartAt (H := ℂ) p).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) p) p)] (fun _ => (0 : ℂ)) :=
    meromorphicOrderAt_eq_top_iff.mp htop
  rw [pairSlot, planarCoeff_congr (G := fun _ => (0 : ℂ)) ?_ _, planarCoeff_zero_fun]
  filter_upwards [hev] with ζ hζ
  show h.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ = 0
  have : h.toFun ((chartAt (H := ℂ) p).symm ζ) = 0 := hζ
  rw [this, zero_mul]

theorem pairFun_add_left (h₁ h₂ : MeromorphicFunction X) (t : GlobalTails X) :
    P.pairFun (h₁ + h₂) t = P.pairFun h₁ t + P.pairFun h₂ t := by
  rw [P.pairFun_apply, P.pairFun_apply, P.pairFun_apply, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun q _ => ?_
  rw [P.pairSlot_add h₁ h₂ q.1 q.2]
  ring

theorem pairFun_smul_left (a : ℂ) (h : MeromorphicFunction X) (t : GlobalTails X) :
    P.pairFun (a • h) t = a * P.pairFun h t := by
  rw [P.pairFun_apply, P.pairFun_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun q _ => ?_
  rw [P.pairSlot_smul a h q.1 q.2]
  ring

/-- The pairing, junk-free: `L(K−D)/junk →ₗ Dual(H¹(D))`. -/
def pairingL (D : Divisor X) :
    lSysModule (X := X) (P.data.K - D) →ₗ[ℂ] Module.Dual ℂ (H1Tail (X := X) D) := by
  refine Submodule.liftQ _
    { toFun := fun h => P.pairingFunctional h
      map_add' := fun h₁ h₂ => ?_
      map_smul' := fun a h => ?_ } ?_
  · refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show P.pairFun _ t = P.pairingFunctional h₁ (Submodule.Quotient.mk t)
      + P.pairingFunctional h₂ (Submodule.Quotient.mk t)
    rw [pairingFunctional_mk, pairingFunctional_mk]
    exact P.pairFun_add_left h₁ h₂ t
  · refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show P.pairFun _ t = a • (P.pairingFunctional h (Submodule.Quotient.mk t))
    rw [pairingFunctional_mk, smul_eq_mul]
    exact P.pairFun_smul_left a h t
  · intro h hj
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hj
    have hj' : (h : MeromorphicFunction X) ∈ germZeroSubmodule (X := X) := hj
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show P.pairingFunctional h (Submodule.Quotient.mk t) = 0
    rw [pairingFunctional_mk, P.pairFun_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [P.pairSlot_eq_zero_of_germZero hj' q.1 q.2, mul_zero]

@[simp] theorem pairingL_mk (D : Divisor X)
    (h : ↥(linearSystem (X := X) (P.data.K - D))) :
    P.pairingL D (Submodule.Quotient.mk h) = P.pairingFunctional h := rfl

/-- **The injectivity half of tail Serre duality** (Miranda VI.3.6 flavour): a section of
`L(K−D)` pairing to zero against every tail class is germ-zero. -/
theorem pairingL_injective (D : Divisor X) : Function.Injective (P.pairingL D) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro u hu
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [LinearMap.mem_ker, pairingL_mk] at hu
  rw [Submodule.Quotient.mk_eq_zero]
  -- evaluate against the single-monomial tails: all slot pairings vanish
  have hvan : ∀ p : X, ∀ k : ℤ, P.pairSlot (h : MeromorphicFunction X) p k = 0 := by
    intro p k
    rcases le_or_gt (-(D p)) k with hk | hk
    · exact P.pairSlot_eq_zero_of_le h.2 hk
    · have := congrArg (fun φ : H1Tail (X := X) D →ₗ[ℂ] ℂ =>
        φ (Submodule.Quotient.mk (Finsupp.single (p, k) (1 : ℂ)))) hu
      simp only [LinearMap.zero_apply] at this
      rw [pairingFunctional_mk, P.pairFun_single] at this
      simpa using this
  -- all full coefficients of every slot product vanish ⟹ each product is germ-zero
  have htop : ∀ p : X, meromorphicOrderAt
      (fun ζ => (h : MeromorphicFunction X).toFun ((chartAt (H := ℂ) p).symm ζ)
        * P.slot p ζ) ((chartAt (H := ℂ) p) p) = ⊤ := by
    intro p
    refine order_eq_top_of_planarCoeff_vanish (P.prodRead_mero p _) fun j => ?_
    have := hvan p (-1 - j)
    rw [pairSlot, show (-1 - (-1 - j) : ℤ) = j from by ring] at this
    exact this
  -- the slot has finite order, so `h` is germ-zero at every point
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  intro p
  have hmul := P.prodRead_order p (h : MeromorphicFunction X)
  rw [htop p] at hmul
  cases hord : (h : MeromorphicFunction X).orderW p with
  | top => exact hord
  | coe n =>
    rw [hord] at hmul
    exfalso
    have hcoe : ((n + P.data.K p : ℤ) : WithTop ℤ)
        = (n : WithTop ℤ) + ((P.data.K p : ℤ) : WithTop ℤ) := WithTop.coe_add n (P.data.K p)
    rw [← hcoe] at hmul
    exact WithTop.coe_ne_top hmul.symm

/-- **`l(K−D) ≤ h¹_t(D)`** — the injectivity-half dimension bound. -/
theorem lDim_le_h1TailDim (D : Divisor X) :
    lDim (X := X) (P.data.K - D) ≤ h1TailDim (X := X) D := by
  haveI := finiteDimensional_H1Tail (X := X) D
  exact SerreDuality.finrank_le_of_injective_to_dual (P.pairingL D) (P.pairingL_injective D)

/-! ## Part E — tail Serre duality under the surjectivity input, and `TailRiemannRoch` -/

/-- **The surjectivity half of tail Serre duality** (Miranda VI.3.10: recovery + growth
pigeonhole) — the remaining mathematical input of the tail tower beyond the frame itself
(`docs/planning/TAILRR_BLOCKER.md`). -/
def PairingSurjective : Prop :=
  ∀ D : Divisor X, Function.Surjective (P.pairingL D)

/-- **Tail Serre duality** under the surjectivity input: `h¹_t(D) = l(K − D)`. -/
theorem h1TailDim_eq_lDim_of_surjective (hs : P.PairingSurjective) (D : Divisor X) :
    h1TailDim (X := X) D = lDim (X := X) (P.data.K - D) := by
  classical
  haveI := finiteDimensional_H1Tail (X := X) D
  haveI hFD : FiniteDimensional ℂ (lSysModule (X := X) (P.data.K - D)) :=
    ((chartDiskCover (X := X)).toFiniteCover.globalSectionsEquivQuot
      (D := P.data.K - D)).symm.finiteDimensional
  refine le_antisymm ?_ (P.lDim_le_h1TailDim D)
  have hrn := LinearMap.finrank_range_add_finrank_ker (P.pairingL D)
  have hrange : finrank ℂ ↥(LinearMap.range (P.pairingL D))
      = finrank ℂ (Module.Dual ℂ (H1Tail (X := X) D)) := by
    rw [LinearMap.range_eq_top.mpr (hs D), finrank_top]
  have hdual : finrank ℂ (Module.Dual ℂ (H1Tail (X := X) D))
      = h1TailDim (X := X) D := Subspace.dual_finrank_eq
  have hsrc : finrank ℂ (lSysModule (X := X) (P.data.K - D))
      = lDim (X := X) (P.data.K - D) := rfl
  omega

/-- `g_t = l(K)` under the surjectivity input (duality at `D = 0`). -/
theorem tailGenus_eq_lDim_K (hs : P.PairingSurjective) :
    tailGenus X = lDim (X := X) P.data.K := by
  rw [show tailGenus X = h1TailDim (X := X) (0 : Divisor X) from rfl,
    P.h1TailDim_eq_lDim_of_surjective hs 0, sub_zero]

/-- `h¹_t(K) = 1` under the surjectivity input (duality at `D = K`). -/
theorem h1TailDim_K_eq_one (hs : P.PairingSurjective) :
    h1TailDim (X := X) P.data.K = 1 := by
  rw [P.h1TailDim_eq_lDim_of_surjective hs P.data.K, sub_self]
  exact lDim_zero_eq_one

/-- `deg K = 2g_t − 2` under the surjectivity input (tail RR-I at `K`). -/
theorem deg_K_eq (hs : P.PairingSurjective) :
    Divisor.deg X P.data.K = 2 * (tailGenus X : ℤ) - 2 := by
  have hRR := tail_riemannRoch_I (X := X) P.data.K
  rw [P.h1TailDim_K_eq_one hs] at hRR
  have hlK : lDim (X := X) P.data.K = tailGenus X := (P.tailGenus_eq_lDim_K hs).symm
  rw [hlK] at hRR
  omega

/-- **`g_t = kirovGenus`** under the surjectivity input: the tail genus is the analytic
genus (duality at `0` + the §17.4 canonical iso `l(K) = kirovGenus`). -/
theorem tailGenus_eq_kirovGenus (hs : P.PairingSurjective) :
    tailGenus X = kirovGenus X := by
  rw [P.tailGenus_eq_lDim_K hs]
  exact P.data.hKgenus (le_of_eq omegaDim_zero_eq_genus)

/-- **`TailRiemannRoch` from the tail tower** — the headline conditional assembly: a tail
pair frame (slots + the pair-frame residue theorem) together with the surjectivity half of
the tail duality pairing yields the named large-degree Riemann–Roch input of
`TailGenusTarget.lean` verbatim. -/
theorem tailRiemannRoch_of_pairingSurjective (hs : P.PairingSurjective) :
    TailRiemannRoch X := by
  intro A hAeff hAdeg
  have hRR := tail_riemannRoch_I (X := X) A
  have hgg := P.tailGenus_eq_kirovGenus hs
  have hdK := P.deg_K_eq hs
  have h1A : h1TailDim (X := X) A = lDim (X := X) (P.data.K - A) :=
    P.h1TailDim_eq_lDim_of_surjective hs A
  have hneg : Divisor.deg X (P.data.K - A) < 0 := by
    rw [Divisor.deg_sub, hdK]
    omega
  have h0 : lDim (X := X) (P.data.K - A) = 0 := lDim_eq_zero_of_deg_neg _ hneg
  rw [h1A, h0] at hRR
  omega

end TailPairFrame

/-- **The keystone-facing corollary**: with a tail pair frame and the surjectivity half, the
canonical-cover arithmetic genus identity `h¹(𝒪) = kirovGenus` of `TailGenusTarget.lean` — the
exact port-side fact the Layer-3 flip consumes — becomes a theorem. -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame (P : TailPairFrame X)
    (hs : P.PairingSurjective) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_chartDiskCover_eq_kirovGenus (P.tailRiemannRoch_of_pairingSurjective hs)

end Dolbeault

end Jacobians

end
