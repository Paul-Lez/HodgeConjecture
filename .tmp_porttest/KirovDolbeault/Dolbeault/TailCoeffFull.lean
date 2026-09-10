/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailFrame

/-!
# Full Laurent coefficients via leading-term stripping (tail tower T1)

The proven `laurentCoeff k F c` (`LocalRealization.lean`) is honest only in the regime
`k ≤ ord F` (the de-pole limit exists), where it reads `0` below the order and the leading
coefficient at the order.  The Miranda tail tower (`docs/planning/TAILRR_ROUTE.md`) needs the
**full** Laurent coefficients — every order `k`, for the truncated-tail map `α_D` and the
residue pairing.  This file builds them by **leading-term stripping**: subtract the leading
monomial read by `laurentCoeff` and read again, one order at a time.

* `stripFun F c lo j` — `F` minus its first `j` Laurent monomials from level `lo` up;
  meromorphic, of order `≥ lo + j` whenever `lo ≤ ord F` (each step is the kernel law
  `laurentCoeff_eq_zero_iff`).
* `fullCoeffFrom F c lo j` — the order-`(lo+j)` coefficient of the stripped function: the
  GENUINE Laurent coefficient `a_{lo+j}(F)`, honest at every order.
* level irrelevance (`fullCoeffFrom_level_irrel`), additivity / ℂ-homogeneity at a common
  level (NO order hypotheses on the indices read), germ-congruence, and the **order law**
  `order_ge_iff_fullCoeffFrom_vanish`: `hi ≤ ord F` iff all full coefficients below `hi`
  vanish — the exactness engine of the tail tower (`ker α_D = L(D)`).

Everything is one-variable Laurent-coefficient algebra over the existing API; no integration.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

variable {F G : ℂ → ℂ} {c : ℂ} {lo lo' hi : ℤ}

/-! ## Part 0 — monomials -/

/-- A (scaled) Laurent monomial is meromorphic at the centre. -/
theorem meromorphicAt_monomial (a c : ℂ) (m : ℤ) :
    MeromorphicAt (fun z => a * (z - c) ^ m) c := by
  have h := meromorphicAt_zpow_sub (-m) c
  simp only [neg_neg] at h
  exact (MeromorphicAt.const a c).mul h

/-- The plain monomial `(z−c)^m` is meromorphic at the centre. -/
theorem meromorphicAt_zpow_self (c : ℂ) (m : ℤ) :
    MeromorphicAt (fun z => (z - c) ^ m) c := by
  have h := meromorphicAt_zpow_sub (-m) c
  simpa only [neg_neg] using h

/-- The order of a nonzero scaled monomial is the exponent. -/
theorem meromorphicOrderAt_monomial {a : ℂ} (ha : a ≠ 0) (c : ℂ) (m : ℤ) :
    meromorphicOrderAt (fun z => a * (z - c) ^ m) c = (m : WithTop ℤ) := by
  have hsm : (fun z => a * (z - c) ^ m)
      = (fun _ : ℂ => a) • (fun z => (z - c) ^ m) := by
    funext z
    rw [Pi.smul_apply', smul_eq_mul]
  rw [hsm, meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using ha),
    meromorphicOrderAt_zpow_self]

/-- The order-`m` coefficient of the scaled monomial `a·(z−c)^m` is `a`. -/
theorem laurentCoeff_monomial (a c : ℂ) (m : ℤ) :
    laurentCoeff m (fun z => a * (z - c) ^ m) c = a := by
  have hsm : (fun z => a * (z - c) ^ m) = a • (fun z => (z - c) ^ m) := rfl
  rw [hsm, laurentCoeff_smul a (meromorphicAt_zpow_self c m)
      (le_of_eq (meromorphicOrderAt_zpow_self m c).symm),
    laurentCoeff_zpow_self, smul_eq_mul, mul_one]

/-- One `WithTop ℤ` upgrade step: strict `l < ord` gives `l + 1 ≤ ord`. -/
private theorem add_one_le_of_lt {l : ℤ} {o : WithTop ℤ} (hl : (l : WithTop ℤ) < o) :
    ((l + 1 : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe v =>
    have hv : l < v := by exact_mod_cast hl
    exact_mod_cast hv

/-! ## Part 1 — the strip iteration -/

/-- **The strip iteration**: `F` minus its first `j` Laurent monomials from level `lo` up,
each read by the proven `laurentCoeff` at the (then-current) bottom order. -/
def stripFun (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) : ℕ → ℂ → ℂ
  | 0 => F
  | j + 1 => fun z =>
      stripFun F c lo j z - laurentCoeff (lo + j) (stripFun F c lo j) c * (z - c) ^ (lo + j)

@[simp] theorem stripFun_zero_iter (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) : stripFun F c lo 0 = F := rfl

theorem stripFun_succ (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) (j : ℕ) :
    stripFun F c lo (j + 1) = fun z =>
      stripFun F c lo j z
        - laurentCoeff (lo + j) (stripFun F c lo j) c * (z - c) ^ (lo + j) := rfl

/-- **The full order-`(lo+j)` Laurent coefficient**, read on the stripped function (honest at
every order, unlike the raw `laurentCoeff`). -/
def fullCoeffFrom (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) (j : ℕ) : ℂ :=
  laurentCoeff (lo + j) (stripFun F c lo j) c

/-- The strip iterates of a meromorphic function are meromorphic. -/
theorem stripFun_meromorphicAt (hF : MeromorphicAt F c) :
    ∀ j : ℕ, MeromorphicAt (stripFun F c lo j) c
  | 0 => hF
  | j + 1 => by
    rw [stripFun_succ]
    exact (stripFun_meromorphicAt hF j).sub
      (meromorphicAt_monomial (laurentCoeff (lo + j) (stripFun F c lo j) c) c (lo + j))

/-- **The strip order law**: from level `lo ≤ ord F`, the `j`-th strip iterate has order
`≥ lo + j` (each step kills the bottom coefficient — the kernel law upgrade). -/
theorem stripFun_order (hF : MeromorphicAt F c)
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∀ j : ℕ, ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (stripFun F c lo j) c
  | 0 => by simpa using hlo
  | j + 1 => by
    have hS : MeromorphicAt (stripFun F c lo j) c := stripFun_meromorphicAt hF j
    have hordS := stripFun_order hF hlo j
    set S := stripFun F c lo j with hSdef
    set a := laurentCoeff (lo + j) S c with hadef
    have hstep : stripFun F c lo (j + 1)
        = fun z => S z - a * (z - c) ^ (lo + j) := rfl
    have hidx : (lo + ((j + 1 : ℕ) : ℤ) : ℤ) = lo + (j : ℤ) + 1 := by push_cast; ring
    rcases eq_or_ne a 0 with ha | ha
    · -- the bottom coefficient was already `0`: the strip is unchanged, the order upgrades
      have hSeq : stripFun F c lo (j + 1) = S := by
        funext z
        rw [hstep]
        show S z - a * (z - c) ^ (lo + j) = S z
        rw [ha]
        ring
      rw [hSeq]
      have hlt : ((lo + j : ℤ) : WithTop ℤ) < meromorphicOrderAt S c :=
        (laurentCoeff_eq_zero_iff hS hordS).mp ha
      have h1 := add_one_le_of_lt hlt
      rw [hidx]
      exact h1
    · -- subtract the (nonzero) bottom monomial: sum order `≥ lo+j`, coefficient `0`, upgrade
      set M : ℂ → ℂ := fun z => -a * (z - c) ^ (lo + j) with hMdef
      have hM : MeromorphicAt M c := meromorphicAt_monomial _ c _
      have hMord : meromorphicOrderAt M c = ((lo + j : ℤ) : WithTop ℤ) :=
        meromorphicOrderAt_monomial (by simpa using ha) c (lo + j)
      have hsum : stripFun F c lo (j + 1) = S + M := by
        funext z
        rw [hstep]
        show S z - a * (z - c) ^ (lo + j) = S z + (-a * (z - c) ^ (lo + j))
        ring
      have hordsum : ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (S + M) c := by
        refine le_trans (le_min hordS (le_of_eq hMord.symm)) (meromorphicOrderAt_add hS hM)
      have hcoeffsum : laurentCoeff (lo + j) (S + M) c = 0 := by
        rw [laurentCoeff_add hS hM hordS (le_of_eq hMord.symm), ← hadef,
          laurentCoeff_monomial]
        ring
      have hlt : ((lo + j : ℤ) : WithTop ℤ) < meromorphicOrderAt (S + M) c :=
        (laurentCoeff_eq_zero_iff (hS.add hM) hordsum).mp hcoeffsum
      have h1 := add_one_le_of_lt hlt
      rw [hsum, hidx]
      exact h1

/-! ## Part 2 — honest reads, level irrelevance -/

/-- As long as the target order stays `≤ ord F`, stripping does nothing (the subtracted
coefficients are all `0`). -/
theorem stripFun_eq_self (hF : MeromorphicAt F c)
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∀ j : ℕ, ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c → stripFun F c lo j = F
  | 0, _ => rfl
  | j + 1, h => by
    have hj : ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
      refine le_trans ?_ h
      exact_mod_cast (by omega : lo + (j : ℤ) ≤ lo + ((j : ℤ) + 1))
    have hprev : stripFun F c lo j = F := stripFun_eq_self hF hlo j hj
    have hlt : ((lo + j : ℤ) : WithTop ℤ) < meromorphicOrderAt F c := by
      refine lt_of_lt_of_le ?_ h
      exact_mod_cast (by omega : lo + (j : ℤ) < lo + ((j : ℤ) + 1))
    have hc0 : laurentCoeff (lo + j) F c = 0 := (laurentCoeff_eq_zero_iff hF hj).mpr hlt
    funext z
    rw [stripFun_succ, hprev, hc0]
    ring

/-- **Honest read**: at orders `≤ ord F`, the full coefficient IS the raw `laurentCoeff`. -/
theorem fullCoeffFrom_eq_laurentCoeff (hF : MeromorphicAt F c)
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) {j : ℕ}
    (hj : ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    fullCoeffFrom F c lo j = laurentCoeff (lo + j) F c := by
  rw [fullCoeffFrom, stripFun_eq_self hF hlo j hj]

/-- Below the order, full coefficients vanish. -/
theorem fullCoeffFrom_eq_zero_of_lt_order (hF : MeromorphicAt F c)
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) {j : ℕ}
    (hj : ((lo + j : ℤ) : WithTop ℤ) < meromorphicOrderAt F c) :
    fullCoeffFrom F c lo j = 0 := by
  rw [fullCoeffFrom_eq_laurentCoeff hF hlo (le_of_lt hj)]
  exact (laurentCoeff_eq_zero_iff hF (le_of_lt hj)).mpr hj

/-- At the (finite) order, the full coefficient is the leading coefficient — NONZERO. -/
theorem fullCoeffFrom_leading_ne_zero (hF : MeromorphicAt F c)
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c) {j : ℕ}
    (hj : meromorphicOrderAt F c = ((lo + j : ℤ) : WithTop ℤ)) :
    fullCoeffFrom F c lo j ≠ 0 := by
  rw [fullCoeffFrom_eq_laurentCoeff hF hlo (le_of_eq hj.symm)]
  intro h0
  have := (laurentCoeff_eq_zero_iff hF (le_of_eq hj.symm)).mp h0
  rw [hj] at this
  exact lt_irrefl _ this

/-- Level shift: stripping from a deeper level `lo ≤ lo' ≤ ord F` reaches the same iterates. -/
theorem stripFun_level_shift (hF : MeromorphicAt F c) (hle : lo ≤ lo')
    (hlo' : ((lo' : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∀ j : ℕ, stripFun F c lo ((lo' - lo).toNat + j) = stripFun F c lo' j
  | 0 => by
    have hlo : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c :=
      le_trans (by exact_mod_cast hle) hlo'
    refine stripFun_eq_self hF hlo _ ?_
    have hidx : (lo + (((lo' - lo).toNat + 0 : ℕ) : ℤ) : ℤ) = lo' := by
      push_cast
      omega
    rw [hidx]
    exact hlo'
  | j + 1 => by
    have ih := stripFun_level_shift hF hle hlo' j
    have hidx : (lo + ((lo' - lo).toNat + j : ℕ) : ℤ) = lo' + j := by push_cast; omega
    show stripFun F c lo (((lo' - lo).toNat + j) + 1) = stripFun F c lo' (j + 1)
    funext z
    rw [stripFun_succ, stripFun_succ, ih, hidx]

/-- Level shift for the full coefficients. -/
theorem fullCoeffFrom_level_shift (hF : MeromorphicAt F c) (hle : lo ≤ lo')
    (hlo' : ((lo' : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) (j : ℕ) :
    fullCoeffFrom F c lo ((lo' - lo).toNat + j) = fullCoeffFrom F c lo' j := by
  rw [fullCoeffFrom, fullCoeffFrom, stripFun_level_shift hF hle hlo' j]
  congr 1
  push_cast
  omega

/-- **Level irrelevance**: the full coefficient at order `k` is the same read from any two
levels `≤ min(ord F, k)`. -/
theorem fullCoeffFrom_level_irrel (hF : MeromorphicAt F c) {k : ℤ}
    (hlo : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hlo' : ((lo' : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hk : lo ≤ k) (hk' : lo' ≤ k) :
    fullCoeffFrom F c lo (k - lo).toNat = fullCoeffFrom F c lo' (k - lo').toNat := by
  rcases le_total lo lo' with hle | hle
  · have hsplit : (k - lo).toNat = (lo' - lo).toNat + (k - lo').toNat := by omega
    rw [hsplit, fullCoeffFrom_level_shift hF hle hlo']
  · have hsplit : (k - lo').toNat = (lo - lo').toNat + (k - lo).toNat := by omega
    rw [hsplit, fullCoeffFrom_level_shift hF hle hlo]

/-! ## Part 3 — algebra: additivity, homogeneity, congruence, zero -/

/-- Strips of a sum split, from any common level. -/
theorem stripFun_add (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hloF : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hloG : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c) :
    ∀ j : ℕ, stripFun (F + G) c lo j = stripFun F c lo j + stripFun G c lo j
  | 0 => rfl
  | j + 1 => by
    have ih := stripFun_add hF hG hloF hloG j
    have hSF : MeromorphicAt (stripFun F c lo j) c := stripFun_meromorphicAt hF j
    have hSG : MeromorphicAt (stripFun G c lo j) c := stripFun_meromorphicAt hG j
    have hOF := stripFun_order hF hloF j
    have hOG := stripFun_order hG hloG j
    have hcoeff : laurentCoeff (lo + j) (stripFun (F + G) c lo j) c
        = laurentCoeff (lo + j) (stripFun F c lo j) c
          + laurentCoeff (lo + j) (stripFun G c lo j) c := by
      rw [ih]
      exact laurentCoeff_add hSF hSG hOF hOG
    funext z
    rw [stripFun_succ]
    show _ = stripFun F c lo (j + 1) z + stripFun G c lo (j + 1) z
    rw [stripFun_succ, stripFun_succ]
    show stripFun (F + G) c lo j z
          - laurentCoeff (lo + j) (stripFun (F + G) c lo j) c * (z - c) ^ (lo + j) = _
    rw [hcoeff, ih]
    show stripFun F c lo j z + stripFun G c lo j z - _ = _
    ring

/-- **Additivity of the full coefficients** at any common level. -/
theorem fullCoeffFrom_add (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hloF : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hloG : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c) (j : ℕ) :
    fullCoeffFrom (F + G) c lo j = fullCoeffFrom F c lo j + fullCoeffFrom G c lo j := by
  rw [fullCoeffFrom, fullCoeffFrom, fullCoeffFrom, stripFun_add hF hG hloF hloG j]
  exact laurentCoeff_add (stripFun_meromorphicAt hF j) (stripFun_meromorphicAt hG j)
    (stripFun_order hF hloF j) (stripFun_order hG hloG j)

/-- Strips of a scalar multiple scale, from any common level. -/
theorem stripFun_smul (s : ℂ) (hF : MeromorphicAt F c)
    (hloF : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∀ j : ℕ, stripFun (s • F) c lo j = s • stripFun F c lo j
  | 0 => rfl
  | j + 1 => by
    have ih := stripFun_smul s hF hloF j
    have hSF : MeromorphicAt (stripFun F c lo j) c := stripFun_meromorphicAt hF j
    have hOF := stripFun_order hF hloF j
    have hcoeff : laurentCoeff (lo + j) (stripFun (s • F) c lo j) c
        = s * laurentCoeff (lo + j) (stripFun F c lo j) c := by
      rw [ih]
      have := laurentCoeff_smul s hSF hOF
      simpa using this
    funext z
    rw [stripFun_succ]
    show stripFun (s • F) c lo j z
        - laurentCoeff (lo + j) (stripFun (s • F) c lo j) c * (z - c) ^ (lo + j)
        = (s • stripFun F c lo (j + 1)) z
    rw [hcoeff, ih, stripFun_succ]
    show s * stripFun F c lo j z - s * laurentCoeff (lo + j) (stripFun F c lo j) c
        * (z - c) ^ (lo + j) = s * _
    ring

/-- **ℂ-homogeneity of the full coefficients** at any common level. -/
theorem fullCoeffFrom_smul (s : ℂ) (hF : MeromorphicAt F c)
    (hloF : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) (j : ℕ) :
    fullCoeffFrom (s • F) c lo j = s * fullCoeffFrom F c lo j := by
  rw [fullCoeffFrom, fullCoeffFrom, stripFun_smul s hF hloF j]
  have := laurentCoeff_smul s (stripFun_meromorphicAt hF j) (stripFun_order hF hloF j)
  simpa using this

/-- Strips depend only on the germ. -/
theorem stripFun_congr (h : F =ᶠ[𝓝[≠] c] G) :
    ∀ j : ℕ, stripFun F c lo j =ᶠ[𝓝[≠] c] stripFun G c lo j
  | 0 => h
  | j + 1 => by
    have ih := stripFun_congr h j
    have hcoeff : laurentCoeff (lo + j) (stripFun F c lo j) c
        = laurentCoeff (lo + j) (stripFun G c lo j) c := laurentCoeff_congr ih
    filter_upwards [ih] with z hz
    rw [stripFun_succ, stripFun_succ]
    show stripFun F c lo j z - _ * _ = stripFun G c lo j z - _ * _
    rw [hz, hcoeff]

/-- **Germ invariance of the full coefficients.** -/
theorem fullCoeffFrom_congr (h : F =ᶠ[𝓝[≠] c] G) (lo : ℤ) (j : ℕ) :
    fullCoeffFrom F c lo j = fullCoeffFrom G c lo j :=
  laurentCoeff_congr (stripFun_congr h j)

/-- Strips of the zero function vanish. -/
theorem stripFun_zero_fun (c : ℂ) (lo : ℤ) :
    ∀ j : ℕ, stripFun (fun _ => (0 : ℂ)) c lo j = fun _ => (0 : ℂ)
  | 0 => rfl
  | j + 1 => by
    have ih := stripFun_zero_fun c lo j
    funext z
    rw [stripFun_succ, ih]
    show (0 : ℂ) - laurentCoeff (lo + j) (fun _ => (0 : ℂ)) c * (z - c) ^ (lo + j) = 0
    rw [show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]
    ring

/-- Full coefficients of the zero function vanish. -/
theorem fullCoeffFrom_zero_fun (c : ℂ) (lo : ℤ) (j : ℕ) :
    fullCoeffFrom (fun _ => (0 : ℂ)) c lo j = 0 := by
  rw [fullCoeffFrom, stripFun_zero_fun c lo j,
    show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]

/-! ## Part 4 — the order law -/

/-- **The order law, upgrade direction**: if all full coefficients at orders `< hi` vanish
(from a valid level), the order is `≥ hi`. -/
theorem order_ge_of_fullCoeffFrom_vanish (hF : MeromorphicAt F c)
    (hlo : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hvan : ∀ j : ℕ, (lo + j : ℤ) < hi → fullCoeffFrom F c lo j = 0) :
    (hi : WithTop ℤ) ≤ meromorphicOrderAt F c := by
  rcases le_total hi lo with hle | hle
  · exact le_trans (by exact_mod_cast hle) hlo
  -- climb from `lo` to `hi` one full coefficient at a time
  have hclimb : ∀ j : ℕ, (lo + j : ℤ) ≤ hi →
      ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := by
    intro j
    induction j with
    | zero => intro _; simpa using hlo
    | succ j ih =>
      intro hj
      have hj' : (lo + j : ℤ) ≤ hi := by push_cast at hj ⊢; omega
      have hjlt : (lo + j : ℤ) < hi := by push_cast at hj ⊢; omega
      have hord_j : ((lo + j : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c := ih hj'
      have hcz : laurentCoeff (lo + j) F c = 0 := by
        have := hvan j hjlt
        rwa [fullCoeffFrom_eq_laurentCoeff hF hlo hord_j] at this
      have hltord := (laurentCoeff_eq_zero_iff hF hord_j).mp hcz
      have h1 := add_one_le_of_lt hltord
      have hidx : (lo + ((j + 1 : ℕ) : ℤ) : ℤ) = lo + (j : ℤ) + 1 := by push_cast; ring
      rw [hidx]
      exact h1
  have hfin := hclimb (hi - lo).toNat (by omega)
  have : (lo + ((hi - lo).toNat : ℤ) : ℤ) = hi := by omega
  rwa [this] at hfin

/-- **The order law (iff form)**: `hi ≤ ord F` iff all full coefficients below `hi` vanish. -/
theorem order_ge_iff_fullCoeffFrom_vanish (hF : MeromorphicAt F c)
    (hlo : ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    (hi : WithTop ℤ) ≤ meromorphicOrderAt F c
      ↔ ∀ j : ℕ, (lo + j : ℤ) < hi → fullCoeffFrom F c lo j = 0 := by
  constructor
  · intro hord j hj
    exact fullCoeffFrom_eq_zero_of_lt_order hF hlo (lt_of_lt_of_le (by exact_mod_cast hj) hord)
  · exact order_ge_of_fullCoeffFrom_vanish hF hlo

end Dolbeault

/-! ## Part 5 — the global full coefficient `coeffAt` on `MeromorphicFunction X` -/

namespace MeromorphicFunction

open Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The full order-`k` Laurent coefficient** of a global meromorphic function at `b ∈ X`,
read in the ambient chart at `b` (the `tailCoeff`/`orderW` chart), honest at EVERY order `k` —
the strip-read `fullCoeffFrom` from the level `min(ord, k)`. -/
noncomputable def coeffAt (f : MeromorphicFunction X) (b : X) (k : ℤ) : ℂ :=
  if f.orderW b = ⊤ then 0
  else
    fullCoeffFrom (f.toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b)
      (min ((f.orderW b).untop₀) k) (k - min ((f.orderW b).untop₀) k).toNat

/-- A germ-zero read has all full coefficients `0`. -/
private theorem fullCoeffFrom_read_eq_zero_of_top {f : MeromorphicFunction X} {b : X}
    (h : f.orderW b = ⊤) (lo : ℤ) (j : ℕ) :
    fullCoeffFrom (f.toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) lo j = 0 := by
  have hev : (f.toFun ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (fun _ => (0 : ℂ)) :=
    meromorphicOrderAt_eq_top_iff.mp h
  rw [fullCoeffFrom_congr hev lo j, fullCoeffFrom_zero_fun]

/-- **The level-free bridge**: for ANY level `lo ≤ min(ord, k)`, `coeffAt` is the strip read
from `lo` (including the germ-zero case, where both sides are `0`). -/
theorem coeffAt_eq_fullCoeffFrom {f : MeromorphicFunction X} {b : X} {k lo : ℤ}
    (hlo : (lo : WithTop ℤ) ≤ f.orderW b) (hlk : lo ≤ k) :
    f.coeffAt b k = fullCoeffFrom (f.toFun ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) lo (k - lo).toNat := by
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · rw [coeffAt, if_pos htop, fullCoeffFrom_read_eq_zero_of_top htop]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [coeffAt, if_neg hne]
    have hun : (f.orderW b).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
    rw [hun]
    refine fullCoeffFrom_level_irrel (f.meromorphic b) ?_ ?_ (min_le_right _ _) hlk
    · show ((min n k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt _ _
      rw [show meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm)
          ((chartAt (H := ℂ) b) b) = f.orderW b from rfl, ← hn]
      exact_mod_cast min_le_left n k
    · show ((lo : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt _ _
      rw [show meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm)
          ((chartAt (H := ℂ) b) b) = f.orderW b from rfl]
      exact hlo

/-- `coeffAt` depends only on the germ of the chart read. -/
theorem coeffAt_eq_of_germEq {f g : MeromorphicFunction X} {b : X}
    (h : (f.toFun ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (g.toFun ∘ (chartAt (H := ℂ) b).symm)) (k : ℤ) :
    f.coeffAt b k = g.coeffAt b k := by
  have hord : f.orderW b = g.orderW b := meromorphicOrderAt_congr h
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · rw [coeffAt, if_pos htop, coeffAt, if_pos (hord ▸ htop)]
  · rw [coeffAt, if_neg hne, coeffAt, if_neg (hord ▸ hne), ← hord,
      fullCoeffFrom_congr h]

/-- **Germ-zero junk does not move full coefficients** (the `lSysModule` well-definedness). -/
theorem coeffAt_eq_of_sub_germZero {f f' : MeromorphicFunction X}
    (hd : f - f' ∈ germZeroSubmodule (X := X)) (b : X) (k : ℤ) :
    f.coeffAt b k = f'.coeffAt b k := by
  refine coeffAt_eq_of_germEq ?_ k
  have htop : meromorphicOrderAt
      ((f - f').toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) = ⊤ := hd b
  have hev : ((f - f').toFun ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] 0 := meromorphicOrderAt_eq_top_iff.mp htop
  filter_upwards [hev] with z hz
  have hz' : f.toFun ((chartAt (H := ℂ) b).symm z)
      - f'.toFun ((chartAt (H := ℂ) b).symm z) = 0 := hz
  show f.toFun ((chartAt (H := ℂ) b).symm z) = f'.toFun ((chartAt (H := ℂ) b).symm z)
  linear_combination hz'

/-- The zero function has all full coefficients `0`. -/
@[simp] theorem coeffAt_zero (b : X) (k : ℤ) :
    (0 : MeromorphicFunction X).coeffAt b k = 0 := by
  rw [coeffAt, if_pos (orderW_zero b)]

/-- **Additivity of `coeffAt`** — NO order hypotheses (contrast `tailCoeff_add`). -/
theorem coeffAt_add (f g : MeromorphicFunction X) (b : X) (k : ℤ) :
    (f + g).coeffAt b k = f.coeffAt b k + g.coeffAt b k := by
  classical
  -- a common finite level under both orders and `k`
  set F : ℂ → ℂ := f.toFun ∘ (chartAt (H := ℂ) b).symm with hF
  set G : ℂ → ℂ := g.toFun ∘ (chartAt (H := ℂ) b).symm with hG
  set c : ℂ := (chartAt (H := ℂ) b) b with hc
  have hreadsum : ((f + g).toFun ∘ (chartAt (H := ℂ) b).symm) = F + G := rfl
  set lo : ℤ := min (min ((f.orderW b).untop₀) ((g.orderW b).untop₀)) k with hlo
  have hlk : lo ≤ k := min_le_right _ _
  have hloF : (lo : WithTop ℤ) ≤ f.orderW b := by
    rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hn]
      have : lo ≤ n := by
        have h1 : (f.orderW b).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
        have := min_le_left (min ((f.orderW b).untop₀) ((g.orderW b).untop₀)) k
        omega
      exact_mod_cast this
  have hloG : (lo : WithTop ℤ) ≤ g.orderW b := by
    rcases eq_or_ne (g.orderW b) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hn]
      have : lo ≤ n := by
        have h1 : (g.orderW b).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
        have := min_le_left (min ((f.orderW b).untop₀) ((g.orderW b).untop₀)) k
        omega
      exact_mod_cast this
  have hloFG : (lo : WithTop ℤ) ≤ (f + g).orderW b := by
    have hmin := meromorphicOrderAt_add (f.meromorphic b) (g.meromorphic b)
    have : (lo : WithTop ℤ) ≤ min (f.orderW b) (g.orderW b) := le_min hloF hloG
    exact le_trans this hmin
  rw [coeffAt_eq_fullCoeffFrom hloF hlk, coeffAt_eq_fullCoeffFrom hloG hlk,
    coeffAt_eq_fullCoeffFrom hloFG hlk]
  show fullCoeffFrom (F + G) c lo (k - lo).toNat = _
  exact fullCoeffFrom_add (f.meromorphic b) (g.meromorphic b) hloF hloG _

/-- **ℂ-homogeneity of `coeffAt`** — no order hypotheses. -/
theorem coeffAt_smul (s : ℂ) (f : MeromorphicFunction X) (b : X) (k : ℤ) :
    (s • f).coeffAt b k = s * f.coeffAt b k := by
  rcases eq_or_ne s 0 with hs | hs
  · rw [hs, zero_smul, coeffAt_zero, zero_mul]
  · set lo : ℤ := min ((f.orderW b).untop₀) k with hlo
    have hlk : lo ≤ k := min_le_right _ _
    have hloF : (lo : WithTop ℤ) ≤ f.orderW b := by
      rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
      · rw [htop]; exact le_top
      · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hn]
        have h1 : (f.orderW b).untop₀ = n := by rw [← hn, WithTop.untop₀_coe]
        have : lo ≤ n := by
          have := min_le_left ((f.orderW b).untop₀) k
          omega
        exact_mod_cast this
    have hordsmul : (s • f).orderW b = f.orderW b :=
      meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hs)
    have hlosF : (lo : WithTop ℤ) ≤ (s • f).orderW b := by rw [hordsmul]; exact hloF
    rw [coeffAt_eq_fullCoeffFrom hloF hlk, coeffAt_eq_fullCoeffFrom hlosF hlk]
    have hread : ((s • f).toFun ∘ (chartAt (H := ℂ) b).symm)
        = s • (f.toFun ∘ (chartAt (H := ℂ) b).symm) := rfl
    rw [hread]
    exact fullCoeffFrom_smul s (f.meromorphic b) hloF _

/-- `fullCoeffFrom` at offset `0` is the raw bottom-level `laurentCoeff`. -/
private theorem fullCoeffFrom_offset_zero (F : ℂ → ℂ) (c : ℂ) (lo : ℤ) :
    fullCoeffFrom F c lo 0 = laurentCoeff lo F c := by
  rw [fullCoeffFrom, stripFun_zero_iter]
  norm_num

/-- **The order law**: `m ≤ ord_b f` iff all full coefficients below `m` vanish — the
exactness engine of the tail tower (`ker α_D = L(D)`). -/
theorem orderW_ge_iff_coeffAt_vanish (f : MeromorphicFunction X) (b : X) (m : ℤ) :
    ((m : WithTop ℤ) ≤ f.orderW b) ↔ ∀ k : ℤ, k < m → f.coeffAt b k = 0 := by
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · constructor
    · intro _ k _
      rw [coeffAt, if_pos htop]
    · intro _
      rw [htop]
      exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    constructor
    · intro hord k hk
      have hkn : (k : WithTop ℤ) ≤ f.orderW b := by
        rw [← hn]
        rw [← hn] at hord
        have hmn : m ≤ n := by exact_mod_cast hord
        exact_mod_cast (by omega : k ≤ n)
      rw [coeffAt_eq_fullCoeffFrom hkn le_rfl]
      rw [sub_self, Int.toNat_zero, fullCoeffFrom_offset_zero]
      refine (laurentCoeff_eq_zero_iff (f.meromorphic b) hkn).mpr ?_
      rw [show meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm)
          ((chartAt (H := ℂ) b) b) = f.orderW b from rfl, ← hn]
      have hmn : m ≤ n := by
        rw [← hn] at hord
        exact_mod_cast hord
      exact_mod_cast (by omega : k < n)
    · intro hvan
      by_contra hcon
      have hnm : n < m := by
        rw [← hn] at hcon
        by_contra hge
        exact hcon (by exact_mod_cast (by omega : m ≤ n))
      have hzero := hvan n hnm
      have hnn : ((n : ℤ) : WithTop ℤ) ≤ f.orderW b := le_of_eq hn
      rw [coeffAt_eq_fullCoeffFrom hnn le_rfl, sub_self, Int.toNat_zero,
        fullCoeffFrom_offset_zero] at hzero
      have := (laurentCoeff_eq_zero_iff (f.meromorphic b) hnn).mp hzero
      rw [show meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm)
          ((chartAt (H := ℂ) b) b) = f.orderW b from rfl, ← hn] at this
      exact lt_irrefl _ (by exact_mod_cast this)

/-- **The leading coefficient is nonzero** at finite order. -/
theorem coeffAt_leading_ne_zero (f : MeromorphicFunction X) (b : X) {n : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) :
    f.coeffAt b n ≠ 0 := by
  intro h0
  have hiff := (orderW_ge_iff_coeffAt_vanish f b (n + 1))
  have : ((n + 1 : ℤ) : WithTop ℤ) ≤ f.orderW b := by
    refine hiff.mpr ?_
    intro k hk
    rcases eq_or_ne k n with hkn | hkn
    · rwa [hkn]
    · have hklt : k < n := by omega
      have hkord : (k : WithTop ℤ) ≤ f.orderW b := by
        rw [hn]
        exact_mod_cast le_of_lt hklt
      rw [coeffAt_eq_fullCoeffFrom hkord le_rfl, sub_self, Int.toNat_zero,
        fullCoeffFrom_offset_zero]
      refine (laurentCoeff_eq_zero_iff (f.meromorphic b) hkord).mpr ?_
      rw [show meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm)
          ((chartAt (H := ℂ) b) b) = f.orderW b from rfl, hn]
      exact_mod_cast hklt
  rw [hn] at this
  exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)

/-- **Agreement with the raw `tailCoeff`** in its honest regime `k ≤ ord` (the rung-1/rung-2
bridge: tail-frame statements transfer to `coeffAt` verbatim there). -/
theorem coeffAt_eq_tailCoeff_of_le {f : MeromorphicFunction X} {b : X} {k : ℤ}
    (h : (k : WithTop ℤ) ≤ f.orderW b) :
    f.coeffAt b k = f.tailCoeff b k := by
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · rw [coeffAt, if_pos htop]
    have hev : (f.toFun ∘ (chartAt (H := ℂ) b).symm)
        =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (fun _ => (0 : ℂ)) :=
      meromorphicOrderAt_eq_top_iff.mp htop
    rw [tailCoeff, laurentCoeff_congr hev,
      show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]
  · rw [coeffAt_eq_fullCoeffFrom h le_rfl, sub_self, Int.toNat_zero,
      fullCoeffFrom_offset_zero]
    rfl

end MeromorphicFunction

end Jacobians

end
