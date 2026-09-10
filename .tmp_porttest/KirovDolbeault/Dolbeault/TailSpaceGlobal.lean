/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailCoeffFull

/-!
# The global truncated-tail space and the tail map `α_D` (tail tower T2–T3)

Miranda Ch. VI in coefficient coordinates over the full Laurent coefficients of
`TailCoeffFull.lean` (route: `docs/planning/TAILRR_ROUTE.md`):

* `GlobalTails X = (X × ℤ) →₀ ℂ` — global formal Laurent tail divisors (finitely many
  points, finitely many coefficients each).
* `tailSpace D = Finsupp.supported … (belowSet D)` — Miranda's truncated space `𝒯[D](X)`:
  tails with terms only at orders `k < −D(p)`; antitone in `D`.
* `truncTails D'` — the truncation (Finsupp filter) onto `𝒯[D']`; linear, identity on
  `𝒯[D']`, compatible with the tail maps.
* `windowSpace D D'` — the truncation kernel window `[−D'(p), −D(p))`; finite-dimensional of
  dimension `deg D' − deg D` (`finrank_windowSpace`) — the dimension bookkeeping driving
  tail Riemann–Roch.
* `tailMap D : ℳ(X) →ₗ 𝒯[D]`-valued — the **Laurent tail map** `α_D` (the full tail of `f`
  below `−D`); `tailMapFun_apply` is the coefficient law, `tailMap_eq_zero_iff` the kernel
  identity `ker α_D = L(D)`, `truncTails_tailMapFun` the level compatibility
  `t_{D'} ∘ α_D = α_{D'}`.

No analysis here: everything reduces to the `coeffAt` API (order law + linearity).
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 0 — `coeffAt` supplements -/

namespace MeromorphicFunction

variable {f : MeromorphicFunction X} {b : X} {k : ℤ}

/-- At a germ-zero point all full coefficients vanish. -/
@[simp] theorem coeffAt_of_orderW_eq_top (h : f.orderW b = ⊤) (k : ℤ) :
    f.coeffAt b k = 0 := by
  rw [coeffAt, if_pos h]

/-- Full coefficients vanish strictly below the order. -/
theorem coeffAt_eq_zero_of_coe_lt_orderW (h : (k : WithTop ℤ) < f.orderW b) :
    f.coeffAt b k = 0 := by
  refine (orderW_ge_iff_coeffAt_vanish f b (k + 1)).mp ?_ k (by omega)
  cases hord : f.orderW b with
  | top => exact le_top
  | coe n =>
    rw [hord] at h
    have : k < n := by exact_mod_cast h
    exact_mod_cast (by omega : k + 1 ≤ n)

/-- Full coefficients vanish strictly below the `untop₀` order. -/
theorem coeffAt_eq_zero_of_lt_untop₀ (h : k < (f.orderW b).untop₀) :
    f.coeffAt b k = 0 := by
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · exact coeffAt_of_orderW_eq_top htop k
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    refine coeffAt_eq_zero_of_coe_lt_orderW ?_
    rw [← hn]
    rw [← hn, WithTop.untop₀_coe] at h
    exact_mod_cast h

/-- Off the divisor support the order is nonnegative (no pole). -/
theorem orderW_nonneg_of_not_mem_div_support {p : X} (h : p ∉ f.div.support) :
    (0 : WithTop ℤ) ≤ f.orderW p := by
  have hdiv0 : (f.div) p = 0 := Finsupp.notMem_support_iff.mp h
  have hord : (f.orderW p).untop₀ = 0 := hdiv0
  rcases eq_or_ne (f.orderW p) ⊤ with htop | hne
  · rw [htop]; exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hn]
    rw [← hn, WithTop.untop₀_coe] at hord
    exact_mod_cast le_of_eq hord.symm

end MeromorphicFunction

namespace Dolbeault

/-! ## Part 1 — the global tail space -/

/-- **Global formal Laurent tails**: finitely many `(point, order)` slots with coefficients. -/
abbrev GlobalTails (X : Type*) := (X × ℤ) →₀ ℂ

/-- The order region strictly below the `−D` cut. -/
def belowSet (D : Divisor X) : Set (X × ℤ) := {q | q.2 < -(D q.1)}

/-- **Miranda's truncated-tail space `𝒯[D](X)`**: formal tails supported strictly below the
`−D` cut. -/
def tailSpace (D : Divisor X) : Submodule ℂ (GlobalTails X) :=
  Finsupp.supported ℂ ℂ (belowSet D)

theorem mem_tailSpace_iff {D : Divisor X} {t : GlobalTails X} :
    t ∈ tailSpace D ↔ ∀ q : X × ℤ, -(D q.1) ≤ q.2 → t q = 0 := by
  constructor
  · intro ht q hq
    by_contra hne
    have hsupp : q ∈ t.support := Finsupp.mem_support_iff.mpr hne
    have := ht hsupp
    simp only [belowSet, Set.mem_setOf_eq] at this
    omega
  · intro h q hq
    by_contra hout
    simp only [belowSet, Set.mem_setOf_eq, not_lt] at hout
    exact (Finsupp.mem_support_iff.mp hq) (h q hout)

/-- The tail spaces are antitone: a coarser cut allows more terms. -/
theorem tailSpace_antitone {D D' : Divisor X} (h : ∀ x, D x ≤ D' x) :
    tailSpace D' ≤ tailSpace D := by
  refine Finsupp.supported_mono ?_
  intro q hq
  simp only [belowSet, Set.mem_setOf_eq] at hq ⊢
  have := h q.1
  omega

/-! ## Part 2 — truncation -/

/-- **The truncation onto `𝒯[D']`**: discard all terms at orders `≥ −D'(p)` (Finsupp filter),
as a linear map. -/
def truncTails (D' : Divisor X) : GlobalTails X →ₗ[ℂ] GlobalTails X where
  toFun t := t.filter (fun q => q.2 < -(D' q.1))
  map_add' t s := by
    ext q
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    split <;> simp
  map_smul' a t := by
    ext q
    simp only [Finsupp.filter_apply, Finsupp.smul_apply, RingHom.id_apply]
    split <;> simp

theorem truncTails_apply (D' : Divisor X) (t : GlobalTails X) (q : X × ℤ) :
    truncTails D' t q = if q.2 < -(D' q.1) then t q else 0 := by
  simp [truncTails, Finsupp.filter_apply]

/-- The truncation lands in `𝒯[D']`. -/
theorem truncTails_mem (D' : Divisor X) (t : GlobalTails X) :
    truncTails D' t ∈ tailSpace D' := by
  rw [mem_tailSpace_iff]
  intro q hq
  rw [truncTails_apply, if_neg (by omega)]

/-- The truncation is the identity on `𝒯[D']`. -/
theorem truncTails_eq_self_of_mem {D' : Divisor X} {t : GlobalTails X}
    (ht : t ∈ tailSpace D') : truncTails D' t = t := by
  ext q
  rw [truncTails_apply]
  split
  · rfl
  · exact ((mem_tailSpace_iff.mp ht) q (by omega)).symm

/-! ## Part 2b — the upper space (the complement of the tail region)

`H¹` lives as a quotient of the FULL ambient `GlobalTails X` by `im α_D ⊔ 𝒰[D]` (the
upper space of terms at orders `≥ −D`), avoiding subtype quotients. -/

/-- **The upper space `𝒰[D]`**: formal tails supported at orders `≥ −D(p)` — the complement
of `𝒯[D]`. -/
def upperSpace (D : Divisor X) : Submodule ℂ (GlobalTails X) :=
  Finsupp.supported ℂ ℂ (belowSet D)ᶜ

theorem mem_upperSpace_iff {D : Divisor X} {t : GlobalTails X} :
    t ∈ upperSpace D ↔ ∀ q : X × ℤ, q.2 < -(D q.1) → t q = 0 := by
  constructor
  · intro ht q hq
    by_contra hne
    have hsupp : q ∈ t.support := Finsupp.mem_support_iff.mpr hne
    have := ht hsupp
    simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq] at this
    omega
  · intro h q hq
    simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq, not_lt]
    by_contra hout
    exact (Finsupp.mem_support_iff.mp hq) (h q (by omega))

/-- The upper spaces are monotone (`D ≤ D'` allows more upper terms). -/
theorem upperSpace_mono {D D' : Divisor X} (h : ∀ x, D x ≤ D' x) :
    upperSpace (X := X) D ≤ upperSpace D' := by
  refine Finsupp.supported_mono ?_
  intro q hq
  simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq, not_lt] at hq ⊢
  have := h q.1
  omega

/-- Tail and upper space are complementary: together they span everything. -/
theorem tailSpace_sup_upperSpace (D : Divisor X) :
    tailSpace (X := X) D ⊔ upperSpace D = ⊤ := by
  rw [tailSpace, upperSpace, ← Finsupp.supported_union, Set.union_compl_self,
    Finsupp.supported_univ]

/-- … and they intersect trivially. -/
theorem tailSpace_inf_upperSpace (D : Divisor X) :
    Disjoint (tailSpace (X := X) D) (upperSpace D) :=
  Finsupp.disjoint_supported_supported disjoint_compl_right

/-- The un-truncated part lies in the upper space (ambient form). -/
theorem sub_truncTails_mem_upperSpace (D' : Divisor X) (t : GlobalTails X) :
    t - truncTails D' t ∈ upperSpace D' := by
  rw [mem_upperSpace_iff]
  intro q hq
  rw [Finsupp.sub_apply, truncTails_apply, if_pos hq, sub_self]

/-- Truncation kills the upper space. -/
theorem truncTails_eq_zero_of_mem_upperSpace {D' : Divisor X} {u : GlobalTails X}
    (hu : u ∈ upperSpace D') : truncTails D' u = 0 := by
  ext q
  rw [truncTails_apply, Finsupp.coe_zero, Pi.zero_apply]
  split
  · exact mem_upperSpace_iff.mp hu q (by assumption)
  · rfl

/-- Truncations compose: the deeper cut wins (`D ≤ D'`). -/
theorem truncTails_comp {D D' : Divisor X} (hDD' : ∀ x, D x ≤ D' x) (t : GlobalTails X) :
    truncTails D' (truncTails D t) = truncTails D' t := by
  ext q
  rw [truncTails_apply, truncTails_apply, truncTails_apply]
  have := hDD' q.1
  by_cases h' : q.2 < -(D' q.1)
  · rw [if_pos h', if_pos h', if_pos (by omega)]
  · rw [if_neg h', if_neg h']

/-! ## Part 3 — the window and its dimension -/

/-- The truncation window region `[−D'(p), −D(p))`. -/
def windowSet (D D' : Divisor X) : Set (X × ℤ) := belowSet D \ belowSet D'

/-- **The window space**: tails living in the truncation window. -/
def windowSpace (D D' : Divisor X) : Submodule ℂ (GlobalTails X) :=
  Finsupp.supported ℂ ℂ (windowSet D D')

/-- The window region as an explicit finite set. -/
def windowFinset (D D' : Divisor X) : Finset (X × ℤ) :=
  (D' - D).support.biUnion fun p => ({p} : Finset X) ×ˢ Finset.Ico (-(D' p)) (-(D p))

theorem coe_windowFinset (D D' : Divisor X) :
    (windowFinset D D' : Set (X × ℤ)) = windowSet D D' := by
  ext q
  simp only [windowFinset, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico, windowSet, belowSet,
    Set.mem_diff, Set.mem_setOf_eq, Finsupp.mem_support_iff, Finsupp.sub_apply, not_lt]
  constructor
  · rintro ⟨p, hp, ⟨rfl, h1, h2⟩⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    refine ⟨q.1, ?_, rfl, h1, h2⟩
    omega

/-- The window split of a `𝒯[D]` tail: the truncated part plus the window part. -/
theorem sub_truncTails_mem_windowSpace {D D' : Divisor X} {t : GlobalTails X}
    (ht : t ∈ tailSpace D) : t - truncTails D' t ∈ windowSpace D D' := by
  intro q hq
  have hval : (t - truncTails D' t) q ≠ 0 := Finsupp.mem_support_iff.mp hq
  rw [Finsupp.sub_apply, truncTails_apply] at hval
  simp only [windowSet, belowSet, Set.mem_diff, Set.mem_setOf_eq, not_lt]
  by_cases hcut : q.2 < -(D' q.1)
  · rw [if_pos hcut, sub_self] at hval
    exact absurd rfl hval
  · rw [if_neg hcut, sub_zero] at hval
    refine ⟨?_, by omega⟩
    by_contra hbig
    exact hval (mem_tailSpace_iff.mp ht q (by omega))

/-- The window space is finite-dimensional (the window region is finite). -/
theorem finiteDimensional_windowSpace (D D' : Divisor X) :
    FiniteDimensional ℂ (windowSpace D D') := by
  rw [windowSpace, ← coe_windowFinset]
  exact (Finsupp.supportedEquivFinsupp
    (↑(windowFinset D D') : Set (X × ℤ))).symm.finiteDimensional

theorem card_windowFinset {D D' : Divisor X} (hDD' : ∀ x, D x ≤ D' x) :
    (windowFinset D D').card = (Divisor.deg X D' - Divisor.deg X D).toNat := by
  classical
  rw [windowFinset, Finset.card_biUnion]
  · have hterm : ∀ p ∈ (D' - D).support,
        (({p} : Finset X) ×ˢ Finset.Ico (-(D' p)) (-(D p))).card = (D' p - D p).toNat := by
      intro p _
      rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm]
    have hcast : ((∑ p ∈ (D' - D).support, (D' p - D p).toNat : ℕ) : ℤ)
        = Divisor.deg X D' - Divisor.deg X D := by
      push_cast
      have hpos : ∀ p ∈ (D' - D).support, ((D' p - D p).toNat : ℤ) = D' p - D p := by
        intro p _
        have := hDD' p
        omega
      rw [Finset.sum_congr rfl hpos]
      have hdeg : Divisor.deg X (D' - D) = ∑ p ∈ (D' - D).support, (D' p - D p) := by
        rw [show Divisor.deg X (D' - D) = Finsupp.degree (D' - D) from rfl,
          Finsupp.degree_apply]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finsupp.sub_apply]
      rw [← hdeg, Divisor.deg_sub]
    omega
  · intro p hp p' hp' hpp'
    refine Finset.disjoint_left.mpr ?_
    intro q hq hq'
    rw [Finset.mem_product, Finset.mem_singleton] at hq hq'
    exact hpp' (hq.1 ▸ hq'.1 ▸ rfl)

/-- **The window dimension**: `dim 𝒲(D, D') = deg D' − deg D` (`D ≤ D'`). -/
theorem finrank_windowSpace {D D' : Divisor X} (hDD' : ∀ x, D x ≤ D' x) :
    Module.finrank ℂ (windowSpace D D')
      = (Divisor.deg X D' - Divisor.deg X D).toNat := by
  rw [windowSpace, ← coe_windowFinset,
    (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
      (↑(windowFinset D D') : Set (X × ℤ))).finrank_eq,
    (Finsupp.linearEquivFunOnFinite ℂ ℂ _).finrank_eq, Module.finrank_pi]
  simp [card_windowFinset hDD']

/-- **The Pi-model of the window** — instance-clean for the quotient/lift machinery
(`Finsupp`-subtype targets choke `liftQ`-style unification; Pi targets do not). -/
abbrev WindowModel (D D' : Divisor X) : Type _ :=
  (↑(windowFinset D D') : Set (X × ℤ)) → ℂ

/-- The window space in its Pi-model coordinates. -/
noncomputable def windowModelEquiv (D D' : Divisor X) :
    ↥(windowSpace (X := X) D D') ≃ₗ[ℂ] WindowModel D D' :=
  (LinearEquiv.ofEq _ _ (by rw [windowSpace, ← coe_windowFinset])).trans
    ((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
      (↑(windowFinset D D') : Set (X × ℤ))).trans
      (Finsupp.linearEquivFunOnFinite ℂ ℂ _))

/-- **The window dimension, Pi-model form**: `dim 𝒲(D, D') = deg D' − deg D` (`D ≤ D'`). -/
theorem finrank_windowModel {D D' : Divisor X} (hDD' : ∀ x, D x ≤ D' x) :
    Module.finrank ℂ (WindowModel (X := X) D D')
      = (Divisor.deg X D' - Divisor.deg X D).toNat := by
  rw [Module.finrank_pi]
  simp [card_windowFinset hDD']

/-! ## Part 4 — the Laurent tail map `α_D` -/

/-- The truncated Laurent tail of `f` below the `−D` cut, as a global formal tail (window
bottom = the order at each contributing point). -/
def tailMapFun (D : Divisor X) (f : MeromorphicFunction X) : GlobalTails X :=
  ∑ p ∈ D.support ∪ f.div.support,
    ∑ k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p)),
      Finsupp.single (p, k) (f.coeffAt p k)

/-- **The coefficient law of the tail map** — the workhorse: `α_D f` reads the full Laurent
coefficient strictly below the cut, `0` at and above it. -/
theorem tailMapFun_apply (D : Divisor X) (f : MeromorphicFunction X) (p : X) (k : ℤ) :
    tailMapFun D f (p, k) = if k < -(D p) then f.coeffAt p k else 0 := by
  classical
  rw [tailMapFun, Finsupp.finsetSum_apply]
  have hinner : ∀ p' : X,
      (∑ k' ∈ Finset.Ico (min ((f.orderW p').untop₀) (-(D p'))) (-(D p')),
        Finsupp.single (p', k') (f.coeffAt p' k')) (p, k)
      = if p' = p
        then (if k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p))
          then f.coeffAt p k else 0)
        else 0 := by
    intro p'
    rw [Finsupp.finsetSum_apply]
    rcases eq_or_ne p' p with rfl | hne
    · rw [if_pos rfl]
      simp only [Finsupp.single_apply, Prod.mk.injEq, true_and]
      exact Finset.sum_ite_eq' _ k (fun k' => f.coeffAt p' k')
    · rw [if_neg hne]
      refine Finset.sum_eq_zero fun k' _ => ?_
      rw [Finsupp.single_apply, if_neg]
      simp only [Prod.mk.injEq, not_and]
      exact fun h => absurd h hne
  rw [Finset.sum_congr rfl (fun p' _ => hinner p'),
    Finset.sum_ite_eq' (D.support ∪ f.div.support) p
      (fun _ => if k ∈ Finset.Ico (min ((f.orderW p).untop₀) (-(D p))) (-(D p))
        then f.coeffAt p k else 0)]
  by_cases hmem : p ∈ D.support ∪ f.div.support
  · rw [if_pos hmem]
    simp only [Finset.mem_Ico]
    by_cases hcut : k < -(D p)
    · rw [if_pos hcut]
      by_cases hbot : min ((f.orderW p).untop₀) (-(D p)) ≤ k
      · rw [if_pos ⟨hbot, hcut⟩]
      · rw [if_neg (by omega)]
        have hk : k < (f.orderW p).untop₀ := by omega
        exact (MeromorphicFunction.coeffAt_eq_zero_of_lt_untop₀ hk).symm
    · rw [if_neg hcut, if_neg (by omega)]
  · rw [if_neg hmem]
    rw [Finset.mem_union, not_or] at hmem
    by_cases hcut : k < -(D p)
    · rw [if_pos hcut]
      have hD0 : D p = 0 := Finsupp.notMem_support_iff.mp hmem.1
      have hord := MeromorphicFunction.orderW_nonneg_of_not_mem_div_support hmem.2
      refine (MeromorphicFunction.coeffAt_eq_zero_of_coe_lt_orderW ?_).symm
      refine lt_of_lt_of_le ?_ hord
      exact_mod_cast (by omega : k < 0)
    · rw [if_neg hcut]

/-- **The Laurent tail map `α_D`** as a linear map (linearity from the `coeffAt` algebra). -/
def tailMap (D : Divisor X) : MeromorphicFunction X →ₗ[ℂ] GlobalTails X where
  toFun := tailMapFun D
  map_add' f g := by
    ext q
    obtain ⟨p, k⟩ := q
    rw [Finsupp.add_apply, tailMapFun_apply, tailMapFun_apply, tailMapFun_apply,
      MeromorphicFunction.coeffAt_add]
    split <;> simp
  map_smul' a f := by
    ext q
    obtain ⟨p, k⟩ := q
    rw [RingHom.id_apply, Finsupp.smul_apply, tailMapFun_apply, tailMapFun_apply,
      MeromorphicFunction.coeffAt_smul, smul_eq_mul]
    split <;> simp

@[simp] theorem tailMap_apply_coeff (D : Divisor X) (f : MeromorphicFunction X) (p : X)
    (k : ℤ) : tailMap D f (p, k) = if k < -(D p) then f.coeffAt p k else 0 :=
  tailMapFun_apply D f p k

/-- `α_D` lands in `𝒯[D]`. -/
theorem tailMap_mem_tailSpace (D : Divisor X) (f : MeromorphicFunction X) :
    tailMap D f ∈ tailSpace D := by
  rw [mem_tailSpace_iff]
  intro q hq
  obtain ⟨p, k⟩ := q
  rw [tailMap_apply_coeff, if_neg (by simpa using not_lt.mpr hq)]

/-- **The kernel identity `ker α_D = L(D)`** (the order law, pointwise). -/
theorem tailMap_eq_zero_iff (D : Divisor X) (f : MeromorphicFunction X) :
    tailMap D f = 0 ↔ f ∈ linearSystem (X := X) D := by
  constructor
  · intro h0 p
    refine (MeromorphicFunction.orderW_ge_iff_coeffAt_vanish f p (-(D p))).mpr ?_
    intro k hk
    have := congrArg (fun t : GlobalTails X => t (p, k)) h0
    simpa [tailMap_apply_coeff, if_pos hk] using this
  · intro hf
    ext q
    obtain ⟨p, k⟩ := q
    rw [tailMap_apply_coeff, Finsupp.coe_zero, Pi.zero_apply]
    split
    · exact (MeromorphicFunction.orderW_ge_iff_coeffAt_vanish f p (-(D p))).mp (hf p) k
        (by omega)
    · rfl

/-- Germ-zero junk does not move the tail map (well-definedness on `lSysModule` classes). -/
theorem tailMap_eq_of_sub_germZero {f f' : MeromorphicFunction X}
    (hd : f - f' ∈ germZeroSubmodule (X := X)) (D : Divisor X) :
    tailMap D f = tailMap D f' := by
  ext q
  obtain ⟨p, k⟩ := q
  rw [tailMap_apply_coeff, tailMap_apply_coeff,
    MeromorphicFunction.coeffAt_eq_of_sub_germZero hd p k]

/-- **Level compatibility**: truncating the level-`D` tail gives the level-`D'` tail
(`D ≤ D'`). -/
theorem truncTails_tailMap {D D' : Divisor X} (hDD' : ∀ x, D x ≤ D' x)
    (f : MeromorphicFunction X) :
    truncTails D' (tailMap D f) = tailMap D' f := by
  ext q
  obtain ⟨p, k⟩ := q
  rw [truncTails_apply, tailMap_apply_coeff, tailMap_apply_coeff]
  have := hDD' p
  by_cases h' : k < -(D' p)
  · rw [if_pos h', if_pos (by omega), if_pos h']
  · rw [if_neg h', if_neg h']

end Dolbeault

end Jacobians

end
