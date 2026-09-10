/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSerre
import KirovDolbeault.Dolbeault.SerreDuality
import KirovDolbeault.Dolbeault.SerreResidueRamifiedRealCover

/-!
# The surjectivity half of tail Serre duality (Miranda VI.3.10) — tail tower T7

Over the T1–T6 substrate (`TailSerre.lean`, route `docs/planning/TAILRR_ROUTE.md`): for every
tail pair frame `P` and every divisor `D`, the residue pairing
`pairingL D : L(K−D)/junk →ₗ Dual(H¹_t(D))` is SURJECTIVE — discharging the named residual
input `P.PairingSurjective` of `tailRiemannRoch_of_pairingSurjective`, so that
`TailRiemannRoch X` now rests on frame existence (`Nonempty (TailPairFrame X)`) alone.

The proof is Miranda's recovery + growth pigeonhole, executed in pure Laurent-coefficient
algebra:

* Part A — the **general window product law** `planarCoeff_mul_window`
  (`c_m(A·B) = ∑_{k ∈ [lo,hi)} c_k(A)·c_{m−k}(B)` for `ord B ≥ m+1−hi`), derived from the
  proven residue case `resCoeff_mul_window` by the monomial shift, and the monomial
  coefficient spectrum `planarCoeff_zpow_self`.
* Part B — the X-level product law `coeffAt_mul_window`.
* Part C — the **multiplication–truncation operator** `mulTail f D : 𝒯 → 𝒯[D]`
  (`t ↦ trunc_D(f·t)` in coefficients), with: linearity in `f`, the upper kill
  (`f ∈ L(E)` sends `𝒰[D−E]` to `0`), the **transport identity**
  `mulTail f D (α_{D−E} g) = α_D (f·g)`, and the **local inverse tails**
  `invMonomialTail f p k lo hi` (the tail of `z^k/f` at `p`) with
  `mulTail f D (invMonomialTail …) = trunc_D(z^k at p)` — the division step, via the
  identity theorem `orderW_ne_top_of_exists` and `MeromorphicAt.inv`.
* Part D — the descended multiplication `mulH1 : H¹_t(D−E) → H¹_t(D)` (surjective for
  `f ≠ 0`), and the `ψ`-action on functionals `tailPsiAct φ : L(E)/junk →ₗ Dual(H¹_t(D−E))`,
  injective for `φ ≠ 0` (Miranda's Lemma VI.3.8 analogue).
* Part E — the **unwind** (Miranda VI.3.7/VI.3.9 analogue): a pigeonhole witness
  `ψ·φ = pairingL_{D−E}(w)` with `ψ ≠ 0` yields `g := w·ψ⁻¹ ∈ L(K−D)` with
  `pairingL D (g) = φ`, all by evaluating both sides on the local inverse tails.
* Part F — the **headline**: `TailPairFrame.pairingSurjective` via
  `serre_surjectivity_dim_core` over the proven `tail_riemannRoch_I` arithmetic, and the
  unconditional-in-`PairingSurjective` upgrades `TailPairFrame.tailRiemannRoch_of_frame`,
  `h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame'`.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI §3,
Proposition 3.10 and Lemmas 3.6–3.9; Forster (GTM 81) §17.9 for the count.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians

namespace Dolbeault

/-! ## Part A — planar supplements: the monomial spectrum and the general window law -/

variable {F G A B : ℂ → ℂ} {c : ℂ}

/-- **The monomial coefficient spectrum**: `c_m((z−c)^k) = δ_{mk}` at every order `m`. -/
theorem planarCoeff_zpow_self (m k : ℤ) (c : ℂ) :
    planarCoeff m (fun z => (z - c) ^ k) c = if m = k then 1 else 0 := by
  have hmer : MeromorphicAt (fun z => (z - c) ^ k) c := meromorphicAt_zpow_self c k
  have hord : meromorphicOrderAt (fun z => (z - c) ^ k) c = (k : WithTop ℤ) :=
    meromorphicOrderAt_zpow_self k c
  rcases lt_trichotomy m k with hmk | rfl | hmk
  · rw [if_neg (by omega)]
    refine planarCoeff_eq_zero_of_lt_order ?_ hmer
    rw [hord]
    exact_mod_cast hmk
  · rw [if_pos rfl, planarCoeff_eq_fullCoeffFrom hmer (le_of_eq hord.symm) le_rfl,
      sub_self, Int.toNat_zero, fullCoeffFrom_offset_zero', laurentCoeff_zpow_self]
  · -- above the top: every strip beyond the leading term is the zero function
    have hstrip : ∀ j : ℕ, stripFun (fun z => (z - c) ^ k) c k (j + 1) = fun _ => (0 : ℂ) := by
      intro j
      induction j with
      | zero =>
        funext z
        rw [stripFun_succ]
        show stripFun (fun z => (z - c) ^ k) c k 0 z
            - laurentCoeff (k + (0 : ℕ)) (stripFun (fun z => (z - c) ^ k) c k 0) c
              * (z - c) ^ (k + (0 : ℕ)) = 0
        rw [stripFun_zero_iter]
        push_cast
        rw [add_zero, laurentCoeff_zpow_self]
        ring
      | succ j ih =>
        funext z
        rw [stripFun_succ, ih]
        show (0 : ℂ) - laurentCoeff (k + (j + 1 : ℕ)) (fun _ => (0 : ℂ)) c
            * (z - c) ^ (k + (j + 1 : ℕ)) = 0
        rw [show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]
        ring
    rw [if_neg (by omega), planarCoeff_eq_fullCoeffFrom hmer (le_of_eq hord.symm) (by omega)]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (m - k).toNat = j + 1 :=
      ⟨(m - k).toNat - 1, by omega⟩
    rw [hj, fullCoeffFrom, hstrip j,
      show (fun _ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, laurentCoeff_zero_fun]

/-- **The general window product law** (`resCoeff_mul_window` at every order `m`): the
order-`m` coefficient of a product reads the window coefficients of `A` against the shifted
coefficients of `B`, provided `B`'s order clears the window top (`ord B ≥ m + 1 − hi`). -/
theorem planarCoeff_mul_window (hA : MeromorphicAt A c) (hB : MeromorphicAt B c)
    {lo hi m : ℤ} (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt A c) (hlohi : lo ≤ hi)
    (hBord : ((m + 1 - hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B c) :
    planarCoeff m (fun z => A z * B z) c
      = ∑ k ∈ Finset.Ico lo hi, planarCoeff k A c * planarCoeff (m - k) B c := by
  -- shift `B` by `(z−c)^{−1−m}` and apply the residue case
  set B' : ℂ → ℂ := fun z => (z - c) ^ (-1 - m) * B z with hB'def
  have hB' : MeromorphicAt B' c := (meromorphicAt_zpow_self c (-1 - m)).mul hB
  have hB'ord : ((-hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt B' c := by
    have hmul : meromorphicOrderAt B' c
        = ((-1 - m : ℤ) : WithTop ℤ) + meromorphicOrderAt B c := by
      rw [hB'def, show (fun z => (z - c) ^ (-1 - m) * B z)
          = (fun z => (z - c) ^ (-1 - m)) * B from rfl,
        meromorphicOrderAt_mul (meromorphicAt_zpow_self c (-1 - m)) hB,
        meromorphicOrderAt_zpow_self]
    rw [hmul]
    calc ((-hi : ℤ) : WithTop ℤ)
        = ((-1 - m : ℤ) : WithTop ℤ) + ((m + 1 - hi : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          ring
      _ ≤ ((-1 - m : ℤ) : WithTop ℤ) + meromorphicOrderAt B c :=
          add_le_add le_rfl hBord
  have hlaw := resCoeff_mul_window hA hB' hlo hlohi hB'ord
  -- LHS: `c_{−1}(A·B') = c_{−1}((z−c)^{−1−m}·(A·B)) = c_m(A·B)`
  have hL : planarCoeff (-1) (fun z => A z * B' z) c
      = planarCoeff m (fun z => A z * B z) c := by
    have hfun : (fun z => A z * B' z)
        = fun z => (z - c) ^ (-1 - m) * (A z * B z) := by
      funext z
      rw [hB'def]
      ring
    have h1 : planarCoeff (-1) (fun z => (z - c) ^ (-1 - m) * (A z * B z)) c
        = planarCoeff (-1 - (-1 - m)) (fun z => A z * B z) c :=
      planarCoeff_monomial_mul (-1 - m) (-1) (hA.mul hB)
    rw [hfun, h1, show (-1 - (-1 - m) : ℤ) = m from by ring]
  -- RHS: `c_{−1−k}(B') = c_{m−k}(B)` termwise
  have hR : ∀ k ∈ Finset.Ico lo hi,
      planarCoeff k A c * planarCoeff (-1 - k) B' c
        = planarCoeff k A c * planarCoeff (m - k) B c := by
    intro k _
    rw [hB'def, planarCoeff_monomial_mul (-1 - m) (-1 - k) hB,
      show (-1 - k - (-1 - m) : ℤ) = m - k from by ring]
  rw [← hL, hlaw]
  exact Finset.sum_congr rfl hR

/-- Level helper: `min(untop₀ o, x)` is a valid level below `o` for every `o : WithTop ℤ`. -/
theorem coe_min_untop₀_le_self (o : WithTop ℤ) (x : ℤ) :
    ((min o.untop₀ x : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe n =>
    rw [WithTop.untop₀_coe]
    exact_mod_cast min_le_left n x

/-! ## Part B — the X-level product window law -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The X-level product window law** (window on the SECOND factor `g`): for `m` cleared by
`f`'s order (`ord_p f ≥ m + 1 − hi`),
`c_m(f·g) = ∑_{k ∈ [lo,hi)} c_k(g)·c_{m−k}(f)`. -/
theorem MeromorphicFunction.coeffAt_mul_window (f g : MeromorphicFunction X) (p : X)
    {lo hi m : ℤ} (hlo : (lo : WithTop ℤ) ≤ g.orderW p) (hlohi : lo ≤ hi)
    (hford : ((m + 1 - hi : ℤ) : WithTop ℤ) ≤ f.orderW p) :
    (f * g).coeffAt p m
      = ∑ k ∈ Finset.Ico lo hi, g.coeffAt p k * f.coeffAt p (m - k) := by
  classical
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set Af : ℂ → ℂ := f.toFun ∘ (chartAt (H := ℂ) p).symm with hAf
  set Ag : ℂ → ℂ := g.toFun ∘ (chartAt (H := ℂ) p).symm with hAg
  have hAfm : MeromorphicAt Af c := f.meromorphic p
  have hAgm : MeromorphicAt Ag c := g.meromorphic p
  have hlaw := planarCoeff_mul_window hAgm hAfm (m := m) hlo hlohi hford
  have hread : (f * g).coeffAt p m = planarCoeff m (fun z => Ag z * Af z) c := by
    show planarCoeff m ((f * g).toFun ∘ (chartAt (H := ℂ) p).symm) c
        = planarCoeff m (fun z => Ag z * Af z) c
    congr 1
    funext z
    show f.toFun ((chartAt (H := ℂ) p).symm z) * g.toFun ((chartAt (H := ℂ) p).symm z)
        = Ag z * Af z
    rw [hAf, hAg]
    show f.toFun ((chartAt (H := ℂ) p).symm z) * g.toFun ((chartAt (H := ℂ) p).symm z)
        = g.toFun ((chartAt (H := ℂ) p).symm z) * f.toFun ((chartAt (H := ℂ) p).symm z)
    ring
  rw [hread, hlaw]
  rfl

/-! ## Part C — the multiplication–truncation operator `mulTail` -/

/-- **The single-slot multiplication tail**: the `D`-truncated tail of `f·(z^k at p)` — the
window `[min(ord f + k, −D p), −D p)` of shifted full coefficients of `f`. -/
def mulTailSingle (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) : GlobalTails X :=
  ∑ m ∈ Finset.Ico (min ((f.orderW q.1).untop₀ + q.2) (-(D q.1))) (-(D q.1)),
    Finsupp.single (q.1, m) (f.coeffAt q.1 (m - q.2))

/-- **The coefficient law of the single-slot tail**: the read at `(p', m)` is the shifted
coefficient `c_{m−k}(f)` strictly below the cut at `p`, `0` elsewhere. -/
theorem mulTailSingle_apply (f : MeromorphicFunction X) (D : Divisor X) (p : X) (k : ℤ)
    (p' : X) (m : ℤ) :
    mulTailSingle f D (p, k) (p', m)
      = if p' = p ∧ m < -(D p) then f.coeffAt p (m - k) else 0 := by
  classical
  rw [mulTailSingle, Finsupp.finsetSum_apply]
  rcases eq_or_ne p' p with rfl | hne
  · have hterm : ∀ m' ∈ Finset.Ico (min ((f.orderW (p', k).1).untop₀ + (p', k).2)
        (-(D (p', k).1))) (-(D (p', k).1)),
        (Finsupp.single ((p', k).1, m') (f.coeffAt (p', k).1 (m' - (p', k).2))) (p', m)
          = if m' = m then f.coeffAt p' (m - k) else 0 := by
      intro m' _
      rw [Finsupp.single_apply]
      simp only [Prod.mk.injEq, true_and]
      rcases eq_or_ne m' m with rfl | hm'
      · simp
      · rw [if_neg hm', if_neg hm']
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ m fun _ => f.coeffAt p' (m - k)]
    simp only [Finset.mem_Ico, true_and]
    by_cases hcut : m < -(D p')
    · rw [if_pos hcut]
      by_cases hbot : min ((f.orderW p').untop₀ + k) (-(D p')) ≤ m
      · rw [if_pos ⟨hbot, hcut⟩]
      · rw [if_neg (by omega)]
        have hk : m - k < (f.orderW p').untop₀ := by omega
        exact (MeromorphicFunction.coeffAt_eq_zero_of_lt_untop₀ hk).symm
    · rw [if_neg hcut, if_neg (by omega)]
  · rw [if_neg (by simp [hne])]
    refine Finset.sum_eq_zero fun m' _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp only [Prod.mk.injEq, not_and]
    exact fun h => absurd h.symm hne

/-- The single-slot tail lands strictly below the cut. -/
theorem mulTailSingle_mem_tailSpace (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle f D q ∈ tailSpace D := by
  obtain ⟨p, k⟩ := q
  rw [mem_tailSpace_iff]
  intro q' hq'
  obtain ⟨p', m⟩ := q'
  rw [mulTailSingle_apply]
  rcases eq_or_ne p' p with rfl | hne
  · rw [if_neg (by simp only [true_and, not_lt]; exact hq')]
  · rw [if_neg (by simp [hne])]

/-- **The multiplication–truncation operator** `t ↦ trunc_D(f·t)`, in coefficients. -/
def mulTail (f : MeromorphicFunction X) (D : Divisor X) :
    GlobalTails X →ₗ[ℂ] GlobalTails X :=
  Finsupp.lsum ℂ fun q => LinearMap.toSpanSingleton ℂ (GlobalTails X) (mulTailSingle f D q)

@[simp] theorem mulTail_single (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ)
    (a : ℂ) : mulTail f D (Finsupp.single q a) = a • mulTailSingle f D q := by
  rw [mulTail, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem mulTail_apply (f : MeromorphicFunction X) (D : Divisor X) (t : GlobalTails X) :
    mulTail f D t = t.sum fun q a => a • mulTailSingle f D q := by
  rw [mulTail, Finsupp.lsum_apply]
  exact Finsupp.sum_congr fun q _ => LinearMap.toSpanSingleton_apply ℂ _ _ _

/-- `mulTail` lands in `𝒯[D]`. -/
theorem mulTail_mem_tailSpace (f : MeromorphicFunction X) (D : Divisor X)
    (t : GlobalTails X) : mulTail f D t ∈ tailSpace D := by
  rw [mulTail_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun q _ => ?_
  exact Submodule.smul_mem _ _ (mulTailSingle_mem_tailSpace f D q)

/-- **The point-tail evaluation** (the shared bookkeeping engine): `mulTail` of a
single-point coefficient window reads the window sum of shifted coefficients below the
cut. -/
theorem mulTail_pointTail_apply (f : MeromorphicFunction X) (D : Divisor X) (p : X)
    (s : Finset ℤ) (φ : ℤ → ℂ) (p' : X) (m : ℤ) :
    mulTail f D (∑ j ∈ s, Finsupp.single (p, j) (φ j)) (p', m)
      = if p' = p ∧ m < -(D p) then ∑ j ∈ s, φ j * f.coeffAt p (m - j) else 0 := by
  classical
  rw [map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ j ∈ s, (mulTail f D (Finsupp.single (p, j) (φ j))) (p', m)
      = if p' = p ∧ m < -(D p) then φ j * f.coeffAt p (m - j) else 0 := by
    intro j _
    rw [mulTail_single, Finsupp.smul_apply, mulTailSingle_apply, smul_eq_mul]
    split
    · rfl
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hcond : p' = p ∧ m < -(D p)
  · rw [if_pos hcond]
    exact Finset.sum_congr rfl fun j _ => by rw [if_pos hcond]
  · rw [if_neg hcond]
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hcond]

/-! ### Linearity of `mulTail` in the function -/

theorem mulTailSingle_add (f g : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle (f + g) D q = mulTailSingle f D q + mulTailSingle g D q := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [Finsupp.add_apply, mulTailSingle_apply, mulTailSingle_apply, mulTailSingle_apply,
    MeromorphicFunction.coeffAt_add]
  split <;> simp

theorem mulTailSingle_smul (a : ℂ) (f : MeromorphicFunction X) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle (a • f) D q = a • mulTailSingle f D q := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [Finsupp.smul_apply, mulTailSingle_apply, mulTailSingle_apply,
    MeromorphicFunction.coeffAt_smul, smul_eq_mul]
  split <;> simp

theorem mulTailSingle_eq_zero_of_germZero {f : MeromorphicFunction X}
    (hf : f ∈ germZeroSubmodule (X := X)) (D : Divisor X) (q : X × ℤ) :
    mulTailSingle f D q = 0 := by
  obtain ⟨p, k⟩ := q
  ext q'
  obtain ⟨p', m⟩ := q'
  rw [mulTailSingle_apply, Finsupp.coe_zero, Pi.zero_apply,
    MeromorphicFunction.coeffAt_of_orderW_eq_top (hf p)]
  split <;> rfl

theorem mulTail_add_fun (f g : MeromorphicFunction X) (D : Divisor X) :
    mulTail (f + g) D = mulTail f D + mulTail g D := by
  refine Finsupp.lhom_ext fun q a => ?_
  rw [LinearMap.add_apply, mulTail_single, mulTail_single, mulTail_single,
    mulTailSingle_add, smul_add]

theorem mulTail_smul_fun (a : ℂ) (f : MeromorphicFunction X) (D : Divisor X) :
    mulTail (a • f) D = a • mulTail f D := by
  refine Finsupp.lhom_ext fun q b => ?_
  rw [LinearMap.smul_apply, mulTail_single, mulTail_single, mulTailSingle_smul,
    smul_comm]

theorem mulTail_eq_zero_of_germZero {f : MeromorphicFunction X}
    (hf : f ∈ germZeroSubmodule (X := X)) (D : Divisor X) :
    mulTail f D = 0 := by
  refine Finsupp.lhom_ext fun q a => ?_
  rw [mulTail_single, mulTailSingle_eq_zero_of_germZero hf D q, smul_zero,
    LinearMap.zero_apply]

/-! ### The upper kill and the transport identity -/

/-- **The upper kill**: for `f ∈ L(E)`, `mulTail f D` annihilates the upper space
`𝒰[D−E]` (the truncation depth clears the multiplier's pole bound). -/
theorem mulTail_eq_zero_of_mem_upperSpace {E : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (D : Divisor X) {u : GlobalTails X}
    (hu : u ∈ upperSpace (D - E)) : mulTail f D u = 0 := by
  classical
  rw [mulTail_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨p, k⟩ := q
  have hcut : -(D p) + E p ≤ k := by
    have hmem := hu hq
    simp only [Set.mem_compl_iff, belowSet, Set.mem_setOf_eq, not_lt, Finsupp.sub_apply]
      at hmem
    omega
  have hzero : mulTailSingle f D (p, k) = 0 := by
    ext q'
    obtain ⟨p', m⟩ := q'
    rw [mulTailSingle_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rename_i hcond
      refine MeromorphicFunction.coeffAt_eq_zero_of_coe_lt_orderW ?_
      refine lt_of_lt_of_le ?_ (hf p)
      exact_mod_cast (by omega : m - k < -(E p))
    · rfl
  rw [hzero, smul_zero]

/-- **The transport identity** (the engine of the descended multiplication): for
`f ∈ L(E)`, multiplying the level-`(D−E)` tail of `g` and truncating at `D` is the
level-`D` tail of `f·g`: `mulTail f D (α_{D−E} g) = α_D (f·g)`. -/
theorem mulTail_tailMap {E : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) E) (D : Divisor X) (g : MeromorphicFunction X) :
    mulTail f D (tailMap (D - E) g) = tailMap D (f * g) := by
  classical
  ext q
  obtain ⟨p, m⟩ := q
  rw [show tailMap (D - E) g = tailMapFun (D - E) g from rfl, tailMapFun, map_sum,
    Finsupp.finsetSum_apply, tailMap_apply_coeff]
  set S : Finset X := (D - E).support ∪ g.div.support with hS
  have hterm : ∀ p' ∈ S,
      (mulTail f D (∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), Finsupp.single (p', k) (g.coeffAt p' k))) (p, m)
      = if p = p' ∧ m < -(D p') then
          ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
            (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k)
        else 0 := by
    intro p' _
    exact mulTail_pointTail_apply f D p' _ _ p m
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∀ p' : X, (if p = p' ∧ m < -(D p') then
      ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0)
      = if p = p' then (if m < -(D p') then
          ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
            (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0)
        else 0 := by
    intro p'
    by_cases h1 : p = p'
    · by_cases h2 : m < -(D p')
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
      · rw [if_neg (by tauto), if_pos h1, if_neg h2]
    · rw [if_neg (by tauto), if_neg h1]
  rw [Finset.sum_congr rfl fun p' _ => hsplit p']
  rw [Finset.sum_ite_eq S p fun p' => if m < -(D p') then
      ∑ k ∈ Finset.Ico (min ((g.orderW p').untop₀) (-((D - E : Divisor X) p')))
        (-((D - E : Divisor X) p')), g.coeffAt p' k * f.coeffAt p' (m - k) else 0]
  -- the window product law identifies the windowed sum with the product coefficient
  have hwindow : m < -(D p) →
      (f * g).coeffAt p m
        = ∑ k ∈ Finset.Ico (min ((g.orderW p).untop₀) (-((D - E : Divisor X) p)))
            (-((D - E : Divisor X) p)), g.coeffAt p k * f.coeffAt p (m - k) := by
    intro hm
    refine MeromorphicFunction.coeffAt_mul_window f g p
      (coe_min_untop₀_le_self _ _) (min_le_right _ _) ?_
    refine le_trans ?_ (hf p)
    have harith : m + 1 - (-((D - E : Divisor X) p)) ≤ -(E p) := by
      rw [Finsupp.sub_apply]
      omega
    exact_mod_cast harith
  by_cases hmem : p ∈ S
  · rw [if_pos hmem]
    by_cases hm : m < -(D p)
    · rw [if_pos hm, if_pos hm, hwindow hm]
    · rw [if_neg hm, if_neg hm]
  · rw [if_neg hmem]
    rw [Finset.mem_union, not_or] at hmem
    by_cases hm : m < -(D p)
    · rw [if_pos hm]
      have hDE0 : (D - E : Divisor X) p = 0 := Finsupp.notMem_support_iff.mp hmem.1
      have hEp : E p = D p := by
        have := Finsupp.sub_apply (g₁ := D) (g₂ := E) (a := p)
        rw [hDE0] at this
        omega
      have hgord : (0 : WithTop ℤ) ≤ g.orderW p :=
        MeromorphicFunction.orderW_nonneg_of_not_mem_div_support hmem.2
      refine (MeromorphicFunction.coeffAt_eq_zero_of_coe_lt_orderW ?_).symm
      rw [MeromorphicFunction.orderW_mul]
      calc ((m : ℤ) : WithTop ℤ) < ((-(E p) : ℤ) : WithTop ℤ) := by
            exact_mod_cast (by omega : m < -(E p))
        _ ≤ f.orderW p := hf p
        _ = f.orderW p + 0 := (add_zero _).symm
        _ ≤ f.orderW p + g.orderW p := add_le_add le_rfl hgord
    · rw [if_neg hm]

/-! ### The local inverse tails (the division step) -/

/-- A single below the cut lies in `𝒯[D]`. -/
theorem single_mem_tailSpace {D : Divisor X} {p : X} {k : ℤ} (hk : k < -(D p)) (a : ℂ) :
    Finsupp.single (p, k) a ∈ tailSpace (X := X) D := by
  rw [mem_tailSpace_iff]
  intro q hq
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact absurd hq (by simpa using hk)

/-- A single at or above the cut lies in `𝒰[D]`. -/
theorem single_mem_upperSpace {D : Divisor X} {p : X} {k : ℤ} (hk : -(D p) ≤ k) (a : ℂ) :
    Finsupp.single (p, k) a ∈ upperSpace (X := X) D := by
  rw [mem_upperSpace_iff]
  intro q hq
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact absurd hq (by simpa using hk)

/-- **The local inverse tail**: the `[lo, hi)` coefficient window of `z^k / f` read in the
chart at `p` — the division witness of Miranda's recovery step (a purely local formal tail;
no global meromorphic inverse data needed beyond the chart read of `f⁻¹`). -/
def invMonomialTail (f : MeromorphicFunction X) (p : X) (k lo hi : ℤ) : GlobalTails X :=
  ∑ j ∈ Finset.Ico lo hi,
    Finsupp.single (p, j)
      (planarCoeff j
        (fun ζ => (ζ - (chartAt (H := ℂ) p) p) ^ k
          * (((f.toFun ∘ (chartAt (H := ℂ) p).symm)) ζ)⁻¹)
        ((chartAt (H := ℂ) p) p))

/-- **The division identity**: multiplying the local inverse tail back by `f` and truncating
at `D` recovers exactly the truncated monomial single — `mulTail f D (tail of z^k/f at p)
= trunc_D (z^k at p)`.  Requires only a finite order `d` of `f` at `p` and a window deep
enough on both sides (`lo ≤ k − d`, `hi ≥ −D p − d`). -/
theorem mulTail_invMonomialTail (f : MeromorphicFunction X) (D : Divisor X) (p : X)
    {k lo hi d : ℤ} (hd : f.orderW p = (d : WithTop ℤ)) (hlo : lo ≤ k - d)
    (hhi : -(D p) - d ≤ hi) (hlohi : lo ≤ hi) :
    mulTail f D (invMonomialTail f p k lo hi)
      = truncTails D (Finsupp.single (p, k) (1 : ℂ)) := by
  classical
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set A : ℂ → ℂ := f.toFun ∘ (chartAt (H := ℂ) p).symm with hA
  set W : ℂ → ℂ := fun ζ => (ζ - c) ^ k * (A ζ)⁻¹ with hW
  have hAm : MeromorphicAt A c := f.meromorphic p
  have hAord : meromorphicOrderAt A c = (d : WithTop ℤ) := hd
  have hWm : MeromorphicAt W c := (meromorphicAt_zpow_self c k).mul hAm.inv
  have hWord : meromorphicOrderAt W c = ((k - d : ℤ) : WithTop ℤ) := by
    rw [hW, show (fun ζ => (ζ - c) ^ k * (A ζ)⁻¹)
        = (fun ζ => (ζ - c) ^ k) * (A⁻¹) from rfl,
      meromorphicOrderAt_mul (meromorphicAt_zpow_self c k) hAm.inv,
      meromorphicOrderAt_zpow_self, meromorphicOrderAt_inv, hAord]
    rw [show -((d : ℤ) : WithTop ℤ) = ((-d : ℤ) : WithTop ℤ) from by simp,
      ← WithTop.coe_add, show (k + -d : ℤ) = k - d from by ring]
  -- `W·A` is the monomial germ (the inverse cancels off the isolated zeros/poles of `A`)
  have hAne : ∀ᶠ ζ in 𝓝[≠] c, A ζ ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hAm).mp (by rw [hAord]; simp)
  have hgerm : (fun ζ => W ζ * A ζ) =ᶠ[𝓝[≠] c] fun ζ => (ζ - c) ^ k := by
    filter_upwards [hAne] with ζ hζ
    rw [hW]
    show (ζ - c) ^ k * (A ζ)⁻¹ * A ζ = (ζ - c) ^ k
    rw [mul_assoc, inv_mul_cancel₀ hζ, mul_one]
  ext q
  obtain ⟨p', m⟩ := q
  rw [invMonomialTail, mulTail_pointTail_apply, truncTails_apply, ← hc, ← hA, ← hW]
  rcases eq_or_ne p' p with heq | hne
  · subst heq
    by_cases hm : m < -(D p')
    · rw [if_pos ⟨rfl, hm⟩, if_pos hm]
      -- the window sum is the product coefficient `c_m(W·A) = c_m(z^k) = δ_{mk}`
      have hsum : ∑ j ∈ Finset.Ico lo hi,
          planarCoeff j W c * f.coeffAt p' (m - j)
          = planarCoeff m (fun ζ => W ζ * A ζ) c := by
        refine (planarCoeff_mul_window hWm hAm ?_ hlohi ?_).symm
        · rw [hWord]
          exact_mod_cast hlo
        · rw [hAord]
          exact_mod_cast (by omega : m + 1 - hi ≤ d)
      rw [hsum, planarCoeff_congr hgerm, planarCoeff_zpow_self, Finsupp.single_apply]
      by_cases hmk : m = k
      · rw [if_pos hmk, if_pos (by rw [hmk])]
      · rw [if_neg hmk, if_neg (fun h => hmk (congrArg Prod.snd h).symm)]
    · rw [if_neg (by tauto), if_neg hm]
  · rw [if_neg (by tauto)]
    split
    · rw [Finsupp.single_apply, if_neg (fun h => hne (congrArg Prod.fst h).symm)]
    · rfl

/-! ## Part D — the descended multiplication and the `ψ`-action on functionals -/

/-- **The descended multiplication map** `H¹_t(D−E) → H¹_t(D)` along `f ∈ L(E)`
(well-defined by the transport identity and the upper kill). -/
def mulH1 (D E : Divisor X) (f : MeromorphicFunction X)
    (hf : f ∈ linearSystem (X := X) E) :
    H1Tail (X := X) (D - E) →ₗ[ℂ] H1Tail (X := X) D := by
  refine Submodule.mapQ _ _ (mulTail f D) (sup_le ?_ ?_)
  · rintro - ⟨g, rfl⟩
    rw [Submodule.mem_comap, mulTail_tailMap hf D g]
    exact Submodule.mem_sup_left ⟨f * g, rfl⟩
  · intro u hu
    rw [Submodule.mem_comap, mulTail_eq_zero_of_mem_upperSpace hf D hu]
    exact Submodule.zero_mem _

@[simp] theorem mulH1_mk (D E : Divisor X) (f : MeromorphicFunction X)
    (hf : f ∈ linearSystem (X := X) E) (t : GlobalTails X) :
    mulH1 D E f hf (Submodule.Quotient.mk t)
      = Submodule.Quotient.mk (mulTail f D t) := rfl

/-- **Division surjectivity**: for `f` of finite order everywhere, every tail class at level
`D` is a `mulTail f D`-image (each below-cut single is hit exactly, by the local inverse
tails; upper singles die). -/
theorem mkQ_mulTail_surjective (f : MeromorphicFunction X) (D : Divisor X)
    (hf0 : ∀ p : X, f.orderW p ≠ ⊤) (ξ : H1Tail (X := X) D) :
    ∃ t : GlobalTails X,
      (Submodule.Quotient.mk (mulTail f D t) : H1Tail (X := X) D) = ξ := by
  classical
  set L : GlobalTails X →ₗ[ℂ] H1Tail (X := X) D :=
    (tailCoker (X := X) D).mkQ.comp (mulTail f D) with hL
  suffices h : ∀ q : X × ℤ, ∀ a : ℂ,
      (Submodule.Quotient.mk (Finsupp.single q a) : H1Tail (X := X) D)
        ∈ LinearMap.range L by
    obtain ⟨t₀, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hmem : (Submodule.Quotient.mk t₀ : H1Tail (X := X) D) ∈ LinearMap.range L := by
      have ht₀ : t₀ = ∑ q ∈ t₀.support, Finsupp.single q (t₀ q) := by
        conv_lhs => rw [← Finsupp.sum_single t₀]
        rfl
      have hexp : (Submodule.Quotient.mk t₀ : H1Tail (X := X) D)
          = ∑ q ∈ t₀.support,
              (Submodule.Quotient.mk (Finsupp.single q (t₀ q)) : H1Tail (X := X) D) := by
        conv_lhs => rw [ht₀]
        exact map_sum ((tailCoker (X := X) D).mkQ) _ _
      rw [hexp]
      exact Submodule.sum_mem _ fun q _ => h q (t₀ q)
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  intro q a
  obtain ⟨p, k⟩ := q
  by_cases hk : k < -(D p)
  · -- hit by the (scaled) local inverse tail
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (hf0 p)
    refine ⟨a • invMonomialTail f p k (k - d) (max (-(D p) - d) (k - d)), ?_⟩
    rw [hL, LinearMap.comp_apply, map_smul, mulTail_invMonomialTail f D p hd.symm le_rfl
      (le_max_left _ _) (le_max_right _ _),
      truncTails_eq_self_of_mem (single_mem_tailSpace hk 1), map_smul,
      Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  · -- upper singles die in `H¹`
    refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (single_mem_upperSpace (by omega) a)

/-- **The `ψ`-action on tail functionals** (Miranda VI.3.8 analogue, dual form):
`f̄ ↦ φ ∘ (mulH1 f) : L(E)/junk →ₗ Dual(H¹_t(D−E))`. -/
def tailPsiAct (D E : Divisor X) (φ : Module.Dual ℂ (H1Tail (X := X) D)) :
    lSysModule (X := X) E →ₗ[ℂ] Module.Dual ℂ (H1Tail (X := X) (D - E)) := by
  refine Submodule.liftQ _
    { toFun := fun f => φ.comp (mulH1 D E (f : MeromorphicFunction X) f.2)
      map_add' := fun f₁ f₂ => ?_
      map_smul' := fun a f => ?_ } ?_
  · refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show φ (Submodule.Quotient.mk (mulTail ((f₁ : MeromorphicFunction X)
        + (f₂ : MeromorphicFunction X)) D t))
      = φ (Submodule.Quotient.mk (mulTail (f₁ : MeromorphicFunction X) D t))
        + φ (Submodule.Quotient.mk (mulTail (f₂ : MeromorphicFunction X) D t))
    rw [mulTail_add_fun, LinearMap.add_apply, Submodule.Quotient.mk_add, map_add]
  · refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show φ (Submodule.Quotient.mk (mulTail (a • (f : MeromorphicFunction X)) D t))
      = a • φ (Submodule.Quotient.mk (mulTail (f : MeromorphicFunction X) D t))
    rw [mulTail_smul_fun, LinearMap.smul_apply, Submodule.Quotient.mk_smul, map_smul]
  · intro f hf
    have hf' : (f : MeromorphicFunction X) ∈ germZeroSubmodule (X := X) := hf
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show φ (Submodule.Quotient.mk (mulTail (f : MeromorphicFunction X) D t)) = 0
    rw [mulTail_eq_zero_of_germZero hf' D, LinearMap.zero_apply,
      Submodule.Quotient.mk_zero, map_zero]

@[simp] theorem tailPsiAct_mk_mk (D E : Divisor X)
    (φ : Module.Dual ℂ (H1Tail (X := X) D)) (f : ↥(linearSystem (X := X) E))
    (t : GlobalTails X) :
    tailPsiAct (X := X) D E φ (Submodule.Quotient.mk f) (Submodule.Quotient.mk t)
      = φ (Submodule.Quotient.mk (mulTail (f : MeromorphicFunction X) D t)) := rfl

/-- A nonzero junk-free class has finite order EVERYWHERE (identity theorem). -/
theorem orderW_ne_top_of_lSys_ne_zero {E : Divisor X} {f : ↥(linearSystem (X := X) E)}
    (hf : (Submodule.Quotient.mk f : lSysModule (X := X) E) ≠ 0) (p : X) :
    (f : MeromorphicFunction X).orderW p ≠ ⊤ := by
  refine MeromorphicFunction.orderW_ne_top_of_exists _ ?_ p
  by_contra hall
  push Not at hall
  refine hf ?_
  rw [Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  intro x
  exact hall x

/-- **Injectivity of the `ψ`-action** for `φ ≠ 0` (Miranda VI.3.8 analogue): the division
surjectivity makes `f·φ = 0` with `f ≠ 0` force `φ = 0`. -/
theorem tailPsiAct_injective (D E : Divisor X) (φ : Module.Dual ℂ (H1Tail (X := X) D))
    (hφ : φ ≠ 0) : Function.Injective (tailPsiAct (X := X) D E φ) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [LinearMap.mem_ker] at hu
  by_contra hne
  have hf0 : ∀ p : X, (f : MeromorphicFunction X).orderW p ≠ ⊤ :=
    orderW_ne_top_of_lSys_ne_zero hne
  refine hφ (LinearMap.ext fun ξ => ?_)
  obtain ⟨t, ht⟩ := mkQ_mulTail_surjective (f : MeromorphicFunction X) D hf0 ξ
  have happ := congrArg (fun χ : Module.Dual ℂ (H1Tail (X := X) (D - E)) =>
    χ (Submodule.Quotient.mk t)) hu
  simp only [LinearMap.zero_apply] at happ
  rw [tailPsiAct_mk_mk, ht] at happ
  rw [happ]
  rfl

/-! ## Part E — the unwind (Miranda VI.3.7/VI.3.9 analogue) -/

namespace TailPairFrame

variable (P : TailPairFrame X)

/-- **The key evaluation** (the heart of the unwind): under the pigeonhole witness identity
`φ ∘ (mulTail ψ D) = ⟨w, ·⟩`, the value of `φ` on any truncated monomial single at `p` is
the slot pairing of the quotient `g = w·ψ⁻¹` — evaluating the identity on the local inverse
tail `z^k/ψ` and running the window product law on both sides. -/
theorem unwind_eval {D E : Divisor X} {ψ w : MeromorphicFunction X}
    (hw : w ∈ linearSystem (X := X) (P.data.K - (D - E)))
    {φ : Module.Dual ℂ (H1Tail (X := X) D)}
    (hkey : ∀ t : GlobalTails X,
      φ (Submodule.Quotient.mk (mulTail ψ D t)) = P.pairFun w t)
    {p : X} {d : ℤ} (hd : ψ.orderW p = (d : WithTop ℤ)) (k : ℤ) :
    φ (Submodule.Quotient.mk (truncTails D (Finsupp.single (p, k) (1 : ℂ))))
      = P.pairSlot (w * ψ⁻¹) p k := by
  classical
  set c : ℂ := (chartAt (H := ℂ) p) p with hc
  set A : ℂ → ℂ := ψ.toFun ∘ (chartAt (H := ℂ) p).symm with hA
  set W : ℂ → ℂ := fun ζ => (ζ - c) ^ k * (A ζ)⁻¹ with hW
  set Bw : ℂ → ℂ := fun ζ => w.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ with hBw
  set Bg : ℂ → ℂ :=
    fun ζ => (w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ with hBg
  set lo : ℤ := k - d with hlodef
  set hi : ℤ := max (max (-(D p) - d) (k - d)) (-((D - E : Divisor X) p)) with hhidef
  have hlo : lo ≤ k - d := le_rfl
  have hhi : -(D p) - d ≤ hi := le_trans (le_max_left _ _) (le_max_left _ _)
  have hlohi : lo ≤ hi := le_trans (le_max_right _ _) (le_max_left _ _)
  -- meromorphy and orders
  have hAm : MeromorphicAt A c := ψ.meromorphic p
  have hAord : meromorphicOrderAt A c = (d : WithTop ℤ) := hd
  have hWm : MeromorphicAt W c := (meromorphicAt_zpow_self c k).mul hAm.inv
  have hWord : meromorphicOrderAt W c = ((k - d : ℤ) : WithTop ℤ) := by
    rw [hW, show (fun ζ => (ζ - c) ^ k * (A ζ)⁻¹)
        = (fun ζ => (ζ - c) ^ k) * (A⁻¹) from rfl,
      meromorphicOrderAt_mul (meromorphicAt_zpow_self c k) hAm.inv,
      meromorphicOrderAt_zpow_self, meromorphicOrderAt_inv, hAord]
    rw [show -((d : ℤ) : WithTop ℤ) = ((-d : ℤ) : WithTop ℤ) from by simp,
      ← WithTop.coe_add, show (k + -d : ℤ) = k - d from by ring]
  have hBwm : MeromorphicAt Bw c := P.prodRead_mero p w
  have hBword : ((-hi : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Bw c := by
    refine le_trans ?_ (P.prodRead_order_ge hw p)
    exact_mod_cast (by
      have := le_max_right (max (-(D p) - d) (k - d)) (-((D - E : Divisor X) p))
      omega : -hi ≤ ((D - E : Divisor X) p))
  have hBgm : MeromorphicAt Bg c := P.prodRead_mero p (w * ψ⁻¹)
  -- step 1: the division identity + the witness identity
  have hstep1 : φ (Submodule.Quotient.mk (truncTails D (Finsupp.single (p, k) (1 : ℂ))))
      = P.pairFun w (invMonomialTail ψ p k lo hi) := by
    rw [← mulTail_invMonomialTail ψ D p hd hlo hhi hlohi]
    exact hkey _
  -- step 2: expand the pairing on the inverse tail
  have hstep2 : P.pairFun w (invMonomialTail ψ p k lo hi)
      = ∑ j ∈ Finset.Ico lo hi, planarCoeff j W c * P.pairSlot w p j := by
    rw [invMonomialTail, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [P.pairFun_single w (p, j)]
  -- step 3: the window product law reassembles the residue of `W·(w·ω₀)`
  have hstep3 : ∑ j ∈ Finset.Ico lo hi, planarCoeff j W c * P.pairSlot w p j
      = planarCoeff (-1) (fun ζ => W ζ * Bw ζ) c := by
    have hlaw := resCoeff_mul_window hWm hBwm (lo := lo) (hi := hi)
      (le_of_le_of_eq
        (by exact_mod_cast hlo : ((lo : ℤ) : WithTop ℤ) ≤ ((k - d : ℤ) : WithTop ℤ))
        hWord.symm) hlohi hBword
    have hpair : ∑ j ∈ Finset.Ico lo hi, planarCoeff j W c * P.pairSlot w p j
        = ∑ j ∈ Finset.Ico lo hi, planarCoeff j W c * planarCoeff (-1 - j) Bw c := rfl
    rw [hpair]
    exact hlaw.symm
  -- step 4: `W·(w·ω₀) = z^k·(g·ω₀)` pointwise (`g = w·ψ⁻¹` is the pointwise quotient)
  have hstep4 : (fun ζ => W ζ * Bw ζ) = fun ζ => (ζ - c) ^ k * Bg ζ := by
    funext ζ
    rw [hW, hBw, hBg]
    show ((ζ - c) ^ k * (A ζ)⁻¹) * (w.toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
        = (ζ - c) ^ k * ((w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
    rw [show (w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ)
        = w.toFun ((chartAt (H := ℂ) p).symm ζ)
          * (ψ.toFun ((chartAt (H := ℂ) p).symm ζ))⁻¹ from rfl,
      show A ζ = ψ.toFun ((chartAt (H := ℂ) p).symm ζ) from by rw [hA]; rfl]
    ring
  -- step 5: the monomial shift lands on the slot pairing of `g`
  have hstep5 : planarCoeff (-1) (fun ζ => (ζ - c) ^ k * Bg ζ) c
      = planarCoeff (-1 - k) Bg c := planarCoeff_monomial_mul k (-1) hBgm
  have hfinal : P.pairSlot (w * ψ⁻¹) p k = planarCoeff (-1 - k) Bg c := rfl
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hfinal]

/-- **Miranda VI.3.9 analogue — the pole-bound regularity of the quotient**: the witness
identity forces `g = w·ψ⁻¹ ∈ L(K−D)` (each below-`D` gap coefficient of `g·ω₀` is a
`φ`-value on an upper single, which dies in `H¹_t(D)`). -/
theorem unwind_mem {D E : Divisor X} {ψ w : MeromorphicFunction X}
    (hψ0 : ∀ q : X, ψ.orderW q ≠ ⊤)
    (hw : w ∈ linearSystem (X := X) (P.data.K - (D - E)))
    {φ : Module.Dual ℂ (H1Tail (X := X) D)}
    (hkey : ∀ t : GlobalTails X,
      φ (Submodule.Quotient.mk (mulTail ψ D t)) = P.pairFun w t) :
    w * ψ⁻¹ ∈ linearSystem (X := X) (P.data.K - D) := by
  intro p
  obtain ⟨d, hd'⟩ := WithTop.ne_top_iff_exists.mp (hψ0 p)
  have hd : ψ.orderW p = (d : WithTop ℤ) := hd'.symm
  -- gap vanishing for the slot product of `g`
  have hvan : ∀ j : ℤ, j < D p → planarCoeff j
      (fun ζ => (w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ((chartAt (H := ℂ) p) p) = 0 := by
    intro j hj
    have h1 := P.unwind_eval hw hkey hd (-1 - j)
    have h2 : truncTails D (Finsupp.single (p, -1 - j) (1 : ℂ)) = 0 :=
      truncTails_eq_zero_of_mem_upperSpace (single_mem_upperSpace (by omega) 1)
    rw [h2, Submodule.Quotient.mk_zero, map_zero] at h1
    have h3 : P.pairSlot (w * ψ⁻¹) p (-1 - j)
        = planarCoeff j
            (fun ζ => (w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
            ((chartAt (H := ℂ) p) p) := by
      rw [pairSlot, show (-1 - (-1 - j) : ℤ) = j from by ring]
    rw [h3] at h1
    exact h1.symm
  -- upgrade to the order bound on the slot product, then peel off the exact slot order
  have hord : ((D p : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => (w * ψ⁻¹).toFun ((chartAt (H := ℂ) p).symm ζ) * P.slot p ζ)
      ((chartAt (H := ℂ) p) p) :=
    (order_ge_iff_planarCoeff_vanish (P.prodRead_mero p (w * ψ⁻¹)) (D p)).mpr
      fun j hjlt => hvan j (by exact_mod_cast hjlt)
  rw [P.prodRead_order p (w * ψ⁻¹)] at hord
  have e1 : (-((P.data.K - D : Divisor X) p) : WithTop ℤ)
      = ((-((P.data.K - D : Divisor X) p) : ℤ) : WithTop ℤ) := rfl
  rw [e1, show (-((P.data.K - D : Divisor X) p) : ℤ) = D p - P.data.K p from by
    rw [Finsupp.sub_apply]; ring]
  cases hg : (w * ψ⁻¹).orderW p with
  | top => exact le_top
  | coe n =>
    rw [hg] at hord
    have hn : D p ≤ n + P.data.K p := by
      have hcoe : ((n : ℤ) : WithTop ℤ) + ((P.data.K p : ℤ) : WithTop ℤ)
          = ((n + P.data.K p : ℤ) : WithTop ℤ) := (WithTop.coe_add n (P.data.K p)).symm
      rw [hcoe] at hord
      exact_mod_cast hord
    exact_mod_cast (by omega : D p - P.data.K p ≤ n)

/-- **The functional identity of the unwind**: `φ` lifted to ambient tails IS the raw
pairing functional of `g = w·ψ⁻¹` (they agree on every single: below the cut by
`unwind_eval`, at/above it both vanish — `φ` through the upper kill, the pairing by the
same evaluation). -/
theorem unwind_pairing_eq {D E : Divisor X} {ψ w : MeromorphicFunction X}
    (hψ0 : ∀ q : X, ψ.orderW q ≠ ⊤)
    (hw : w ∈ linearSystem (X := X) (P.data.K - (D - E)))
    {φ : Module.Dual ℂ (H1Tail (X := X) D)}
    (hkey : ∀ t : GlobalTails X,
      φ (Submodule.Quotient.mk (mulTail ψ D t)) = P.pairFun w t) :
    φ.comp (tailCoker (X := X) D).mkQ = P.pairFun (w * ψ⁻¹) := by
  refine Finsupp.lhom_ext fun q a => ?_
  obtain ⟨p, k⟩ := q
  obtain ⟨d, hd'⟩ := WithTop.ne_top_iff_exists.mp (hψ0 p)
  have h1 := P.unwind_eval hw hkey hd'.symm k
  have hsm : Finsupp.single ((p, k) : X × ℤ) a = a • Finsupp.single (p, k) (1 : ℂ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have hmk : (Submodule.Quotient.mk (Finsupp.single ((p, k) : X × ℤ) a)
        : H1Tail (X := X) D)
      = Submodule.Quotient.mk (truncTails D (Finsupp.single (p, k) a)) := by
    rw [Submodule.Quotient.eq]
    exact Submodule.mem_sup_right (sub_truncTails_mem_upperSpace D _)
  calc (φ.comp (tailCoker (X := X) D).mkQ) (Finsupp.single (p, k) a)
      = φ (Submodule.Quotient.mk (truncTails D (Finsupp.single (p, k) a))) := by
        rw [LinearMap.comp_apply, Submodule.mkQ_apply, hmk]
    _ = a • φ (Submodule.Quotient.mk (truncTails D (Finsupp.single (p, k) (1 : ℂ)))) := by
        rw [hsm, map_smul, Submodule.Quotient.mk_smul, map_smul]
    _ = a • P.pairSlot (w * ψ⁻¹) p k := by rw [h1]
    _ = P.pairFun (w * ψ⁻¹) (Finsupp.single (p, k) a) := by
        rw [P.pairFun_single, smul_eq_mul]

/-- **The unwind, packaged** (Miranda VI.3.7 analogue): a nonzero pigeonhole witness
`ψ·φ = ι_{D−E}(w)` puts `φ` in the range of the level-`D` pairing — via `g = w·ψ⁻¹`. -/
theorem unwind {D E : Divisor X} {φ : Module.Dual ℂ (H1Tail (X := X) D)}
    (ψq : lSysModule (X := X) E)
    (wq : lSysModule (X := X) (P.data.K - (D - E)))
    (hψq : ψq ≠ 0)
    (heq : tailPsiAct (X := X) D E φ ψq = P.pairingL (D - E) wq) :
    ∃ u : lSysModule (X := X) (P.data.K - D), P.pairingL D u = φ := by
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ ψq
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wq
  have hψ0 : ∀ q : X, (ψ : MeromorphicFunction X).orderW q ≠ ⊤ :=
    orderW_ne_top_of_lSys_ne_zero hψq
  have hkey : ∀ t : GlobalTails X,
      φ (Submodule.Quotient.mk (mulTail (ψ : MeromorphicFunction X) D t))
        = P.pairFun (w : MeromorphicFunction X) t := by
    intro t
    have happ := congrArg (fun χ : Module.Dual ℂ (H1Tail (X := X) (D - E)) =>
      χ (Submodule.Quotient.mk t)) heq
    simpa only [tailPsiAct_mk_mk, pairingL_mk, pairingFunctional_mk] using happ
  have hg : (w : MeromorphicFunction X) * (ψ : MeromorphicFunction X)⁻¹
      ∈ linearSystem (X := X) (P.data.K - D) := P.unwind_mem hψ0 w.2 hkey
  refine ⟨Submodule.Quotient.mk ⟨_, hg⟩, ?_⟩
  have hfn := P.unwind_pairing_eq hψ0 w.2 hkey
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [pairingL_mk, pairingFunctional_mk]
  have happ := congrArg (fun L : GlobalTails X →ₗ[ℂ] ℂ => L t) hfn
  exact happ.symm

/-! ## Part F — the headline: `PairingSurjective` is a theorem -/

/-- **Miranda VI.3.10 — the surjectivity half of tail Serre duality.**  For EVERY tail pair
frame `P` and every divisor `D`, the residue pairing
`pairingL D : L(K−D)/junk →ₗ Dual(H¹_t(D))` is surjective: the named residual input
`PairingSurjective` of the tail tower (`docs/planning/TAILRR_BLOCKER.md`, input 2) is
DISCHARGED.  Proof: the recovery + growth pigeonhole — `serre_surjectivity_dim_core` over
the proven tail Riemann–Roch I arithmetic, with the `ψ`-action injectivity
(`tailPsiAct_injective`, via division surjectivity by local inverse tails) and the
pairing injectivity (`pairingL_injective`) feeding the two dimension lower bounds, and
the unwind (`unwind`) converting the intersection witness into a preimage. -/
theorem pairingSurjective (P : TailPairFrame X) : P.PairingSurjective := by
  intro D φ
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, map_zero _⟩
  obtain ⟨P₀⟩ : Nonempty X := inferInstance
  haveI hfinH : ∀ n : ℕ, FiniteDimensional ℂ
      (H1Tail (X := X) (D - Finsupp.single P₀ (n : ℤ))) :=
    fun _ => finiteDimensional_H1Tail _
  haveI : ∀ n : ℕ, FiniteDimensional ℂ
      (Module.Dual ℂ (H1Tail (X := X) (D - Finsupp.single P₀ (n : ℤ)))) :=
    fun _ => inferInstance
  -- `dim Λ n = l(nP₀) ≥ n + 1 − g_t` (action injectivity + tail RR-I)
  have hΛ : ∀ n : ℕ, (1 : ℤ) - (tailGenus X : ℤ) + (n : ℤ) ≤
      (finrank ℂ
        ↥(LinearMap.range (tailPsiAct (X := X) D (Finsupp.single P₀ (n : ℤ)) φ)) : ℤ) := by
    intro n
    have hrk : finrank ℂ
        ↥(LinearMap.range (tailPsiAct (X := X) D (Finsupp.single P₀ (n : ℤ)) φ))
        = lDim (X := X) (Finsupp.single P₀ (n : ℤ)) :=
      ((LinearEquiv.ofInjective _
        (tailPsiAct_injective D (Finsupp.single P₀ (n : ℤ)) φ hφ)).finrank_eq).symm
    have hRR := tail_riemannRoch_I (X := X) (Finsupp.single P₀ (n : ℤ))
    rw [Divisor.deg_single] at hRR
    rw [hrk]
    omega
  -- `dim I n = l(K − (D − nP₀)) ≥ n + (deg K + 1 − g_t) − deg D` (pairing injectivity + RR-I)
  have hI : ∀ n : ℕ, (n : ℤ) + (Divisor.deg X P.data.K + 1 - (tailGenus X : ℤ))
      - Divisor.deg X D ≤
      (finrank ℂ
        ↥(LinearMap.range (P.pairingL (D - Finsupp.single P₀ (n : ℤ)))) : ℤ) := by
    intro n
    have hrk : finrank ℂ
        ↥(LinearMap.range (P.pairingL (D - Finsupp.single P₀ (n : ℤ))))
        = lDim (X := X) (P.data.K - (D - Finsupp.single P₀ (n : ℤ))) :=
      ((LinearEquiv.ofInjective _
        (P.pairingL_injective (D - Finsupp.single P₀ (n : ℤ)))).finrank_eq).symm
    have hRR := tail_riemannRoch_I (X := X)
      (P.data.K - (D - Finsupp.single P₀ (n : ℤ)))
    rw [Divisor.deg_sub, Divisor.deg_sub, Divisor.deg_single] at hRR
    rw [hrk]
    omega
  -- `dim V n = h¹_t(D − nP₀) = n + g_t − 1 − deg D` for `n > deg D` (RR-I, negative degree)
  have hV : ∀ n : ℕ, Divisor.deg X D < (n : ℤ) →
      ((finrank ℂ
        (Module.Dual ℂ (H1Tail (X := X) (D - Finsupp.single P₀ (n : ℤ))))) : ℤ)
        = (n : ℤ) + (tailGenus X : ℤ) - 1 - Divisor.deg X D := by
    intro n hdn
    have hdual : finrank ℂ
        (Module.Dual ℂ (H1Tail (X := X) (D - Finsupp.single P₀ (n : ℤ))))
        = h1TailDim (X := X) (D - Finsupp.single P₀ (n : ℤ)) :=
      Subspace.dual_finrank_eq
    have hRR := tail_riemannRoch_I (X := X) (D - Finsupp.single P₀ (n : ℤ))
    have h0 : lDim (X := X) (D - Finsupp.single P₀ (n : ℤ)) = 0 := by
      refine lDim_eq_zero_of_deg_neg _ ?_
      rw [Divisor.deg_sub, Divisor.deg_single]
      omega
    rw [h0, Divisor.deg_sub, Divisor.deg_single] at hRR
    rw [hdual]
    omega
  -- the pigeonhole: the two subspaces of `Dual(H¹_t(D − NP₀))` meet for large `N`
  obtain ⟨N, hN⟩ := SerreDuality.serre_surjectivity_dim_core
    (V := fun n => Module.Dual ℂ (H1Tail (X := X) (D - Finsupp.single P₀ (n : ℤ))))
    (fun n => LinearMap.range (tailPsiAct (X := X) D (Finsupp.single P₀ (n : ℤ)) φ))
    (fun n => LinearMap.range (P.pairingL (D - Finsupp.single P₀ (n : ℤ))))
    (tailGenus X : ℤ) (Divisor.deg X D)
    (Divisor.deg X P.data.K + 1 - (tailGenus X : ℤ)) hΛ hI hV
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (hN N le_rfl)
  rw [Submodule.mem_inf] at hv
  obtain ⟨ψq, hψ⟩ := LinearMap.mem_range.mp hv.1
  obtain ⟨wq, hwq⟩ := LinearMap.mem_range.mp hv.2
  have hψ0 : ψq ≠ 0 := by
    rintro rfl
    rw [map_zero] at hψ
    exact hv0 hψ.symm
  exact P.unwind ψq wq hψ0 (hψ.trans hwq.symm)

/-- **Tail Riemann–Roch from a frame alone**: with `PairingSurjective` a theorem, the tail
tower's headline conditional collapses to frame existence. -/
theorem tailRiemannRoch (P : TailPairFrame X) : TailRiemannRoch X :=
  P.tailRiemannRoch_of_pairingSurjective P.pairingSurjective

end TailPairFrame

/-- **The keystone-facing corollary, frame-only form**: a tail pair frame alone yields the
canonical-cover arithmetic genus identity `h¹(𝒪) = kirovGenus` — the surjectivity input of
`h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame` is discharged. -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame' (P : TailPairFrame X) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame P P.pairingSurjective

end Dolbeault

end Jacobians

end
