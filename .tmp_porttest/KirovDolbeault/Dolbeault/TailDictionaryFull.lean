/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailDictionary
import KirovDolbeault.Dolbeault.FineResidue.GlobalCorrection

/-!
# The Čech↔tail dictionary, UNCONDITIONAL: `UnwindRegularity` for the concrete fine sheaf

The W2–W5 cocycle-side bookkeeping of `docs/planning/DICT_ROUTE.md`, on top of the W1
analytic engine (`FineResidue/GlobalCorrection.lean`).  At a forced bad point `b` that is
NOT cover-isolated (`K b = 0`, discovery D2), the single-chart skyscraper test cochain of
`SerreUnwindDetect.lean` fails level-`E` membership on star overlaps; this file builds the
**deep-matching star cochain** instead, presents the cup coboundary in the
global-cutoff-subtracted form, and runs the W1 engine to evaluate the residue functional —
removing the `BadPointsIsolated` discipline from the §17.7 chain.

* **W2 — the triangular window realization** (`exists_window_matching_section`): per star
  chart `U i ∋ b`, a section `c_i ∈ 𝒪_{Ě+b}(U i)` whose FULL ambient-chart Laurent window at
  `b` (orders `−(m+1) … −(E b+1)`) matches a prescribed meromorphic target — downward
  triangular induction on the window over `ExactOrderWitness` sections, reading invariantly
  at `b` through `Gext` and the ambient chart (`ordU_eq_orderAt_Gext`).  Packaged as
  `DeepTestData`; the deep cochain `i ↦ [c_i]` has `δ⁰c ∈ Z¹(𝒪_E)` (matching windows cancel
  on star overlaps; `b` is absent from mixed overlaps) and dies in `H¹(𝒪_D)`.
* **W3 — the X-side cutoff** `θ` (a `SmoothBumpFunction` at `b` with support inside
  `U j₀ ∖ posSupp K`), the global correction scalar `H := θ·h⁰_{j₀}`, and the repaired
  presentation `h̃_i := repairAtX b (h⁰_i − H)`.
* **W4 — the presentation bookkeeping**: `h̃` is smooth at `b` (the matching principal parts
  cancel: `ord ≥ n − E b ≥ 0`), `IsCoboundaryOn` survives the repair by continuity (the
  level-`K` cocycle is honest at `b` since `K b = 0`), `SlotProductExtendsAt` at the
  unmarked K-points is inherited from the vanish engine (`supp θ` avoids them), and the
  marked simple-pole shape comes from the (component-generalized)
  `exists_slotProductSimplePoleAt`.
* **W5 — assembly**: `unwindRegularity_concrete` (case split: cover-isolated bad point →
  the proven `SerreUnwindDetect` engine; otherwise → the W2–W4 construction into the W1
  engine), then `cechTailComparison_concrete` and `pairing_surjective_concrete`.

References: Forster (GTM 81) Lemma 17.7; Miranda (GSM 5) VI.3.6;
`docs/planning/DICT_ROUTE.md` (D1–D3, W-table), `docs/planning/DICT_BLOCKER.md`.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module Complex
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

open FineResidue

variable {𝔇 : ChartDiskCover X}

/-! ## Part 0 — planar and `Gext` helpers -/

/-- A meromorphic function of nonnegative order agrees, on a punctured neighbourhood, with an
analytic function (the normal form; `q := 0` at order `⊤`). -/
theorem exists_analyticAt_extension {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q c ∧ F =ᶠ[𝓝[≠] c] q := by
  rcases eq_or_ne (meromorphicOrderAt F c) ⊤ with htop | hne
  · refine ⟨0, analyticAt_const, ?_⟩
    have h := meromorphicOrderAt_eq_top_iff.mp htop
    filter_upwards [h] with z hz
    exact hz
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    have hn0 : 0 ≤ n := by
      rw [← hn] at h0
      exact_mod_cast h0
    obtain ⟨w, hwan, _, hwe⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hn.symm
    refine ⟨fun z => (z - c) ^ n.toNat * w z, ?_, ?_⟩
    · exact (((analyticAt_id.sub analyticAt_const).pow _).mul hwan)
    · filter_upwards [hwe] with z hz
      rw [hz, smul_eq_mul]
      congr 1
      rw [show (z - c) ^ n = (z - c) ^ ((n.toNat : ℤ)) from by rw [Int.toNat_of_nonneg hn0],
        zpow_natCast]

/-- One `WithTop ℤ` upgrade step: strict `l < ord` gives `l + 1 ≤ ord`. -/
private theorem add_one_le_of_lt' {l : ℤ} {o : WithTop ℤ} (hl : (l : WithTop ℤ) < o) :
    ((l + 1 : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe v =>
    have hv : l < v := by exact_mod_cast hl
    exact_mod_cast hv

/-- Constant rescales preserve planar meromorphy. -/
private theorem meromorphicAt_const_smul {F : ℂ → ℂ} {c : ℂ} (s : ℂ)
    (hF : MeromorphicAt F c) : MeromorphicAt (s • F) c := by
  have h := ((analyticAt_const (v := s) (x := c)).meromorphicAt).smul hF
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp

/-- Constant nonzero rescales preserve the planar meromorphic order. -/
private theorem meromorphicOrderAt_const_smul {F : ℂ → ℂ} {c : ℂ} {s : ℂ} (hs : s ≠ 0) :
    meromorphicOrderAt (s • F) c = meromorphicOrderAt F c := by
  have h : (s • F) = (fun _ : ℂ => s) • F := by
    funext z
    simp
  rw [h]
  exact meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hs)

/-- `laurentCoeff` is subtractive on functions of order `≥ k`. -/
theorem laurentCoeff_sub {k : ℤ} {F G : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hordF : (k : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hordG : (k : WithTop ℤ) ≤ meromorphicOrderAt G c) :
    laurentCoeff k (F - G) c = laurentCoeff k F c - laurentCoeff k G c := by
  have hneg : F - G = F + (-1 : ℂ) • G := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hordG' : (k : WithTop ℤ) ≤ meromorphicOrderAt ((-1 : ℂ) • G) c := by
    rwa [meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [hneg, laurentCoeff_add hF (meromorphicAt_const_smul _ hG) hordF hordG',
    laurentCoeff_smul (-1 : ℂ) hG hordG]
  simp only [smul_eq_mul]
  ring

/-- The order of a difference is at least the minimum of the orders. -/
theorem min_le_meromorphicOrderAt_sub {F G : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c) :
    min (meromorphicOrderAt F c) (meromorphicOrderAt G c)
      ≤ meromorphicOrderAt (F - G) c := by
  have hneg : F - G = F + (-1 : ℂ) • G := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hGord : meromorphicOrderAt ((-1 : ℂ) • G) c = meromorphicOrderAt G c :=
    meromorphicOrderAt_const_smul (by norm_num)
  rw [hneg]
  refine le_trans (le_of_eq ?_) (meromorphicOrderAt_add hF (meromorphicAt_const_smul _ hG))
  rw [hGord]

/-- **Strictly dominated sums keep the smaller order**: `ord F = n < ord G ⟹ ord (F+G) = n`. -/
theorem meromorphicOrderAt_add_of_lt {F G : ℂ → ℂ} {c : ℂ} {n : ℤ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hFn : meromorphicOrderAt F c = (n : WithTop ℤ))
    (hlt : (n : WithTop ℤ) < meromorphicOrderAt G c) :
    meromorphicOrderAt (F + G) c = (n : WithTop ℤ) := by
  have hsum : MeromorphicAt (F + G) c := hF.add hG
  have hge : (n : WithTop ℤ) ≤ meromorphicOrderAt (F + G) c := by
    refine le_trans ?_ (meromorphicOrderAt_add hF hG)
    rw [hFn]
    exact le_min le_rfl (le_of_lt hlt)
  -- the order-`n` coefficient of the sum is the (nonzero) coefficient of `F`
  have hcF : laurentCoeff n F c ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff hF (le_of_eq hFn.symm)).mp h0
    rw [hFn] at this
    exact lt_irrefl _ this
  have hcG : laurentCoeff n G c = 0 :=
    (laurentCoeff_eq_zero_iff hG (le_of_lt hlt)).mpr hlt
  have hcsum : laurentCoeff n (F + G) c ≠ 0 := by
    rw [laurentCoeff_add hF hG (le_of_eq hFn.symm) (le_of_lt hlt), hcG, add_zero]
    exact hcF
  -- nonzero coefficient pins the order to `≤ n`
  have hle : meromorphicOrderAt (F + G) c ≤ (n : WithTop ℤ) := by
    by_contra hgt
    push Not at hgt
    exact hcsum ((laurentCoeff_eq_zero_iff hsum hge).mpr hgt)
  exact le_antisymm hle hge

variable {b : X}

/-- The ambient chart point at `b` (the common read point of all window matches). -/
private abbrev βpt (b : X) : ℂ := (chartAt (H := ℂ) b) b

/-- The ambient read of a section through `Gext` and the chart at `b`. -/
private abbrev ambRead {U : Opens X} (c : ↥U → ℂ) (b : X) : ℂ → ℂ :=
  Gext c ∘ (chartAt (H := ℂ) b).symm

/-- The ambient read of a member of `OmegaD` is meromorphic at `βpt b` with order `ordU`. -/
theorem ambRead_meromorphicAt {U : Opens X} {c : ↥U → ℂ} {D' : Divisor X}
    (hc : c ∈ OmegaD D' U) (hb : b ∈ U) :
    MeromorphicAt (ambRead c b) (βpt b) :=
  Gext_meromorphicAt hc.1 hb

/-- Divisor bookkeeping: the window package at `b`, away from `b`. -/
private theorem window_divisor_apply_ne {E : Divisor X} {m : ℤ} {x : X} (hx : x ≠ b) :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x = E x := by
  rw [Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx]
  ring

/-- Divisor bookkeeping: the window package at `b`, at `b`. -/
private theorem window_divisor_apply_self {E : Divisor X} {m : ℤ} :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) b = m + 1 := by
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  ring

/-- Window packages are monotone in the window length. -/
theorem OmegaD_window_mono {E : Divisor X} {U : Opens X} {m m' : ℤ} (hm : m ≤ m')
    (hEm : E b ≤ m) :
    OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) U
      ≤ OmegaD (E + Finsupp.single b (m' - E b) + Finsupp.single b 1) U := by
  refine OmegaD_mono fun x _ => ?_
  by_cases hx : x = b
  · subst hx
    rw [window_divisor_apply_self, window_divisor_apply_self]
    omega
  · rw [window_divisor_apply_ne hx, window_divisor_apply_ne hx]

/-- **Pole-bound transfer off a marked point**: a section satisfying the window package whose
order at `b` meets the `𝒪_E` bound lies in `𝒪_E`. -/
theorem mem_OmegaD_of_window_of_ordU {E : Divisor X} {m : ℤ} {U : Opens X} {f : ↥U → ℂ}
    (hf : f ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) U)
    (hb : b ∈ U) (hord : ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU f ⟨b, hb⟩) :
    f ∈ OmegaD E U := by
  refine ⟨hf.1, fun x => ?_⟩
  by_cases hx : x.1 = b
  · have hxb : x = ⟨b, hb⟩ := Subtype.ext hx
    rw [hxb]
    exact_mod_cast hord
  · have h := hf.2 x
    rwa [show (-((E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x.1)
        : WithTop ℤ) = (-(E x.1) : WithTop ℤ) from by
      rw [window_divisor_apply_ne hx]] at h

/-! ## Part 1 — W2: the triangular window realization

At a marked point `b ∈ U j`, build a section of the window package
`𝒪_{E + (m−E b)·b + b}(U j)` whose ambient-chart Laurent window at `b` (orders
`−(m+1) … −(E b+1)`) matches a prescribed meromorphic target `t`: realize the lowest-order
coefficient by a scaled `ExactOrderWitness` section, subtract, recurse upward. -/

/-- The "target already regular" case: the zero section matches. -/
private theorem window_zero_case {j : 𝔇.toFiniteCover.ι} {E : Divisor X} {m : ℤ}
    {t : ℂ → ℂ} (hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)) :
    (0 : ↥(𝔇.U j) → ℂ)
        ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      ((-(E b) : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (ambRead (0 : ↥(𝔇.U j) → ℂ) b - t) (βpt b) := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  have hread : ambRead (0 : ↥(𝔇.U j) → ℂ) b - t = (-1 : ℂ) • t := by
    funext z
    simp only [Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [show Gext (0 : ↥(𝔇.U j) → ℂ) ((chartAt (H := ℂ) b).symm z) = 0 from by
      unfold Gext
      split <;> rfl]
    ring
  rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
  exact hcase

/-- **The cancellation step**: a target of exact finite window order `n` is matched at its
lowest-order coefficient by a scaled `ExactOrderWitness` section, strictly raising the order
of the residual. -/
private theorem window_cancel_step (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) {m n : ℤ}
    (_hEm : E b ≤ m) {t : ℂ → ℂ} (ht : MeromorphicAt t (βpt b))
    (hn : meromorphicOrderAt t (βpt b) = (n : WithTop ℤ))
    (hge : -m - 1 ≤ n) (hlt : n < -E b) :
    ∃ c₀ : ↥(𝔇.U j) → ℂ,
      c₀ ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      MeromorphicAt (ambRead c₀ b) (βpt b) ∧
      ((n + 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (t - ambRead c₀ b) (βpt b) := by
  classical
  set d' : ℤ := -n - 1 - E b with hd'def
  have hd'0 : 0 ≤ d' := by omega
  have hd'm : d' ≤ m - E b := by omega
  -- the witness section of exact order `n` at `b`
  obtain ⟨γ', hγmem, hγord⟩ := hwit (E + Finsupp.single b d') j b hb
  have hDb : (E + Finsupp.single b d' : Divisor X) b = E b + d' := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  have hγordn : ordU γ' ⟨b, hb⟩ = (n : WithTop ℤ) := by
    rw [hγord, hDb]
    congr 1
    omega
  -- repackage the membership into the window package
  have harg : (E b + d') - E b = d' := by ring
  have hγmem' : γ' ∈ OmegaD
      (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) := by
    refine OmegaD_window_mono (by omega : E b + d' ≤ m) (by omega) ?_
    rw [harg]
    exact hγmem
  -- the ambient read of the witness has exact order `n`
  have hγmer : MeromorphicAt (ambRead γ' b) (βpt b) := ambRead_meromorphicAt hγmem' hb
  have hreadord : meromorphicOrderAt (ambRead γ' b) (βpt b) = (n : WithTop ℤ) := by
    rw [show meromorphicOrderAt (ambRead γ' b) (βpt b)
        = ordU γ' ⟨b, hb⟩ from (ordU_eq_orderAt_Gext γ' hb).symm]
    exact hγordn
  -- the leading coefficients
  set lt : ℂ := laurentCoeff n t (βpt b) with hltdef
  set lγ : ℂ := laurentCoeff n (ambRead γ' b) (βpt b) with hlγdef
  have hlt0 : lt ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff ht (le_of_eq hn.symm)).mp h0
    rw [hn] at this
    exact lt_irrefl _ this
  have hlγ0 : lγ ≠ 0 := by
    intro h0
    have := (laurentCoeff_eq_zero_iff hγmer (le_of_eq hreadord.symm)).mp h0
    rw [hreadord] at this
    exact lt_irrefl _ this
  set s : ℂ := lt / lγ with hsdef
  have hs0 : s ≠ 0 := div_ne_zero hlt0 hlγ0
  refine ⟨s • γ', Submodule.smul_mem _ s hγmem', ?_, ?_⟩
  all_goals
    have hreadsmul : ambRead (s • γ') b = s • ambRead γ' b := by
      funext z
      show Gext (s • γ') ((chartAt (H := ℂ) b).symm z) = s • Gext γ' ((chartAt (H := ℂ) b).symm z)
      rw [Gext_smul]
      rfl
  · rw [hreadsmul]
    exact meromorphicAt_const_smul s hγmer
  · have hsmer : MeromorphicAt (s • ambRead γ' b) (βpt b) := meromorphicAt_const_smul s hγmer
    have hsord : meromorphicOrderAt (s • ambRead γ' b) (βpt b) = (n : WithTop ℤ) := by
      rw [meromorphicOrderAt_const_smul hs0]
      exact hreadord
    have hscoeff : laurentCoeff n (s • ambRead γ' b) (βpt b) = lt := by
      rw [laurentCoeff_smul s hγmer (le_of_eq hreadord.symm), ← hlγdef, smul_eq_mul, hsdef,
        div_mul_cancel₀ lt hlγ0]
    have htsub : MeromorphicAt (t - s • ambRead γ' b) (βpt b) := ht.sub hsmer
    have hsubge : (n : WithTop ℤ) ≤ meromorphicOrderAt (t - s • ambRead γ' b) (βpt b) := by
      refine le_trans ?_ (min_le_meromorphicOrderAt_sub ht hsmer)
      rw [hn, hsord, min_self]
    have hcoeff0 : laurentCoeff n (t - s • ambRead γ' b) (βpt b) = 0 := by
      rw [laurentCoeff_sub ht hsmer (le_of_eq hn.symm) (le_of_eq hsord.symm), hscoeff]
      exact sub_self lt
    have hstrict := (laurentCoeff_eq_zero_iff htsub hsubge).mp hcoeff0
    rw [hreadsmul]
    exact add_one_le_of_lt' hstrict

/-- The induction core: window length bounded by `N`. -/
private theorem exists_window_matching_aux (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) :
    ∀ (N : ℕ) (m : ℤ), E b ≤ m → m - E b ≤ (N : ℤ) →
      ∀ t : ℂ → ℂ, MeromorphicAt t (βpt b) →
        ((-m - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b) →
        ∃ c : ↥(𝔇.U j) → ℂ,
          c ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
          ((-(E b) : ℤ) : WithTop ℤ)
            ≤ meromorphicOrderAt (ambRead c b - t) (βpt b) := by
  intro N
  induction N with
  | zero =>
    intro m hEm hN t ht hord
    by_cases hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)
    · exact ⟨0, window_zero_case hcase⟩
    · -- exactly one window slot: cancel the leading coefficient with the scaled witness
      push Not at hcase
      have hm : m = E b := by omega
      obtain ⟨n, hn, hge, hlt⟩ : ∃ n : ℤ, meromorphicOrderAt t (βpt b) = (n : WithTop ℤ) ∧
          -m - 1 ≤ n ∧ n < -E b := by
        have hne : meromorphicOrderAt t (βpt b) ≠ ⊤ := fun hc => by
          rw [hc] at hcase
          exact absurd le_top (not_le.mpr hcase)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        refine ⟨n, hn.symm, ?_, ?_⟩
        · rw [← hn] at hord
          exact_mod_cast hord
        · rw [← hn] at hcase
          exact_mod_cast hcase
      obtain ⟨c₀, hc₀mem, hc₀mer, hc₀ord⟩ := window_cancel_step hwit hb E hEm ht hn hge hlt
      refine ⟨c₀, hc₀mem, ?_⟩
      -- `n + 1 = −E b` here: the residual is already regular
      have hread : ambRead c₀ b - t = (-1 : ℂ) • (t - ambRead c₀ b) := by
        funext z
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
      refine le_trans (le_of_eq ?_) hc₀ord
      congr 1
      omega
  | succ N ih =>
    intro m hEm hN t ht hord
    by_cases hcase : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)
    · exact ⟨0, window_zero_case hcase⟩
    · push Not at hcase
      obtain ⟨n, hn, hge, hlt⟩ : ∃ n : ℤ, meromorphicOrderAt t (βpt b) = (n : WithTop ℤ) ∧
          -m - 1 ≤ n ∧ n < -E b := by
        have hne : meromorphicOrderAt t (βpt b) ≠ ⊤ := fun hc => by
          rw [hc] at hcase
          exact absurd le_top (not_le.mpr hcase)
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
        refine ⟨n, hn.symm, ?_, ?_⟩
        · rw [← hn] at hord
          exact_mod_cast hord
        · rw [← hn] at hcase
          exact_mod_cast hcase
      obtain ⟨c₀, hc₀mem, hc₀mer, hc₀ord⟩ := window_cancel_step hwit hb E hEm ht hn hge hlt
      set t₁ : ℂ → ℂ := t - ambRead c₀ b with ht₁def
      have ht₁mer : MeromorphicAt t₁ (βpt b) := ht.sub hc₀mer
      by_cases hcase₁ : ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t₁ (βpt b)
      · -- the residual is already regular: `c₀` matches
        refine ⟨c₀, hc₀mem, ?_⟩
        have hread : ambRead c₀ b - t = (-1 : ℂ) • t₁ := by
          funext z
          simp only [ht₁def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hread, meromorphicOrderAt_const_smul (by norm_num : (-1 : ℂ) ≠ 0)]
        exact hcase₁
      · -- recurse on the strictly shorter window `[n+1, −E b)`
        push Not at hcase₁
        have hn1 : n + 1 < -E b := by
          rcases lt_or_ge (n + 1) (-E b) with h | h
          · exact h
          · exfalso
            exact absurd (le_trans (by exact_mod_cast h) hc₀ord) (not_le.mpr hcase₁)
        set m₁ : ℤ := -n - 2 with hm₁def
        have hEm₁ : E b ≤ m₁ := by omega
        have hN₁ : m₁ - E b ≤ (N : ℤ) := by
          have : (↑(N + 1) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
          omega
        have hord₁ : ((-m₁ - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t₁ (βpt b) := by
          refine le_trans (le_of_eq ?_) hc₀ord
          congr 1
          omega
        obtain ⟨c₁, hc₁mem, hc₁ord⟩ := ih m₁ hEm₁ hN₁ t₁ ht₁mer hord₁
        refine ⟨c₀ + c₁, ?_, ?_⟩
        · exact Submodule.add_mem _ hc₀mem
            (OmegaD_window_mono (by omega : m₁ ≤ m) hEm₁ hc₁mem)
        · have hread : ambRead (c₀ + c₁) b - t = ambRead c₁ b - t₁ := by
            funext z
            show Gext (c₀ + c₁) ((chartAt (H := ℂ) b).symm z) - t z
              = Gext c₁ ((chartAt (H := ℂ) b).symm z) - t₁ z
            rw [Gext_add]
            simp only [ht₁def, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
            ring
          rw [hread]
          exact hc₁ord

/-- **W2 — the triangular window realization** (`DICT_ROUTE.md` W2): at a marked point
`b ∈ U j` of a cover with the `ExactOrderWitness`, every meromorphic target `t` of ambient
order `≥ −(m+1)` is matched, through the full Laurent window `−(m+1) … −(E b+1)`, by a
section of the window package `𝒪_{E + (m−E b)·b + b}(U j)`: the difference of the ambient
reads has order `≥ −E b` at `b`. -/
theorem exists_window_matching_section (hwit : ExactOrderWitness 𝔇)
    {j : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j : Set X)) (E : Divisor X) {m : ℤ}
    (hEm : E b ≤ m) {t : ℂ → ℂ} (ht : MeromorphicAt t (βpt b))
    (hord : ((-m - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt t (βpt b)) :
    ∃ c : ↥(𝔇.U j) → ℂ,
      c ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j) ∧
      ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead c b - t) (βpt b) :=
  exists_window_matching_aux hwit hb E (m - E b).toNat m hEm (Int.self_le_toNat _) t ht hord

/-- Reads through the ambient chart at `b` agree near `βpt b` whenever the `X`-side functions
agree on an open set containing `b`. -/
theorem read_eventuallyEq_of_eqOn {F G : X → ℂ} {V : Set X} (hV : IsOpen V) (hbV : b ∈ V)
    (hFG : ∀ x ∈ V, F x = G x) :
    F ∘ (chartAt (H := ℂ) b).symm =ᶠ[𝓝 (βpt b)] G ∘ (chartAt (H := ℂ) b).symm := by
  have hb' : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  have hcont : ContinuousAt (chartAt (H := ℂ) b).symm (βpt b) :=
    (chartAt (H := ℂ) b).continuousAt_symm ((chartAt (H := ℂ) b).map_source hb')
  have hli : (chartAt (H := ℂ) b).symm (βpt b) = b := (chartAt (H := ℂ) b).left_inv hb'
  have hmem : ∀ᶠ ζ in 𝓝 (βpt b), (chartAt (H := ℂ) b).symm ζ ∈ V := by
    refine hcont.preimage_mem_nhds ?_
    rw [hli]
    exact hV.mem_nhds hbV
  filter_upwards [hmem] with ζ hζ
  exact hFG _ hζ

/-- Restriction membership for `OmegaD` by precomposition with the open inclusion. -/
theorem OmegaD_comp_openIncl {D' : Divisor X} {U V : Opens X} (h : V ≤ U) {f : ↥U → ℂ}
    (hf : f ∈ OmegaD D' U) : f ∘ openIncl h ∈ OmegaD D' V :=
  ⟨isMeromorphic_comp_openIncl h hf.1, fun v => by
    rw [ordU_comp_openIncl]
    exact hf.2 _⟩

/-! ## Part 2 — the deep-matching star cochain (`DeepTestData`)

The multi-chart replacement of `TestCocycleData` at a possibly non-isolated marked point:
one section per star chart, all matching a COMMON ambient window target `t` of exact order
`−(m+1)` at `b`.  Pairwise differences then meet the `𝒪_E` bound at `b`, so the coboundary
is a `Z¹(𝒪_E)` test cocycle trivialized at level `D` by the cochain itself. -/

variable {E : Divisor X} {m : ℤ}

/-- **The deep-matching star test datum** at `(E, b, m)`: a common ambient window target `t`
of exact order `−(m+1)` at `b`, and per-chart sections of the window package matching `t`
through the full window (zero off the star). -/
structure DeepTestData (𝔇 : ChartDiskCover X) (E : Divisor X) (b : X) (m : ℤ) where
  /-- The window bound `E b ≤ m`. -/
  hmE : E b ≤ m
  /-- The common ambient window target. -/
  t : ℂ → ℂ
  /-- The target is meromorphic at the ambient chart point. -/
  tmer : MeromorphicAt t (βpt b)
  /-- The target has exact order `−(m+1)`. -/
  tord : meromorphicOrderAt t (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ)
  /-- The per-chart sections. -/
  c : ∀ i : 𝔇.toFiniteCover.ι, ↥(𝔇.U i) → ℂ
  /-- Star sections satisfy the window package bounds. -/
  mem : ∀ i, ∀ _ : b ∈ (𝔇.U i : Set X),
    c i ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i)
  /-- Off-star sections vanish. -/
  zero : ∀ i, b ∉ (𝔇.U i : Set X) → c i = 0
  /-- Star sections match the target through the full window. -/
  matched : ∀ i, ∀ _ : b ∈ (𝔇.U i : Set X),
    ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead (c i) b - t) (βpt b)

/-- The deep test datum exists on any cover with the exact-order witness (the common target
is the ambient read of the distinguished-chart witness section). -/
theorem DeepTestData.exists_of_witness (hwit : ExactOrderWitness 𝔇)
    {j₀ : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j₀ : Set X)) (hmE : E b ≤ m) :
    Nonempty (DeepTestData 𝔇 E b m) := by
  classical
  -- the distinguished witness section and its ambient read
  obtain ⟨γ, hγmem, hγord⟩ := hwit (E + Finsupp.single b (m - E b)) j₀ b hb
  have hDb : (E + Finsupp.single b (m - E b) : Divisor X) b = m := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    ring
  have hγordm : ordU γ ⟨b, hb⟩ = ((-m - 1 : ℤ) : WithTop ℤ) := by
    rw [hγord, hDb]
  set t : ℂ → ℂ := ambRead γ b with htdef
  have hγmer : IsMeromorphic ((𝔇.U j₀ : Opens X) : Type _) γ := hγmem.1
  have tmer : MeromorphicAt t (βpt b) := Gext_meromorphicAt hγmer hb
  have tord : meromorphicOrderAt t (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ) := by
    rw [htdef, show meromorphicOrderAt (ambRead γ b) (βpt b) = ordU γ ⟨b, hb⟩ from
      (ordU_eq_orderAt_Gext γ hb).symm]
    exact hγordm
  -- per-chart matching sections
  have hsec : ∀ i : 𝔇.toFiniteCover.ι, ∃ ci : ↥(𝔇.U i) → ℂ,
      (b ∈ (𝔇.U i : Set X) →
        ci ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i) ∧
        ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead ci b - t) (βpt b)) ∧
      (b ∉ (𝔇.U i : Set X) → ci = 0) := by
    intro i
    by_cases hi : b ∈ (𝔇.U i : Set X)
    · obtain ⟨ci, hcm, hco⟩ := exists_window_matching_section hwit hi E hmE tmer
        (le_of_eq tord.symm)
      exact ⟨ci, fun _ => ⟨hcm, hco⟩, fun h => absurd hi h⟩
    · exact ⟨0, fun h => absurd h hi, fun _ => rfl⟩
  choose cfun hstar hoff using hsec
  exact ⟨⟨hmE, t, tmer, tord, cfun, fun i hi => (hstar i hi).1, hoff,
    fun i hi => (hstar i hi).2⟩⟩

namespace DeepTestData

variable (dd : DeepTestData 𝔇 E b m)

/-- The ambient read of a star section is meromorphic at `βpt b`. -/
theorem ambRead_mer {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    MeromorphicAt (ambRead (dd.c i) b) (βpt b) :=
  ambRead_meromorphicAt (dd.mem i hi) hi

/-- **Star sections have exact order `−(m+1)` at `b`** (the target order dominates the
matching defect: `−(m+1) < −E b`). -/
theorem ordU_c {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    ordU (dd.c i) ⟨b, hi⟩ = ((-m - 1 : ℤ) : WithTop ℤ) := by
  have hsplit : ambRead (dd.c i) b = dd.t + (ambRead (dd.c i) b - dd.t) := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hlt : ((-m - 1 : ℤ) : WithTop ℤ)
      < meromorphicOrderAt (ambRead (dd.c i) b - dd.t) (βpt b) := by
    refine lt_of_lt_of_le ?_ (dd.matched i hi)
    have := dd.hmE
    exact_mod_cast (by omega : -m - 1 < -(E b))
  rw [ordU_eq_orderAt_Gext (dd.c i) hi]
  show meromorphicOrderAt (ambRead (dd.c i) b) (βpt b) = ((-m - 1 : ℤ) : WithTop ℤ)
  rw [hsplit]
  exact meromorphicOrderAt_add_of_lt dd.tmer ((dd.ambRead_mer hi).sub dd.tmer) dd.tord hlt

/-- The per-star-chart `TestCocycleData` package carried by the deep datum. -/
noncomputable def toTestCocycleData {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) :
    TestCocycleData 𝔇 E i b hi m :=
  ⟨dd.c i, dd.mem i hi, dd.ordU_c hi⟩

/-- **The window defect of two star sections** meets the `𝒪_E` bound at `b` (read on any
common sub-open): the two matching defects subtract. -/
theorem ordU_sub_ge {i k : 𝔇.toFiniteCover.ι} {V : Opens X} (h₁ : V ≤ 𝔇.U i)
    (h₂ : V ≤ 𝔇.U k) (hi : b ∈ (𝔇.U i : Set X)) (hk : b ∈ (𝔇.U k : Set X)) (hbV : b ∈ V) :
    ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU
      ((dd.c i ∘ openIncl h₁) - (dd.c k ∘ openIncl h₂)) ⟨b, hbV⟩ := by
  set d : ↥V → ℂ := (dd.c i ∘ openIncl h₁) - (dd.c k ∘ openIncl h₂) with hddef
  -- the ambient read of the difference is the difference of the ambient reads, near `βpt b`
  have hev : ambRead d b =ᶠ[𝓝 (βpt b)] (ambRead (dd.c i) b - ambRead (dd.c k) b) := by
    have heq : ∀ x ∈ (V : Set X), Gext d x = (Gext (dd.c i) - Gext (dd.c k)) x := by
      intro x hx
      have hxi : x ∈ (𝔇.U i : Set X) := h₁ hx
      have hxk : x ∈ (𝔇.U k : Set X) := h₂ hx
      rw [Gext_apply_mem d hx, Pi.sub_apply, Gext_apply_mem (dd.c i) hxi,
        Gext_apply_mem (dd.c k) hxk]
      rfl
    exact read_eventuallyEq_of_eqOn V.isOpen hbV heq
  show ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU d ⟨b, hbV⟩
  rw [ordU_eq_orderAt_Gext d hbV]
  show ((-(E b) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (ambRead d b) (βpt b)
  rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)]
  -- subtract the two matching defects
  have hsplit : ambRead (dd.c i) b - ambRead (dd.c k) b
      = (ambRead (dd.c i) b - dd.t) - (ambRead (dd.c k) b - dd.t) := by
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  refine le_trans ?_ (min_le_meromorphicOrderAt_sub ((dd.ambRead_mer hi).sub dd.tmer)
    ((dd.ambRead_mer hk).sub dd.tmer))
  exact le_min (dd.matched i hi) (dd.matched k hk)

/-- The deep test 0-cochain: the germ of the matching section on each cover set. -/
noncomputable def cochain : 𝔇.toFiniteCover.toFiniteFamily.Cochain0 :=
  fun i => toGerm (𝔇.U i) (dd.c i)

theorem cochain_apply (i : 𝔇.toFiniteCover.ι) :
    dd.cochain i = toGerm (𝔇.U i) (dd.c i) := rfl

/-- **Level-`E` membership of the deep coboundary**: on star overlaps the matching windows
cancel; mixed overlaps avoid `b`; off-star components vanish. -/
theorem delta_mem_sections1 :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections1 E := by
  intro p
  obtain ⟨i, k⟩ := p
  have hδ : 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain (i, k)
      = rawRestrictG inf_le_right (dd.cochain k)
        - rawRestrictG inf_le_left (dd.cochain i) := by
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
  rw [hδ]
  by_cases hi : b ∈ (𝔇.U i : Set X) <;> by_cases hk : b ∈ (𝔇.U k : Set X)
  · -- both star: the matching windows cancel at `b`
    have hbV : b ∈ (𝔇.U i ⊓ 𝔇.U k : Opens X) := ⟨hi, hk⟩
    set d : ↥(𝔇.U i ⊓ 𝔇.U k : Opens X) → ℂ :=
      (dd.c k ∘ openIncl inf_le_right) - (dd.c i ∘ openIncl inf_le_left) with hddef
    have hcomp : rawRestrictG (inf_le_right : (𝔇.U i ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U k)
          (dd.cochain k)
        - rawRestrictG (inf_le_left : (𝔇.U i ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U i) (dd.cochain i)
        = toGerm _ d := by
      rw [cochain_apply, cochain_apply, rawRestrictG_coe, rawRestrictG_coe, hddef, map_sub]
    rw [hcomp]
    -- the difference satisfies the window package and the `𝒪_E` order bound at `b`
    have hdmem : d ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1)
        (𝔇.U i ⊓ 𝔇.U k) :=
      sub_mem (OmegaD_comp_openIncl _ (dd.mem k hk)) (OmegaD_comp_openIncl _ (dd.mem i hi))
    have hdord : ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU d ⟨b, hbV⟩ :=
      dd.ordU_sub_ge inf_le_right inf_le_left hk hi hbV
    exact ⟨d, mem_OmegaD_of_window_of_ordU hdmem hbV hdord, rfl⟩
  · -- `i` star, `k` off-star: the overlap avoids `b`
    have h0 : dd.cochain k = 0 := by
      rw [cochain_apply, dd.zero k hk, map_zero]
    rw [h0, map_zero, zero_sub]
    refine neg_mem ?_
    refine OmegaDGerm_mono (fun x hx => ?_)
      (rawRestrictG_omegaDGerm _ ⟨dd.c i, dd.mem i hi, rfl⟩)
    have hxb : x ≠ b := fun hc => hk (hc ▸ hx.2)
    rw [window_divisor_apply_ne hxb]
  · -- `i` off-star, `k` star: symmetric
    have h0 : dd.cochain i = 0 := by
      rw [cochain_apply, dd.zero i hi, map_zero]
    rw [h0, map_zero, sub_zero]
    refine OmegaDGerm_mono (fun x hx => ?_)
      (rawRestrictG_omegaDGerm _ ⟨dd.c k, dd.mem k hk, rfl⟩)
    have hxb : x ≠ b := fun hc => hi (hc ▸ hx.1)
    rw [window_divisor_apply_ne hxb]
  · -- both off-star
    have h0i : dd.cochain i = 0 := by
      rw [cochain_apply, dd.zero i hi, map_zero]
    have h0k : dd.cochain k = 0 := by
      rw [cochain_apply, dd.zero k hk, map_zero]
    rw [h0i, h0k, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _

/-- **Level-`D` membership of the deep cochain** (`m + 1 ≤ D b`, `E ≤ D`): the trivializing
0-cochain of the test class in `H¹(𝒪_D)`. -/
theorem cochain_mem_sections0 {D : Divisor X} (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    dd.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 D := by
  intro i
  by_cases hi : b ∈ (𝔇.U i : Set X)
  · refine OmegaDGerm_mono (D₁ := E + Finsupp.single b (m - E b) + Finsupp.single b 1)
      (fun x _ => ?_) ⟨dd.c i, dd.mem i hi, rfl⟩
    by_cases hx : x = b
    · subst hx
      rw [window_divisor_apply_self]
      exact hmD
    · rw [window_divisor_apply_ne hx]
      exact hED x
  · rw [cochain_apply, dd.zero i hi, map_zero]
    exact Submodule.zero_mem _

/-- The deep test coboundary is a cocycle (`δ¹ ∘ δ⁰ = 0`). -/
theorem delta_mem_ker :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta1
      (𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain) = 0 := by
  have h := DFunLike.congr_fun
    (𝔇.toFiniteCover.toFiniteFamily.cechDelta1_comp_cechDelta0) dd.cochain
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

/-- **The deep test cocycle**, as an element of `Z¹(𝒪_E)`. -/
noncomputable def cocycle : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 E) :=
  ⟨𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain,
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr dd.delta_mem_ker, dd.delta_mem_sections1⟩⟩

@[simp] theorem cocycle_coe :
    (dd.cocycle : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 dd.cochain := rfl

/-- **The deep test class dies in `H¹(𝒪_D)`**. -/
theorem h1InclMono_cocycle_eq_zero {D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (hmD : m + 1 ≤ D b) :
    𝔇.toFiniteCover.h1InclMono hED (Submodule.Quotient.mk dd.cocycle) = 0 := by
  rw [𝔇.toFiniteCover.h1InclMono_mk, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  exact ⟨dd.cochain, dd.cochain_mem_sections0 hED hmD, rfl⟩

/-! ## Part 3 — the cup of the deep cochain with `f ∈ L(K−E)` -/

variable {K : Divisor X}

/-- **Level-`K+b` membership of the deep cup 0-cochain** `f·ĉ`: poles cancel against the
linear-system bounds on every star chart, leaving the single marked simple excess at `b`. -/
theorem cup_mem_sections0 {f : MeromorphicFunction X}
    (hfE : f ∈ linearSystem (X := X) (K - E)) {n : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1) := by
  intro i
  by_cases hi : b ∈ (𝔇.U i : Set X)
  · rw [cupCochain0_apply]
    exact mulConstG_omegaDGerm (mem_linearSystem_marked hfE hn hm)
      ⟨dd.c i, dd.mem i hi, rfl⟩
  · rw [cupCochain0_apply, cochain_apply, dd.zero i hi, map_zero, mul_zero]
    exact Submodule.zero_mem _

/-- The deep cup cochain restricts on the distinguished chart to the `TestCocycleData` cup
component (the input shape of the generalized `exists_slotProductSimplePoleAt`). -/
theorem cup_component_eq [DecidableEq 𝔇.toFiniteCover.ι] {f : MeromorphicFunction X}
    {j₀ : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j₀ : Set X)) :
    cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain j₀
      = cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f
          ((dd.toTestCocycleData hb).cochain) j₀ := by
  rw [cupCochain0_apply, cupCochain0_apply, TestCocycleData.cochain_self]
  rfl

end DeepTestData

/-! ## Part 4 — W3/W4: the cutoff, the repaired presentation, and the engine application

The marked point `b` may lie in several cover sets (`K b = 0`).  The level-`K+b` extraction
`h⁰ := vanishFn (f·ĉ)` has a simple pole at `b` in every star chart; the global cutoff
scalar `H := θ·h⁰_{j₀}` (W3) carries the common principal part, and the repaired
presentation `h̃_i := repairAtX b (h⁰_i − H)` (W4) is smooth at `b`, presents the same
cocycle, and feeds the W1 engine
(`resFunctional_eq_neg_residue_of_global_correction`). -/

/-- The marked-point support bookkeeping: with `K b = 0`, the `(K+b)`-points are the
K-points plus `b` itself. -/
theorem mem_posSupp_add_single_iff {K : Divisor X} (hKb : K b = 0) {x : X} :
    x ∈ posSupp (K + Finsupp.single b 1) ↔ x = b ∨ x ∈ posSupp K := by
  rw [mem_posSupp_iff, mem_posSupp_iff]
  by_cases hx : x = b
  · subst hx
    rw [Finsupp.add_apply, Finsupp.single_eq_same, hKb]
    simp
  · rw [Finsupp.add_apply, show (Finsupp.single b 1 : Divisor X) x = 0 from
      Finsupp.single_eq_of_ne hx, add_zero]
    simp [hx]

/-- **X-side single-point limit repair**: replace the value at `b` by the punctured limit. -/
noncomputable def repairAtX (b : X) (F : X → ℂ) : X → ℂ :=
  fun x => if x = b then limUnder (𝓝[≠] b) F else F x

theorem repairAtX_apply_ne {F : X → ℂ} {y : X} (hy : y ≠ b) : repairAtX b F y = F y :=
  if_neg hy

@[simp] theorem repairAtX_apply_self {F : X → ℂ} :
    repairAtX b F b = limUnder (𝓝[≠] b) F := if_pos rfl

theorem repairAtX_eventuallyEq_off {F : X → ℂ} {x : X} (hx : x ≠ b) :
    repairAtX b F =ᶠ[𝓝 x] F := by
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (by simpa using hx : x ∈ ({b}ᶜ : Set X))] with y hy
  exact repairAtX_apply_ne (by simpa using hy)

/-- X-side punctured eventual equality transfers to the ambient chart reads. -/
theorem read_eventuallyEq_of_eventuallyEq_nhdsNE {F G : X → ℂ} (h : F =ᶠ[𝓝[≠] b] G) :
    (F ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝[≠] (βpt b)] (G ∘ (chartAt (H := ℂ) b).symm) := by
  have hbsrc : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  have hzt := (chartAt (H := ℂ) b).map_source hbsrc
  have hsymtend : Tendsto (chartAt (H := ℂ) b).symm (𝓝[≠] (βpt b)) (𝓝[≠] b) := by
    have h2 := (chartAt (H := ℂ) b).symm.tendsto_nhdsNE (x := βpt b) (by simp [hzt])
    rwa [(chartAt (H := ℂ) b).left_inv hbsrc] at h2
  filter_upwards [hsymtend.eventually h] with ζ hζ
  exact hζ

/-- **X-side limit from a chart-side punctured analytic extension.** -/
theorem tendsto_of_read_extension {F : X → ℂ} {q : ℂ → ℂ}
    (hq : AnalyticAt ℂ q (βpt b))
    (hev : (F ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝[≠] (βpt b)] q) :
    Tendsto F (𝓝[≠] b) (𝓝 (q (βpt b))) := by
  have hbsrc : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  have hfwd : Tendsto (chartAt (H := ℂ) b) (𝓝[≠] b) (𝓝[≠] (βpt b)) :=
    (chartAt (H := ℂ) b).tendsto_nhdsNE hbsrc
  have h1 : Tendsto (fun x => q ((chartAt (H := ℂ) b) x)) (𝓝[≠] b) (𝓝 (q (βpt b))) :=
    hq.continuousAt.tendsto.comp (hfwd.mono_right nhdsWithin_le_nhds)
  refine h1.congr' ?_
  have hFev : (fun x => q ((chartAt (H := ℂ) b) x)) =ᶠ[𝓝[≠] b] F := by
    filter_upwards [hfwd.eventually hev, eventually_nhdsWithin_of_eventually_nhds
        ((chartAt (H := ℂ) b).open_source.mem_nhds hbsrc)] with y h1' h2'
    have h3 : (F ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) y) = F y := by
      rw [Function.comp_apply, (chartAt (H := ℂ) b).left_inv h2']
    rw [← h3]
    exact h1'.symm
  exact hFev

/-- **The repaired read agrees with the analytic extension on a FULL neighbourhood** of the
ambient chart point (punctured agreement + the limit value at `b`). -/
theorem repairAtX_read_eventuallyEq {F : X → ℂ} {q : ℂ → ℂ}
    (hq : AnalyticAt ℂ q (βpt b))
    (hev : (F ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝[≠] (βpt b)] q) :
    (repairAtX b F ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝 (βpt b)] q := by
  haveI := nhdsNE_neBot b
  have hlim : limUnder (𝓝[≠] b) F = q (βpt b) :=
    (tendsto_of_read_extension hq hev).limUnder_eq
  have hbsrc : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  have hzt : βpt b ∈ (chartAt (H := ℂ) b).target := (chartAt (H := ℂ) b).map_source hbsrc
  rw [EventuallyEq, eventually_nhdsWithin_iff] at hev
  filter_upwards [hev, (chartAt (H := ℂ) b).open_target.mem_nhds hzt] with ζ h1 h2
  by_cases hζ : ζ = βpt b
  · subst hζ
    show repairAtX b F ((chartAt (H := ℂ) b).symm (βpt b)) = q (βpt b)
    rw [(chartAt (H := ℂ) b).left_inv hbsrc, repairAtX_apply_self, hlim]
  · have hsne : (chartAt (H := ℂ) b).symm ζ ≠ b := by
      intro hc
      apply hζ
      have h3 := congrArg (chartAt (H := ℂ) b) hc
      rwa [(chartAt (H := ℂ) b).right_inv h2] at h3
    show repairAtX b F ((chartAt (H := ℂ) b).symm ζ) = q ζ
    rw [repairAtX_apply_ne hsne]
    exact h1 (by simpa using hζ)

section Engine

variable [Nonempty X] [DecidableEq 𝔇.toFiniteCover.ι] {K : Divisor X}

/-- **The presentation identity off the positive locus**: the level-`K` cocycle extraction
agrees pointwise with the coboundary of a level-`K'` cochain extraction at every overlap
point where `K'` is non-positive (the localized form of
`isCoboundaryOn_cocycleFn_vanishFn`, no pole separation at level `K'` required). -/
theorem cocycleFn_eq_vanishFn_sub_at {K' : Divisor X} (hsep : SeparatesPoles 𝔇 K)
    (z : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K))
    {F0 : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hF0 : F0 ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 K')
    (hcb : (z : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 F0)
    {i j : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X))
    (hxK' : K' x ≤ 0) :
    cocycleFn 𝔇 hsep z i j x = vanishFn F0 hF0 j x - vanishFn F0 hF0 i x := by
  by_cases h : i = j
  · subst h
    rw [cocycleFn_diag]
    simp
  · set V : Opens X := (𝔇.U i ⊓ 𝔇.U j) ⊓ offPos K' with hVdef
    have hxV : x ∈ V := ⟨hx, mem_offPos_iff.mpr hxK'⟩
    have hVij : V ≤ 𝔇.U i ⊓ 𝔇.U j := inf_le_left
    have hle_i : V ≤ 𝔇.U i ⊓ offPos K' :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hle_j : V ≤ 𝔇.U j ⊓ offPos K' :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hxi : x ∈ (𝔇.U i ⊓ offPos K' : Opens X) := hle_i hxV
    have hxj : x ∈ (𝔇.U j ⊓ offPos K' : Opens X) := hle_j hxV
    refine eq_at_of_toGerm_eq (V := V) ?_ hxV (continuousAt_cocycleFn 𝔇 hsep z hx)
      (((holoFn_contMDiffAt (restrict_mem_omegaDGerm_zero hF0 j) hxj).continuousAt).sub
        ((holoFn_contMDiffAt (restrict_mem_omegaDGerm_zero hF0 i) hxi).continuousAt))
    show toGerm V (fun v => cocycleFn 𝔇 hsep z i j v.1)
        = toGerm V ((fun v : ↥V => vanishFn F0 hF0 j v.1) - fun v => vanishFn F0 hF0 i v.1)
    have hj' : toGerm V (fun v => vanishFn F0 hF0 j v.1)
        = rawRestrictG (hVij.trans inf_le_right) (F0 j) := by
      have h1 : rawRestrictG hle_j
            (toGerm (𝔇.U j ⊓ offPos K') (fun v => vanishFn F0 hF0 j v.1))
          = toGerm V (fun v => vanishFn F0 hF0 j v.1) := rfl
      rw [← h1, vanishFn, toGerm_holoFn (restrict_mem_omegaDGerm_zero hF0 j),
        FiniteFamily.rawRestrictG_comp_apply]
    have hi' : toGerm V (fun v => vanishFn F0 hF0 i v.1)
        = rawRestrictG (hVij.trans inf_le_left) (F0 i) := by
      have h1 : rawRestrictG hle_i
            (toGerm (𝔇.U i ⊓ offPos K') (fun v => vanishFn F0 hF0 i v.1))
          = toGerm V (fun v => vanishFn F0 hF0 i v.1) := rfl
      rw [← h1, vanishFn, toGerm_holoFn (restrict_mem_omegaDGerm_zero hF0 i),
        FiniteFamily.rawRestrictG_comp_apply]
    rw [map_sub, hj', hi', toGerm_cocycleFn_restrict 𝔇 hsep z h hVij, hcb]
    have hδ : 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 F0 (i, j)
        = rawRestrictG inf_le_right (F0 j) - rawRestrictG inf_le_left (F0 i) := by
      simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hδ, map_sub, FiniteFamily.rawRestrictG_comp_apply,
      FiniteFamily.rawRestrictG_comp_apply]

namespace DeepTestData

variable {E : Divisor X} {m : ℤ} (dd : DeepTestData 𝔇 E b m)

/-- **The boundary read-back of the deep cup extraction** at a star chart: near the marked
point, the level-`K+b` extraction agrees with the honest product representative `f·c_i`. -/
theorem vanishFn_eventuallyEq_Gext_cupRep {f : MeromorphicFunction X}
    {n : ℤ} (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b)
    {i : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X))
    (hF0 : cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1)) :
    ∀ᶠ x in 𝓝[≠] b,
      vanishFn (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain) hF0 i x
        = Gext ((dd.toTestCocycleData hi).cupRep f) x := by
  classical
  set td := dd.toTestCocycleData hi with htddef
  set W : Opens X := 𝔇.U i ⊓ offPos (K + Finsupp.single b 1) with hWdef
  set F : ↥W → ℂ := td.cupRep f ∘ openIncl (inf_le_left : W ≤ 𝔇.U i) with hFdef
  have hgF : toGerm W F = rawRestrictG (inf_le_left : W ≤ 𝔇.U i)
      (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f dd.cochain i) := by
    rw [dd.cup_component_eq hi, ← td.toGerm_cupRep f]
    rfl
  -- punctured neighbourhoods of `b` lie in `W`
  have hWnear : ∀ᶠ x in 𝓝[≠] b, x ∈ W := by
    set T : Finset X := (posSupp (K + Finsupp.single b 1)).erase b with hTdef
    have hTcl : IsClosed ((T : Finset X) : Set X) := T.finite_toSet.isClosed
    have hbT : b ∉ ((T : Finset X) : Set X) := by simp [hTdef]
    rw [eventually_nhdsWithin_iff]
    filter_upwards [(𝔇.U i).isOpen.mem_nhds hi, hTcl.isOpen_compl.mem_nhds hbT]
      with x hx1 hx2 hxb
    have hxb' : x ≠ b := by simpa using hxb
    refine ⟨hx1, mem_offPos_iff.mpr ?_⟩
    by_contra hpos
    push Not at hpos
    exact hx2 (Finset.mem_erase.mpr ⟨hxb', mem_posSupp_iff.mpr hpos⟩)
  -- ambient-chart meromorphy and exact order of the honest representative
  have hcmer : MeromorphicAt (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) :=
    Gext_meromorphicAt (td.isMeromorphic_cupRep f) hi
  have hcord : meromorphicOrderAt (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) = ((-(K b) - 1 : ℤ) : WithTop ℤ) := by
    rw [← ordU_eq_orderAt_Gext (td.cupRep f) hi]
    exact td.ordU_cupRep hn hm
  have hGFeq : ∀ᶠ x in 𝓝[≠] b, Gext F x = Gext (td.cupRep f) x := by
    filter_upwards [hWnear] with x hxW
    rw [Gext_apply_mem F hxW, Gext_apply_mem (td.cupRep f)
      ((inf_le_left : W ≤ 𝔇.U i) hxW : x ∈ 𝔇.U i)]
    rfl
  have hψtend : Tendsto (chartAt (H := ℂ) b).symm
      (𝓝[≠] ((chartAt (H := ℂ) b) b)) (𝓝[≠] b) := by
    have h := (chartAt (H := ℂ) b).symm.tendsto_nhdsNE (x := (chartAt (H := ℂ) b) b)
      (by simp [(chartAt (H := ℂ) b).map_source (mem_chart_source ℂ b)])
    simpa [(chartAt (H := ℂ) b).left_inv (mem_chart_source ℂ b)] using h
  have hreadeq : (Gext F ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm) :=
    hψtend.eventually hGFeq
  have hFmer : MeromorphicAt (Gext F ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) := hcmer.congr hreadeq.symm
  have hFord : meromorphicOrderAt (Gext F ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) = ((-(K b) - 1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr hreadeq]
    exact hcord
  have hread := holoFn_eventuallyEq_near_marked (restrict_mem_omegaDGerm_zero hF0 i)
    hgF hWnear hFmer hFord
  filter_upwards [hread, hGFeq] with x h1 h2
  exact h1.trans h2

/-- **The analytic cancellation of two star cup representatives** at the marked point: with
`E b ≤ n`, the difference `f·c_i − f·c_k` has nonnegative order at `b`, hence an analytic
punctured extension of its ambient read. -/
theorem exists_analyticAt_cupRep_sub {f : MeromorphicFunction X} {n : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) (hnE : E b ≤ n)
    {i k : 𝔇.toFiniteCover.ι} (hi : b ∈ (𝔇.U i : Set X)) (hk : b ∈ (𝔇.U k : Set X)) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (βpt b) ∧
      ((fun x => Gext ((dd.toTestCocycleData hi).cupRep f) x
          - Gext ((dd.toTestCocycleData hk).cupRep f) x)
        ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝[≠] (βpt b)] q := by
  set V : Opens X := 𝔇.U i ⊓ 𝔇.U k with hVdef
  have hbV : b ∈ V := ⟨hi, hk⟩
  set diff : ↥V → ℂ :=
    (dd.c i ∘ openIncl inf_le_left) - (dd.c k ∘ openIncl inf_le_right) with hdiffdef
  have hdiffmem : diff ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) V :=
    sub_mem (OmegaD_comp_openIncl _ (dd.mem i hi)) (OmegaD_comp_openIncl _ (dd.mem k hk))
  have hdiffmer : IsMeromorphic (V : Type _) diff := hdiffmem.1
  set dV : ↥V → ℂ := (f.toFun ∘ Subtype.val) * diff with hdVdef
  have hdVmer : IsMeromorphic (V : Type _) dV :=
    fun v => ((isMeromorphic_val f) v).mul (hdiffmer v)
  have hordb : (0 : WithTop ℤ) ≤ ordU dV ⟨b, hbV⟩ := by
    rw [hdVdef, ordU_globalMul f hdiffmer ⟨b, hbV⟩, hn]
    have h2 : ((-(E b) : ℤ) : WithTop ℤ) ≤ ordU diff ⟨b, hbV⟩ :=
      dd.ordU_sub_ge inf_le_left inf_le_right hi hk hbV
    have h3 : ((n + -(E b) : ℤ) : WithTop ℤ)
        ≤ ((n : ℤ) : WithTop ℤ) + ordU diff ⟨b, hbV⟩ := by
      have hcast : ((n + -(E b) : ℤ) : WithTop ℤ)
          = ((n : ℤ) : WithTop ℤ) + ((-(E b) : ℤ) : WithTop ℤ) := by
        exact_mod_cast (WithTop.coe_add n (-(E b)))
      rw [hcast]
      exact add_le_add le_rfl h2
    refine le_trans ?_ h3
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + -(E b))
  have hread_mer : MeromorphicAt (ambRead dV b) (βpt b) := Gext_meromorphicAt hdVmer hbV
  have hread_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (ambRead dV b) (βpt b) := by
    rw [show meromorphicOrderAt (ambRead dV b) (βpt b) = ordU dV ⟨b, hbV⟩ from
      (ordU_eq_orderAt_Gext dV hbV).symm]
    exact hordb
  obtain ⟨q, hq, hqe⟩ := exists_analyticAt_extension hread_mer hread_ord
  refine ⟨q, hq, ?_⟩
  have heqOn : ∀ x ∈ (V : Set X),
      (fun x => Gext ((dd.toTestCocycleData hi).cupRep f) x
        - Gext ((dd.toTestCocycleData hk).cupRep f) x) x = Gext dV x := by
    intro x hx
    show Gext ((dd.toTestCocycleData hi).cupRep f) x
        - Gext ((dd.toTestCocycleData hk).cupRep f) x = Gext dV x
    rw [Gext_apply_mem ((dd.toTestCocycleData hi).cupRep f) (hx.1 : x ∈ 𝔇.U i),
      Gext_apply_mem ((dd.toTestCocycleData hk).cupRep f) (hx.2 : x ∈ 𝔇.U k),
      Gext_apply_mem dV hx]
    show f.toFun x * dd.c i ⟨x, hx.1⟩ - f.toFun x * dd.c k ⟨x, hx.2⟩
        = f.toFun x * (dd.c i ⟨x, hx.1⟩ - dd.c k ⟨x, hx.2⟩)
    ring
  have hev2 := read_eventuallyEq_of_eqOn V.isOpen hbV heqOn
  exact (hev2.filter_mono nhdsWithin_le_nhds).trans hqe

end DeepTestData

/-- **THE NON-ISOLATED §17.7 EVALUATION** — the fine-sheaf residue functional does not
vanish on the cup of `f ∈ L(K−E)` with the DEEP test cocycle at a forced bad point `b` with
`K b = 0` (the residual case of the dictionary: `b` may lie in several cover sets).  The cup
coboundary is presented in the global-cutoff-subtracted form (`H := θ·h⁰_{j₀}`,
`h̃ := repairAtX b (h⁰ − H)`) and evaluated by the W1 engine
(`resFunctional_eq_neg_residue_of_global_correction`) to `−r ≠ 0`. -/
theorem resCocycle_cup_deepTestCocycle_ne_zero {E : Divisor X} {m : ℤ}
    (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (dd : DeepTestData 𝔇 E b m)
    {j₀ : 𝔇.toFiniteCover.ι} (hb : b ∈ (𝔇.U j₀ : Set X)) (hKb : K b = 0)
    (f : ↥(linearSystem (X := X) (K - E)))
    {n : ℤ} (hn : (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ))
    (hm : m = n + K b) :
    resCocycle 𝔇 hsep g hg
      (cupCocyclesMap (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f.2 dd.cocycle) ≠ 0 := by
  classical
  haveI := nhdsNE_neBot b
  have hKb0 : 0 ≤ K b := le_of_eq hKb.symm
  have hnE : E b ≤ n := by
    have h1 := dd.hmE
    omega
  -- the cup data and its coboundary presentation
  have hF0 : cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) (f : MeromorphicFunction X)
      dd.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1) :=
    dd.cup_mem_sections0 f.2 hn hm
  set z : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) :=
    cupCocyclesMap (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f.2 dd.cocycle with hzdef
  have hcb : (z : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0
        (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) (f : MeromorphicFunction X)
          dd.cochain) := by
    have h1 := LinearMap.congr_fun
      (cupCochain1_comp_cechDelta0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily)
        (f : MeromorphicFunction X)) dd.cochain
    simp only [LinearMap.comp_apply] at h1
    rw [hzdef, cupCocyclesMap_coe, dd.cocycle_coe]
    exact h1
  set h0 : 𝔇.toFiniteCover.ι → X → ℂ :=
    vanishFn (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) (f : MeromorphicFunction X)
      dd.cochain) hF0 with hh0def
  -- the bad set and the marked point
  have hbS : b ∉ posSupp K := fun hc => by
    rw [mem_posSupp_iff, hKb] at hc
    exact lt_irrefl 0 hc
  have hSiso : ∀ a ∈ posSupp K, ∃ i₀, MLIsolated 𝔇 i₀ a := fun a ha =>
    exists_isolated_of_separatesPoles 𝔇 hsep (mem_posSupp_iff.mp ha)
  have hnotpos : ∀ x : X, x ≠ b → x ∉ ((posSupp K : Finset X) : Set X) →
      x ∉ ((posSupp (K + Finsupp.single b 1) : Finset X) : Set X) := by
    intro x hxb hxS hc
    rcases (mem_posSupp_add_single_iff hKb).mp (Finset.mem_coe.mp hc) with h | h
    · exact hxb h
    · exact hxS (Finset.mem_coe.mpr h)
  have h0sm := smoothOnSetsOff_vanishFn hF0
  have h0hol := holomorphicOnSetsOff_vanishFn hF0
  -- W3: the bump and the global correction scalar
  set O : Set X := (𝔇.U j₀ : Set X) ∩ ((posSupp K : Finset X) : Set X)ᶜ with hOdef
  have hOopen : IsOpen O :=
    (𝔇.U j₀).isOpen.inter (posSupp K).finite_toSet.isClosed.isOpen_compl
  have hbO : O ∈ 𝓝 b := hOopen.mem_nhds ⟨hb, by simpa using hbS⟩
  obtain ⟨χ, -, hχsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℂ)) b).mem_iff).mp hbO
  set θ : X → ℂ := fun x => ((χ x : ℝ) : ℂ) with hθdef
  set H : X → ℂ := fun x => θ x * h0 j₀ x with hHdef
  have hθsupp : tsupport θ ⊆ O := by
    refine subset_trans (closure_mono ?_) (subset_trans (closure_minimal
      (subset_closure) (isClosed_tsupport χ)) hχsupp)
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    apply hy
    show ((χ y : ℝ) : ℂ) = 0
    rw [hc, Complex.ofReal_zero]
  have hHsuppθ : tsupport H ⊆ tsupport θ := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    apply hy
    show θ y * h0 j₀ y = 0
    rw [hc, zero_mul]
  have hHsupp : tsupport H ⊆ (𝔇.U j₀ : Set X) :=
    (hHsuppθ.trans hθsupp).trans Set.inter_subset_left
  have hθ1 : ∀ᶠ y in 𝓝 b, θ y = 1 := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    show ((χ y : ℝ) : ℂ) = 1
    rw [show χ y = 1 from hy, Complex.ofReal_one]
  have hHev : H =ᶠ[𝓝 b] h0 j₀ := by
    filter_upwards [hθ1] with y hy
    show θ y * h0 j₀ y = h0 j₀ y
    rw [hy, one_mul]
  have hθsm : ∀ x : X, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) θ x := by
    intro x
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (fun y => (χ y : ℝ)) x := χ.contMDiffAt
    exact (Complex.ofRealCLM.contMDiff.contMDiffAt).comp x h1
  have hHsm : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x := by
    intro x hxb
    by_cases hxθ : x ∈ tsupport θ
    · have hxO : x ∈ O := hθsupp hxθ
      exact (hθsm x).mul (h0sm j₀ x hxO.1 (hnotpos x hxb hxO.2))
    · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport θ).isOpen_compl.mem_nhds hxθ] with y hy
      show H y = 0
      have hθ0 : θ y = 0 := image_eq_zero_of_notMem_tsupport hy
      show θ y * h0 j₀ y = 0
      rw [hθ0, zero_mul]
  -- the per-star analytic extension of `h0 i − H` across `b`
  have hQ : ∀ i : 𝔇.toFiniteCover.ι, ∃ q : ℂ → ℂ, b ∈ (𝔇.U i : Set X) →
      AnalyticAt ℂ q (βpt b) ∧
      ((fun x => h0 i x - H x) ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝[≠] (βpt b)] q := by
    intro i
    by_cases hi : b ∈ (𝔇.U i : Set X)
    · obtain ⟨q, hq, hqe⟩ := dd.exists_analyticAt_cupRep_sub hn hnE hi hb
      refine ⟨q, fun _ => ⟨hq, ?_⟩⟩
      have hXev : (fun x => h0 i x - H x) =ᶠ[𝓝[≠] b]
          fun x => Gext ((dd.toTestCocycleData hi).cupRep (f : MeromorphicFunction X)) x
            - Gext ((dd.toTestCocycleData hb).cupRep (f : MeromorphicFunction X)) x := by
        have h1 := dd.vanishFn_eventuallyEq_Gext_cupRep hn hm hi hF0
        have h2 := dd.vanishFn_eventuallyEq_Gext_cupRep hn hm hb hF0
        filter_upwards [h1, h2, eventually_nhdsWithin_of_eventually_nhds hHev]
          with y hy1 hy2 hy3
        show h0 i y - H y = _
        rw [hy3, hh0def, hy1, hy2]
      exact (read_eventuallyEq_of_eventuallyEq_nhdsNE hXev).trans hqe
    · exact ⟨0, fun h => absurd h hi⟩
  choose qf hqf using hQ
  -- W4: the repaired presentation
  set ht : 𝔇.toFiniteCover.ι → X → ℂ :=
    fun i => repairAtX b (fun x => h0 i x - H x) with htdef
  have htread : ∀ i, ∀ hi : b ∈ (𝔇.U i : Set X),
      (ht i ∘ (chartAt (H := ℂ) b).symm) =ᶠ[𝓝 (βpt b)] qf i := fun i hi =>
    repairAtX_read_eventuallyEq (hqf i hi).1 (hqf i hi).2
  have htsmooth_b : ∀ i, b ∈ (𝔇.U i : Set X) →
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (ht i) b := by
    intro i hi
    refine contMDiffAt_real_of_chart_analyticAt ?_
    exact ((hqf i hi).1).congr (htread i hi).symm
  have htval : ∀ i, ∀ hi : b ∈ (𝔇.U i : Set X), ht i b = qf i (βpt b) := by
    intro i hi
    have h1 := (htread i hi).self_of_nhds
    rwa [Function.comp_apply, (chartAt (H := ℂ) b).left_inv (mem_chart_source ℂ b)] at h1
  have httend : ∀ i, ∀ _ : b ∈ (𝔇.U i : Set X),
      Tendsto (fun x => h0 i x - H x) (𝓝[≠] b) (𝓝 (qf i (βpt b))) := fun i hi =>
    tendsto_of_read_extension (hqf i hi).1 (hqf i hi).2
  -- engine hypothesis: smoothness off the K-points
  have hsm : SmoothOnSetsOff 𝔇 ((posSupp K : Finset X) : Set X) ht := by
    intro i x hx hxS
    by_cases hxb : x = b
    · subst hxb
      exact htsmooth_b i hx
    · have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => h0 i y - H y) x :=
        (h0sm i x hx (hnotpos x hxb hxS)).sub (hHsm x hxb)
      exact h1.congr_of_eventuallyEq (repairAtX_eventuallyEq_off hxb)
  -- engine hypothesis: the coboundary presentation
  have hδ : IsCoboundaryOn 𝔇 (cocycleFn 𝔇 hsep z) ht := by
    intro i j x hx
    by_cases hij : i = j
    · subst hij
      rw [cocycleFn_diag]
      simp
    by_cases hxb : x = b
    · have hbx : b = x := hxb.symm
      subst hbx
      have hi : b ∈ (𝔇.U i : Set X) := hx.1
      have hj : b ∈ (𝔇.U j : Set X) := hx.2
      have hev : cocycleFn 𝔇 hsep z i j =ᶠ[𝓝[≠] b]
          fun y => (h0 j y - H y) - (h0 i y - H y) := by
        rw [EventuallyEq, eventually_nhdsWithin_iff]
        filter_upwards [(𝔇.U i ⊓ 𝔇.U j : Opens X).isOpen.mem_nhds hx] with y hy hyb
        have hyb' : y ≠ b := by simpa using hyb
        have hK'y : (K + Finsupp.single b 1 : Divisor X) y ≤ 0 := by
          rw [Finsupp.add_apply, show (Finsupp.single b 1 : Divisor X) y = 0 from
            Finsupp.single_eq_of_ne hyb', add_zero]
          exact hsep i j hij y hy
        have h1 := cocycleFn_eq_vanishFn_sub_at hsep z hF0 hcb hy hK'y
        show cocycleFn 𝔇 hsep z i j y = (h0 j y - H y) - (h0 i y - H y)
        rw [h1, hh0def]
        ring
      have ht1 : Tendsto (cocycleFn 𝔇 hsep z i j) (𝓝[≠] b)
          (𝓝 (cocycleFn 𝔇 hsep z i j b)) :=
        (continuousAt_cocycleFn 𝔇 hsep z hx).tendsto.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (cocycleFn 𝔇 hsep z i j) (𝓝[≠] b)
          (𝓝 (qf j (βpt b) - qf i (βpt b))) := by
        refine Tendsto.congr' hev.symm ?_
        exact (httend j hj).sub (httend i hi)
      rw [tendsto_nhds_unique ht1 ht2, htval i hi, htval j hj]
    · have hK'x : (K + Finsupp.single b 1 : Divisor X) x ≤ 0 := by
        rw [Finsupp.add_apply, show (Finsupp.single b 1 : Divisor X) x = 0 from
          Finsupp.single_eq_of_ne hxb, add_zero]
        exact hsep i j hij x hx
      have h1 := cocycleFn_eq_vanishFn_sub_at hsep z hF0 hcb hx hK'x
      have h2 : ∀ k : 𝔇.toFiniteCover.ι, ht k x = h0 k x - H x := fun k =>
        repairAtX_apply_ne hxb
      rw [h1, h2 i, h2 j, hh0def]
      ring
  -- engine hypothesis: slot-product extension at the unmarked K-points
  have hext : ∀ a ∈ posSupp K, ∀ i₀, MLIsolated 𝔇 i₀ a →
      SlotProductExtendsAt 𝔇 ht g i₀ a := by
    intro a haS i₀ hiso
    have hab : a ≠ b := fun hc => hbS (hc ▸ haS)
    have haK' : 0 < (K + Finsupp.single b 1 : Divisor X) a := by
      rw [Finsupp.add_apply, show (Finsupp.single b 1 : Divisor X) a = 0 from
        Finsupp.single_eq_of_ne hab, add_zero]
      exact mem_posSupp_iff.mp haS
    obtain ⟨u, huan, hu0, hgv⟩ := hexact a i₀ hiso.1
    have hgv' : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i₀ a), g i₀ ζ
        = (ζ - chartMap 𝔇 i₀ a) ^ ((K + Finsupp.single b 1 : Divisor X) a).toNat * u ζ := by
      rw [show ((K + Finsupp.single b 1 : Divisor X) a).toNat = (K a).toNat from by
        rw [Finsupp.add_apply, show (Finsupp.single b 1 : Divisor X) a = 0 from
          Finsupp.single_eq_of_ne hab, add_zero]]
      exact hgv
    obtain ⟨q', hq', hev'⟩ := slotProductExtendsAt_vanishFn hF0 hg haK' hiso huan hgv'
    refine ⟨q', hq', ?_⟩
    have haN : a ∈ (tsupport θ)ᶜ ∩ ({b}ᶜ : Set X) :=
      ⟨fun hc => (hθsupp hc).2 (by simpa using haS), by simpa using hab⟩
    have hNopen : IsOpen ((tsupport θ)ᶜ ∩ ({b}ᶜ : Set X)) :=
      (isClosed_tsupport θ).isOpen_compl.inter isOpen_compl_singleton
    have hhteq : ∀ y ∈ (tsupport θ)ᶜ ∩ ({b}ᶜ : Set X), ht i₀ y = h0 i₀ y := by
      intro y hy
      have hyb : y ≠ b := by simpa using hy.2
      show repairAtX b (fun x => h0 i₀ x - H x) y = h0 i₀ y
      rw [repairAtX_apply_ne hyb]
      show h0 i₀ y - H y = h0 i₀ y
      have hθ0 : θ y = 0 := image_eq_zero_of_notMem_tsupport hy.1
      show h0 i₀ y - θ y * h0 j₀ y = h0 i₀ y
      rw [hθ0, zero_mul, sub_zero]
    have hsrc : a ∈ (chartAt ℂ (𝔇.center i₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
    have hcont : ContinuousAt (chartAt ℂ (𝔇.center i₀)).symm (chartMap 𝔇 i₀ a) :=
      (chartAt ℂ (𝔇.center i₀)).continuousAt_symm
        ((chartAt ℂ (𝔇.center i₀)).map_source hsrc)
    have hli : (chartAt ℂ (𝔇.center i₀)).symm (chartMap 𝔇 i₀ a) = a :=
      (chartAt ℂ (𝔇.center i₀)).left_inv hsrc
    have hmemN : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i₀ a),
        (chartAt ℂ (𝔇.center i₀)).symm ζ ∈ (tsupport θ)ᶜ ∩ ({b}ᶜ : Set X) := by
      refine hcont.preimage_mem_nhds ?_
      rw [hli]
      exact hNopen.mem_nhds haN
    refine Filter.EventuallyEq.trans ?_ hev'
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hmemN] with ζ hζ
    show ht i₀ ((chartAt ℂ (𝔇.center i₀)).symm ζ) * g i₀ ζ
      = h0 i₀ ((chartAt ℂ (𝔇.center i₀)).symm ζ) * g i₀ ζ
    rw [hhteq _ hζ]
  -- engine hypothesis: punctured holomorphy of the `H`-read near the marked point
  have hH0' : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x) := by
    obtain ⟨V₁, hV₁sub, hV₁open, hbV₁⟩ := eventually_nhds_iff.mp hHev
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hV₁open.mem_nhds hbV₁, (𝔇.U j₀).isOpen.mem_nhds hb,
      (posSupp K).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hbS)]
      with x hx1 hx2 hx3 hxb
    have hxb' : x ≠ b := by simpa using hxb
    have hsrc : x ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hx2
    have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ x) :=
      (chartAt ℂ (𝔇.center j₀)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j₀)).map_source hsrc)
    have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ x) = x :=
      (chartAt ℂ (𝔇.center j₀)).left_inv hsrc
    have hev2 : (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ))
        =ᶠ[𝓝 (chartMap 𝔇 j₀ x)]
          fun ζ => h0 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) := by
      have hmem : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ x),
          (chartAt ℂ (𝔇.center j₀)).symm ζ ∈ V₁ := by
        refine hcont.preimage_mem_nhds ?_
        rw [hli]
        exact hV₁open.mem_nhds hx1
      filter_upwards [hmem] with ζ hζ
      exact hV₁sub _ hζ
    exact (h0hol j₀ x hx2 (hnotpos x hxb' (by simpa using hx3))).congr_of_eventuallyEq hev2
  -- engine hypothesis: holomorphy of the corrected presentation off `S ∪ {b}`
  have hhol' : ∀ i, ∀ x ∈ (𝔇.U i : Set X), x ∉ ((posSupp K : Finset X) : Set X) → x ≠ b →
      DifferentiableAt ℂ (fun ζ => ht i ((chartAt ℂ (𝔇.center i)).symm ζ)
        + H ((chartAt ℂ (𝔇.center i)).symm ζ)) (chartMap 𝔇 i x) := by
    intro i x hx hxS hxb
    have heqN : ∀ y : X, y ≠ b → ht i y + H y = h0 i y := by
      intro y hyb
      show repairAtX b (fun w => h0 i w - H w) y + H y = h0 i y
      rw [repairAtX_apply_ne hyb]
      ring
    have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
    have hcont : ContinuousAt (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) :=
      (chartAt ℂ (𝔇.center i)).continuousAt_symm ((chartAt ℂ (𝔇.center i)).map_source hsrc)
    have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
      (chartAt ℂ (𝔇.center i)).left_inv hsrc
    have hev2 : (fun ζ => ht i ((chartAt ℂ (𝔇.center i)).symm ζ)
          + H ((chartAt ℂ (𝔇.center i)).symm ζ))
        =ᶠ[𝓝 (chartMap 𝔇 i x)] fun ζ => h0 i ((chartAt ℂ (𝔇.center i)).symm ζ) := by
      have hmem : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i x),
          (chartAt ℂ (𝔇.center i)).symm ζ ∈ ({b}ᶜ : Set X) := by
        refine hcont.preimage_mem_nhds ?_
        rw [hli]
        exact isOpen_compl_singleton.mem_nhds (by simpa using hxb)
      filter_upwards [hmem] with ζ hζ
      exact heqN _ (by simpa using hζ)
    exact (h0hol i x hx (hnotpos x hxb hxS)).congr_of_eventuallyEq hev2
  -- the marked simple pole, transferred to `H`
  obtain ⟨r, hr0, hpole⟩ := (dd.toTestCocycleData hb).exists_slotProductSimplePoleAt
    hn hm hKb0 hg hexact hF0 (dd.cup_component_eq hb)
  obtain ⟨q, hqan, hpe0⟩ := hpole
  have hpe : (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ b)]
        fun ζ => r * (ζ - chartMap 𝔇 j₀ b)⁻¹ + q ζ := by
    refine Filter.EventuallyEq.trans ?_ hpe0
    obtain ⟨V₁, hV₁sub, hV₁open, hbV₁⟩ := eventually_nhds_iff.mp hHev
    have hsrc : b ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hb
    have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ b) :=
      (chartAt ℂ (𝔇.center j₀)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j₀)).map_source hsrc)
    have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ b) = b :=
      (chartAt ℂ (𝔇.center j₀)).left_inv hsrc
    have hmem : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ b),
        (chartAt ℂ (𝔇.center j₀)).symm ζ ∈ V₁ := by
      refine hcont.preimage_mem_nhds ?_
      rw [hli]
      exact hV₁open.mem_nhds hbV₁
    refine Filter.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds hmem) fun ζ hζ => ?_
    show H ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ
      = h0 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ
    rw [hV₁sub _ hζ]
  -- the W1 engine evaluation
  have heval : resFunctional 𝔇 (⟨glueCoeff 𝔇 (cocycleFn 𝔇 hsep z) g,
      glueCoeff_cocycleFn_mem 𝔇 hsep z hg⟩ : oneOneCoeff 𝔇) = -r :=
    resFunctional_eq_neg_residue_of_global_correction
      (S := posSupp K) (w := cocycleFn 𝔇 hsep z) (H := H) (b := b)
      _ rfl hg hSiso hsm hδ hext hb hHsupp hHsm hH0' hhol' hqan hpe
  rw [resCocycle_apply, heval]
  exact neg_ne_zero.mpr hr0

/-! ## Part 5 — W5: the unconditional assembly -/

/-- **THE UNCONDITIONAL §17.7 HEADLINE — `UnwindRegularity` is a THEOREM for the concrete
fine-sheaf residue at EVERY level `D`**, with no `BadPointsIsolated` discipline: at a forced
bad point, either the point is cover-isolated (the proven `SerreUnwindDetect` engine), or
pole separation forces `K b = 0` (D2) and the deep-matching test cocycle feeds the
global-correction engine (W1–W4).  Forster (GTM 81) Lemma 17.7, unconditional form. -/
theorem unwindRegularity_concrete (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) (hwitness : ExactOrderWitness 𝔇)
    (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X) :
    ((cousinResidueData_of_witnessR hsep g hg (SlotMatchesK_of_exact hexact)
      hwit).toGlobalResidue).UnwindRegularity D := by
  classical
  refine GlobalResidue.unwindRegularity_of_detects _ D ?_
  intro E hED v hno
  obtain ⟨fE, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨b, n, hn, hge, hlt⟩ := exists_bad_point hED fE hno
  by_cases hiso : ∃ j₀, MLIsolated 𝔇 j₀ b
  · -- the cover-isolated branch: the proven marked engine
    obtain ⟨j₀, hbiso⟩ := hiso
    have hb : b ∈ (𝔇.U j₀ : Set X) := hbiso.1
    set m : ℤ := n + K b with hmdef
    have hmE : E b ≤ m := by
      have := hKeff b
      omega
    have hmD : m + 1 ≤ D b := by omega
    obtain ⟨td⟩ := TestCocycleData.exists_of_witness hwitness hb hmE
    refine ⟨Submodule.Quotient.mk (td.cocycle hbiso),
      td.h1InclMono_cocycle_eq_zero hbiso hED hmD, ?_⟩
    rw [GlobalResidue.pairing_apply, cup_mk, cupH1_mk]
    exact resCocycle_cup_testCocycle_ne_zero hsep hg hexact td hbiso (hKeff b) fE hn hmdef
  · -- the non-isolated branch: `K b = 0`, the deep cocycle into the W1 engine
    have hKb : K b = 0 := K_apply_eq_zero_of_not_isolated hsep hKeff hiso
    obtain ⟨j₀, hb⟩ := FiniteCover.exists_cover_index 𝔇.toFiniteCover b
    set m : ℤ := n + K b with hmdef
    have hmE : E b ≤ m := by
      have := hKeff b
      omega
    have hmD : m + 1 ≤ D b := by omega
    obtain ⟨dd⟩ := DeepTestData.exists_of_witness (E := E) (m := m) hwitness hb hmE
    refine ⟨Submodule.Quotient.mk dd.cocycle,
      dd.h1InclMono_cocycle_eq_zero hED hmD, ?_⟩
    rw [GlobalResidue.pairing_apply, cup_mk, cupH1_mk]
    exact resCocycle_cup_deepTestCocycle_ne_zero hsep hg hexact dd hb hKb fE hn hmdef

/-- **`CechTailComparison` is a THEOREM for the concrete fine-sheaf residue at EVERY `D`** —
the unconditional Čech↔tail dictionary (`docs/planning/DICT_ROUTE.md`, W5): the keystone
comparison law with NO isolation hypothesis. -/
theorem cechTailComparison_concrete (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) (hwitness : ExactOrderWitness 𝔇)
    (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X) :
    CechTailComparison 𝔇 g ((cousinResidueData_of_witnessR hsep g hg
      (SlotMatchesK_of_exact hexact) hwit).toGlobalResidue) D :=
  cechTailComparison_of_unwindRegularity hexact hKeff _
    (unwindRegularity_concrete hsep hg hexact hwit hwitness hKeff D)

/-- **§17.9 surjectivity for the concrete fine-sheaf residue, unconditional in `D`**: the
assembled Serre residue pairing is surjective at every level, with the dictionary input
supplied by `cechTailComparison_concrete`. -/
theorem pairing_surjective_concrete (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) (hwitness : ExactOrderWitness 𝔇)
    (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X) (P : X)
    (hR : 𝔇.toFiniteCover.LocallyRealizable) :
    Function.Surjective (((cousinResidueData_of_witnessR hsep g hg
      (SlotMatchesK_of_exact hexact) hwit).toGlobalResidue).toSerreResidueRealization.pairing
        D) :=
  pairing_surjective_of_cechTailComparison hexact hKeff _ D P hR
    (cechTailComparison_concrete hsep hg hexact hwit hwitness hKeff D)

end Engine

end Dolbeault

end Jacobians

end
