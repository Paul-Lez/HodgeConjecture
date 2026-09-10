/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailFrame
import KirovDolbeault.Dolbeault.SerreUnwindDetect

/-!
# Miranda Lemma VI.3.6 — pole-bound regularity via the single-monomial tail witness (rung 2)

The tail-frame replacement of the §17.7 pole-bound regularity (`GlobalResidue.UnwindRegularity`,
`SerreUnwind.lean`): **a section pairing to zero against all Laurent tails of the gap range
`[E, D)` satisfies the coarser pole bound `D`** — with the regularity witness a SINGLE-MONOMIAL
Laurent tail, evaluated by pure coefficient algebra (`laurentCoeff_eq_zero_iff`).  No cover, no
isolated points, no Čech cocycle, no integration: the two walls of the Čech-side discharge
(`docs/planning/UNWIND_BLOCKER.md` — the forced NON-isolated bad point, and the
`E`-of-arbitrary-sign level bookkeeping) never arise, because

* the "bad point evaluation" is, in the tail frame, *by definition* a Laurent-coefficient read
  (`tailCoeff_leading_ne_zero` — the single monomial pairs `f` to its nonzero leading
  coefficient), and
* "tail membership at negative divisor entries" is an order window on coefficients, not
  holomorphy-with-zeros on cover overlaps.

## Statements

* `meromorphicOrderAt_ge_of_gap_vanish` — the one-variable engine: vanishing coefficients on
  `[lo, hi)` upgrade `ord ≥ lo` to `ord ≥ hi` (downward induction on the window, each step =
  `laurentCoeff_eq_zero_iff`).
* `mem_linearSystem_of_tailCoeff_gap_vanish` — **Miranda VI.3.6, coefficient form**:
  `f ∈ L(K−E)` with all gap coefficients zero lies in `L(K−D)`.
* `tailRegularity_lSysInclMono` — the same, **stated in the exact shape the §17.7/§17.9 chain
  consumes** (`∃ u : L(K−D)-class, lSysInclMono u = [f]`, the conclusion of
  `GlobalResidue.UnwindRegularity`).  The *hypothesis* differs: tail-pairing vanishing replaces
  the Čech-functional factorization `ι_E(v) = λ ∘ i_{E→D}`.  Deriving the factorization ⟹
  tail-vanishing implication for the CONCRETE Čech residue is exactly the Čech↔tail pairing
  comparison — the remaining bridge, recorded in `docs/planning/TAIL_BLOCKER.md`.  On the
  Miranda route the chain is instead re-pointed at the tail pairing itself, where the
  hypothesis is native.
* `mem_linearSystem_of_tailPairingSlot_gap_vanish` — **Miranda VI.3.6, pair frame**: the same
  upgrade with the pairing taken against the `dz`-slot coefficients of the canonical form
  (`SlotExactK`, `K = div ω₀`), i.e. against tails of the FORM pairing `Res(f·t·ω₀)` — the
  exact bookkeeping of the marked-divisor engine (`SerreUnwindDetect`, orders
  `m = k + K b`, slot order exactly `K b`).

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI Lemma 3.6 (the
Serre-duality pole-bound lemma); Forster (GTM 81) Lemma 17.7 for the Čech-side counterpart.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Module
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

/-! ## Part 0 — the one-variable gap-induction engine -/

/-- One `WithTop ℤ` upgrade step: strict `l < ord` gives `l + 1 ≤ ord`. -/
private theorem add_one_le_of_lt {l : ℤ} {o : WithTop ℤ} (hl : (l : WithTop ℤ) < o) :
    ((l + 1 : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => exact le_top
  | coe v =>
    have hv : l < v := by exact_mod_cast hl
    exact_mod_cast hv

/-- **The gap-induction engine** (one variable): if `F` is meromorphic at `c` with `ord ≥ lo`
and ALL Laurent coefficients in the window `[lo, hi)` vanish, then `ord ≥ hi`.  Downward
induction on the window; each step is the kernel law `laurentCoeff_eq_zero_iff`. -/
theorem meromorphicOrderAt_ge_of_gap_vanish {F : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) {lo hi : ℤ}
    (hlo : (lo : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hvan : ∀ k, lo ≤ k → k < hi → laurentCoeff k F c = 0) :
    (hi : WithTop ℤ) ≤ meromorphicOrderAt F c := by
  suffices H : ∀ (n : ℕ) (l : ℤ), hi - l ≤ (n : ℤ) →
      (l : WithTop ℤ) ≤ meromorphicOrderAt F c →
      (∀ k, l ≤ k → k < hi → laurentCoeff k F c = 0) →
      (hi : WithTop ℤ) ≤ meromorphicOrderAt F c by
    exact H (hi - lo).toNat lo (Int.self_le_toNat _) hlo hvan
  intro n
  induction n with
  | zero =>
    intro l hn hl _
    have hle : hi ≤ l := by omega
    exact le_trans (by exact_mod_cast hle) hl
  | succ n ih =>
    intro l hn hl hv
    by_cases hcase : hi ≤ l
    · exact le_trans (by exact_mod_cast hcase) hl
    have hcase' : l < hi := lt_of_not_ge hcase
    -- the coefficient at the window bottom vanishes, so the order strictly improves
    have hstep : (l : WithTop ℤ) < meromorphicOrderAt F c :=
      (laurentCoeff_eq_zero_iff hF hl).mp (hv l le_rfl hcase')
    exact ih (l + 1) (by omega) (add_one_le_of_lt hstep)
      (fun k hk1 hk2 => hv k (by omega) hk2)

/-! ## Part 1 — Miranda VI.3.6, coefficient form, and the §17.9-shaped statement -/

/-- The divisor-coefficient unfolding `−((K−D) b) = D b − K b` (cf. `exists_bad_point`). -/
private theorem neg_sub_apply (K D : Divisor X) (b : X) :
    (-((K - D : Divisor X) b) : ℤ) = D b - K b := by
  rw [Finsupp.sub_apply]
  ring

/-- **Miranda Lemma VI.3.6, coefficient form**: a function `f ∈ L(K−E)` whose tail
coefficients vanish on the whole gap window `[E b − K b, D b − K b)` at every point satisfies
the coarser bound `f ∈ L(K−D)` (`E ≤ D`).  Pure coefficient algebra; contrast with the
Čech-side `UnwindRegularity`, whose discharge needs the non-isolated marked-point integral
evaluation (`docs/planning/UNWIND_BLOCKER.md`). -/
theorem mem_linearSystem_of_tailCoeff_gap_vanish {K E D : Divisor X}
    {f : MeromorphicFunction X} (hfE : f ∈ linearSystem (X := X) (K - E))
    (hvan : ∀ (b : X) (k : ℤ), E b - K b ≤ k → k < D b - K b → f.tailCoeff b k = 0) :
    f ∈ linearSystem (X := X) (K - D) := by
  intro b
  have e1 : (-((K - D : Divisor X) b) : WithTop ℤ)
      = ((-((K - D : Divisor X) b) : ℤ) : WithTop ℤ) := rfl
  rw [e1, neg_sub_apply]
  have hlo : ((E b - K b : ℤ) : WithTop ℤ) ≤ f.orderW b := by
    have h1 := hfE b
    have e2 : (-((K - E : Divisor X) b) : WithTop ℤ)
        = ((-((K - E : Divisor X) b) : ℤ) : WithTop ℤ) := rfl
    rw [e2, neg_sub_apply] at h1
    exact h1
  exact meromorphicOrderAt_ge_of_gap_vanish (f.meromorphic b) hlo (hvan b)

/-- **Miranda VI.3.6 in the shape the §17.7/§17.9 chain consumes** — the conclusion of
`GlobalResidue.UnwindRegularity`, with the Čech-functional factorization hypothesis replaced
by tail-pairing vanishing on the gap range.  UNCONDITIONAL: no cover, no isolation discipline,
no residue integral.  (The class-level statement: tail coefficients are representative-
independent by `tailCoeff_eq_of_sub_germZero`.) -/
theorem tailRegularity_lSysInclMono {K E D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (fE : ↥(linearSystem (X := X) (K - E)))
    (hvan : ∀ (b : X) (k : ℤ), E b - K b ≤ k → k < D b - K b →
      (fE : MeromorphicFunction X).tailCoeff b k = 0) :
    ∃ u : lSysModule (X := X) (K - D),
      lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk fE :=
  (exists_lSysInclMono_eq_iff hED fE).mpr
    (mem_linearSystem_of_tailCoeff_gap_vanish fE.2 hvan)

/-! ## Part 2 — the centre-chart read of a global meromorphic function

Public counterpart of the (private) `centerRead_data` of `SerreUnwindDetect.lean`, specialized
to `MeromorphicFunction`: the centre-chart read at a cover point is meromorphic with order
EXACTLY `orderW` (the two chart reads differ by an analytic transition with nonvanishing
derivative). -/

/-- Some cover set contains any given point (`⨆ U i = ⊤`). -/
theorem FiniteCover.exists_cover_index (𝔘 : FiniteCover X) (b : X) : ∃ j, b ∈ 𝔘.U j := by
  have hb : b ∈ ((⊤ : Opens X) : Set X) := trivial
  rw [← 𝔘.covers] at hb
  exact (Opens.mem_iSup (x := b)).mp hb

open FineResidue in
/-- **Centre-chart read of `f` at a cover point**: meromorphy and the exact order transfer
`ord_{chartMap j b}(f ∘ (chart centre j)⁻¹) = orderW f b`. -/
theorem MeromorphicFunction.meromorphicAt_centerRead_and_order {𝔇 : ChartDiskCover X}
    {j : 𝔇.toFiniteCover.ι} {b : X} (hb : b ∈ (𝔇.U j : Set X)) (f : MeromorphicFunction X) :
    MeromorphicAt (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j b) ∧
      meromorphicOrderAt (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ))
        (chartMap 𝔇 j b) = f.orderW b := by
  have hbsrc : b ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hb
  have hbb : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  set σ : ℂ → ℂ := (chartAt (H := ℂ) b) ∘ (chartAt ℂ (𝔇.center j)).symm with hσdef
  have hσan : AnalyticAt ℂ σ (chartMap 𝔇 j b) :=
    transition_analyticAt_of_mem (y := 𝔇.center j) (z := b) hbsrc hbb
  have hσd : deriv σ (chartMap 𝔇 j b) ≠ 0 :=
    transition_deriv_ne_zero (y := 𝔇.center j) (z := b) hbsrc hbb
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j b) = b :=
    (chartAt ℂ (𝔇.center j)).left_inv hbsrc
  have hσpt : σ (chartMap 𝔇 j b) = (chartAt (H := ℂ) b) b := by
    simp only [hσdef, Function.comp_apply, hli]
  have hzt : chartMap 𝔇 j b ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hbsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j b) :=
    (chartAt ℂ (𝔇.center j)).continuousAt_symm hzt
  have hmem : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j b),
      (chartAt ℂ (𝔇.center j)).symm ζ ∈ (chartAt (H := ℂ) b).source := by
    refine hcont.preimage_mem_nhds ?_
    rw [hli]
    exact (chartAt (H := ℂ) b).open_source.mem_nhds hbb
  have hev : (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ))
      =ᶠ[𝓝 (chartMap 𝔇 j b)] ((f.toFun ∘ (chartAt (H := ℂ) b).symm) ∘ σ) := by
    filter_upwards [hmem] with ζ hζ
    show f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ)
        = f.toFun ((chartAt (H := ℂ) b).symm (σ ζ))
    simp only [hσdef, Function.comp_apply]
    rw [(chartAt (H := ℂ) b).left_inv hζ]
  have hfσ : MeromorphicAt ((f.toFun ∘ (chartAt (H := ℂ) b).symm) ∘ σ) (chartMap 𝔇 j b) := by
    refine MeromorphicAt.comp_analyticAt ?_ hσan
    rw [hσpt]
    exact f.meromorphic b
  constructor
  · exact hfσ.congr (hev.filter_mono nhdsWithin_le_nhds).symm
  · rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_comp_of_deriv_ne_zero hσan hσd, hσpt]
    rfl

/-! ## Part 3 — Miranda VI.3.6 in the pair frame (tails against the `dz`-slot coefficients) -/

open FineResidue

variable {𝔇 : ChartDiskCover X}

/-- **The slot tail pairing** `⟨f, z^{−1−m}·dz at b⟩`: the order-`m` Laurent coefficient of
the centre-chart slot product `f̂ · g j` at the marked coordinate — by `laurentCoeff_shift`,
the *residue* of the slot product against the Miranda monomial tail `(ζ−α)^{−1−m}`.  This is
the residue pairing of `f·ω₀` against single-monomial Laurent tails, in pure coefficient
algebra (the marked-divisor bookkeeping of `SerreUnwindDetect`: function order `k`, slot order
exactly `K b`, pairing index `m = k + K b`). -/
noncomputable def tailPairingSlot (𝔇 : ChartDiskCover X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j : 𝔇.toFiniteCover.ι) (b : X) (m : ℤ) (f : MeromorphicFunction X) : ℂ :=
  laurentCoeff m (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
    (chartMap 𝔇 j b)

/-- The slot pairing is the residue of the slot product against the monomial tail
`(ζ−α)^{−1−m}` (the pairing-form reading). -/
theorem tailPairingSlot_eq_residue_monomial (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j : 𝔇.toFiniteCover.ι) (b : X) (m : ℤ) (f : MeromorphicFunction X) :
    tailPairingSlot 𝔇 g j b m f
      = laurentCoeff (-1)
          (fun ζ => (ζ - chartMap 𝔇 j b) ^ (-1 - m)
            * (f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ))
          (chartMap 𝔇 j b) :=
  laurentCoeff_shift m _ _

/-- The `dz`-slot is analytic of order exactly `K b` at the marked coordinate
(`SlotExactK` + `K b ≥ 0`). -/
theorem slot_analyticAt_and_order {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {K : Divisor X}
    (hexact : SlotExactK 𝔇 g K) {j : 𝔇.toFiniteCover.ι} {b : X}
    (hb : b ∈ (𝔇.U j : Set X)) (hKb : 0 ≤ K b) :
    AnalyticAt ℂ (g j) (chartMap 𝔇 j b) ∧
      meromorphicOrderAt (g j) (chartMap 𝔇 j b) = ((K b : ℤ) : WithTop ℤ) := by
  obtain ⟨u, huan, hu0, hgv⟩ := hexact b j hb
  have hRHS : AnalyticAt ℂ (fun ζ => (ζ - chartMap 𝔇 j b) ^ (K b).toNat * u ζ)
      (chartMap 𝔇 j b) := ((analyticAt_id.sub analyticAt_const).pow _).mul huan
  have hgan : AnalyticAt ℂ (g j) (chartMap 𝔇 j b) := by
    refine hRHS.congr ?_
    filter_upwards [hgv] with ζ hζ
    rw [hζ]
  refine ⟨hgan, ?_⟩
  refine (meromorphicOrderAt_eq_int_iff hgan.meromorphicAt).mpr ⟨u, huan, hu0, ?_⟩
  filter_upwards [hgv.filter_mono nhdsWithin_le_nhds] with ζ hζ
  rw [hζ, smul_eq_mul]
  congr 1
  rw [show (ζ - chartMap 𝔇 j b) ^ (K b) = (ζ - chartMap 𝔇 j b) ^ (((K b).toNat : ℤ)) from by
    rw [Int.toNat_of_nonneg hKb], zpow_natCast]

/-- **Miranda VI.3.6, pair frame**: a function `f ∈ L(K−E)` whose slot tail pairings vanish on
the whole gap range `E b ≤ m < D b`, in every cover chart, satisfies the coarser bound
`f ∈ L(K−D)`.  The slot product has order `orderW f + K b` (exact slot order `K b`), so the
gap induction runs directly at the product level and the bound transfers by exact order
subtraction. -/
theorem mem_linearSystem_of_tailPairingSlot_gap_vanish
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {K : Divisor X}
    (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    {E D : Divisor X} {f : MeromorphicFunction X}
    (hfE : f ∈ linearSystem (X := X) (K - E))
    (hvan : ∀ (j : 𝔇.toFiniteCover.ι) (b : X), b ∈ (𝔇.U j : Set X) → ∀ m : ℤ,
      E b ≤ m → m < D b → tailPairingSlot 𝔇 g j b m f = 0) :
    f ∈ linearSystem (X := X) (K - D) := by
  intro b
  have e1 : (-((K - D : Divisor X) b) : WithTop ℤ)
      = ((-((K - D : Divisor X) b) : ℤ) : WithTop ℤ) := rfl
  rw [e1, neg_sub_apply]
  rcases eq_or_ne (f.orderW b) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  -- the cover chart at `b` and the slot product
  obtain ⟨j, hb⟩ := FiniteCover.exists_cover_index 𝔇.toFiniteCover b
  obtain ⟨hread, hordread⟩ := MeromorphicFunction.meromorphicAt_centerRead_and_order hb f
  obtain ⟨hgan, hgord⟩ := slot_analyticAt_and_order hexact hb (hKeff b)
  set H : ℂ → ℂ := fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ with hHdef
  have hHmer : MeromorphicAt H (chartMap 𝔇 j b) := by
    have h := hread.mul hgan.meromorphicAt
    exact h
  have hHord : meromorphicOrderAt H (chartMap 𝔇 j b) = ((n + K b : ℤ) : WithTop ℤ) := by
    rw [show H = (fun ζ => f.toFun ((chartAt ℂ (𝔇.center j)).symm ζ)) * g j from rfl,
      meromorphicOrderAt_mul hread hgan.meromorphicAt, hordread, ← hn, hgord]
    exact_mod_cast (WithTop.coe_add n (K b)).symm
  -- the `L(K−E)` lower bound at the product level: `n + K b ≥ E b`
  have hlo : E b - K b ≤ n := by
    have h1 := hfE b
    have e2 : (-((K - E : Divisor X) b) : WithTop ℤ)
        = ((-((K - E : Divisor X) b) : ℤ) : WithTop ℤ) := rfl
    rw [e2, neg_sub_apply, ← hn] at h1
    exact_mod_cast h1
  have hloH : ((E b : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H (chartMap 𝔇 j b) := by
    rw [hHord]
    exact_mod_cast (by omega : E b ≤ n + K b)
  -- the gap induction at the product level
  have hgap := meromorphicOrderAt_ge_of_gap_vanish hHmer hloH
    (fun m hm1 hm2 => hvan j b hb m hm1 hm2)
  -- subtract the exact slot order
  rw [hHord] at hgap
  have hDb : D b ≤ n + K b := by exact_mod_cast hgap
  rw [← hn]
  exact_mod_cast (by omega : D b - K b ≤ n)

/-- **The pair-frame regularity in §17.9 shape**: the `UnwindRegularity` conclusion
(`∃ u : L(K−D)-class, lSysInclMono u = [f]`) from slot-tail-pairing vanishing on the gap
range.  Unconditional in the cover geometry — compare `unwindRegularity_concrete_of_isolated`
(`SerreUnwindDetect.lean`), which needs the `BadPointsIsolated` discipline that provably fails
for general `D` (`docs/planning/UNWIND_BLOCKER.md`). -/
theorem tailRegularitySlot_lSysInclMono {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {K : Divisor X}
    (hexact : SlotExactK 𝔇 g K) (hKeff : ∀ x, 0 ≤ K x)
    {E D : Divisor X} (hED : ∀ x, E x ≤ D x) (fE : ↥(linearSystem (X := X) (K - E)))
    (hvan : ∀ (j : 𝔇.toFiniteCover.ι) (b : X), b ∈ (𝔇.U j : Set X) → ∀ m : ℤ,
      E b ≤ m → m < D b → tailPairingSlot 𝔇 g j b m (fE : MeromorphicFunction X) = 0) :
    ∃ u : lSysModule (X := X) (K - D),
      lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk fE :=
  (exists_lSysInclMono_eq_iff hED fE).mpr
    (mem_linearSystem_of_tailPairingSlot_gap_vanish hexact hKeff fE.2 hvan)

end Dolbeault

end Jacobians

end
