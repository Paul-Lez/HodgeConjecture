/-
  Dolbeault ladder — the LOCAL REALIZATION analytic kernel (Mittag–Leffler / Cousin-I).

  This is the genuine analytic content that the χ-additivity skyscraper LES
  (`CohomologicalRR.exists_skyscraperLES`) bottoms out in.

  For the skyscraper short exact sequence `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`, the local fact is:
  the order-`k` Laurent coefficient at `P` (where `k = -(D+P)(P) = -(D P) - 1`) gives, for an open
  `W ∋ P`, an isomorphism

      `OmegaDGerm (D + single P 1) W  ⧸  (image of OmegaDGerm D W)  ≅ₗ[ℂ]  ℂ`,

  and `= 0` for `W ∌ P`. The membership characterization is: a germ lies in `OmegaDGerm D` iff its
  order-`k` coefficient vanishes (pole order at `P` is `≤ D(P)`).

  The order-`k` coefficient functional is realised as a genuine LIMIT (the repo's `resAt`/`holoRepr`
  style): for `f` with `ord_P f ≥ k`, the chart pullback `F = f ∘ chart.symm` satisfies that
  `z ↦ (z - c)^(-k) · F(z)` is analytic at `c = chart P`, so its punctured-neighbourhood limit
  exists; that limit is the coefficient.  It is ℂ-linear because each summand's limit exists.

  Explicit witness (surjectivity): the germ of `(chart - chart P)^k` (transported through the
  `↥W`-chart machinery of `CechSection`) realises coefficient `1` with a pole only at `P`; this uses
  the Mathlib explicit order witness `meromorphicOrderAt_zpow_id_sub_const`.

  Everything here is complete.
-/
import KirovDolbeault.Dolbeault.CechSection
import KirovDolbeault.Dolbeault.CechH0

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The order-`k` Laurent coefficient as a limit (one-variable, on `ℂ`)

We first work purely on `ℂ → ℂ`: for `F` meromorphic at `c` with `meromorphicOrderAt F c ≥ k`, the
"de-poled" function `z ↦ (z - c)^{-k} · F(z)` has nonnegative order, hence a punctured-neighbourhood
limit (`tendsto_nhds_of_meromorphicOrderAt_nonneg`).  That limit is the order-`k` coefficient
`laurentCoeff k F c`.  It is ℂ-linear in `F` (limits add and scale) on the subspace `ord ≥ k`. -/

/-- The "de-poled" function `z ↦ (z - c)^{-k} · F(z)` (multiply by `(z-c)^{-k}` to clear a pole of
order `≤ k` at `c`). -/
noncomputable def dePole (k : ℤ) (F : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  fun z => (z - c) ^ (-k) * F z

/-- The order-`k` Laurent coefficient of `F` at `c`: the punctured-neighbourhood limit of the
de-poled function.  When `ord_c F ≥ k` (so the de-pole has nonnegative order) this is the genuine
coefficient `a_k` of `(z-c)^k` in the Laurent expansion; the junk value `0` otherwise. -/
noncomputable def laurentCoeff (k : ℤ) (F : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[≠] c) (dePole k F c)

/-- `(· - c)^{-k}` is meromorphic at `c` (a `zpow` of the analytic `id - const`). -/
theorem meromorphicAt_zpow_sub (k : ℤ) (c : ℂ) :
    MeromorphicAt (fun z => (z - c) ^ (-k)) c := by
  have h1 : MeromorphicAt (fun z : ℂ => z - c) c := by fun_prop
  have := h1.zpow (-k)
  rwa [show ((fun z : ℂ => z - c) ^ (-k)) = (fun z => (z - c) ^ (-k)) from rfl] at this

/-- The order of `(· - c)^{-k}` at `c` is `-k` (Mathlib's explicit witness). -/
theorem meromorphicOrderAt_zpow_sub (k : ℤ) (c : ℂ) :
    meromorphicOrderAt (fun z => (z - c) ^ (-k)) c = (-k : ℤ) := by
  rw [show (fun z => (z - c) ^ (-k)) = ((· - c) ^ (-k) : ℂ → ℂ) from rfl,
    meromorphicOrderAt_zpow_id_sub_const]

/-- The de-pole is meromorphic at `c` when `F` is. -/
theorem meromorphicAt_dePole {k : ℤ} {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c) :
    MeromorphicAt (dePole k F c) c :=
  (meromorphicAt_zpow_sub k c).mul hF

/-- The order of the de-pole is `-k + ord_c F` (additivity of `meromorphicOrderAt` under `mul`). -/
theorem meromorphicOrderAt_dePole {k : ℤ} {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c) :
    meromorphicOrderAt (dePole k F c) c = (-k : ℤ) + meromorphicOrderAt F c := by
  show meromorphicOrderAt (fun z => (z - c) ^ (-k) * F z) c = _
  rw [show (fun z => (z - c) ^ (-k) * F z) = (fun z => (z - c) ^ (-k)) * F from rfl,
    meromorphicOrderAt_mul (meromorphicAt_zpow_sub k c) hF, meromorphicOrderAt_zpow_sub]

/-- **Existence of the coefficient limit.**  If `ord_c F ≥ k` then the de-pole has nonnegative order,
so it tends to the (well-defined) coefficient `laurentCoeff k F c` on the punctured neighbourhood. -/
theorem tendsto_dePole {k : ℤ} {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (hord : (k : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    Tendsto (dePole k F c) (𝓝[≠] c) (𝓝 (laurentCoeff k F c)) := by
  have hmer : MeromorphicAt (dePole k F c) c := meromorphicAt_dePole hF
  have hnn : 0 ≤ meromorphicOrderAt (dePole k F c) c := by
    rw [meromorphicOrderAt_dePole hF]
    have h2 : ((k : ℤ) : WithTop ℤ) + ((-k : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt F c + ((-k : ℤ) : WithTop ℤ) :=
      add_le_add_left hord ((-k : ℤ) : WithTop ℤ)
    have h3 : ((k : ℤ) : WithTop ℤ) + ((-k : ℤ) : WithTop ℤ) = 0 := by
      rw [← WithTop.coe_add]; norm_num
    rw [h3, add_comm] at h2
    exact h2
  obtain ⟨a, ha⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmer hnn
  rw [laurentCoeff, ha.limUnder_eq]
  exact ha

/-- The de-pole distributes over addition (pointwise). -/
theorem dePole_add (k : ℤ) (F G : ℂ → ℂ) (c : ℂ) :
    dePole k (F + G) c = dePole k F c + dePole k G c := by
  funext z; simp only [dePole, Pi.add_apply]; ring

/-- The de-pole commutes with scalar multiplication (pointwise). -/
theorem dePole_smul (k : ℤ) (s : ℂ) (F : ℂ → ℂ) (c : ℂ) :
    dePole k (s • F) c = s • dePole k F c := by
  funext z; simp only [dePole, Pi.smul_apply, smul_eq_mul]; ring

/-- The de-pole depends only on the germ of `F` at `c`. -/
theorem dePole_congr {k : ℤ} {F G : ℂ → ℂ} {c : ℂ} (h : F =ᶠ[𝓝[≠] c] G) :
    dePole k F c =ᶠ[𝓝[≠] c] dePole k G c := by
  filter_upwards [h] with z hz
  simp only [dePole, hz]

/-- **`laurentCoeff` is additive** on functions of order `≥ k`. -/
theorem laurentCoeff_add {k : ℤ} {F G : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hG : MeromorphicAt G c)
    (hordF : (k : WithTop ℤ) ≤ meromorphicOrderAt F c)
    (hordG : (k : WithTop ℤ) ≤ meromorphicOrderAt G c) :
    laurentCoeff k (F + G) c = laurentCoeff k F c + laurentCoeff k G c := by
  have hsum : Tendsto (dePole k (F + G) c) (𝓝[≠] c)
      (𝓝 (laurentCoeff k F c + laurentCoeff k G c)) := by
    rw [dePole_add]
    exact (tendsto_dePole hF hordF).add (tendsto_dePole hG hordG)
  rw [laurentCoeff, hsum.limUnder_eq]

/-- **`laurentCoeff` is ℂ-homogeneous** on functions of order `≥ k`. -/
theorem laurentCoeff_smul {k : ℤ} (s : ℂ) {F : ℂ → ℂ} {c : ℂ}
    (hF : MeromorphicAt F c) (hordF : (k : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    laurentCoeff k (s • F) c = s • laurentCoeff k F c := by
  have hscaled : Tendsto (dePole k (s • F) c) (𝓝[≠] c) (𝓝 (s • laurentCoeff k F c)) := by
    rw [dePole_smul]
    exact (tendsto_dePole hF hordF).const_smul s
  rw [laurentCoeff, hscaled.limUnder_eq]

/-- **`laurentCoeff` depends only on the germ** of `F` at `c`. -/
theorem laurentCoeff_congr {k : ℤ} {F G : ℂ → ℂ} {c : ℂ} (h : F =ᶠ[𝓝[≠] c] G) :
    laurentCoeff k F c = laurentCoeff k G c := by
  rw [laurentCoeff, laurentCoeff, limUnder, limUnder, Filter.map_congr (dePole_congr h)]

/-- **The kernel characterization (one-variable form).**  For `F` of order `≥ k` at `c`, the
order-`k` coefficient vanishes iff the order is *strictly* `> k` (i.e. the pole order is `< k`, so
`F` already lies one order below). The de-pole has order `-k + ord F ≥ 0`, and its limit
(`laurentCoeff`) is `0` iff that order is `> 0` (`tendsto_zero_iff`/`tendsto_ne_zero_iff`). -/
theorem laurentCoeff_eq_zero_iff {k : ℤ} {F : ℂ → ℂ} {c : ℂ} (hF : MeromorphicAt F c)
    (hord : (k : WithTop ℤ) ≤ meromorphicOrderAt F c) :
    laurentCoeff k F c = 0 ↔ (k : WithTop ℤ) < meromorphicOrderAt F c := by
  have hmer : MeromorphicAt (dePole k F c) c := meromorphicAt_dePole hF
  have hord' : meromorphicOrderAt (dePole k F c) c = (-k : ℤ) + meromorphicOrderAt F c :=
    meromorphicOrderAt_dePole hF
  have hnn : 0 ≤ meromorphicOrderAt (dePole k F c) c := by
    rw [hord']
    have h2 : ((k : ℤ) : WithTop ℤ) + ((-k : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt F c + ((-k : ℤ) : WithTop ℤ) :=
      add_le_add_left hord ((-k : ℤ) : WithTop ℤ)
    have h3 : ((k : ℤ) : WithTop ℤ) + ((-k : ℤ) : WithTop ℤ) = 0 := by
      rw [← WithTop.coe_add]; norm_num
    rw [h3, add_comm] at h2; exact h2
  have hL : Tendsto (dePole k F c) (𝓝[≠] c) (𝓝 (laurentCoeff k F c)) := tendsto_dePole hF hord
  -- `laurentCoeff = 0 ↔ ord(dePole) > 0`
  have hiff : laurentCoeff k F c = 0 ↔ 0 < meromorphicOrderAt (dePole k F c) c := by
    constructor
    · intro h0
      rcases hnn.eq_or_lt with heq | hlt
      · exfalso
        obtain ⟨c', hc'ne, hc'tend⟩ :=
          (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hmer).2 heq.symm
        exact hc'ne ((tendsto_nhds_unique hL hc'tend) ▸ h0)
      · exact hlt
    · intro hpos
      exact tendsto_nhds_unique hL (tendsto_zero_of_meromorphicOrderAt_pos hpos)
  rw [hiff, hord']
  -- `0 < -k + ord F ↔ k < ord F`
  cases h : meromorphicOrderAt F c with
  | top => simp
  | coe n =>
    rw [← WithTop.coe_add, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
      WithTop.coe_lt_coe, WithTop.coe_lt_coe]
    omega

/-! ### The explicit witness (one-variable): `F = (· - c)^k` realises coefficient `1` -/

/-- The order of `(· - c)^k` at `c` is `k` (Mathlib's explicit witness, positive power form). -/
theorem meromorphicOrderAt_zpow_self (k : ℤ) (c : ℂ) :
    meromorphicOrderAt (fun z => (z - c) ^ k) c = (k : ℤ) := by
  rw [show (fun z => (z - c) ^ k) = ((· - c) ^ k : ℂ → ℂ) from rfl,
    meromorphicOrderAt_zpow_id_sub_const]

/-- **The witness coefficient is `1`.**  The order-`k` Laurent coefficient of `(· - c)^k` at `c`
is `1`: the de-pole `(z-c)^{-k}·(z-c)^k = (z-c)^0 = 1` off `c`, so its limit is `1`. -/
theorem laurentCoeff_zpow_self (k : ℤ) (c : ℂ) :
    laurentCoeff k (fun z => (z - c) ^ k) c = 1 := by
  have heq : dePole k (fun z => (z - c) ^ k) c =ᶠ[𝓝[≠] c] (fun _ => (1 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    simp only [dePole]
    rw [← zpow_add₀ hzc]; simp
  have ht : Tendsto (dePole k (fun z => (z - c) ^ k) c) (𝓝[≠] c) (𝓝 1) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  rw [laurentCoeff, ht.limUnder_eq]

/-! ### The order-`k` coefficient on the open submanifold `↥W` (in `↥W`'s chart at `P`)

`coeffWFn k Pw f` reads the order-`k` Laurent coefficient of `f : ↥W → ℂ` at the point `Pw : ↥W`,
computed in `↥W`'s own chart (exactly the chart `ordU` uses).  It inherits germ-invariance and — on
the subspace `ordU f Pw ≥ k` — ℂ-linearity from `laurentCoeff`.  The relevant exponent for the
skyscraper SES at `P` with target `𝒪_{D+P}` is `k = -(D P) - 1`. -/

/-- The order-`k` coefficient of `f : ↥W → ℂ` at `Pw : ↥W`, in `↥W`'s chart. -/
noncomputable def coeffWFn {W : Opens X} (k : ℤ) (Pw : W) (f : W → ℂ) : ℂ :=
  laurentCoeff k (f ∘ (chartAt (H := ℂ) Pw).symm) ((chartAt (H := ℂ) Pw) Pw)

/-- The chart pullback `f ∘ (chartAt Pw).symm` is meromorphic at the chart centre, for `f`
meromorphic on `↥W`. -/
theorem meromorphicAt_pullback {W : Opens X} {f : W → ℂ} (hf : IsMeromorphic (W : Type _) f)
    (Pw : W) : MeromorphicAt (f ∘ (chartAt (H := ℂ) Pw).symm) ((chartAt (H := ℂ) Pw) Pw) :=
  hf Pw

/-- The chart-pullback order is exactly `ordU f Pw` (definitional). -/
theorem meromorphicOrderAt_pullback {W : Opens X} (f : W → ℂ) (Pw : W) :
    meromorphicOrderAt (f ∘ (chartAt (H := ℂ) Pw).symm) ((chartAt (H := ℂ) Pw) Pw) = ordU f Pw :=
  rfl

/-- **`coeffWFn` is additive** on `↥W`-functions of order `≥ k` at `Pw`. -/
theorem coeffWFn_add {W : Opens X} {k : ℤ} {Pw : W} {f g : W → ℂ}
    (hf : IsMeromorphic (W : Type _) f) (hg : IsMeromorphic (W : Type _) g)
    (hfo : (k : WithTop ℤ) ≤ ordU f Pw) (hgo : (k : WithTop ℤ) ≤ ordU g Pw) :
    coeffWFn k Pw (f + g) = coeffWFn k Pw f + coeffWFn k Pw g := by
  have hcomp : ((f + g) ∘ (chartAt (H := ℂ) Pw).symm)
      = (f ∘ (chartAt (H := ℂ) Pw).symm) + (g ∘ (chartAt (H := ℂ) Pw).symm) := by
    funext z; simp only [Function.comp_apply, Pi.add_apply]
  simp only [coeffWFn, hcomp]
  exact laurentCoeff_add (meromorphicAt_pullback hf Pw) (meromorphicAt_pullback hg Pw) hfo hgo

/-- **`coeffWFn` is ℂ-homogeneous** on `↥W`-functions of order `≥ k` at `Pw`. -/
theorem coeffWFn_smul {W : Opens X} {k : ℤ} {Pw : W} (s : ℂ) {f : W → ℂ}
    (hf : IsMeromorphic (W : Type _) f) (hfo : (k : WithTop ℤ) ≤ ordU f Pw) :
    coeffWFn k Pw (s • f) = s • coeffWFn k Pw f := by
  have hcomp : ((s • f) ∘ (chartAt (H := ℂ) Pw).symm)
      = s • (f ∘ (chartAt (H := ℂ) Pw).symm) := by
    funext z; simp only [Function.comp_apply, Pi.smul_apply]
  simp only [coeffWFn, hcomp]
  exact laurentCoeff_smul s (meromorphicAt_pullback hf Pw) hfo

/-- **`coeffWFn` depends only on the germ class** (`MGerm`): if two representatives agree off a
discrete set near every point, their coefficients at `Pw` agree (the relevant agreement is on
`𝓝[≠] Pw`, transported to the chart via the repo's `eventually_comp_chart_iff'`). -/
theorem coeffWFn_congr {W : Opens X} {k : ℤ} {Pw : W} {f g : W → ℂ}
    (h : f =ᶠ[𝓝[≠] Pw] g) : coeffWFn k Pw f = coeffWFn k Pw g := by
  refine laurentCoeff_congr ?_
  have hkey := eventually_comp_chart_iff' (f - g) Pw (· = 0)
  have h' : ∀ᶠ z in 𝓝[≠] Pw, (f - g) z = 0 := by
    filter_upwards [h] with z hz; simp only [Pi.sub_apply, sub_eq_zero]; exact hz
  filter_upwards [hkey.2 h'] with w hw
  simp only [Function.comp_apply, Pi.sub_apply, sub_eq_zero] at hw
  exact hw

/-- **The kernel characterization on `↥W`.**  For `f` meromorphic on `↥W` with `ordU f Pw ≥ k`, the
order-`k` coefficient at `Pw` vanishes iff `ordU f Pw > k` (one order lower pole). -/
theorem coeffWFn_eq_zero_iff {W : Opens X} {k : ℤ} {Pw : W} {f : W → ℂ}
    (hf : IsMeromorphic (W : Type _) f) (hord : (k : WithTop ℤ) ≤ ordU f Pw) :
    coeffWFn k Pw f = 0 ↔ (k : WithTop ℤ) < ordU f Pw :=
  laurentCoeff_eq_zero_iff (meromorphicAt_pullback hf Pw) hord

/-! ### The explicit witness on `↥W`: the principal part `(chart − chart(P))^k`

`witnessFn Pw k : ↥W → ℂ` is `w ↦ (chartAt Pw w − chartAt Pw Pw)^k`, the chart-pullback of which is
`(z − c)^k`.  Hence it realises coefficient `1` and has order exactly `k` at `Pw`. -/

/-- The witness section on `↥W`: the `k`-th power of the centred chart coordinate at `Pw`. -/
noncomputable def witnessFn {W : Opens X} (Pw : W) (k : ℤ) : W → ℂ :=
  fun w => ((chartAt (H := ℂ) Pw) w - (chartAt (H := ℂ) Pw) Pw) ^ k

/-- The chart pullback of the witness is exactly `(z − c)^k` on the chart target. -/
theorem witnessFn_pullback_eqOn {W : Opens X} (Pw : W) (k : ℤ) :
    Set.EqOn (witnessFn Pw k ∘ (chartAt (H := ℂ) Pw).symm)
      (fun z => (z - (chartAt (H := ℂ) Pw) Pw) ^ k) (chartAt (H := ℂ) Pw).target := by
  intro z hz
  simp only [witnessFn, Function.comp_apply, (chartAt (H := ℂ) Pw).right_inv hz]

/-- The chart pullback of the witness agrees with `(z − c)^k` near the chart centre `c`. -/
theorem witnessFn_pullback_eventuallyEq {W : Opens X} (Pw : W) (k : ℤ) :
    (witnessFn Pw k ∘ (chartAt (H := ℂ) Pw).symm)
      =ᶠ[𝓝 ((chartAt (H := ℂ) Pw) Pw)] (fun z => (z - (chartAt (H := ℂ) Pw) Pw) ^ k) := by
  have htgt : (chartAt (H := ℂ) Pw).target ∈ 𝓝 ((chartAt (H := ℂ) Pw) Pw) :=
    (chartAt (H := ℂ) Pw).open_target.mem_nhds
      ((chartAt (H := ℂ) Pw).map_source (mem_chart_source ℂ Pw))
  exact Filter.eventuallyEq_of_mem htgt (witnessFn_pullback_eqOn Pw k)

/-- The chart pullback of the witness is meromorphic at the chart centre (it agrees near `c` with
`(z−c)^k`). This is the only meromorphy fact needed for the order/coefficient at `Pw`. -/
theorem witnessFn_meromorphicAt_center {W : Opens X} (Pw : W) (k : ℤ) :
    MeromorphicAt (witnessFn Pw k ∘ (chartAt (H := ℂ) Pw).symm) ((chartAt (H := ℂ) Pw) Pw) := by
  have hev := witnessFn_pullback_eventuallyEq Pw k
  have hmer : MeromorphicAt (fun z => (z - (chartAt (H := ℂ) Pw) Pw) ^ k)
      ((chartAt (H := ℂ) Pw) Pw) := by
    have h1 : MeromorphicAt (fun z : ℂ => z - (chartAt (H := ℂ) Pw) Pw)
        ((chartAt (H := ℂ) Pw) Pw) := by fun_prop
    have := h1.zpow k
    rwa [show ((fun z : ℂ => z - (chartAt (H := ℂ) Pw) Pw) ^ k)
      = (fun z => (z - (chartAt (H := ℂ) Pw) Pw) ^ k) from rfl] at this
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

/-- The order of the witness at `Pw` is exactly `k`. -/
theorem ordU_witnessFn {W : Opens X} (Pw : W) (k : ℤ) :
    ordU (witnessFn Pw k) Pw = (k : ℤ) := by
  rw [ordU, meromorphicOrderAt_congr
    ((witnessFn_pullback_eventuallyEq Pw k).filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_zpow_self]

/-- **The witness coefficient is `1`.**  The order-`k` Laurent coefficient of the witness at `Pw`
equals `1` (its pullback is `(z−c)^k`, whose order-`k` coefficient is `1`). -/
theorem coeffWFn_witnessFn {W : Opens X} (Pw : W) (k : ℤ) :
    coeffWFn k Pw (witnessFn Pw k) = 1 := by
  rw [coeffWFn, laurentCoeff_congr
    ((witnessFn_pullback_eventuallyEq Pw k).filter_mono nhdsWithin_le_nhds),
    laurentCoeff_zpow_self]

/-! ### Order bridges between `𝒪_D` and `𝒪_{D+P}` at `P`

The skyscraper exponent is `k := -(D P) - 1`.  A section of `𝒪_{D+P}` has `ordU ≥ k` at `P`; it lies
in `𝒪_D` iff additionally `ordU ≥ k + 1` there (away from `P` the two order bounds coincide, since
`(D + P)(P') = D(P')` for `P' ≠ P`). -/

section Bridges

variable {W : Opens X} {D : Divisor X} {P : X}

/-- The skyscraper exponent `k = -(D P) - 1 = -(D + single P 1)(P)`. -/
private theorem neg_add_single_self (D : Divisor X) (P : X) :
    (-((D + Finsupp.single P 1 : Divisor X) P) : ℤ) = -(D P) - 1 := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same]; ring

/-- A section of `𝒪_{D+P}` has order `≥ k = -(D P) - 1` at `P` (the membership bound at `P`). -/
theorem ordU_ge_of_mem_add_single {f : W → ℂ} (hP : P ∈ W)
    (hf : f ∈ OmegaD (D + Finsupp.single P 1) W) :
    ((-(D P) - 1 : ℤ) : WithTop ℤ) ≤ ordU f ⟨P, hP⟩ := by
  have h := hf.2 ⟨P, hP⟩
  rw [show ((-(D P) - 1 : ℤ)) = (-((D + Finsupp.single P 1 : Divisor X) P) : ℤ) from
    (neg_add_single_self D P).symm]
  exact_mod_cast h

/-- **Membership reduction.**  For `f ∈ 𝒪_{D+P}(W)`, `f ∈ 𝒪_D(W)` iff its order at `P` is at least
`k + 1 = -(D P)`. Away from `P` the order bounds for `𝒪_D` and `𝒪_{D+P}` coincide. -/
theorem mem_OmegaD_iff_ordU_at_P {f : W → ℂ} (hP : P ∈ W)
    (hf : f ∈ OmegaD (D + Finsupp.single P 1) W) :
    f ∈ OmegaD D W ↔ ((-(D P) : ℤ) : WithTop ℤ) ≤ ordU f ⟨P, hP⟩ := by
  constructor
  · intro hfD; exact_mod_cast hfD.2 ⟨P, hP⟩
  · intro hPord
    classical
    refine ⟨hf.1, fun u => ?_⟩
    by_cases hu : u.1 = P
    · -- at `P`: use the supplied order bound
      have : u = ⟨P, hP⟩ := Subtype.ext hu
      rw [this]; exact_mod_cast hPord
    · -- away from `P`: `(D + single P 1)(u) = D(u)`, so the `𝒪_{D+P}` bound IS the `𝒪_D` bound
      have hsingle : (Finsupp.single P 1 : Divisor X) u.1 = 0 := by
        rw [Finsupp.single_apply, if_neg (fun h => hu h.symm)]
      have hadd : (D + Finsupp.single P 1 : Divisor X) u.1 = D u.1 := by
        rw [Finsupp.add_apply, hsingle, add_zero]
      have h := hf.2 u
      rwa [hadd] at h

end Bridges

/-! ### The order-`k` coefficient as a ℂ-linear functional on `𝒪_{D+P}(W)`

On `𝒪_{D+P}(W)` every section has `ordU ≥ k = -(D P) - 1` at `P`, so `coeffWFn k Pw` is genuinely
ℂ-linear there (`coeffWFn_add`/`coeffWFn_smul`).  We package it as a `LinearMap` to `ℂ`. -/

section Functional

variable {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)

/-- The order-`k` coefficient functional `𝒪_{D+P}(W) →ₗ[ℂ] ℂ` at `P` (`k = -(D P) - 1`). Linear
because every section of `𝒪_{D+P}` has order `≥ k` at `P` (so `coeffWFn` is additive/homogeneous). -/
noncomputable def coeffLin :
    OmegaD (D + Finsupp.single P 1) W →ₗ[ℂ] ℂ where
  toFun f := coeffWFn (-(D P) - 1) ⟨P, hP⟩ (f : W → ℂ)
  map_add' f g := by
    exact coeffWFn_add f.2.1 g.2.1 (ordU_ge_of_mem_add_single hP f.2)
      (ordU_ge_of_mem_add_single hP g.2)
  map_smul' c f := by
    exact coeffWFn_smul c f.2.1 (ordU_ge_of_mem_add_single hP f.2)

@[simp] theorem coeffLin_apply (f : OmegaD (D + Finsupp.single P 1) W) :
    coeffLin hP f = coeffWFn (-(D P) - 1) ⟨P, hP⟩ (f : W → ℂ) := rfl

/-- **The kernel of `coeffLin` is exactly `𝒪_D(W)`** (the membership characterization).  For
`f ∈ 𝒪_{D+P}(W)`, the order-`k` coefficient at `P` vanishes iff `ordU f P > k` iff `f ∈ 𝒪_D(W)`. -/
theorem coeffLin_eq_zero_iff (f : OmegaD (D + Finsupp.single P 1) W) :
    coeffLin hP f = 0 ↔ (f : W → ℂ) ∈ OmegaD D W := by
  rw [coeffLin_apply,
    coeffWFn_eq_zero_iff f.2.1 (ordU_ge_of_mem_add_single hP f.2),
    mem_OmegaD_iff_ordU_at_P hP f.2]
  -- `(-(D P) - 1 : ℤ) < ordU` ↔ `(-(D P) : ℤ) ≤ ordU`
  cases h : ordU (f : W → ℂ) ⟨P, hP⟩ with
  | top => exact iff_of_true (by exact_mod_cast WithTop.coe_lt_top _) (le_top)
  | coe n =>
    rw [WithTop.coe_lt_coe, WithTop.coe_le_coe]; omega

/-- **The witness realises every coefficient.**  Given that the witness section
`(chart − chart P)^k` lies in `𝒪_{D+P}(W)` (the geometric input — true when `W` is a coordinate disk
where `D` is supported only at `P`), `coeffLin` is surjective onto `ℂ`: scaling the witness by
`a : ℂ` hits coefficient `a`. -/
theorem coeffLin_surjective
    (hwit : witnessFn ⟨P, hP⟩ (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W) :
    Function.Surjective (coeffLin hP (D := D)) := by
  intro a
  refine ⟨a • ⟨witnessFn ⟨P, hP⟩ (-(D P) - 1), hwit⟩, ?_⟩
  have hmem : witnessFn ⟨P, hP⟩ (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W := hwit
  show coeffWFn (-(D P) - 1) ⟨P, hP⟩ (a • witnessFn ⟨P, hP⟩ (-(D P) - 1)) = a
  rw [coeffWFn_smul a hmem.1 (ordU_ge_of_mem_add_single hP hmem),
    coeffWFn_witnessFn, smul_eq_mul, mul_one]

end Functional

/-! ### The local realization isomorphism `𝒪_{D+P}(W) ⧸ 𝒪_D(W) ≅ₗ[ℂ] ℂ`

Putting the three pieces together (linearity, `ker = 𝒪_D`, surjectivity via the witness) gives the
clean local Mittag–Leffler iso at the function level — the genuine analytic content of the skyscraper
SES `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0`.  The single geometric input is the membership of the witness
section. -/

section Iso

variable {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)

/-- `𝒪_D(W) ⊆ 𝒪_{D+P}(W)` (the order bound `−(D+P) ≤ −D` weakens), as a submodule inclusion of the
function spaces. -/
theorem OmegaD_le_add_single : OmegaD D W ≤ OmegaD (D + Finsupp.single P 1) W := by
  intro f hf
  refine ⟨hf.1, fun u => le_trans ?_ (hf.2 u)⟩
  have hmono : (D : Divisor X) u.1 ≤ (D + Finsupp.single P 1 : Divisor X) u.1 := by
    classical
    rw [Finsupp.add_apply, Finsupp.single_apply]
    split <;> omega
  exact_mod_cast neg_le_neg hmono

/-- The kernel of `coeffLin` as a submodule equals `𝒪_D(W)` viewed inside `𝒪_{D+P}(W)`. -/
theorem ker_coeffLin :
    LinearMap.ker (coeffLin hP (D := D)) = (OmegaD D W).submoduleOf (OmegaD (D + Finsupp.single P 1) W) := by
  ext f
  rw [LinearMap.mem_ker, coeffLin_eq_zero_iff hP f, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.coe_subtype]

/-- **The local realization isomorphism** (function level):
`𝒪_{D+P}(W) ⧸ 𝒪_D(W) ≅ₗ[ℂ] ℂ`, the order-`k` coefficient at `P`.  Given the witness membership
(`hwit`), this is the genuine 1-dimensional skyscraper stalk: the quotient of meromorphic sections by
the pole-order condition is realised by the single Laurent coefficient.  This is the isolated analytic
content that `exists_skyscraperLES` bottoms out in. -/
noncomputable def localRealizationEquiv
    (hwit : witnessFn ⟨P, hP⟩ (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W) :
    (OmegaD (D + Finsupp.single P 1) W ⧸
        (OmegaD D W).submoduleOf (OmegaD (D + Finsupp.single P 1) W)) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ (ker_coeffLin hP).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (coeffLin_surjective hP hwit))

end Iso

/-! ### The germ-class coefficient (`OmegaDGerm`) — the form the skyscraper LES `h0ToSky` uses

The order-`k` coefficient at `P` descends to the junk-free germ-class space `MGerm W`: it depends only
on the germ (`coeffWFn_congr`, lifted along `codiscreteWithin`-agreement via `toGerm_eq_iff`).  On the
submodule `OmegaDGerm (D+P) W` it is ℂ-linear, with kernel `OmegaDGerm D W` and (witness) surjective —
the germ-class restatement of `localRealizationEquiv`. -/

section Germ

variable {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)

/-- The order-`k` coefficient at `P`, lifted to the germ-class space `MGerm W`.  Well-defined because
`coeffWFn` depends only on the germ at `P` (and `codiscreteWithin`-agreement implies `𝓝[≠] Pw`-
agreement). -/
noncomputable def coeffGermFn (k : ℤ) (Pw : W) : MGerm W → ℂ :=
  fun γ => Filter.Germ.liftOn γ (coeffWFn k Pw) (fun f g h => by
    refine coeffWFn_congr ?_
    exact (toGerm_eq_iff f g).mp (Filter.Germ.coe_eq.mpr h) Pw)

@[simp] theorem coeffGermFn_coe (k : ℤ) (Pw : W) (f : W → ℂ) :
    coeffGermFn k Pw (toGerm W f) = coeffWFn k Pw f := rfl

/-- The germ-class coefficient functional on `𝒪_{D+P}(W)`-germs, `OmegaDGerm (D+P) W →ₗ[ℂ] ℂ`.  The
form the skyscraper coefficient arrow `h0ToSky` is built from (per-overlap; the global arrow is the
matching family of these). -/
noncomputable def coeffGermLin :
    OmegaDGerm (D + Finsupp.single P 1) W →ₗ[ℂ] ℂ where
  toFun γ := coeffGermFn (-(D P) - 1) ⟨P, hP⟩ (γ : MGerm W)
  map_add' γ δ := by
    obtain ⟨f, hf, hfeq⟩ := γ.2
    obtain ⟨g, hg, hgeq⟩ := δ.2
    have hγ : (γ : MGerm W) = toGerm W f := hfeq.symm
    have hδ : (δ : MGerm W) = toGerm W g := hgeq.symm
    rw [show ((γ + δ : OmegaDGerm (D + Finsupp.single P 1) W) : MGerm W)
        = (γ : MGerm W) + (δ : MGerm W) from rfl, hγ, hδ, ← map_add (toGerm W),
      coeffGermFn_coe, coeffGermFn_coe, coeffGermFn_coe]
    exact coeffWFn_add hf.1 hg.1 (ordU_ge_of_mem_add_single hP hf)
      (ordU_ge_of_mem_add_single hP hg)
  map_smul' c γ := by
    obtain ⟨f, hf, hfeq⟩ := γ.2
    have hγ : (γ : MGerm W) = toGerm W f := hfeq.symm
    rw [show ((c • γ : OmegaDGerm (D + Finsupp.single P 1) W) : MGerm W)
        = c • (γ : MGerm W) from rfl, hγ, ← map_smul (toGerm W),
      coeffGermFn_coe, coeffGermFn_coe, RingHom.id_apply]
    exact coeffWFn_smul c hf.1 (ordU_ge_of_mem_add_single hP hf)

@[simp] theorem coeffGermLin_coe_toGerm
    (f : OmegaD (D + Finsupp.single P 1) W) :
    coeffGermLin hP (⟨toGerm W (f : W → ℂ), ⟨f, f.2, rfl⟩⟩ :
      OmegaDGerm (D + Finsupp.single P 1) W)
      = coeffWFn (-(D P) - 1) ⟨P, hP⟩ (f : W → ℂ) := rfl

/-- `OmegaDGerm D W ≤ OmegaDGerm (D+P) W` (germ image of the function-level inclusion). -/
theorem OmegaDGerm_le_add_single :
    OmegaDGerm D W ≤ OmegaDGerm (D + Finsupp.single P 1) W := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, OmegaD_le_add_single hg, rfl⟩

/-- **Surjectivity of the germ-class coefficient** (given the witness membership): every `a : ℂ` is
realised by the germ of `a • witness`. -/
theorem coeffGermLin_surjective
    (hwit : witnessFn ⟨P, hP⟩ (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W) :
    Function.Surjective (coeffGermLin hP (D := D)) := by
  intro a
  refine ⟨⟨toGerm W (a • witnessFn ⟨P, hP⟩ (-(D P) - 1)),
    ⟨a • witnessFn ⟨P, hP⟩ (-(D P) - 1), Submodule.smul_mem _ a hwit, rfl⟩⟩, ?_⟩
  show coeffGermFn (-(D P) - 1) ⟨P, hP⟩ (toGerm W (a • witnessFn ⟨P, hP⟩ (-(D P) - 1))) = a
  rw [coeffGermFn_coe, coeffWFn_smul a hwit.1 (ordU_ge_of_mem_add_single hP hwit),
    coeffWFn_witnessFn, smul_eq_mul, mul_one]

/-- A germ in `OmegaDGerm D W` (image of `𝒪_D(W)`) has vanishing order-`k` coefficient at `P` (it
already lies one order below: `ordU g P ≥ -(D P) = k + 1 > k`). -/
theorem coeffGermFn_eq_zero_of_mem_OmegaDGerm {γ : MGerm W}
    (hγ : γ ∈ OmegaDGerm D W) :
    coeffGermFn (-(D P) - 1) ⟨P, hP⟩ γ = 0 := by
  obtain ⟨g, hg, rfl⟩ := hγ
  rw [coeffGermFn_coe]
  -- `ordU g P ≥ -(D P)` (membership in `𝒪_D`), and `-(D P) - 1 < -(D P)`
  have hge : ((-(D P) : ℤ) : WithTop ℤ) ≤ ordU g ⟨P, hP⟩ := by exact_mod_cast hg.2 ⟨P, hP⟩
  have hlt : ((-(D P) - 1 : ℤ) : WithTop ℤ) < ((-(D P) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_lt_coe]; omega
  have hk_le : ((-(D P) - 1 : ℤ) : WithTop ℤ) ≤ ordU g ⟨P, hP⟩ := le_of_lt (lt_of_lt_of_le hlt hge)
  rw [coeffWFn_eq_zero_iff hg.1 hk_le]
  exact lt_of_lt_of_le hlt hge

/-- **The kernel of the germ-class coefficient is exactly `OmegaDGerm D W`** (the membership
characterization at the germ level). -/
theorem ker_coeffGermLin :
    LinearMap.ker (coeffGermLin hP (D := D))
      = (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W) := by
  ext γ
  rw [LinearMap.mem_ker, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · -- coefficient `0` ⟹ the chosen representative lies in `𝒪_D(W)`, so the germ is in `𝒪_D`-germs
    intro h0
    obtain ⟨f, hf, hfeq⟩ := γ.2
    have hcoeff : coeffWFn (-(D P) - 1) ⟨P, hP⟩ f = 0 := by
      have : coeffGermLin hP γ = coeffWFn (-(D P) - 1) ⟨P, hP⟩ f := by
        show coeffGermFn (-(D P) - 1) ⟨P, hP⟩ (γ : MGerm W) = _
        rw [← hfeq, coeffGermFn_coe]
      rwa [this] at h0
    have hfD : f ∈ OmegaD D W := by
      rw [← coeffLin_eq_zero_iff hP ⟨f, hf⟩]; exact hcoeff
    exact ⟨f, hfD, hfeq⟩
  · -- germ in `𝒪_D`-germs ⟹ coefficient `0`
    intro hγD
    exact coeffGermFn_eq_zero_of_mem_OmegaDGerm hP hγD

/-- **The local realization isomorphism (germ-class form)**:
`OmegaDGerm (D+P) W ⧸ OmegaDGerm D W ≅ₗ[ℂ] ℂ`, the order-`k` Laurent coefficient at `P`.  This is
the genuine 1-dimensional skyscraper stalk `ℂ_P` in junk-free germ-class form — exactly the local
analytic content the χ-additivity skyscraper LES (`exists_skyscraperLES`) bottoms out in.  The single
geometric input is the witness membership `hwit` (true on a coordinate disk where `D` is supported
only at `P`). -/
noncomputable def localRealizationGermEquiv
    (hwit : witnessFn ⟨P, hP⟩ (-(D P) - 1) ∈ OmegaD (D + Finsupp.single P 1) W) :
    (OmegaDGerm (D + Finsupp.single P 1) W ⧸
        (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ (ker_coeffGermLin hP).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (coeffGermLin_surjective hP hwit))

end Germ

end Jacobians.Dolbeault
