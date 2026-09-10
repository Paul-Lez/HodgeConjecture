/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedMultiplicityBridge
import KirovDolbeault.Dolbeault.FormTraceInftyFibreNF
import KirovDolbeault.Dolbeault.CanonicalFormDifferential
import KirovDolbeault.Dolbeault.TailFrameGenus0

/-!
# The conservation-of-number engine for the plain value trace (T lane)

Frame-free geometric layer for the residual wall `exists_frameTraceFunctionData_df`
(`FrameTrace.lean`): the **plain value trace**

> `valueTrace F f : ℂ → ℂ`,  `valueTrace F f w = ∑_{y ∈ F⁻¹(coe w)} F.holoRepr y`

of a global meromorphic `F` through the branched cover `𝔉 = f.toRiemannSphere`, together with
the local fibre control needed for its analyticity/meromorphy/residue fields:

* **fibre basics** — every preimage of a finite value `coe z` is a non-pole with
  `holoRepr = z` and local degree `≥ 1`;
* **the sheet decomposition** — through the PROVEN multiplicity-patching engine
  (`MultiplicityPatchingData`: pairwise-disjoint sheets + per-sheet conservation + no-escape),
  near any centre value the fibre splits into per-sheet slices, the trace into per-slice sums;
* **slice enumeration by counting** — a slice's local-degree sum is the sheet weight
  `m = localDeg` and each preimage weighs `≥ 1`, so `m` *distinct exhibited preimages* in a
  slice enumerate it exactly (the conservation-of-number step of Miranda §VIII.3, step 1);
* **the regularity bridges** — `localDeg = 1` at a fibre point gives a nonvanishing
  chart-pullback derivative of `f.holoRepr` (feeding the planar-section/IFT machinery), and
  conversely a fibre point off the canonical-divisor support of an `ω₀ = df` datum is
  unramified.

No frame, no residue here: pure cover geometry over the proven engine.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), §VIII.3.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §17.
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FrameTraceWall

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatching
  Jacobians.MultiplicityPatchingConstruct

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The plain value trace and the fibre `Finset` -/

/-- **The plain value trace** of `F` through the cover `𝔉 = f.toRiemannSphere`, read in the
finite chart of `ℂℙ¹`: at `w : ℂ`, the sum of the junk-free values `F.holoRepr` over the fibre
`𝔉⁻¹(coe w)` (a `finsum`, which is the honest finite sum on the finite fibres of a nonconstant
cover and `0` otherwise). -/
def valueTrace (F f : MeromorphicFunction X) : ℂ → ℂ :=
  fun w => ∑ᶠ y ∈ f.toRiemannSphere ⁻¹' {((w : ℂ) : RiemannSphere)}, F.holoRepr y

/-- The fibre of `𝔉 = f.toRiemannSphere` over `w`, as a `Finset` (nonconstant cover). -/
def fibreFinset (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w : RiemannSphere) : Finset X :=
  (fibre_finite_of_div_ne_zero f hdiv w).toFinset

@[simp] theorem mem_fibreFinset {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {w : RiemannSphere} {y : X} :
    y ∈ fibreFinset f hdiv w ↔ f.toRiemannSphere y = w := by
  rw [fibreFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]

theorem coe_fibreFinset (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w : RiemannSphere) :
    (fibreFinset f hdiv w : Set X) = f.toRiemannSphere ⁻¹' {w} :=
  (fibre_finite_of_div_ne_zero f hdiv w).coe_toFinset

/-- The value trace as an honest `Finset` sum over the fibre. -/
theorem valueTrace_eq_sum_fibreFinset (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (w : ℂ) :
    valueTrace F f w = ∑ y ∈ fibreFinset f hdiv (((w : ℂ) : RiemannSphere)), F.holoRepr y := by
  rw [valueTrace, ← coe_fibreFinset f hdiv, finsum_mem_coe_finset]

/-! ## Fibre basics over a finite value -/

/-- A preimage of a finite value is a non-pole. -/
theorem nonpole_of_fibre_coe {f : MeromorphicFunction X} {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) : 0 ≤ f.orderAtPoint y := by
  by_contra h
  rw [f.toRiemannSphere_of_pole (not_le.mp h)] at hy
  exact OnePoint.infty_ne_coe z hy

/-- A preimage of a finite value reads that value through `holoRepr`. -/
theorem holoRepr_of_fibre_coe {f : MeromorphicFunction X} {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) : f.holoRepr y = z :=
  holoRepr_eq_of_fibre_nonpole f hy (nonpole_of_fibre_coe hy)

/-- **Local degree positivity**: a preimage of a finite value has local degree `≥ 1`. -/
theorem one_le_localDeg_of_fibre_coe (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere)) :
    1 ≤ localDeg f (((z : ℂ) : RiemannSphere)) y := by
  obtain ⟨h1, _, heq⟩ :=
    analyticOrderAt_holoRepr_sub_eq_mult f hdiv hy (nonpole_of_fibre_coe hy)
  rw [heq]
  exact_mod_cast h1

/-- **The simple-point regularity bridge**: at a fibre point of local degree `1`, the
chart-pullback derivative of `f.holoRepr` is nonzero (the planar-section/IFT input). -/
theorem holoRepr_pullback_deriv_ne_zero_of_localDeg_eq_one (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere))
    (h1 : localDeg f (((z : ℂ) : RiemannSphere)) y = 1) :
    deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ)) ((chartAt (H := ℂ) y) y) ≠ 0 := by
  have hnp := nonpole_of_fibre_coe hy
  obtain ⟨_, hord, _⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv hy hnp
  rw [h1] at hord
  -- the shifted pullback has a simple zero, so its derivative is nonzero
  have hg_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ))
      ((chartAt (H := ℂ) y) y) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  have hgz_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ) - z)
      ((chartAt (H := ℂ) y) y) := hg_an.sub analyticAt_const
  have hd : deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ) - z)
      ((chartAt (H := ℂ) y) y) ≠ 0 :=
    Jacobians.Dolbeault.FormTraceInftyFibre.deriv_ne_zero_of_analyticOrderAt_eq_one hgz_an
      (by exact_mod_cast hord)
  rwa [deriv_sub_const] at hd

/-! ## The sheet decomposition of the trace near a centre

Through the PROVEN multiplicity-patching engine: at any centre value `w₀`, the patching datum
`P` provides pairwise-disjoint sheets `P.U x` around the fibre points `P.xs`, an open value
neighbourhood `P.W ∋ w₀`, the per-sheet conservation `∑_{slice} localDeg = P.m x`, fibre
finiteness, and **no escape**.  We re-read these as `Finset` statements about
`fibreFinset f hdiv (coe z)` for `coe z ∈ P.W`. -/

/-- The patching datum of a nonconstant cover at a centre value (the proven engine). -/
def patchAt (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (w₀ : RiemannSphere) : MultiplicityPatchingData f w₀ :=
  (localMultiplicitySheets_of_nonconstant f hdiv w₀).toPatchingData

/-- **The per-sheet slice** of the fibre over `coe z`: the fibre points lying in the sheet
`P.U x`. -/
def slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) (x : X) (z : ℂ) : Finset X :=
  (fibreFinset f hdiv (((z : ℂ) : RiemannSphere))).filter (fun y => y ∈ P.U x)

theorem mem_slice {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {w₀ : RiemannSphere} {P : MultiplicityPatchingData f w₀} {x : X} {z : ℂ} {y : X} :
    y ∈ slice hdiv P x z ↔
      f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) ∧ y ∈ P.U x := by
  rw [slice, Finset.mem_filter, mem_fibreFinset]

/-- The slice coincides with the patching engine's set-level slice. -/
theorem coe_slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) (x : X) (z : ℂ) :
    (slice hdiv P x z : Set X)
      = P.U x ∩ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))} := by
  ext y
  rw [Finset.mem_coe, mem_slice]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  tauto

/-- **The slice conservation count** (`Finset` form of the engine's `sheetMult_eq`). -/
theorem sum_localDeg_slice {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    ∑ y ∈ slice hdiv P x z, localDeg f (((z : ℂ) : RiemannSphere)) y = P.m x := by
  have h := P.sheetMult_eq x hx _ hz
  rw [← h, ← finsum_mem_coe_finset, coe_slice]

/-- **The fibre splits into the slices** (no-escape + disjointness, `Finset` form): for
`coe z ∈ P.W`, any sum over the fibre is the double sum over the per-sheet slices. -/
theorem sum_fibre_eq_sum_slices {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (g : X → ℂ) :
    ∑ y ∈ fibreFinset f hdiv (((z : ℂ) : RiemannSphere)), g y
      = ∑ x ∈ P.xs, ∑ y ∈ slice hdiv P x z, g y := by
  classical
  rw [← Finset.sum_biUnion ?hdisj]
  · congr 1
    ext y
    simp only [Finset.mem_biUnion, mem_fibreFinset, mem_slice]
    constructor
    · intro hy
      have hyW : y ∈ f.toRiemannSphere ⁻¹' P.W := by
        rw [Set.mem_preimage, hy]; exact hz
      obtain ⟨x, hx, hyU⟩ := Set.mem_iUnion₂.mp (P.preimage_W_subset hyW)
      exact ⟨x, hx, hy, hyU⟩
    · rintro ⟨x, _, hy, _⟩
      exact hy
  · intro x hx x' hx' hne s hs hs' y hy
    have h1 : y ∈ slice hdiv P x z := hs hy
    have h2 : y ∈ slice hdiv P x' z := hs' hy
    rw [mem_slice] at h1 h2
    exact absurd (Set.mem_inter h1.2 h2.2)
      (Set.disjoint_iff.mp
        (P.U_pairwiseDisjoint x (Finset.mem_coe.mp hx) x' (Finset.mem_coe.mp hx') hne) ·)

/-- **The trace splits into the per-sheet slice sums** near a centre. -/
theorem valueTrace_eq_sum_slices (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {w₀ : RiemannSphere}
    (P : MultiplicityPatchingData f w₀) {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    valueTrace F f z = ∑ x ∈ P.xs, ∑ y ∈ slice hdiv P x z, F.holoRepr y := by
  rw [valueTrace_eq_sum_fibreFinset F f hdiv, sum_fibre_eq_sum_slices hdiv P hz]

/-! ## Slice enumeration by counting -/

/-- The slice at the centre value itself is the singleton of its sheet's fibre point. -/
theorem slice_centre_eq_singleton {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere))) {x : X} (hx : x ∈ P.xs) :
    slice hdiv P x c = {x} := by
  ext y
  rw [mem_slice, Finset.mem_singleton]
  constructor
  · rintro ⟨hyfib, hyU⟩
    -- `y` is a fibre point of the centre, so `y ∈ P.xs`; distinct fibre points have
    -- disjoint sheets, and `y` lies in its own sheet, so `y = x`.
    have hyxs : y ∈ P.xs := by
      have : y ∈ (P.xs : Set X) := by rw [P.xs_coe]; exact hyfib
      exact this
    by_contra hne
    exact Set.disjoint_iff.mp (P.U_pairwiseDisjoint y hyxs x hx hne)
      (Set.mem_inter (P.mem_U_self y hyxs) hyU)
  · rintro rfl
    have : y ∈ (P.xs : Set X) := hx
    rw [P.xs_coe] at this
    exact ⟨this, P.mem_U_self y hx⟩

/-- **The sheet weight is the local degree of its fibre point** (read the conservation at the
centre, where the slice is the singleton). -/
theorem patch_m_eq_localDeg {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {c : ℂ} (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere))) {x : X}
    (hx : x ∈ P.xs) :
    P.m x = localDeg f (((c : ℂ) : RiemannSphere)) x := by
  have h := sum_localDeg_slice hdiv P hx P.w₀_mem_W
  rw [slice_centre_eq_singleton hdiv P hx, Finset.sum_singleton] at h
  exact h.symm

/-- **The slice cardinality is bounded by the sheet weight** (each preimage weighs `≥ 1`). -/
theorem slice_card_le {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) :
    ((slice hdiv P x z).card : ℤ) ≤ P.m x := by
  have hone : ∀ y ∈ slice hdiv P x z, (1 : ℤ) ≤ localDeg f (((z : ℂ) : RiemannSphere)) y :=
    fun y hy => one_le_localDeg_of_fibre_coe f hdiv (mem_slice.mp hy).1
  calc ((slice hdiv P x z).card : ℤ)
      = (slice hdiv P x z).card • (1 : ℤ) := by simp
    _ ≤ ∑ y ∈ slice hdiv P x z, localDeg f (((z : ℂ) : RiemannSphere)) y :=
        Finset.card_nsmul_le_sum _ _ _ hone
    _ = P.m x := sum_localDeg_slice hdiv P hx hz

/-- **Slice enumeration**: if `m` distinct exhibited preimages lie in a slice of weight `m`,
they exhaust it (conservation of number). -/
theorem slice_eq_of_exhibited {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (cand : Finset X)
    (hsub : cand ⊆ slice hdiv P x z) (hcard : P.m x ≤ (cand.card : ℤ)) :
    slice hdiv P x z = cand :=
  (Finset.eq_of_subset_of_card_le hsub (by
    exact_mod_cast le_trans (slice_card_le hdiv P hx hz) hcard)).symm

/-! ## The unramified slice: a single moving preimage

At a sheet of weight `1`, the slice over every nearby value is a single point, and any
exhibited preimage in the sheet *is* that point.  This feeds the planar-section identification:
the section value `chart⁻¹ (s z)` is a preimage in the sheet, hence THE slice point. -/

/-- A slice of weight `1` over a finite value is a singleton consisting of any exhibited
preimage in the sheet. -/
theorem slice_eq_singleton_of_weight_one {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) {w₀ : RiemannSphere}
    (P : MultiplicityPatchingData f w₀) {x : X} (hx : x ∈ P.xs)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∈ P.W) (hm : P.m x = 1) {y : X}
    (hyfib : f.toRiemannSphere y = (((z : ℂ) : RiemannSphere))) (hyU : y ∈ P.U x) :
    slice hdiv P x z = {y} :=
  slice_eq_of_exhibited hdiv P hx hz {y}
    (Finset.singleton_subset_iff.mpr (mem_slice.mpr ⟨hyfib, hyU⟩))
    (by rw [hm, Finset.card_singleton]; norm_num)

/-! ## Regularity bridges

The local degree is `1` exactly when the chart-pullback derivative of `f.holoRepr` is nonzero;
for an `ω₀ = df` datum the latter is read off the canonical-divisor order (`K x = 0`). -/

/-- An analytic function with nonvanishing derivative has a **simple** level set: the order of
`g − g(p)` at `p` is exactly `1`. -/
theorem analyticOrderAt_sub_eq_one_of_deriv_ne_zero {g : ℂ → ℂ} {p c : ℂ}
    (hg : AnalyticAt ℂ g p) (hval : g p = c) (hd : deriv g p ≠ 0) :
    analyticOrderAt (fun ζ => g ζ - c) p = 1 := by
  have hga : AnalyticAt ℂ (fun ζ => g ζ - c) p := hg.sub analyticAt_const
  -- the order is finite (else `g` is locally constant, killing the derivative)
  have hne_top : analyticOrderAt (fun ζ => g ζ - c) p ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hconst : g =ᶠ[𝓝 p] fun _ => c := by
      filter_upwards [htop] with ζ hζ
      exact sub_eq_zero.mp hζ
    rw [hconst.deriv_eq, deriv_const] at hd
    exact hd rfl
  -- the order is nonzero (the value vanishes)
  have hne_zero : analyticOrderAt (fun ζ => g ζ - c) p ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hga, by simp [hval]⟩
  -- write the order as a natural number `n ≥ 1` and factorize
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne_top
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · exact absurd (by rw [← hn, h0]; rfl) hne_zero
    · exact h1
  -- if `n ≥ 2` the derivative would vanish at `p`
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1' : n = 1 := by omega
    rw [← hn, hn1']
    rfl
  · exfalso
    obtain ⟨u, hu_an, hu_ne, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
    have hd0 : deriv (fun ζ => g ζ - c) p = 0 := by
      have hpow : HasDerivAt (fun ζ : ℂ => (ζ - p) ^ n)
          ((n : ℂ) * (p - p) ^ (n - 1)) p := by
        simpa using ((hasDerivAt_id p).sub_const p).pow n
      have hprod := hpow.smul hu_an.differentiableAt.hasDerivAt
      have hderiv_eq : deriv ((fun ζ : ℂ => (ζ - p) ^ n) • u) p
          = (p - p) ^ n • deriv u p + ((n : ℂ) * (p - p) ^ (n - 1)) • u p := hprod.deriv
      rw [(EventuallyEq.deriv_eq hfac : deriv (fun ζ => g ζ - c) p = _),
        show (fun ζ : ℂ => (ζ - p) ^ n • u ζ) = (fun ζ : ℂ => (ζ - p) ^ n) • u from rfl,
        hderiv_eq, sub_self, zero_pow (by omega : n ≠ 0), zero_pow (by omega : n - 1 ≠ 0)]
      simp
    rw [deriv_sub_const] at hd0
    exact hd hd0

/-- **`localDeg = 1` at a fibre point with nonvanishing `holoRepr`-pullback derivative.** -/
theorem localDeg_eq_one_of_deriv_ne_zero (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ} {y : X}
    (hy : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere))
    (hd : deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ))
      ((chartAt (H := ℂ) y) y) ≠ 0) :
    localDeg f (((z : ℂ) : RiemannSphere)) y = 1 := by
  have hnp := nonpole_of_fibre_coe hy
  obtain ⟨_, hord, heq⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv hy hnp
  have hg_an : AnalyticAt ℂ (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ))
      ((chartAt (H := ℂ) y) y) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  have hval : (fun ζ => f.holoRepr ((chartAt (H := ℂ) y).symm ζ)) ((chartAt (H := ℂ) y) y)
      = z := by
    show f.holoRepr ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y)) = z
    rw [(chartAt (H := ℂ) y).left_inv (mem_chart_source ℂ y)]
    exact holoRepr_of_fibre_coe hy
  have h1 := analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg_an hval hd
  rw [h1] at hord
  have : (localDeg f (((z : ℂ) : RiemannSphere)) y).toNat = 1 := by
    exact_mod_cast hord.symm
  omega

/-- **The `df`-datum unramifiedness bridge**: at a non-pole `x` where the chart-pullback
derivative of `f.toFun` has meromorphic order `0` (i.e. `K x = 0` for the canonical divisor of
`df`), the `holoRepr`-pullback derivative is nonzero. -/
theorem holoRepr_pullback_deriv_ne_zero_of_derivOrder_zero (f : MeromorphicFunction X)
    {x : X} (hnp : 0 ≤ f.orderAtPoint x)
    (hK : meromorphicOrderAt (deriv (f.toFun ∘ (chartAt (H := ℂ) x).symm))
      ((chartAt (H := ℂ) x) x) = 0) :
    deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) x).symm ζ)) ((chartAt (H := ℂ) x) x) ≠ 0 := by
  set pre := (chartAt (H := ℂ) x) x with hpre
  have hpre_tgt : pre ∈ (chartAt (H := ℂ) x).target :=
    (chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x)
  have hg_an : AnalyticAt ℂ (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) pre :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  -- transport the order through the punctured germ agreement
  have hagree : deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) =ᶠ[𝓝[≠] pre]
      deriv (f.toFun ∘ (chartAt (H := ℂ) x).symm) :=
    Jacobians.Dolbeault.deriv_eventuallyEq_punctured
      (holoRepr_pullback_eventuallyEq_toFun f x hpre_tgt)
  have hord : meromorphicOrderAt (deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm)) pre = 0 := by
    rw [meromorphicOrderAt_congr hagree]
    exact hK
  -- order `0` means the (analytic, hence continuous) derivative has a nonzero punctured limit
  have hd_an : AnalyticAt ℂ (deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm)) pre := hg_an.deriv
  obtain ⟨u, hu_an, hu_ne, hev⟩ :=
    (meromorphicOrderAt_eq_int_iff hd_an.meromorphicAt).mp hord
  have hval : deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) pre = u pre := by
    have h1 : Tendsto (deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm)) (𝓝[≠] pre)
        (𝓝 (deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) pre)) :=
      hd_an.continuousAt.continuousWithinAt.tendsto
    have h2 : Tendsto (deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm)) (𝓝[≠] pre)
        (𝓝 (u pre)) := by
      refine (hu_an.continuousAt.continuousWithinAt.tendsto).congr' ?_
      filter_upwards [hev] with ζ hζ
      rw [hζ]
      simp
    exact tendsto_nhds_unique h1 h2
  intro hv0
  rw [show deriv (fun ζ => f.holoRepr ((chartAt (H := ℂ) x).symm ζ)) pre
      = deriv (f.holoRepr ∘ (chartAt (H := ℂ) x).symm) pre from rfl, hval] at hv0
  exact hu_ne hv0

/-! ## The unramified section sum

At a centre `c` whose fibre is enumerated by weight-`1` sheet points `xs i` carrying planar
sections `s i` (analytic at `c`, based at the chart images, right-inverting the
`holoRepr`-pullback), the value trace agrees **on a full neighbourhood of `c`** with the moving
section sum `w ↦ ∑ i, F.holoRepr (chart⁻¹ (s i w))`. -/

/-- The non-pole locus of a meromorphic function is open. -/
theorem isOpen_nonpole (f : MeromorphicFunction X) : IsOpen {y : X | 0 ≤ f.orderAtPoint y} := by
  have : {y : X | 0 ≤ f.orderAtPoint y} = {y | f.orderAtPoint y < 0}ᶜ := by
    ext y; simp [not_lt]
  rw [this]
  exact (f.finite_poles.isClosed).isOpen_compl

/-- **The unramified section-sum identification.**  Given a patching datum `P` at the finite
centre `c`, an injective enumeration `xs` of its fibre points, weight-`1` sheets, and planar
sections `s i` of the cover through each fibre point, the value trace equals the moving section
sum near `c`. -/
theorem valueTrace_eventuallyEq_sectionSum (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere)))
    {ι : Type*} [Fintype ι] (xs : ι → X) (hinj : Function.Injective xs)
    (himg : ∀ y, y ∈ P.xs ↔ ∃ i, xs i = y)
    (hm : ∀ i, P.m (xs i) = 1)
    (s : ι → ℂ → ℂ)
    (hs_an : ∀ i, AnalyticAt ℂ (s i) c)
    (hs_base : ∀ i, s i c = (chartAt (H := ℂ) (xs i)) (xs i))
    (hrinv : ∀ i, ∀ᶠ w in 𝓝 c, f.holoRepr ((chartAt (H := ℂ) (xs i)).symm (s i w)) = w) :
    valueTrace F f =ᶠ[𝓝 c]
      fun w => ∑ i, F.holoRepr ((chartAt (H := ℂ) (xs i)).symm (s i w)) := by
  classical
  have hxs_mem : ∀ i, xs i ∈ P.xs := fun i => (himg (xs i)).mpr ⟨i, rfl⟩
  have hxs_fib : ∀ i, f.toRiemannSphere (xs i) = (((c : ℂ) : RiemannSphere)) := fun i => by
    have : xs i ∈ (P.xs : Set X) := hxs_mem i
    rwa [P.xs_coe] at this
  -- the moving fibre point of the `i`-th sheet
  set yy : ι → ℂ → X := fun i w => (chartAt (H := ℂ) (xs i)).symm (s i w) with hyy
  -- (a) eventually the value lies in the patching neighbourhood
  have hW : ∀ᶠ w in 𝓝 c, (((w : ℂ) : RiemannSphere)) ∈ P.W := by
    have hcont : ContinuousAt (fun w : ℂ => ((w : ℂ) : RiemannSphere)) c :=
      OnePoint.continuous_coe.continuousAt
    exact hcont (P.W_open.mem_nhds P.w₀_mem_W)
  -- (b) per sheet: eventually the moving point is in the sheet, a non-pole, and on the fibre
  have hsheet : ∀ i, ∀ᶠ w in 𝓝 c,
      f.toRiemannSphere (yy i w) = (((w : ℂ) : RiemannSphere)) ∧ yy i w ∈ P.U (xs i) := by
    intro i
    -- the moving point tends to `xs i`
    have hcm : ContinuousAt (yy i) c := by
      have h1 : ContinuousAt (chartAt (H := ℂ) (xs i)).symm (s i c) := by
        rw [hs_base i]
        exact (chartAt (H := ℂ) (xs i)).continuousAt_symm
          ((chartAt (H := ℂ) (xs i)).map_source (mem_chart_source ℂ (xs i)))
      exact h1.comp (hs_an i).continuousAt
    have hyc : yy i c = xs i := by
      rw [hyy]
      simp only
      rw [hs_base i, (chartAt (H := ℂ) (xs i)).left_inv (mem_chart_source ℂ (xs i))]
    -- eventually in the open sheet
    have hU : ∀ᶠ w in 𝓝 c, yy i w ∈ P.U (xs i) := by
      have : P.U (xs i) ∈ 𝓝 (yy i c) := by
        rw [hyc]
        exact (P.U_open (xs i) (hxs_mem i)).mem_nhds (P.mem_U_self (xs i) (hxs_mem i))
      exact hcm this
    -- eventually a non-pole
    have hnp : ∀ᶠ w in 𝓝 c, 0 ≤ f.orderAtPoint (yy i w) := by
      have : {y : X | 0 ≤ f.orderAtPoint y} ∈ 𝓝 (yy i c) := by
        rw [hyc]
        exact (isOpen_nonpole f).mem_nhds (nonpole_of_fibre_coe (hxs_fib i))
      exact hcm this
    filter_upwards [hU, hnp, hrinv i] with w hwU hwnp hwval
    refine ⟨?_, hwU⟩
    rw [f.toRiemannSphere_of_nonneg hwnp]
    exact congrArg (fun t : ℂ => ((t : ℂ) : RiemannSphere)) hwval
  have hsheets : ∀ᶠ w in 𝓝 c, ∀ i,
      f.toRiemannSphere (yy i w) = (((w : ℂ) : RiemannSphere)) ∧ yy i w ∈ P.U (xs i) :=
    Filter.eventually_all.mpr hsheet
  -- assemble
  filter_upwards [hW, hsheets] with w hwW hwsheets
  have hxs_img : P.xs = (Finset.univ : Finset ι).image xs := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rw [himg y]
  rw [valueTrace_eq_sum_slices F f hdiv P hwW, hxs_img,
    Finset.sum_image (fun i _ j _ h => hinj h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slice_eq_singleton_of_weight_one hdiv P (hxs_mem i) hwW (hm i)
    (hwsheets i).1 (hwsheets i).2, Finset.sum_singleton]

/-- **Analyticity of the value trace at an unramified `F`-regular centre** (the `hoff` shape):
with the section data of `valueTrace_eventuallyEq_sectionSum` and `F` non-polar on the fibre,
the value trace is analytic at `c`. -/
theorem analyticAt_valueTrace_of_sections (F f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    (P : MultiplicityPatchingData f (((c : ℂ) : RiemannSphere)))
    {ι : Type*} [Fintype ι] (xs : ι → X) (hinj : Function.Injective xs)
    (himg : ∀ y, y ∈ P.xs ↔ ∃ i, xs i = y)
    (hm : ∀ i, P.m (xs i) = 1)
    (s : ι → ℂ → ℂ)
    (hs_an : ∀ i, AnalyticAt ℂ (s i) c)
    (hs_base : ∀ i, s i c = (chartAt (H := ℂ) (xs i)) (xs i))
    (hrinv : ∀ i, ∀ᶠ w in 𝓝 c, f.holoRepr ((chartAt (H := ℂ) (xs i)).symm (s i w)) = w)
    (hFnp : ∀ i, 0 ≤ F.orderAtPoint (xs i)) :
    AnalyticAt ℂ (valueTrace F f) c := by
  have hsum : AnalyticAt ℂ
      (fun w => ∑ i, F.holoRepr ((chartAt (H := ℂ) (xs i)).symm (s i w))) c := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have hF_an : AnalyticAt ℂ (F.holoRepr ∘ (chartAt (H := ℂ) (xs i)).symm) (s i c) := by
      rw [hs_base i]
      exact F.analyticAt_holoRepr_chartPullback_of_orderNonneg (hFnp i)
    exact hF_an.comp (hs_an i)
  exact hsum.congr
    (valueTrace_eventuallyEq_sectionSum F f hdiv P xs hinj himg hm s hs_an hs_base hrinv).symm

end Jacobians.Dolbeault.FrameTraceWall

end
