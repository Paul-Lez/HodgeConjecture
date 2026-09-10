/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetEngineLocal
import KirovDolbeault.Dolbeault.SegmentPeriod

/-!
# Abel ⊆ campaign, E3: the per-arc weak solution (Forster 20.5)

The E3 per-arc constructor of `docs/planning/AB_E_ROUTE.md` §2: for two distinct points
`a ≠ b` of one cover disk `U j₀` of a `ChartDiskCover`, the Forster 20.5 one-disk weak
solution for the divisor `(b) − (a)`:

* **planar layer** (`SegTube`): a tube system around the coordinate segment `[za, zb]`
  inside the coordinate ball — radius `δ`, a smooth cutoff `ψ` (`1` on the half-tube, `0`
  off the `δ`-tube) and a smooth co-cutoff `θ` (`0` near the segment, `1` off the
  quarter-tube) from the smooth Urysohn lemma; the weak solution
  `F̃ = exp(ψ·log((z−zb)/(z−za)))` glued across the segment as the Möbius ratio
  (`SegTube.Ffun`), with the master planar identity `∂̄F̃ = F̃·(H·∂̄ψ)` off the endpoints
  (`SegTube.dbar_Ffun`), where `H = θ·log((z−zb)/(z−za))` (`SegTube.Hfun`) is globally
  smooth;
* **interface** (`ArcWeakSolution`): the geometric fields of `RawLogDbarDatum` for a
  divisor `D` — everything except the E4 pairing identity, which enters only through the
  constructor `ArcWeakSolution.toRaw` as an explicit hypothesis (E4 is rung-separate; the
  constructor is *conditional on the pairing field*, as `AB_E_ROUTE.md` §2 prescribes);
* **the per-arc constructor** (`exists_arcWeakSolution_avoiding` / `exists_arcWeakSolution`):
  the lifted weak solution `F = F̃ ∘ e` on `U j₀` (extended by `1`), the one-chart `(0,1)`
  datum `σ = (lift H)·∂̄(lift ψ)` (the `exists_pairOmega_pos` single-chart support pattern),
  the geometric fields (nonvanishing, chart-read differentiability, the logarithmic
  `∂̄`-identity in every cover chart, the local normal form `(z−za)^{∓1}·(analytic unit)` at
  the endpoints via `dslope` of the biholomorphic chart transition), and **tameness at any
  prescribed finite avoid set** (analytic read + vanishing `σ`, the tube shrunk by
  `SegTube.exists_segTube_avoiding`);
* **the chain fold** (`ArcWeakSolution.exists_mul`): the product of two weak-solution data
  is one for the divisor sum — `F₁·F₂` patched at cancellation points by the product of
  the analytic units (the zero of one arc cancels the pole of the next), `σ₁ + σ₂`; the
  factors must be `TameAt` each other's unshared support, which the avoid set supplies,
  and the fold propagates tameness (the list-fold invariant);
* **E3 complete** (`exists_arcWeakSolution_boundary`): every `SmoothOneChain` admits an
  `ArcWeakSolution` for its boundary divisor — chart-disk subdivision of each arc
  (`exists_subdivision`, Lebesgue number), ℤ-coefficients as repeated/reversed dipole
  lists (`zsmulList`), telescoping (`consecPairs`), master fold over the flat dipole list
  (`exists_arcWeakSolution_dipoleList`);
* **the E4-pinned engine** (`exists_meromorphic_of_zeroPeriodChain_of_pairing`): with E3
  unconditional, the §20 engine's sole remaining obligation is the E4 pairing identity for
  the constructed datum;
* **E4 complete — THE UNCONDITIONAL ENGINE** (`exists_meromorphic_of_zeroPeriodChain'`):
  the per-arc constructor now exposes its pairing value `π·segPeriod` (the planar atom
  `integral_slitLog_dbar_mul` after the single-chart collapse), the fold exposes
  `σ = σ₁ + σ₂` and accumulates the values over chart-tagged dipole lists
  (`exists_arcWeakSolution_dipoleListChart`), and inside each chart ball the segment
  value is the line-integral piece (`intervalIntegral_form_eq_segPeriod` over the
  whole-piece subdivision `exists_subdivision_pieces`) — so
  `exists_arcWeakSolution_boundary_pairing` delivers `pairOmega 𝔇 W.σ α = π·∫_c α`
  (the honest constant: Forster's `2πi` against `dz̄∧dz`, i.e. `π` against Lebesgue
  area), and zero periods discharge the E2 pairing field.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.4–20.5; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VIII §4.
-/

open Complex Metric
open scoped Manifold ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Jacobians.Dolbeault

open FineResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The planar layer: the segment tube system -/

/-- **The segment tube system** (the planar geometry of Forster 20.5): for the segment
`[a, b]` inside the ball `B(c₀, R)`, a tube radius `δ` with the closed `δ`-tube inside the
ball, a smooth cutoff `ψ` (`≡ 1` on the closed half-tube, `≡ 0` off the open `δ`-tube) and
a smooth co-cutoff `θ` (`≡ 0` on the closed eighth-tube, `≡ 1` off the open quarter-tube).
`θ` kills the segment singularity of the slit logarithm (`Hfun` is globally smooth) and is
`≡ 1` wherever `∂̄ψ ≠ 0`. -/
structure SegTube (a b c₀ : ℂ) (R : ℝ) where
  /-- The tube radius. -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- The closed `δ`-tube lies inside the coordinate ball. -/
  tube_subset : cthickening δ (segment ℝ a b) ⊆ ball c₀ R
  /-- The cutoff. -/
  ψ : ℂ → ℝ
  /-- The co-cutoff. -/
  θ : ℂ → ℝ
  ψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ
  θ_smooth : ContDiff ℝ (⊤ : ℕ∞) θ
  ψ_one : Set.EqOn ψ 1 (cthickening (δ / 2) (segment ℝ a b))
  ψ_zero : Set.EqOn ψ 0 (thickening δ (segment ℝ a b))ᶜ
  θ_zero : Set.EqOn θ 0 (cthickening (δ / 8) (segment ℝ a b))
  θ_one : Set.EqOn θ 1 (thickening (δ / 4) (segment ℝ a b))ᶜ

/-- A segment tube system exists at any prescribed radius whose closed tube fits in the
ball: the two cutoffs from the smooth Urysohn lemma
(`exists_contMDiffMap_zero_one_of_isClosed` on the manifold `ℂ`). -/
theorem SegTube.exists_segTube_of_radius {a b c₀ : ℂ} {R δ : ℝ} (hδpos : 0 < δ)
    (hδsub : cthickening δ (segment ℝ a b) ⊆ ball c₀ R) :
    ∃ T : SegTube a b c₀ R, T.δ = δ := by
  -- the cutoff ψ: `0` off the open δ-tube, `1` on the closed half-tube
  obtain ⟨ψ, hψ0, hψ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) isOpen_thickening.isClosed_compl (isClosed_cthickening
      (δ := δ / 2) (E := segment ℝ a b))
    (disjoint_compl_left.mono_right
      (cthickening_subset_thickening' hδpos (by linarith) (segment ℝ a b)))
  -- the co-cutoff θ: `0` on the closed eighth-tube, `1` off the open quarter-tube
  obtain ⟨θ, hθ0, hθ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, ℂ)) (isClosed_cthickening (δ := δ / 8) (E := segment ℝ a b))
    (isOpen_thickening (δ := δ / 4) (E := segment ℝ a b)).isClosed_compl
    (disjoint_compl_right.mono_left
      (cthickening_subset_thickening' (by linarith) (by linarith) (segment ℝ a b)))
  exact ⟨{
    δ := δ
    δ_pos := hδpos
    tube_subset := hδsub
    ψ := ψ
    θ := θ
    ψ_smooth := contMDiff_iff_contDiff.mp ψ.contMDiff
    θ_smooth := contMDiff_iff_contDiff.mp θ.contMDiff
    ψ_one := hψ1
    ψ_zero := hψ0
    θ_zero := hθ0
    θ_one := hθ1 }, rfl⟩

/-- A segment tube system exists for any segment inside an open ball
(`IsCompact.exists_cthickening_subset_open` picks the radius). -/
theorem SegTube.exists_segTube {a b c₀ : ℂ} {R : ℝ}
    (hseg : segment ℝ a b ⊆ ball c₀ R) : Nonempty (SegTube a b c₀ R) := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_segment a b).exists_cthickening_subset_open isOpen_ball hseg
  obtain ⟨T, -⟩ := SegTube.exists_segTube_of_radius hδpos hδsub
  exact ⟨T⟩

/-- **Avoiding tube**: the tube radius can additionally be chosen so the closed tube misses
any prescribed finite planar set off the segment (shrink into the ball minus those points).
This is what lets a chain of arcs keep each tube's cutoff annulus away from all OTHER
endpoints: a foreign point ON the segment is automatically in the half-tube where the weak
solution is the holomorphic Möbius ratio, and a foreign point OFF the segment is now
outside the whole tube, where the weak solution is `≡ 1`. -/
theorem SegTube.exists_segTube_avoiding {a b c₀ : ℂ} {R : ℝ}
    (hseg : segment ℝ a b ⊆ ball c₀ R) (A : Finset ℂ) :
    ∃ T : SegTube a b c₀ R,
      ∀ q ∈ A, q ∉ segment ℝ a b → q ∉ cthickening T.δ (segment ℝ a b) := by
  have hopen : IsOpen (ball c₀ R ∩ ((↑A : Set ℂ) \ segment ℝ a b)ᶜ) :=
    isOpen_ball.inter (A.finite_toSet.subset Set.diff_subset).isClosed.isOpen_compl
  have hsub : segment ℝ a b ⊆ ball c₀ R ∩ ((↑A : Set ℂ) \ segment ℝ a b)ᶜ := fun z hz =>
    ⟨hseg hz, fun hzd => hzd.2 hz⟩
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_segment a b).exists_cthickening_subset_open hopen hsub
  obtain ⟨T, hTδ⟩ := SegTube.exists_segTube_of_radius hδpos
    (hδsub.trans Set.inter_subset_left)
  refine ⟨T, fun q hqA hqseg hqth => ?_⟩
  rw [hTδ] at hqth
  exact (hδsub hqth).2 ⟨Finset.mem_coe.mpr hqA, hqseg⟩

namespace SegTube

variable {a b c₀ : ℂ} {R : ℝ} (T : SegTube a b c₀ R)

/-- The cutoff, complex-valued. -/
def psiC : ℂ → ℂ := fun z => (T.ψ z : ℂ)

/-- The globally smooth logarithm weight `H = θ·log((z−b)/(z−a))`: the co-cutoff `θ` kills
the slit-segment singularity. -/
def Hfun : ℂ → ℂ := fun z => (T.θ z : ℂ) * slitLogRatio a b z

/-- **The Forster 20.5 one-disk weak solution**: the Möbius ratio `(z−b)/(z−a)` on the open
half-tube (across the segment), glued as `exp(ψ·log((z−b)/(z−a)))` off the segment;
`≡ 1` off the `δ`-tube. -/
def Ffun : ℂ → ℂ := fun z =>
  if z ∈ thickening (T.δ / 2) (segment ℝ a b) then (z - b) / (z - a)
  else Complex.exp (T.psiC z * slitLogRatio a b z)

theorem psiC_smooth : ContDiff ℝ (⊤ : ℕ∞) T.psiC :=
  Complex.ofRealCLM.contDiff.comp T.ψ_smooth

/-- The slit-segment logarithm is real-`C^∞` off the segment (holomorphic ⟹ analytic). -/
theorem contDiffAt_slitLogRatio_real {z : ℂ} (hz : z ∉ segment ℝ a b) :
    ContDiffAt ℝ (⊤ : ℕ∞) (slitLogRatio a b) z := by
  have hopen : IsOpen (segment ℝ a b)ᶜ := (isCompact_segment a b).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ (slitLogRatio a b) (segment ℝ a b)ᶜ := fun w hw =>
    (differentiableAt_slitLogRatio hw).differentiableWithinAt
  exact (((hdiff.analyticOnNhd hopen) z hz).restrictScalars (𝕜 := ℝ)).contDiffAt

theorem Hfun_smooth : ContDiff ℝ (⊤ : ℕ∞) T.Hfun := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ thickening (T.δ / 8) (segment ℝ a b)
  · -- near the segment, `θ ≡ 0` kills everything
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
    rw [Hfun, T.θ_zero (thickening_subset_cthickening _ _ hw)]
    simp
  · -- off the eighth-tube the slit logarithm is smooth
    have hzs : z ∉ segment ℝ a b := fun hmem =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ hmem)
    exact ((Complex.ofRealCLM.contDiff.comp T.θ_smooth).contDiffAt).mul
      (contDiffAt_slitLogRatio_real hzs)

/-- Off the segment, the weak solution is the exponential `exp(ψ·log)`. -/
theorem Ffun_eq_exp {z : ℂ} (hz : z ∉ segment ℝ a b) :
    T.Ffun z = Complex.exp (T.psiC z * slitLogRatio a b z) := by
  rw [Ffun]
  split_ifs with hmem
  · rw [psiC, T.ψ_one (thickening_subset_cthickening _ _ hmem)]
    simp only [Pi.one_apply, Complex.ofReal_one, one_mul]
    exact (exp_slitLogRatio hz).symm
  · rfl

/-- On the open half-tube (across the segment), the weak solution is the Möbius ratio. -/
theorem Ffun_eq_ratio {z : ℂ} (hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)) :
    T.Ffun z = (z - b) / (z - a) := if_pos hz

/-- Off the closed `δ`-tube, the weak solution is `1`. -/
theorem Ffun_eq_one {z : ℂ} (hz : z ∉ cthickening T.δ (segment ℝ a b)) :
    T.Ffun z = 1 := by
  have hzth : z ∉ thickening T.δ (segment ℝ a b) := fun h =>
    hz (thickening_subset_cthickening _ _ h)
  have hzs : z ∉ segment ℝ a b := fun h =>
    hzth (self_subset_thickening T.δ_pos _ h)
  rw [T.Ffun_eq_exp hzs, psiC, T.ψ_zero hzth]
  simp

/-- The weak solution is nonvanishing off the endpoints. -/
theorem Ffun_ne_zero {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) : T.Ffun z ≠ 0 := by
  rw [Ffun]
  split_ifs
  · exact div_ne_zero (sub_ne_zero.mpr hzb) (sub_ne_zero.mpr hza)
  · exact Complex.exp_ne_zero _

/-- The weak solution is real-differentiable off the pole `a` (even at the zero `b`). -/
theorem differentiableAt_Ffun {z : ℂ} (hza : z ≠ a) :
    DifferentiableAt ℝ T.Ffun z := by
  by_cases hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)
  · -- across the segment: the ratio is holomorphic at `z ≠ a`
    have hev : T.Ffun =ᶠ[𝓝 z] fun w => (w - b) / (w - a) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      exact T.Ffun_eq_ratio hw
    have hd : DifferentiableAt ℂ (fun w : ℂ => (w - b) / (w - a)) z :=
      (differentiableAt_id.sub_const b).div (differentiableAt_id.sub_const a)
        (sub_ne_zero.mpr hza)
    exact hev.differentiableAt_iff.mpr (hd.restrictScalars ℝ)
  · -- off the half-tube: the exponential of a smooth function
    have hzs : z ∉ segment ℝ a b := fun h =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ h)
    have hev : T.Ffun =ᶠ[𝓝 z]
        fun w => Complex.exp (T.psiC w * slitLogRatio a b w) := by
      filter_upwards [(isCompact_segment a b).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      exact T.Ffun_eq_exp hw
    have hv : DifferentiableAt ℝ (fun w => T.psiC w * slitLogRatio a b w) z :=
      (T.psiC_smooth.contDiffAt.differentiableAt (by simp)).mul
        ((contDiffAt_slitLogRatio_real hzs).differentiableAt (by simp))
    exact hev.differentiableAt_iff.mpr hv.cexp

/-- **The master planar `∂̄`-identity** (Forster 20.5): off the endpoints,
`∂̄F̃ = F̃·(H·∂̄ψ)`.  Across the segment both sides vanish (the ratio is holomorphic, the
cutoff locally constant); off the half-tube `θ ≡ 1` makes `H` the slit logarithm and the
chain rule on `exp(ψ·log)` produces exactly `F̃·log·∂̄ψ`. -/
theorem dbar_Ffun {z : ℂ} (hza : z ≠ a) :
    DbarDisk.dbar T.Ffun z = T.Ffun z * (T.Hfun z * DbarDisk.dbar T.psiC z) := by
  by_cases hz : z ∈ thickening (T.δ / 2) (segment ℝ a b)
  · -- across the segment: `∂̄(ratio) = 0` and `∂̄ψ = 0`
    have hev : T.Ffun =ᶠ[𝓝 z] fun w => (w - b) / (w - a) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      exact T.Ffun_eq_ratio hw
    have hL : DbarDisk.dbar T.Ffun z = 0 := by
      rw [dbar_congr_of_eventuallyEq hev]
      exact DbarDisk.dbar_eq_zero_of_differentiableAt
        ((differentiableAt_id.sub_const b).div (differentiableAt_id.sub_const a)
          (sub_ne_zero.mpr hza))
    have hψev : T.psiC =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
      filter_upwards [isOpen_thickening.mem_nhds hz] with w hw
      rw [psiC, T.ψ_one (thickening_subset_cthickening _ _ hw)]
      simp
    rw [hL, dbar_congr_of_eventuallyEq hψev, DbarDisk.dbar_const]
    ring
  · -- off the half-tube: chain rule on the exponential, `θ ≡ 1`
    have hzs : z ∉ segment ℝ a b := fun h =>
      hz (self_subset_thickening (by linarith [T.δ_pos]) _ h)
    have hθ1 : T.θ z = 1 := by
      refine T.θ_one fun h => hz (thickening_mono (by linarith [T.δ_pos]) _ h)
    have hev : T.Ffun =ᶠ[𝓝 z]
        fun w => Complex.exp (T.psiC w * slitLogRatio a b w) := by
      filter_upwards [(isCompact_segment a b).isClosed.isOpen_compl.mem_nhds hzs] with w hw
      exact T.Ffun_eq_exp hw
    have hψd : DifferentiableAt ℝ T.psiC z :=
      T.psiC_smooth.contDiffAt.differentiableAt (by simp)
    have hLd : DifferentiableAt ℝ (slitLogRatio a b) z :=
      (contDiffAt_slitLogRatio_real hzs).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ (fun w => T.psiC w * slitLogRatio a b w) z := hψd.mul hLd
    rw [dbar_congr_of_eventuallyEq hev, dbarFun_exp hv,
      dbarFun_mul' hψd hLd,
      DbarDisk.dbar_eq_zero_of_differentiableAt (differentiableAt_slitLogRatio hzs),
      ← T.Ffun_eq_exp hzs, Hfun, hθ1]
    push_cast
    ring

end SegTube

/-! ## The per-arc interface: the geometric fields of `RawLogDbarDatum`

`ArcWeakSolution 𝔇 D` is `RawLogDbarDatum` for a divisor `D` in place of a chain boundary,
*without* the E4 pairing field: exactly the geometric output of the per-arc construction.
The pairing identity enters only through `toRaw`, as an explicit hypothesis — the E2
constructor is **conditional on the pairing field** (E4 is its own rung). -/

/-- **The per-arc weak-solution datum** for a divisor `D`: the geometric fields of
`RawLogDbarDatum` (weak solution, global `(0,1)` datum, nonvanishing, chart-read
differentiability and logarithmic `∂̄`-identity off the support, endpoint normal forms) —
everything except the E4 pairing identity. -/
structure ArcWeakSolution (𝔇 : ChartDiskCover X) (D : Divisor X) where
  /-- The weak solution. -/
  F : X → ℂ
  /-- The global smooth `(0,1)` logarithmic datum. -/
  σ : ↥(OneFormsZeroOne X)
  /-- `F` is nonvanishing off the support of `D`. -/
  F_ne : ∀ x : X, D x = 0 → F x ≠ 0
  /-- Off the support, the cover-chart read of `F` is real-differentiable. -/
  diff_off : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
    DifferentiableAt ℝ (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w))
      (chartMap 𝔇 j x)
  /-- Off the support, the planar logarithmic `∂̄`-identity `∂̄F = F·σ̃` holds in every
  cover chart. -/
  dbar_eq : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
    DbarDisk.dbar (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
      = F x * 𝔇.cutoffPullback j (σ : SmoothCOneForms X) (chartMap 𝔇 j x)
  /-- The `(0,1)` datum vanishes (pointwise) at the support: the cutoff annulus carrying
  `∂̄ψ` stays away from the segment endpoints.  (Used by the chain fold: at a cancelling
  support point the folded `σ`'s stay zero, so the folded `∂̄`-identity survives.) -/
  σ_vanish : ∀ x : X, D x ≠ 0 → (σ : SmoothCOneForms X) x = 0
  /-- At each support point, the own-chart read of `F` has the local normal form
  `(z − a)^{D(a)}·(analytic nonvanishing unit)` — analytic (not merely continuous) because
  near its endpoints the weak solution is the Möbius ratio on the half-tube.  (Analyticity
  is what lets the chain fold cancel a zero of one arc against the pole of the next.) -/
  norm_form : ∀ a : X, D a ≠ 0 → ∃ w : ℂ → ℂ,
    AnalyticAt ℂ w ((chartAt (H := ℂ) a) a) ∧ w ((chartAt (H := ℂ) a) a) ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
      F ((chartAt (H := ℂ) a).symm z)
        = (z - (chartAt (H := ℂ) a) a) ^ (D a) * w z

/-- **The conditional E2/E3 constructor**: a per-arc weak solution for the boundary divisor
of a chain, *plus* the E4 pairing identity for its `σ`, yields the raw logarithmic-`∂̄`
datum (and hence, through `RawLogDbarDatum.toLogDbarDatum`, the full E2 interface).  The
pairing hypothesis is the one remaining E4 obligation. -/
def ArcWeakSolution.toRaw {𝔇 : ChartDiskCover X} {D : Divisor X}
    (W : ArcWeakSolution 𝔇 D) (c : SmoothOneChain X) (hD : c.boundary = D)
    (hpair : ∀ α : HolomorphicOneForms X,
      FineResidue.pairOmega 𝔇 W.σ α = 2 * (Real.pi : ℂ) * Complex.I * c.period α) :
    RawLogDbarDatum 𝔇 c := by
  subst hD
  exact {
    F := W.F
    σ := W.σ
    pairing := hpair
    F_ne := W.F_ne
    diff_off := W.diff_off
    dbar_eq := W.dbar_eq
    norm_form := fun x hx => by
      obtain ⟨w, hwa, hw0, hev⟩ := W.norm_form x hx
      exact ⟨w, hwa.continuousAt, hw0, hev⟩ }

/-! ## E3 — the per-arc lift: from the planar tube system to `ArcWeakSolution`

The lift of the planar Forster 20.5 data through one cover chart `j₀`: the weak solution
`F = F̃ ∘ e` (extended by `1` off the closed tube preimage `K`), the single-chart `(0,1)`
datum `σ = (lift H)·∂̄(lift ψ)` (the `exists_pairOmega_pos` support pattern), the chart-`j`
reads handled by the holomorphic transition `w = e_{j₀} ∘ e_j⁻¹` and the `∂̄` chain rule
`dbarDisk_comp_holo`, and the Möbius normal forms at the endpoints by `dslope` of the
biholomorphic transition from the endpoint's own chart. -/

section ArcLift

/-- `∂̄u` vanishes at any point where `u` is locally constant
(`mfderiv` congruence + `mfderiv_const`). -/
theorem dbarL_apply_eq_zero_of_eventuallyEq_const (u : SmoothCFunctions X) {x : X} {c : ℂ}
    (h : ⇑u =ᶠ[𝓝 x] fun _ => c) : dbarL u x = 0 := by
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) = 0
  rw [h.mfderiv_eq, mfderiv_const, map_zero]

variable (𝔇 : ChartDiskCover X) (j₀ : 𝔇.toFiniteCover.ι)

/-- On the cover disk, a chart lift reads back the planar function at the chart
coordinate (the disk bump is `1` there). -/
theorem chartLift_read_of_mem_U {G : ℂ → ℂ} {hG : ContDiff ℝ (⊤ : ℕ∞) G} {y : X}
    (hy : y ∈ (𝔇.U j₀ : Set X)) :
    chartLift 𝔇 j₀ G hG y = G (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) y) := by
  have hsrc : y ∈ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).source := 𝔇.subset_chart_source j₀ hy
  have hball : extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) y
      ∈ Metric.ball (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := hy
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have h := chartLift_symm_read 𝔇 j₀ (F := G) (hF := hG) hball
  rwa [(extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)).left_inv hsrc] at h

/-- **E3, the per-arc constructor** (Forster 20.5, lifted to the surface): two distinct
points `a ≠ b` of one cover disk carry an `ArcWeakSolution` for the divisor `(b) − (a)`:
the lifted tube weak solution `F = F̃ ∘ e` (extended by `1` off the tube preimage), the
single-chart `(0,1)` datum `σ = (lift H)·∂̄(lift ψ)`, the logarithmic `∂̄`-identity in every
cover chart, and analytic-unit Möbius normal forms `(z−·)^{±1}·unit` at the endpoints.

**Avoidance**: the tube additionally avoids any prescribed finite set `A` — at every
`q ∈ A` other than the pole `a`, the own-chart read of `F` is *analytic* and `σ` vanishes
(the tube's cutoff annulus misses `q`).  This is the tameness a chain fold needs at the
other arcs' endpoints. -/
theorem exists_arcWeakSolution_avoiding (A : Finset X) {a b : X}
    (ha : a ∈ (𝔇.U j₀ : Set X)) (hb : b ∈ (𝔇.U j₀ : Set X)) (hab : a ≠ b) :
    ∃ W : ArcWeakSolution 𝔇 (Finsupp.single b 1 - Finsupp.single a 1),
      (∀ α : HolomorphicOneForms X,
        FineResidue.pairOmega 𝔇 W.σ α
          = (Real.pi : ℂ) * segPeriod α (𝔇.center j₀) (chartMap 𝔇 j₀ a) (chartMap 𝔇 j₀ b)) ∧
      ∀ q ∈ A, q ≠ a →
        AnalyticAt ℂ (fun ζ => W.F ((chartAt (H := ℂ) q).symm ζ)) ((chartAt (H := ℂ) q) q)
        ∧ (W.σ : SmoothCOneForms X) q = 0 := by
  classical
  set e := extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀) with he
  set za := e a with hza
  set zb := e b with hzb
  set D : Divisor X := Finsupp.single b 1 - Finsupp.single a 1 with hD
  -- chart bookkeeping for the two endpoints
  have hasrc : a ∈ e.source := 𝔇.subset_chart_source j₀ ha
  have hbsrc : b ∈ e.source := 𝔇.subset_chart_source j₀ hb
  have haball : za ∈ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := ha
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have hbball : zb ∈ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := by
    have h := hb
    rw [𝔇.isDisk j₀] at h
    exact h.1
  have hzab : za ≠ zb := fun h => hab (e.injOn hasrc hbsrc h)
  -- the divisor values
  have hDa : D a = -1 := by
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_of_ne hab, Finsupp.single_eq_same]
    ring
  have hDb : D b = 1 := by
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hab)]
    ring
  have hsupp : ∀ x : X, D x ≠ 0 → x = a ∨ x = b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    refine hx ?_
    rw [hD, Finsupp.sub_apply, Finsupp.single_eq_of_ne hcon.2,
      Finsupp.single_eq_of_ne hcon.1, sub_zero]
  have hne_pts : ∀ {x : X}, D x = 0 → x ∈ e.source → e x ≠ za ∧ e x ≠ zb := by
    intro x hx0 hxsrc
    constructor
    · intro h
      have hxa : x = a := e.injOn hxsrc hasrc h
      rw [hxa, hDa] at hx0
      norm_num at hx0
    · intro h
      have hxb : x = b := e.injOn hxsrc hbsrc h
      rw [hxb, hDb] at hx0
      norm_num at hx0
  -- the planar tube
  have hseg : segment ℝ za zb ⊆ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) :=
    (convex_ball _ _).segment_subset haball hbball
  obtain ⟨T, hTavoid⟩ := SegTube.exists_segTube_avoiding hseg (A.image fun q => e q)
  -- the global data
  set ψl := chartLift 𝔇 j₀ T.psiC T.psiC_smooth with hψl
  set Hl := chartLift 𝔇 j₀ T.Hfun T.Hfun_smooth with hHl
  set σ₀ : SmoothCOneForms X := cSmulForm Hl (dbarL ψl) with hσ₀
  have hσmem : σ₀ ∈ OneFormsZeroOne X := cSmulForm_mem_zeroOne Hl (dbarL_mem_zeroOne ψl)
  set F : X → ℂ := fun x => if x ∈ (𝔇.U j₀ : Set X) then T.Ffun (e x) else 1 with hF
  set K : Set X := e.symm '' cthickening T.δ (segment ℝ za zb) with hK
  -- the tube preimage K: compact inside the cover disk
  have htube_ball : cthickening T.δ (segment ℝ za zb)
      ⊆ Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) := T.tube_subset
  have hKU : K ⊆ (𝔇.U j₀ : Set X) := by
    rintro y ⟨z, hz, rfl⟩
    exact symm_mem_U_of_mem_ball 𝔇 (htube_ball hz)
  have hKcl : IsClosed K := by
    refine IsCompact.isClosed ?_
    refine ((isCompact_segment za zb).cthickening).image_of_continuousOn ?_
    exact (continuousOn_extChartAt_symm (𝔇.center j₀)).mono fun z hz =>
      𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall (htube_ball hz))
  have hmemK : ∀ {y : X}, y ∈ e.source →
      e y ∈ cthickening T.δ (segment ℝ za zb) → y ∈ K :=
    fun {y} hysrc hyth => ⟨e y, hyth, e.left_inv hysrc⟩
  -- the reads on the cover disk
  have hψread : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → ψl y = T.psiC (e y) :=
    fun {y} hy => chartLift_read_of_mem_U 𝔇 j₀ hy
  have hHread : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → Hl y = T.Hfun (e y) :=
    fun {y} hy => chartLift_read_of_mem_U 𝔇 j₀ hy
  have hFU : ∀ {y : X}, y ∈ (𝔇.U j₀ : Set X) → F y = T.Ffun (e y) := by
    intro y hy
    simp only [hF, if_pos hy]
  -- `F ≡ 1` and `lift ψ ≡ 0` off the tube preimage
  have hFone : ∀ y ∉ K, F y = 1 := by
    intro y hyK
    rw [hF]
    dsimp only
    split_ifs with hyU
    · exact T.Ffun_eq_one fun hth => hyK (hmemK (𝔇.subset_chart_source j₀ hyU) hth)
    · rfl
  have hψzero : ∀ y ∉ K, ψl y = 0 := by
    intro y hyK
    by_contra hne
    rw [hψl] at hne
    obtain ⟨hysrc, hψ⟩ := chartLift_ne_zero 𝔇 hne
    have hysrc' : y ∈ e.source := by
      rw [he, extChartAt_source]
      exact hysrc
    have hyth : e y ∈ thickening T.δ (segment ℝ za zb) := by
      by_contra hth
      refine hψ ?_
      show ((T.ψ (e y) : ℝ) : ℂ) = 0
      rw [T.ψ_zero hth]
      simp
    exact hyK (hmemK hysrc' (thickening_subset_cthickening _ _ hyth))
  -- `lift ψ ≡ 1` near the segment preimage (kills `∂̄(lift ψ)` at the endpoints)
  have hψone_ev : ∀ {x : X}, x ∈ (𝔇.U j₀ : Set X) → e x ∈ segment ℝ za zb →
      ⇑ψl =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    intro x hxU hxseg
    have hxsrc : x ∈ e.source := 𝔇.subset_chart_source j₀ hxU
    have hcont : ContinuousAt e x := continuousAt_extChartAt' hxsrc
    have hth : e x ∈ thickening (T.δ / 2) (segment ℝ za zb) :=
      self_subset_thickening (by linarith [T.δ_pos]) _ hxseg
    filter_upwards [(𝔇.U j₀).isOpen.mem_nhds hxU,
      hcont.preimage_mem_nhds (isOpen_thickening.mem_nhds hth)] with y hyU hyth
    rw [hψread hyU]
    show ((T.ψ (e y) : ℝ) : ℂ) = 1
    rw [T.ψ_one (thickening_subset_cthickening _ _ hyth)]
    simp
  -- σ vanishes at the support
  have hσsupp : ∀ x : X, D x ≠ 0 → σ₀ x = 0 := by
    intro x hx
    have hxU : x ∈ (𝔇.U j₀ : Set X) := by
      rcases hsupp x hx with rfl | rfl
      exacts [ha, hb]
    have hxseg : e x ∈ segment ℝ za zb := by
      rcases hsupp x hx with rfl | rfl
      · exact left_mem_segment ℝ za zb
      · exact right_mem_segment ℝ za zb
    have hdb : dbarL ψl x = 0 :=
      dbarL_apply_eq_zero_of_eventuallyEq_const ψl (hψone_ev hxU hxseg)
    rw [hσ₀, cSmulForm_apply, hdb]
    module
  -- F is nonvanishing off the support
  have hFne : ∀ x : X, D x = 0 → F x ≠ 0 := by
    intro x hx0
    by_cases hxU : x ∈ (𝔇.U j₀ : Set X)
    · rw [hFU hxU]
      obtain ⟨hexa, hexb⟩ := hne_pts hx0 (𝔇.subset_chart_source j₀ hxU)
      exact T.Ffun_ne_zero hexa hexb
    · rw [hF]
      simp [hxU]
  -- the chart-j differentiability of the read, off the support
  have hdiff : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
      DifferentiableAt ℝ (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w))
        (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmx : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmc : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    by_cases hxK : x ∈ K
    · -- on the tube: the read is `F̃ ∘ (holomorphic transition)`
      have hxU0 : x ∈ (𝔇.U j₀ : Set X) := hKU hxK
      have hxsrc0 : x ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hxU0
      set w : ℂ → ℂ := (chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ (𝔇.center j)).symm with hw
      have hwz : w (chartMap 𝔇 j x) = e x := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) = e x
        rw [hsymmx]
        rfl
      have hwan : AnalyticAt ℂ w (chartMap 𝔇 j x) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ (𝔇.center j))
          (chart_mem_atlas ℂ (𝔇.center j₀)) hxsrcj hxsrc0
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.Ffun ∘ w := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact (𝔇.U j₀).isOpen.mem_nhds hxU0)] with ζ hζ
        rw [hFU hζ]
        rfl
      have hFd : DifferentiableAt ℝ T.Ffun (w (chartMap 𝔇 j x)) := by
        rw [hwz]
        exact T.differentiableAt_Ffun (hne_pts hx0 (𝔇.subset_chart_source j₀ hxU0)).1
      exact hevF.differentiableAt_iff.mpr
        (hFd.comp _ (hwan.differentiableAt.restrictScalars ℝ))
    · -- off the tube: the read is locally `1`
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hFone _ hζ
      exact hevF.differentiableAt_iff.mpr (differentiableAt_const _)
  -- the chart-j logarithmic ∂̄-identity, off the support
  have hdbar : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → D x = 0 →
      DbarDisk.dbar (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
        = F x * 𝔇.cutoffPullback j σ₀ (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmx : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmc : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    -- the cutoff pullback of σ₀ collapses to `Hl x · ∂̄(read of lift ψ)`
    have hsymmx' : (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).left_inv (𝔇.subset_chart_source j hxU)
    have hcut : 𝔇.cutoffPullback j σ₀ (chartMap 𝔇 j x)
        = Hl x * DbarDisk.dbar (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
            (chartMap 𝔇 j x) := by
      rw [hσ₀, cutoffPullback_cSmulForm, hsymmx', cutoffPullback_dbarL 𝔇 hxU]
    by_cases hxK : x ∈ K
    · -- on the tube: transition chain rule + the planar master identity
      have hxU0 : x ∈ (𝔇.U j₀ : Set X) := hKU hxK
      have hxsrc0 : x ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hxU0
      obtain ⟨hexa, hexb⟩ := hne_pts hx0 (𝔇.subset_chart_source j₀ hxU0)
      set w : ℂ → ℂ := (chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ (𝔇.center j)).symm with hw
      have hwz : w (chartMap 𝔇 j x) = e x := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) = e x
        rw [hsymmx]
        rfl
      have hwan : AnalyticAt ℂ w (chartMap 𝔇 j x) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ (𝔇.center j))
          (chart_mem_atlas ℂ (𝔇.center j₀)) hxsrcj hxsrc0
      have hwd : DifferentiableAt ℂ w (chartMap 𝔇 j x) := hwan.differentiableAt
      have hevU : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j x),
          (chartAt ℂ (𝔇.center j)).symm ζ ∈ (𝔇.U j₀ : Set X) :=
        hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact (𝔇.U j₀).isOpen.mem_nhds hxU0)
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.Ffun ∘ w := by
        filter_upwards [hevU] with ζ hζ
        rw [hFU hζ]
        rfl
      have hevψ : (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] T.psiC ∘ w := by
        filter_upwards [hevU] with ζ hζ
        rw [hψread hζ]
        rfl
      have hFd : DifferentiableAt ℝ T.Ffun (w (chartMap 𝔇 j x)) := by
        rw [hwz]
        exact T.differentiableAt_Ffun hexa
      have hψd : DifferentiableAt ℝ T.psiC (w (chartMap 𝔇 j x)) :=
        T.psiC_smooth.contDiffAt.differentiableAt (by simp)
      rw [dbar_congr_of_eventuallyEq hevF, dbarDisk_comp_holo _ _ _ hFd hwd,
        hcut, dbar_congr_of_eventuallyEq hevψ, dbarDisk_comp_holo _ _ _ hψd hwd,
        hwz, T.dbar_Ffun hexa, hFU hxU0, hHread hxU0]
      ring
    · -- off the tube: both sides vanish
      have hevF : (fun ζ => F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hFone _ hζ
      have hevψ : (fun ζ => ψl ((chartAt ℂ (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun _ => (0 : ℂ) := by
        filter_upwards [hsymmc.preimage_mem_nhds
          (by rw [hsymmx]; exact hKcl.isOpen_compl.mem_nhds hxK)] with ζ hζ
        exact hψzero _ hζ
      rw [dbar_congr_of_eventuallyEq hevF, hcut, dbar_congr_of_eventuallyEq hevψ,
        DbarDisk.dbar_const, DbarDisk.dbar_const, mul_zero, mul_zero]
  -- the endpoint normal forms (Möbius, with analytic units)
  have hnorm : ∀ p : X, D p ≠ 0 → ∃ wp : ℂ → ℂ,
      AnalyticAt ℂ wp ((chartAt (H := ℂ) p) p) ∧ wp ((chartAt (H := ℂ) p) p) ≠ 0 ∧
      ∀ᶠ ζ in 𝓝[≠] ((chartAt (H := ℂ) p) p),
        F ((chartAt (H := ℂ) p).symm ζ) = (ζ - (chartAt (H := ℂ) p) p) ^ (D p) * wp ζ := by
    intro p hp
    -- shared transition data at the endpoint's own chart
    have hpU : p ∈ (𝔇.U j₀ : Set X) := by
      rcases hsupp p hp with rfl | rfl
      exacts [ha, hb]
    have hpsrc0 : p ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hpU
    have hpsrc : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
    have hsymmp : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
      (chartAt ℂ p).left_inv hpsrc
    have hva : AnalyticAt ℂ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p) :=
      analyticAt_atlasTransition (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ (𝔇.center j₀))
        hpsrc hpsrc0
    have hvζ : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = e p := by
      show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ p).symm ((chartAt ℂ p) p)) = e p
      rw [hsymmp]
      rfl
    have hq : AnalyticAt ℂ (dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p)) ((chartAt ℂ p) p) := by
      obtain ⟨pser, hpser⟩ := id hva
      exact hpser.has_fpower_series_dslope_fslope.analyticAt
    have hdv : deriv ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ≠ 0 := by
      have h := deriv_chartTransition_ne_zero (𝔇.center j₀) p (𝔇.subset_chart_source j₀ hpU)
      have hfe : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
          = (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j₀)) ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm := by
        funext zz
        simp [mfld_simps]
      have hpe : ((chartAt ℂ p) p : ℂ) = extChartAt 𝓘(ℝ, ℂ) p p := by
        simp [mfld_simps]
      rw [hfe, hpe]
      exact h
    have hq0 : dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
        ((chartAt ℂ p) p) ((chartAt ℂ p) p) ≠ 0 := by
      rw [dslope_same]
      exact hdv
    have hsymmc : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source hpsrc)
    have hmemU : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
        (chartAt ℂ p).symm ζ ∈ (𝔇.U j₀ : Set X) := by
      refine hsymmc.preimage_mem_nhds ((𝔇.U j₀).isOpen.mem_nhds ?_)
      rw [hsymmp]
      exact hpU
    have hqne : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
        dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ ≠ 0 :=
      hq.continuousAt.eventually_ne hq0
    have hvread : ∀ {ζ : ℂ}, (chartAt ℂ p).symm ζ ∈ (𝔇.U j₀ : Set X) →
        F ((chartAt ℂ p).symm ζ)
          = T.Ffun (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ) := by
      intro ζ hζ
      rw [hFU hζ]
      rfl
    rcases hsupp p hp with rfl | rfl
    · -- the pole endpoint (`D p = −1`):  F = (ζ−ζ₀)⁻¹ · (v−zb)/dslope
      have hvζa : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = za := by
        rw [hza]
        exact hvζ
      have hmemHT : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
          ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ
            ∈ thickening (T.δ / 2) (segment ℝ za zb) := by
        refine hva.continuousAt.preimage_mem_nhds (isOpen_thickening.mem_nhds ?_)
        rw [hvζa]
        exact self_subset_thickening (by linarith [T.δ_pos]) _ (left_mem_segment ℝ za zb)
      refine ⟨fun ζ => (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - zb)
          / dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ,
        (hva.sub analyticAt_const).div hq hq0, ?_, ?_⟩
      · dsimp only
        rw [dslope_same, hvζa]
        exact div_ne_zero (sub_ne_zero.mpr hzab) hdv
      · filter_upwards [self_mem_nhdsWithin, hmemU.filter_mono nhdsWithin_le_nhds,
          hmemHT.filter_mono nhdsWithin_le_nhds, hqne.filter_mono nhdsWithin_le_nhds]
          with ζ hζne hζU hζT hζq
        have hζne' : ζ ≠ (chartAt ℂ p) p := hζne
        have hsub : ζ - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr hζne'
        rw [hvread hζU, T.Ffun_eq_ratio hζT, hDa, zpow_neg_one]
        have hvza : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - za
            = (ζ - (chartAt ℂ p) p)
              * dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ := by
          rw [dslope_of_ne _ hζne', slope_def_field, hvζa]
          field_simp [hsub]
        rw [hvza]
        field_simp [hsub, hζq]
    · -- the zero endpoint (`D p = 1`):  F = (ζ−ζ₀) · dslope/(v−za)
      have hvζb : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = zb := by
        rw [hzb]
        exact hvζ
      have hmemHT : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p),
          ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ
            ∈ thickening (T.δ / 2) (segment ℝ za zb) := by
        refine hva.continuousAt.preimage_mem_nhds (isOpen_thickening.mem_nhds ?_)
        rw [hvζb]
        exact self_subset_thickening (by linarith [T.δ_pos]) _ (right_mem_segment ℝ za zb)
      refine ⟨fun ζ => dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm)
            ((chartAt ℂ p) p) ζ
          / (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - za),
        hq.div (hva.sub analyticAt_const)
          (by rw [hvζb]; exact sub_ne_zero.mpr (Ne.symm hzab)), ?_, ?_⟩
      · dsimp only
        rw [dslope_same, hvζb]
        exact div_ne_zero hdv (sub_ne_zero.mpr (Ne.symm hzab))
      · filter_upwards [self_mem_nhdsWithin, hmemU.filter_mono nhdsWithin_le_nhds,
          hmemHT.filter_mono nhdsWithin_le_nhds]
          with ζ hζne hζU hζT
        have hζne' : ζ ≠ (chartAt ℂ p) p := hζne
        have hsub : ζ - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr hζne'
        rw [hvread hζU, T.Ffun_eq_ratio hζT, hDb, zpow_one]
        have hvzb : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ζ - zb
            = (ζ - (chartAt ℂ p) p)
              * dslope ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ζ := by
          rw [dslope_of_ne _ hζne', slope_def_field, hvζb]
          field_simp [hsub]
        rw [hvzb]
        ring
  -- E4 pairing value: collapse to chart `j₀` and apply the planar atom
  have hσK : ∀ y, y ∉ K → σ₀ y = 0 := by
    intro y hyK
    have hψ0ev : ⇑ψl =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [hKcl.isOpen_compl.mem_nhds hyK] with y' hy'
      exact hψzero y' hy'
    have hdb : dbarL ψl y = 0 := dbarL_apply_eq_zero_of_eventuallyEq_const ψl hψ0ev
    rw [hσ₀, cSmulForm_apply, hdb]
    module
  have hpair : ∀ α : HolomorphicOneForms X,
      FineResidue.pairOmega 𝔇 (⟨σ₀, hσmem⟩ : ↥(OneFormsZeroOne X)) α
        = (Real.pi : ℂ) * segPeriod α (𝔇.center j₀) za zb := by
    intro α
    set g : ℂ → ℂ := omegaCoeff 𝔇 α j₀ with hgdef
    set ballc := Metric.ball (e (𝔇.center j₀)) (𝔇.radius j₀) with hballc
    have hball_tgt : ∀ {w : ℂ}, w ∈ ballc → w ∈ e.target := fun {w} hw =>
      𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall hw)
    have hchart_tgt : ∀ {w : ℂ}, w ∈ ballc → w ∈ (chartAt ℂ (𝔇.center j₀)).target := by
      intro w hw
      have hyU : e.symm w ∈ (𝔇.U j₀ : Set X) := symm_mem_U_of_mem_ball 𝔇 hw
      have h := (chartAt ℂ (𝔇.center j₀)).map_source (mem_chartSource_of_mem_U 𝔇 hyU)
      rwa [show (chartAt ℂ (𝔇.center j₀)) (e.symm w) = w from e.right_inv (hball_tgt hw)] at h
    -- `∂̄ψ` vanishes off the closed tube
    have hψ_supp0 : ∀ {w : ℂ}, w ∉ cthickening T.δ (segment ℝ za zb) →
        DbarDisk.dbar T.psiC w = 0 := by
      intro w hw
      refine dbar_eq_zero_of_eventuallyEq_const (c := 0) ?_
      filter_upwards [(isClosed_cthickening).isOpen_compl.mem_nhds hw] with w' hw'
      show ((T.ψ w' : ℝ) : ℂ) = 0
      rw [T.ψ_zero fun hth => hw' (thickening_subset_cthickening _ _ hth)]
      simp
    -- pointwise: the chart-`j₀` integrand is `Hfun·∂̄ψ·g`
    have hpt : ∀ z, pairCoeff 𝔇 σ₀ (omegaCoeff 𝔇 α) j₀ z
        = T.Hfun z * DbarDisk.dbar T.psiC z * g z := by
      intro z
      by_cases hzc : z ∈ ballc
      · have hyU : e.symm z ∈ (𝔇.U j₀ : Set X) := symm_mem_U_of_mem_ball 𝔇 hzc
        have hzx' : chartMap 𝔇 j₀ (e.symm z) = z := e.right_inv (hball_tgt hzc)
        have hHread' : Hl (e.symm z) = T.Hfun z := chartLift_symm_read 𝔇 j₀ hzc
        have hcut : 𝔇.cutoffPullback j₀ σ₀ z
            = T.Hfun z * 𝔇.cutoffPullback j₀ (dbarL ψl) z := by
          rw [hσ₀, cutoffPullback_cSmulForm]
          congr 1
        have hcdb : 𝔇.cutoffPullback j₀ (dbarL ψl) z = DbarDisk.dbar T.psiC z := by
          have h1 := cutoffPullback_dbarL 𝔇 (u := ψl) hyU
          rw [hzx'] at h1
          rw [h1]
          have hev : (fun ζ => ψl ((chartAt ℂ (𝔇.center j₀)).symm ζ))
              =ᶠ[𝓝 z] T.psiC := by
            filter_upwards [Metric.isOpen_ball.mem_nhds hzc] with ζ hζc
            exact chartLift_symm_read 𝔇 j₀ hζc
          exact dbar_congr_of_eventuallyEq hev
        rw [pairCoeff_apply, hcut, hcdb]
      · have hzth : z ∉ cthickening T.δ (segment ℝ za zb) := fun hc => hzc (htube_ball hc)
        have hcut0 : 𝔇.cutoffPullback j₀ σ₀ z = 0 := by
          by_contra hne
          obtain ⟨hztgt, hzS⟩ := cutoffPullback_ne_zero 𝔇 hσK hne
          obtain ⟨w', hw', heq⟩ := hzS
          have hw't : w' ∈ e.target :=
            𝔇.closedBall_subset_target j₀
              (Metric.ball_subset_closedBall (htube_ball hw'))
          have hzw : z = w' := by
            have h1 : e (e.symm z) = z := e.right_inv hztgt
            have h2 : e (e.symm w') = w' := e.right_inv hw't
            rw [← h1, ← heq]
            exact h2
          exact hzc (hzw ▸ htube_ball hw')
        rw [pairCoeff_apply, hcut0, zero_mul, hψ_supp0 hzth]
        ring
    -- the planar atom hypotheses
    have hψcsupp : HasCompactSupport T.psiC := by
      refine HasCompactSupport.intro (K := cthickening T.δ (segment ℝ za zb))
        ((isCompact_segment za zb).cthickening) ?_
      intro w hw
      show ((T.ψ w : ℝ) : ℂ) = 0
      rw [T.ψ_zero fun hth => hw (thickening_subset_cthickening _ _ hth)]
      simp
    have hψUsub : tsupport T.psiC ⊆ ballc := by
      have hsupp_sub : Function.support T.psiC ⊆ thickening T.δ (segment ℝ za zb) := by
        intro w hw
        by_contra hth
        refine hw ?_
        show ((T.ψ w : ℝ) : ℂ) = 0
        rw [T.ψ_zero hth]
        simp
      calc tsupport T.psiC
          ⊆ closure (thickening T.δ (segment ℝ za zb)) := closure_mono hsupp_sub
        _ ⊆ cthickening T.δ (segment ℝ za zb) := closure_thickening_subset_cthickening _ _
        _ ⊆ ballc := htube_ball
    have hψ1 : Set.EqOn T.psiC 1 (thickening (T.δ / 2) (segment ℝ za zb)) := by
      intro w hw
      show ((T.ψ w : ℝ) : ℂ) = 1
      rw [T.ψ_one (thickening_subset_cthickening _ _ hw)]
      simp
    have hHθ : ∀ ζ, DbarDisk.dbar T.psiC ζ ≠ 0 → T.Hfun ζ = slitLogRatio za zb ζ := by
      intro ζ hζ
      have hζth : ζ ∉ thickening (T.δ / 2) (segment ℝ za zb) := by
        intro hth
        refine hζ (dbar_eq_zero_of_eventuallyEq_const (c := 1) ?_)
        filter_upwards [isOpen_thickening.mem_nhds hth] with w hw
        exact hψ1 hw
      have hζ4 : ζ ∉ thickening (T.δ / 4) (segment ℝ za zb) := fun h4 =>
        hζth (thickening_mono (by linarith [T.δ_pos]) _ h4)
      show ((T.θ ζ : ℝ) : ℂ) * slitLogRatio za zb ζ = slitLogRatio za zb ζ
      rw [T.θ_one hζ4]
      simp
    have hgdiff : DifferentiableOn ℂ g ballc := fun w hw =>
      (coeffAt_analyticAt α (𝔇.center j₀)
        (hchart_tgt hw)).differentiableAt.differentiableWithinAt
    rw [pairOmega_apply,
      resIntegral_pairElem_of_support 𝔇 hσmem (isOneZeroCoeff_omegaCoeff 𝔇 α) hKcl hKU hσK,
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_slitLog_dbar_mul (by linarith [T.δ_pos] : (0 : ℝ) < T.δ / 2)
        Metric.isOpen_ball T.psiC_smooth hψcsupp hψUsub hψ1 hHθ hgdiff,
      segPeriod, mul_assoc]
    simp only [hgdef, omegaCoeff_apply]
  -- assemble, then discharge the avoidance conclusions
  refine ⟨{
    F := F
    σ := ⟨σ₀, hσmem⟩
    F_ne := hFne
    diff_off := hdiff
    dbar_eq := hdbar
    σ_vanish := hσsupp
    norm_form := hnorm }, hpair, ?_⟩
  intro q hqA hqa
  have hsymmq : (chartAt ℂ q).symm ((chartAt ℂ q) q) = q :=
    (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
  have hsymmcq : ContinuousAt (chartAt ℂ q).symm ((chartAt ℂ q) q) :=
    (chartAt ℂ q).continuousAt_symm ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
  by_cases hqK : q ∈ K
  · -- in the tube preimage: avoidance forces `e q` ON the segment, where `F` is the ratio
    have hqU : q ∈ (𝔇.U j₀ : Set X) := hKU hqK
    have hqsrc : q ∈ e.source := 𝔇.subset_chart_source j₀ hqU
    have hqth : e q ∈ cthickening T.δ (segment ℝ za zb) := by
      obtain ⟨z', hz', hzq⟩ := hqK
      have hz't : z' ∈ e.target :=
        𝔇.closedBall_subset_target j₀ (Metric.ball_subset_closedBall (htube_ball hz'))
      have heq : e q = z' := by
        rw [← hzq]
        exact e.right_inv hz't
      rwa [heq]
    have hqseg : e q ∈ segment ℝ za zb := by
      by_contra hqs
      exact hTavoid (e q) (Finset.mem_image_of_mem _ hqA) hqs hqth
    have hqea : e q ≠ za := fun h => hqa (e.injOn hqsrc hasrc h)
    constructor
    · -- the read is the Möbius ratio of the holomorphic transition
      have hτa : AnalyticAt ℂ ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm)
          ((chartAt ℂ q) q) :=
        analyticAt_atlasTransition (chart_mem_atlas ℂ q) (chart_mem_atlas ℂ (𝔇.center j₀))
          (mem_chart_source ℂ q) (mem_chartSource_of_mem_U 𝔇 hqU)
      have hτq : ((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) = e q := by
        show (chartAt ℂ (𝔇.center j₀)) ((chartAt ℂ q).symm ((chartAt ℂ q) q)) = e q
        rw [hsymmq]
        rfl
      have hread_an : AnalyticAt ℂ
          (fun ζ => (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ζ - zb)
            / (((chartAt ℂ (𝔇.center j₀)) ∘ (chartAt ℂ q).symm) ζ - za)) ((chartAt ℂ q) q) :=
        (hτa.sub analyticAt_const).div (hτa.sub analyticAt_const)
          (by rw [hτq]; exact sub_ne_zero.mpr hqea)
      refine hread_an.congr ?_
      have hth2 : e q ∈ thickening (T.δ / 2) (segment ℝ za zb) :=
        self_subset_thickening (by linarith [T.δ_pos]) _ hqseg
      filter_upwards [hsymmcq.preimage_mem_nhds
          (by rw [hsymmq]; exact (𝔇.U j₀).isOpen.mem_nhds hqU),
        hτa.continuousAt.preimage_mem_nhds
          (by rw [hτq]; exact isOpen_thickening.mem_nhds hth2)] with ζ hζU hζT
      rw [hFU hζU, ← T.Ffun_eq_ratio hζT]
      rfl
    · -- `lift ψ ≡ 1` near the segment kills `∂̄(lift ψ)` at `q`
      have hdb : dbarL ψl q = 0 :=
        dbarL_apply_eq_zero_of_eventuallyEq_const ψl (hψone_ev hqU hqseg)
      show σ₀ q = 0
      rw [hσ₀, cSmulForm_apply, hdb]
      module
  · -- off the tube preimage: `F ≡ 1`, `lift ψ ≡ 0` near `q`
    constructor
    · have hev : (fun ζ => F ((chartAt (H := ℂ) q).symm ζ))
          =ᶠ[𝓝 ((chartAt ℂ q) q)] fun _ => (1 : ℂ) := by
        filter_upwards [hsymmcq.preimage_mem_nhds
          (by rw [hsymmq]; exact hKcl.isOpen_compl.mem_nhds hqK)] with ζ hζ
        exact hFone _ hζ
      exact analyticAt_const.congr hev.symm
    · have hψ0ev : ⇑ψl =ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hqK] with y hy
        exact hψzero y hy
      have hdb : dbarL ψl q = 0 := dbarL_apply_eq_zero_of_eventuallyEq_const ψl hψ0ev
      show σ₀ q = 0
      rw [hσ₀, cSmulForm_apply, hdb]
      module

/-- **E3, the per-arc constructor** (plain form, no avoidance set). -/
theorem exists_arcWeakSolution {a b : X} (ha : a ∈ (𝔇.U j₀ : Set X))
    (hb : b ∈ (𝔇.U j₀ : Set X)) (hab : a ≠ b) :
    Nonempty (ArcWeakSolution 𝔇 (Finsupp.single b 1 - Finsupp.single a 1)) := by
  obtain ⟨W, -, -⟩ := exists_arcWeakSolution_avoiding 𝔇 j₀ ∅ ha hb hab
  exact ⟨W⟩

end ArcLift

/-! ## The chain fold: multiplying arc solutions

The product of two weak-solution data, with the zero of one arc cancelling the pole of the
next at shared boundary points.  The product `F₁·F₂` is patched at cancellation points by
the product of the analytic normal-form units (the pointwise product is `0·junk` there);
the `(0,1)` data add.  At *mixed* support points (in the support of one divisor only) the
other arc must be tame — `TameAt`, exactly what `exists_arcWeakSolution_avoiding`
guarantees at every avoided point. -/

section ChainFold

variable {𝔇 : ChartDiskCover X}

/-- **Tameness** of a weak-solution datum at a point: the own-chart read of `F` is
analytic and `σ` vanishes there.  Holds at every avoided point of
`exists_arcWeakSolution_avoiding`; the fold hypothesis at the other factor's support. -/
def ArcWeakSolution.TameAt {D : Divisor X} (W : ArcWeakSolution 𝔇 D) (q : X) : Prop :=
  AnalyticAt ℂ (fun ζ => W.F ((chartAt (H := ℂ) q).symm ζ)) ((chartAt (H := ℂ) q) q)
    ∧ (W.σ : SmoothCOneForms X) q = 0

/-- A section vanishing at the surface point has vanishing cutoff pullback at the
corresponding planar point. -/
theorem cutoffPullback_apply_eq_zero {σ : SmoothCOneForms X} {j : 𝔇.toFiniteCover.ι}
    {z : ℂ} (h : σ ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z) = 0) :
    𝔇.cutoffPullback j σ z = 0 := by
  show ((𝔇.diskBump j) z : ℝ) •
    (σ ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z))
      ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) (𝔇.center j))
        ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm z)) (1 : ℂ)) = 0
  rw [h]
  simp

/-- **The binary chain fold** (Forster §20.5, the product over the chain): the product of
two weak-solution data is a weak-solution datum for the divisor sum.  `F = F₁·F₂` patched
at cancellation points by the product of the analytic units, `σ = σ₁ + σ₂`.  Each factor
must be tame (`TameAt`) at the support points it does not share with the other.

The construction also **propagates tameness** — the invariant the full chain fold carries
along a dipole list: at any off-support point of the sum where each factor is tame
wherever its own divisor vanishes, the product is tame.  At a shared cancellation point
this holds *unconditionally*, via the patched analytic continuation transported into the
point's own chart (`analyticAt_chartRead_transfer`). -/
theorem ArcWeakSolution.exists_mul {D₁ D₂ : Divisor X}
    (W₁ : ArcWeakSolution 𝔇 D₁) (W₂ : ArcWeakSolution 𝔇 D₂)
    (h₁ : ∀ x, D₂ x ≠ 0 → D₁ x = 0 → W₁.TameAt x)
    (h₂ : ∀ x, D₁ x ≠ 0 → D₂ x = 0 → W₂.TameAt x) :
    ∃ W : ArcWeakSolution 𝔇 (D₁ + D₂),
      W.σ = W₁.σ + W₂.σ ∧
      ∀ q : X, (D₁ + D₂) q = 0 → (D₁ q = 0 → W₁.TameAt q) → (D₂ q = 0 → W₂.TameAt q) →
        W.TameAt q := by
  classical
  -- the cancellation (patch) set: finite, closed
  set P : Set X := {x | D₁ x ≠ 0 ∧ D₁ x + D₂ x = 0} with hP
  have hPfin : P.Finite :=
    D₁.support.finite_toSet.subset fun x hx => Finsupp.mem_support_iff.mpr hx.1
  have hPcl : IsClosed P := hPfin.isClosed
  have hD2ne : ∀ {x : X}, D₁ x ≠ 0 → D₁ x + D₂ x = 0 → D₂ x ≠ 0 := by
    intro x hx1 hsum hx2
    rw [hx2, add_zero] at hsum
    exact hx1 hsum
  have hsum_apply : ∀ x : X, (D₁ + D₂) x = D₁ x + D₂ x := fun x => Finsupp.add_apply D₁ D₂ x
  -- the patched product
  set Fp : X → ℂ := fun x =>
    if h : D₁ x ≠ 0 ∧ D₁ x + D₂ x = 0 then
      (W₁.norm_form x h.1).choose ((chartAt (H := ℂ) x) x)
        * (W₂.norm_form x (hD2ne h.1 h.2)).choose ((chartAt (H := ℂ) x) x)
    else W₁.F x * W₂.F x
    with hFp
  have hFp_off : ∀ {x : X}, x ∉ P → Fp x = W₁.F x * W₂.F x := by
    intro x hx
    rw [hFp]
    exact dif_neg hx
  have hFp_on : ∀ {x : X} (hx1 : D₁ x ≠ 0) (hx0 : D₁ x + D₂ x = 0),
      Fp x = (W₁.norm_form x hx1).choose ((chartAt (H := ℂ) x) x)
        * (W₂.norm_form x (hD2ne hx1 hx0)).choose ((chartAt (H := ℂ) x) x) := by
    intro x hx1 hx0
    rw [hFp]
    exact dif_pos ⟨hx1, hx0⟩
  -- the added (0,1) datum
  set σs : ↥(OneFormsZeroOne X) := W₁.σ + W₂.σ with hσs
  have hσs_apply : ∀ x : X, (σs : SmoothCOneForms X) x
      = (W₁.σ : SmoothCOneForms X) x + (W₂.σ : SmoothCOneForms X) x := by
    intro x
    rw [hσs]
    simp only [Submodule.coe_add, ContMDiffSection.coe_add, Pi.add_apply]
  -- F_ne
  have hFne : ∀ x : X, (D₁ + D₂) x = 0 → Fp x ≠ 0 := by
    intro x hx0
    rw [hsum_apply] at hx0
    by_cases hx1 : D₁ x = 0
    · have hx2 : D₂ x = 0 := by rwa [hx1, zero_add] at hx0
      have hxP : x ∉ P := fun h => h.1 hx1
      rw [hFp_off hxP]
      exact mul_ne_zero (W₁.F_ne x hx1) (W₂.F_ne x hx2)
    · rw [hFp_on hx1 hx0]
      exact mul_ne_zero (W₁.norm_form x hx1).choose_spec.2.1
        (W₂.norm_form x (hD2ne hx1 hx0)).choose_spec.2.1
  -- σ_vanish
  have hσvan : ∀ x : X, (D₁ + D₂) x ≠ 0 → (σs : SmoothCOneForms X) x = 0 := by
    intro x hx
    rw [hsum_apply] at hx
    have hσ1 : (W₁.σ : SmoothCOneForms X) x = 0 := by
      by_cases hx1 : D₁ x = 0
      · have hx2 : D₂ x ≠ 0 := fun h => hx (by rw [hx1, h, add_zero])
        exact (h₁ x hx2 hx1).2
      · exact W₁.σ_vanish x hx1
    have hσ2 : (W₂.σ : SmoothCOneForms X) x = 0 := by
      by_cases hx2 : D₂ x = 0
      · have hx1 : D₁ x ≠ 0 := fun h => hx (by rw [h, hx2, add_zero])
        exact (h₂ x hx1 hx2).2
      · exact W₂.σ_vanish x hx2
    rw [hσs_apply x, hσ1, hσ2, add_zero]
  -- norm_form
  have hnorm : ∀ p : X, (D₁ + D₂) p ≠ 0 → ∃ w : ℂ → ℂ,
      AnalyticAt ℂ w ((chartAt (H := ℂ) p) p) ∧ w ((chartAt (H := ℂ) p) p) ≠ 0 ∧
      ∀ᶠ ζ in 𝓝[≠] ((chartAt (H := ℂ) p) p),
        Fp ((chartAt (H := ℂ) p).symm ζ)
          = (ζ - (chartAt (H := ℂ) p) p) ^ ((D₁ + D₂) p) * w ζ := by
    intro p hp
    have hpP : p ∉ P := by
      intro h
      rw [hsum_apply] at hp
      exact hp h.2
    have hsymmp : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hsymmcp : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) :=
      (chartAt ℂ p).continuousAt_symm ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    have hPev : ∀ᶠ ζ in 𝓝 ((chartAt ℂ p) p), (chartAt ℂ p).symm ζ ∈ (Pᶜ : Set X) :=
      hsymmcp.preimage_mem_nhds (by rw [hsymmp]; exact hPcl.isOpen_compl.mem_nhds hpP)
    by_cases hp1 : D₁ p = 0
    · -- the form lives on `D₂`; `W₁` is tame
      have hp2 : D₂ p ≠ 0 := by
        intro h
        rw [hsum_apply, hp1, h, add_zero] at hp
        exact hp rfl
      obtain ⟨ht_an, -⟩ := h₁ p hp2 hp1
      obtain ⟨w₂, hw₂a, hw₂0, hw₂ev⟩ := W₂.norm_form p hp2
      refine ⟨fun ζ => W₁.F ((chartAt (H := ℂ) p).symm ζ) * w₂ ζ, ht_an.mul hw₂a, ?_, ?_⟩
      · exact mul_ne_zero (by rw [hsymmp]; exact W₁.F_ne p hp1) hw₂0
      · filter_upwards [hw₂ev, hPev.filter_mono nhdsWithin_le_nhds] with ζ hζ2 hζP
        rw [hFp_off hζP, hζ2, hsum_apply, hp1, zero_add]
        ring
    · by_cases hp2 : D₂ p = 0
      · -- the form lives on `D₁`; `W₂` is tame
        obtain ⟨ht_an, -⟩ := h₂ p hp1 hp2
        obtain ⟨w₁, hw₁a, hw₁0, hw₁ev⟩ := W₁.norm_form p hp1
        refine ⟨fun ζ => w₁ ζ * W₂.F ((chartAt (H := ℂ) p).symm ζ), hw₁a.mul ht_an, ?_, ?_⟩
        · exact mul_ne_zero hw₁0 (by rw [hsymmp]; exact W₂.F_ne p hp2)
        · filter_upwards [hw₁ev, hPev.filter_mono nhdsWithin_le_nhds] with ζ hζ1 hζP
          rw [hFp_off hζP, hζ1, hsum_apply, hp2, add_zero]
          ring
      · -- a genuinely shared support point: units multiply, exponents add
        obtain ⟨w₁, hw₁a, hw₁0, hw₁ev⟩ := W₁.norm_form p hp1
        obtain ⟨w₂, hw₂a, hw₂0, hw₂ev⟩ := W₂.norm_form p hp2
        refine ⟨fun ζ => w₁ ζ * w₂ ζ, hw₁a.mul hw₂a, mul_ne_zero hw₁0 hw₂0, ?_⟩
        filter_upwards [hw₁ev, hw₂ev, hPev.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with ζ hζ1 hζ2 hζP hζne
        have hζsub : ζ - (chartAt ℂ p) p ≠ 0 :=
          sub_ne_zero.mpr (by exact hζne)
        rw [hFp_off hζP, hζ1, hζ2, hsum_apply, zpow_add₀ hζsub]
        ring
  -- the analytic continuation across a cancellation point, in any cover chart
  have hkey : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → x ∈ P →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (chartMap 𝔇 j x) ∧
        (fun ζ => Fp ((chartAt (H := ℂ) (𝔇.center j)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] g := by
    intro j x hxU hxP
    obtain ⟨hx1, hx0⟩ := hxP
    have hx2 : D₂ x ≠ 0 := hD2ne hx1 hx0
    obtain ⟨hw₁a, hw₁0, hw₁ev⟩ := (W₁.norm_form x hx1).choose_spec
    obtain ⟨hw₂a, hw₂0, hw₂ev⟩ := (W₂.norm_form x (hD2ne hx1 hx0)).choose_spec
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmxj : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmcj : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    -- the transition into the own chart of `x`
    have hτa : AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm)
        (chartMap 𝔇 j x) :=
      analyticAt_atlasTransition (chart_mem_atlas ℂ (𝔇.center j)) (chart_mem_atlas ℂ x)
        hxsrcj (mem_chart_source ℂ x)
    have hτz : ((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) (chartMap 𝔇 j x)
        = (chartAt ℂ x) x := by
      show (chartAt ℂ x) ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) = (chartAt ℂ x) x
      rw [hsymmxj]
    have hτc : Filter.Tendsto ((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm)
        (𝓝 (chartMap 𝔇 j x)) (𝓝 ((chartAt ℂ x) x)) := by
      rw [← hτz]
      exact hτa.continuousAt
    -- pull the punctured norm forms back along the transition
    have hτev1 := hτc.eventually (eventually_nhdsWithin_iff.mp hw₁ev)
    have hτev2 := hτc.eventually (eventually_nhdsWithin_iff.mp hw₂ev)
    -- the source/patch/target bookkeeping
    have hsrcev : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j x),
        (chartAt ℂ (𝔇.center j)).symm ζ ∈ (chartAt ℂ x).source :=
      hsymmcj.preimage_mem_nhds
        (by rw [hsymmxj]; exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
    have hPev' : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j x),
        (chartAt ℂ (𝔇.center j)).symm ζ ∈ ((P \ {x})ᶜ : Set X) :=
      hsymmcj.preimage_mem_nhds
        (by
          rw [hsymmxj]
          exact ((hPfin.subset Set.diff_subset).isClosed).isOpen_compl.mem_nhds
            fun h => h.2 rfl)
    have htgtev : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j x), ζ ∈ (chartAt ℂ (𝔇.center j)).target :=
      (chartAt ℂ (𝔇.center j)).open_target.mem_nhds
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    refine ⟨fun ζ => (W₁.norm_form x hx1).choose
          (((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ)
        * (W₂.norm_form x (hD2ne hx1 hx0)).choose
          (((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ),
      ((by rw [hτz]; exact hw₁a : AnalyticAt ℂ _ _).comp hτa).mul
        ((by rw [hτz]; exact hw₂a : AnalyticAt ℂ _ _).comp hτa), ?_⟩
    filter_upwards [hτev1, hτev2, hsrcev, hPev', htgtev] with ζ hτ1 hτ2 hζsrc hζP hζtgt
    by_cases hζx : (chartAt ℂ (𝔇.center j)).symm ζ = x
    · -- at the cancellation point itself: the patch value
      have hζz : ζ = chartMap 𝔇 j x := by
        have h := (chartAt ℂ (𝔇.center j)).right_inv hζtgt
        rw [hζx] at h
        exact h.symm
      rw [hζz, hsymmxj, hτz]
      exact hFp_on hx1 hx0
    · -- nearby: the two norm forms cancel against each other
      have hζP'' : (chartAt ℂ (𝔇.center j)).symm ζ ∉ P := fun h => hζP ⟨h, hζx⟩
      have hτζo : ((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ ≠ (chartAt ℂ x) x := by
        intro h
        exact hζx ((chartAt ℂ x).injOn hζsrc (mem_chart_source ℂ x) h)
      have h1eq := hτ1 hτζo
      have h2eq := hτ2 hτζo
      have hback : (chartAt ℂ x).symm (((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ)
          = (chartAt ℂ (𝔇.center j)).symm ζ := (chartAt ℂ x).left_inv hζsrc
      rw [hback] at h1eq h2eq
      rw [hFp_off hζP'', h1eq, h2eq]
      have hτsub : ((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ - (chartAt ℂ x) x ≠ 0 :=
        sub_ne_zero.mpr hτζo
      have hzz : (((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ - (chartAt ℂ x) x)
            ^ (D₁ x)
          * (((chartAt ℂ x) ∘ (chartAt ℂ (𝔇.center j)).symm) ζ - (chartAt ℂ x) x)
            ^ (D₂ x) = 1 := by
        rw [← zpow_add₀ hτsub, hx0, zpow_zero]
      rw [mul_mul_mul_comm, hzz, one_mul]
  -- diff_off
  have hdiff : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → (D₁ + D₂) x = 0 →
      DifferentiableAt ℝ (fun w => Fp ((chartAt (H := ℂ) (𝔇.center j)).symm w))
        (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    by_cases hxP : x ∈ P
    · obtain ⟨g, hgan, hgev⟩ := hkey j x hxU hxP
      exact hgev.differentiableAt_iff.mpr (hgan.differentiableAt.restrictScalars ℝ)
    · have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
      have hsymmxj : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
      have hsymmcj : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
        (chartAt ℂ (𝔇.center j)).continuousAt_symm
          ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
      rw [hsum_apply] at hx0
      have hx1 : D₁ x = 0 := by
        by_contra h
        exact hxP ⟨h, hx0⟩
      have hx2 : D₂ x = 0 := by rwa [hx1, zero_add] at hx0
      have hev : (fun w => Fp ((chartAt (H := ℂ) (𝔇.center j)).symm w))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun ζ =>
            W₁.F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ)
              * W₂.F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ) := by
        filter_upwards [hsymmcj.preimage_mem_nhds
          (by rw [hsymmxj]; exact hPcl.isOpen_compl.mem_nhds hxP)] with ζ hζ
        exact hFp_off hζ
      exact hev.differentiableAt_iff.mpr
        ((W₁.diff_off j x hxU hx1).mul (W₂.diff_off j x hxU hx2))
  -- dbar_eq
  have hdbar : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → (D₁ + D₂) x = 0 →
      DbarDisk.dbar (fun w => Fp ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
        = Fp x * 𝔇.cutoffPullback j (σs : SmoothCOneForms X) (chartMap 𝔇 j x) := by
    intro j x hxU hx0
    have hxsrcj : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsymmxj : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt ℂ (𝔇.center j)).left_inv hxsrcj
    have hsymmxj' : (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).left_inv (𝔇.subset_chart_source j hxU)
    have hsymmcj : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
      (chartAt ℂ (𝔇.center j)).continuousAt_symm
        ((chartAt ℂ (𝔇.center j)).map_source hxsrcj)
    have hcpadd : 𝔇.cutoffPullback j (σs : SmoothCOneForms X) (chartMap 𝔇 j x)
        = 𝔇.cutoffPullback j (W₁.σ : SmoothCOneForms X) (chartMap 𝔇 j x)
          + 𝔇.cutoffPullback j (W₂.σ : SmoothCOneForms X) (chartMap 𝔇 j x) := by
      rw [hσs, Submodule.coe_add, ChartDiskCover.cutoffPullback_add]
      rfl
    by_cases hxP : x ∈ P
    · -- cancelled point: both sides vanish
      obtain ⟨g, hgan, hgev⟩ := hkey j x hxU hxP
      obtain ⟨hx1, hxsum⟩ := hxP
      rw [dbar_congr_of_eventuallyEq hgev,
        DbarDisk.dbar_eq_zero_of_differentiableAt hgan.differentiableAt, hcpadd,
        cutoffPullback_apply_eq_zero (by rw [hsymmxj']; exact W₁.σ_vanish x hx1),
        cutoffPullback_apply_eq_zero
          (by rw [hsymmxj']; exact W₂.σ_vanish x (hD2ne hx1 hxsum))]
      ring
    · -- generic point: planar Leibniz against the two logarithmic identities
      rw [hsum_apply] at hx0
      have hx1 : D₁ x = 0 := by
        by_contra h
        exact hxP ⟨h, hx0⟩
      have hx2 : D₂ x = 0 := by rwa [hx1, zero_add] at hx0
      have hev : (fun w => Fp ((chartAt (H := ℂ) (𝔇.center j)).symm w))
          =ᶠ[𝓝 (chartMap 𝔇 j x)] fun ζ =>
            W₁.F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ)
              * W₂.F ((chartAt (H := ℂ) (𝔇.center j)).symm ζ) := by
        filter_upwards [hsymmcj.preimage_mem_nhds
          (by rw [hsymmxj]; exact hPcl.isOpen_compl.mem_nhds hxP)] with ζ hζ
        exact hFp_off hζ
      rw [dbar_congr_of_eventuallyEq hev,
        dbarFun_mul' (W₁.diff_off j x hxU hx1) (W₂.diff_off j x hxU hx2),
        W₁.dbar_eq j x hxU hx1, W₂.dbar_eq j x hxU hx2, hsymmxj, hcpadd,
        hFp_off hxP]
      ring
  refine ⟨{
    F := Fp
    σ := σs
    F_ne := hFne
    diff_off := hdiff
    dbar_eq := hdbar
    σ_vanish := hσvan
    norm_form := hnorm }, hσs, ?_⟩
  intro q hq0 ht₁ ht₂
  rw [hsum_apply] at hq0
  by_cases hq1 : D₁ q = 0
  · -- both factors tame near `q`; the product read is the product of analytic reads
    have hq2 : D₂ q = 0 := by rwa [hq1, zero_add] at hq0
    have hqP : q ∉ P := fun h => h.1 hq1
    obtain ⟨ha₁, hs₁⟩ := ht₁ hq1
    obtain ⟨ha₂, hs₂⟩ := ht₂ hq2
    have hsymmq : (chartAt ℂ q).symm ((chartAt ℂ q) q) = q :=
      (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
    have hsymmcq : ContinuousAt (chartAt ℂ q).symm ((chartAt ℂ q) q) :=
      (chartAt ℂ q).continuousAt_symm ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
    refine ⟨?_, ?_⟩
    · refine (ha₁.mul ha₂).congr ?_
      filter_upwards [hsymmcq.preimage_mem_nhds
        (by rw [hsymmq]; exact hPcl.isOpen_compl.mem_nhds hqP)] with ζ hζ
      exact (hFp_off hζ).symm
    · show (σs : SmoothCOneForms X) q = 0
      rw [hσs_apply, hs₁, hs₂, add_zero]
  · -- `q` is a cancellation point: the patched continuation, transported to the own chart
    have hqP : q ∈ P := ⟨hq1, hq0⟩
    obtain ⟨j, hqU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (𝔇.toFiniteCover.covers ▸ Set.mem_univ q : q ∈ ⨆ i, 𝔇.toFiniteCover.U i)
    obtain ⟨g, hgan, hgev⟩ := hkey j q hqU hqP
    refine ⟨?_, ?_⟩
    · have hcov_an : AnalyticAt ℂ (Fp ∘ (chartAt ℂ (𝔇.center j)).symm)
          ((chartAt ℂ (𝔇.center j)) q) := hgan.congr hgev.symm
      exact analyticAt_chartRead_transfer (chart_mem_atlas ℂ q)
        (chart_mem_atlas ℂ (𝔇.center j)) (mem_chart_source ℂ q)
        (mem_chartSource_of_mem_U 𝔇 hqU) hcov_an
    · show (σs : SmoothCOneForms X) q = 0
      rw [hσs_apply, W₁.σ_vanish q hq1, W₂.σ_vanish q (hD2ne hq1 hq0), add_zero]

end ChainFold

/-! ## The full chain fold: from a `SmoothOneChain` to its weak-solution datum

The assembly of E3: subdivide each arc of the chain into chart-disk-sized steps
(Lebesgue number of the cover along the path), expand the ℤ-coefficients into repeated
(or reversed) dipole lists, and fold `exists_arcWeakSolution_avoiding` over the resulting
flat dipole list with `ArcWeakSolution.exists_mul`, carrying the tameness invariant at
the global endpoint set.  The boundary divisor telescopes to `∂c`. -/

section ChainAssembly

variable (𝔇 : ChartDiskCover X)

/-- The zero `(0,1)` datum evaluates to zero at every point. -/
theorem zeroOneForm_apply (x : X) :
    (((0 : ↥(OneFormsZeroOne X))) : SmoothCOneForms X) x = 0 := by
  rw [ZeroMemClass.coe_zero, ContMDiffSection.coe_zero]
  rfl

/-- **The trivial weak-solution datum** for the zero divisor: `F ≡ 1`, `σ = 0`.  The base
case of the chain fold. -/
def ArcWeakSolution.one : ArcWeakSolution 𝔇 (0 : Divisor X) where
  F := fun _ => 1
  σ := 0
  F_ne := fun _ _ => one_ne_zero
  diff_off := fun j x _ _ => differentiableAt_const 1
  dbar_eq := fun j x _ _ => by
    have hR : 𝔇.cutoffPullback j (((0 : ↥(OneFormsZeroOne X))) : SmoothCOneForms X)
        (chartMap 𝔇 j x) = 0 :=
      cutoffPullback_apply_eq_zero (zeroOneForm_apply _)
    rw [hR, mul_zero]
    exact DbarDisk.dbar_const 1 (chartMap 𝔇 j x)
  σ_vanish := fun x _ => zeroOneForm_apply x
  norm_form := fun a ha => absurd (by simp) ha

/-- The trivial datum is tame everywhere. -/
theorem ArcWeakSolution.one_tameAt (q : X) : (ArcWeakSolution.one 𝔇).TameAt q :=
  ⟨analyticAt_const, zeroOneForm_apply q⟩

/-! ### The dipole-list layer -/

/-- The boundary dipole of one (source, target) pair: `(target) − (source)`. -/
def dipole (p : X × X) : Divisor X :=
  Finsupp.single p.2 1 - Finsupp.single p.1 1

theorem dipole_apply_eq_zero {p : X × X} {x : X} (hx1 : x ≠ p.1) (hx2 : x ≠ p.2) :
    dipole p x = 0 := by
  rw [dipole, Finsupp.sub_apply, Finsupp.single_eq_of_ne hx2,
    Finsupp.single_eq_of_ne hx1, sub_zero]

theorem eq_fst_or_snd_of_dipole_ne_zero {p : X × X} {x : X} (h : dipole p x ≠ 0) :
    x = p.1 ∨ x = p.2 := by
  by_contra hcon
  push Not at hcon
  exact h (dipole_apply_eq_zero hcon.1 hcon.2)

theorem dipole_apply_fst {p : X × X} (hab : p.1 ≠ p.2) : dipole p p.1 = -1 := by
  rw [dipole, Finsupp.sub_apply, Finsupp.single_eq_of_ne hab, Finsupp.single_eq_same]
  ring

theorem ne_fst_of_dipole_apply_eq_zero {p : X × X} (hab : p.1 ≠ p.2) {x : X}
    (h : dipole p x = 0) : x ≠ p.1 := by
  rintro rfl
  rw [dipole_apply_fst hab] at h
  norm_num at h

/-- The boundary divisor of a list of dipoles. -/
def dipoleDiv (L : List (X × X)) : Divisor X :=
  (L.map dipole).sum

@[simp] theorem dipoleDiv_nil : dipoleDiv ([] : List (X × X)) = 0 := rfl

theorem dipoleDiv_cons (p : X × X) (L : List (X × X)) :
    dipoleDiv (p :: L) = dipole p + dipoleDiv L := by
  rw [dipoleDiv, dipoleDiv, List.map_cons, List.sum_cons]

theorem dipoleDiv_append (L₁ L₂ : List (X × X)) :
    dipoleDiv (L₁ ++ L₂) = dipoleDiv L₁ + dipoleDiv L₂ := by
  rw [dipoleDiv, dipoleDiv, dipoleDiv, List.map_append, List.sum_append]

/-- The telescoping list of consecutive pairs `(p k, p (k+1))`, `k < N`. -/
def consecPairs (p : ℕ → X) : ℕ → List (X × X)
  | 0 => []
  | N + 1 => consecPairs p N ++ [(p N, p (N + 1))]

/-- **Telescoping**: the dipole divisor of the consecutive-pair list is the endpoint
dipole. -/
theorem dipoleDiv_consecPairs (p : ℕ → X) :
    ∀ N : ℕ, dipoleDiv (consecPairs p N)
      = Finsupp.single (p N) 1 - Finsupp.single (p 0) 1
  | 0 => by rw [consecPairs, dipoleDiv_nil, sub_self]
  | N + 1 => by
    rw [consecPairs, dipoleDiv_append, dipoleDiv_consecPairs p N, dipoleDiv_cons,
      dipoleDiv_nil, dipole]
    abel

theorem mem_consecPairs {p : ℕ → X} {q : X × X} :
    ∀ {N : ℕ}, q ∈ consecPairs p N → ∃ k, k < N ∧ q = (p k, p (k + 1))
  | 0, h => absurd h (List.not_mem_nil)
  | N + 1, h => by
    rw [consecPairs] at h
    rcases List.mem_append.mp h with h' | h'
    · obtain ⟨k, hk, hq⟩ := mem_consecPairs h'
      exact ⟨k, Nat.lt_succ_of_lt hk, hq⟩
    · rw [List.mem_singleton] at h'
      exact ⟨N, Nat.lt_succ_self N, h'⟩

/-- `k` concatenated copies of a dipole list (ℕ-scalar of the divisor). -/
def nsmulList (L : List (X × X)) : ℕ → List (X × X)
  | 0 => []
  | k + 1 => L ++ nsmulList L k

theorem dipoleDiv_nsmulList (L : List (X × X)) :
    ∀ k : ℕ, dipoleDiv (nsmulList L k) = k • dipoleDiv L
  | 0 => by rw [nsmulList, dipoleDiv_nil, zero_nsmul]
  | k + 1 => by
    rw [nsmulList, dipoleDiv_append, dipoleDiv_nsmulList L k, succ_nsmul]
    abel

theorem mem_nsmulList {L : List (X × X)} {q : X × X} :
    ∀ {k : ℕ}, q ∈ nsmulList L k → q ∈ L
  | 0, h => absurd h (List.not_mem_nil)
  | k + 1, h => by
    rw [nsmulList] at h
    rcases List.mem_append.mp h with h' | h'
    · exact h'
    · exact mem_nsmulList h'

/-- Reversing every dipole negates the divisor. -/
theorem dipoleDiv_swap (L : List (X × X)) :
    dipoleDiv (L.map Prod.swap) = -dipoleDiv L := by
  induction L with
  | nil => rw [List.map_nil, dipoleDiv_nil, neg_zero]
  | cons hd tl ih =>
    rw [List.map_cons, dipoleDiv_cons, dipoleDiv_cons, ih, dipole, dipole,
      Prod.fst_swap, Prod.snd_swap]
    abel

/-- The ℤ-scalar of a dipole list: `n ≥ 0` repeats it, `n < 0` repeats its reversal. -/
def zsmulList (L : List (X × X)) (n : ℤ) : List (X × X) :=
  if 0 ≤ n then nsmulList L n.toNat else nsmulList (L.map Prod.swap) (-n).toNat

theorem dipoleDiv_zsmulList (L : List (X × X)) (n : ℤ) :
    dipoleDiv (zsmulList L n) = n • dipoleDiv L := by
  rw [zsmulList]
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [dipoleDiv_nsmulList, Int.toNat_natCast, natCast_zsmul]
  · have hk : (((-n).toNat : ℤ)) = -n :=
      Int.toNat_of_nonneg (by linarith [lt_of_not_ge hn])
    rw [dipoleDiv_nsmulList, dipoleDiv_swap, smul_neg, ← natCast_zsmul, hk, neg_smul,
      neg_neg]

theorem mem_zsmulList {L : List (X × X)} {n : ℤ} {q : X × X} (h : q ∈ zsmulList L n) :
    q ∈ L ∨ Prod.swap q ∈ L := by
  rw [zsmulList] at h
  split_ifs at h with hn
  · exact Or.inl (mem_nsmulList h)
  · obtain ⟨r, hr, hq⟩ := List.mem_map.mp (mem_nsmulList h)
    right
    rw [← hq, Prod.swap_swap]
    exact hr

theorem dipoleDiv_flatten (LL : List (List (X × X))) :
    dipoleDiv LL.flatten = (LL.map dipoleDiv).sum := by
  induction LL with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatten_cons, dipoleDiv_append, ih, List.map_cons, List.sum_cons]

/-! ### Chart-disk subdivision of a smooth path -/

/-- **Chart-disk subdivision** (Lebesgue number of the cover along the path): finitely
many parameter points whose consecutive path values lie pairwise in one cover disk. -/
theorem exists_subdivision {P Q : X} {γ : ℝ → X} (h : IsSmoothPath P Q γ) :
    ∃ (N : ℕ) (p : ℕ → X), p 0 = P ∧ p N = Q ∧
      ∀ k, k < N → ∃ j : 𝔇.toFiniteCover.ι,
        p k ∈ (𝔇.U j : Set X) ∧ p (k + 1) ∈ (𝔇.U j : Set X) := by
  have hcov : Set.Icc (0 : ℝ) 1 ⊆ ⋃ j : 𝔇.toFiniteCover.ι, γ ⁻¹' (𝔇.U j : Set X) := by
    intro t _
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (𝔇.toFiniteCover.covers ▸ Set.mem_univ (γ t) : γ t ∈ ⨆ i, 𝔇.toFiniteCover.U i)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun j => (𝔇.U j).isOpen.preimage h.cont) hcov
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  refine ⟨N, fun k => γ ((k : ℝ) / N), ?_, ?_, ?_⟩
  · show γ (((0 : ℕ) : ℝ) / N) = P
    rw [Nat.cast_zero, zero_div]
    exact h.start
  · show γ ((N : ℝ) / N) = Q
    rw [div_self hNpos.ne']
    exact h.finish
  · intro k hk
    have hmem : ((k : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hNpos]
        exact_mod_cast hk.le
    obtain ⟨j, hsub⟩ := hball _ hmem
    refine ⟨j, hsub (Metric.mem_ball_self hδ), hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
      push_cast
      ring
    rw [heq, abs_of_pos (by positivity), div_lt_iff₀ hNpos, mul_comm]
    exact (div_lt_iff₀ hδ).mp hN

/-! ### The master fold over a dipole list -/

/-- **The full chain fold over a dipole list** (the E3 induction): a list of
(source, target) pairs, each pair inside one cover disk and with endpoints in the avoid
set `S`, carries an arc weak solution for the sum of its boundary dipoles, supported in
`S` and tame at every off-support point of `S`.  The head arc's tube solution
(`exists_arcWeakSolution_avoiding`, avoiding all of `S`) multiplies onto the tail's fold
(`ArcWeakSolution.exists_mul`); the avoid-set tameness supplies the fold hypotheses at
the unshared support points, and the fold propagates the tameness invariant. -/
theorem exists_arcWeakSolution_dipoleList (S : Finset X) (L : List (X × X))
    (hdisk : ∀ q ∈ L, ∃ j : 𝔇.toFiniteCover.ι,
      q.1 ∈ (𝔇.U j : Set X) ∧ q.2 ∈ (𝔇.U j : Set X))
    (hS : ∀ q ∈ L, q.1 ∈ S ∧ q.2 ∈ S) :
    ∃ W : ArcWeakSolution 𝔇 (dipoleDiv L),
      (∀ x : X, dipoleDiv L x ≠ 0 → x ∈ S) ∧
      ∀ q ∈ S, dipoleDiv L q = 0 → W.TameAt q := by
  induction L with
  | nil =>
    rw [dipoleDiv_nil]
    exact ⟨ArcWeakSolution.one 𝔇, fun x hx => (hx (by simp)).elim,
      fun q _ _ => ArcWeakSolution.one_tameAt 𝔇 q⟩
  | cons hd tl ih =>
    obtain ⟨W₁, hsupp₁, htame₁⟩ := ih (fun q hq => hdisk q (List.mem_cons_of_mem _ hq))
      (fun q hq => hS q (List.mem_cons_of_mem _ hq))
    by_cases hab : hd.1 = hd.2
    · -- degenerate dipole: the head contributes nothing
      have h0 : dipole hd = 0 := by rw [dipole, hab, sub_self]
      rw [dipoleDiv_cons, h0, zero_add]
      exact ⟨W₁, hsupp₁, htame₁⟩
    · obtain ⟨j, haU, hbU⟩ := hdisk hd List.mem_cons_self
      obtain ⟨haS, hbS⟩ := hS hd List.mem_cons_self
      obtain ⟨W₂, -, hW₂⟩ := exists_arcWeakSolution_avoiding 𝔇 j S haU hbU hab
      have hW₂tame : ∀ q ∈ S, q ≠ hd.1 → W₂.TameAt q :=
        fun q hq hqa => ⟨(hW₂ q hq hqa).1, (hW₂ q hq hqa).2⟩
      have h₁ : ∀ x, dipoleDiv tl x ≠ 0 → dipole hd x = 0 → W₂.TameAt x :=
        fun x hx hdx =>
          hW₂tame x (hsupp₁ x hx) (ne_fst_of_dipole_apply_eq_zero hab hdx)
      have h₂ : ∀ x, dipole hd x ≠ 0 → dipoleDiv tl x = 0 → W₁.TameAt x := by
        intro x hx h0
        have hxS : x ∈ S := by
          rcases eq_fst_or_snd_of_dipole_ne_zero hx with rfl | rfl
          exacts [haS, hbS]
        exact htame₁ x hxS h0
      obtain ⟨W, -, hWtame⟩ := ArcWeakSolution.exists_mul W₂ W₁ h₁ h₂
      rw [dipoleDiv_cons]
      refine ⟨W, ?_, ?_⟩
      · intro x hx
        by_cases hx1 : dipole hd x = 0
        · refine hsupp₁ x fun h0 => hx ?_
          rw [Finsupp.add_apply, hx1, h0, add_zero]
        · rcases eq_fst_or_snd_of_dipole_ne_zero hx1 with rfl | rfl
          exacts [haS, hbS]
      · intro q hqS hq0
        exact hWtame q hq0
          (fun hd0 => hW₂tame q hqS (ne_fst_of_dipole_apply_eq_zero hab hd0))
          (fun ht0 => htame₁ q hqS ht0)

/-! ### E3 COMPLETE: the chain-level constructor and the E4-pinned engine -/

/-- **E3, complete**: every smooth 1-chain admits an arc weak solution for its boundary
divisor — the full Forster 20.5 weak-solution datum (weak solution `F`, global `(0,1)`
datum `σ`, nonvanishing, chart differentiability, logarithmic `∂̄`-identity, analytic
endpoint normal forms), with no hypothesis on the chain.  Subdivide each arc into
chart-disk steps, expand the ℤ-coefficients, fold. -/
theorem exists_arcWeakSolution_boundary (c : SmoothOneChain X) :
    Nonempty (ArcWeakSolution 𝔇 c.boundary) := by
  classical
  choose N p hp0 hpN hpdisk using fun i : Fin c.n => exists_subdivision 𝔇 (c.smooth i)
  set L : List (X × X) :=
    (List.ofFn fun i => zsmulList (consecPairs (p i) (N i)) (c.coeff i)).flatten with hL
  have hdiv : dipoleDiv L = c.boundary := by
    rw [hL, dipoleDiv_flatten, List.map_ofFn, List.sum_ofFn, SmoothOneChain.boundary]
    refine Finset.sum_congr rfl fun i _ => ?_
    show dipoleDiv (zsmulList (consecPairs (p i) (N i)) (c.coeff i)) = _
    rw [dipoleDiv_zsmulList, dipoleDiv_consecPairs, hpN i, hp0 i]
  have hdisk : ∀ q ∈ L, ∃ j : 𝔇.toFiniteCover.ι,
      q.1 ∈ (𝔇.U j : Set X) ∧ q.2 ∈ (𝔇.U j : Set X) := by
    intro q hq
    rw [hL, List.mem_flatten] at hq
    obtain ⟨l, hl, hql⟩ := hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    rcases mem_zsmulList hql with hmem | hmem
    · obtain ⟨k, hk, rfl⟩ := mem_consecPairs hmem
      exact hpdisk i k hk
    · obtain ⟨k, hk, hswap⟩ := mem_consecPairs hmem
      obtain ⟨j, h1, h2⟩ := hpdisk i k hk
      have hq' : q = (p i (k + 1), p i k) := by
        have hss := congrArg Prod.swap hswap
        rwa [Prod.swap_swap] at hss
      rw [hq']
      exact ⟨j, h2, h1⟩
  set S : Finset X := (L.map Prod.fst ++ L.map Prod.snd).toFinset with hSdef
  have hSmem : ∀ q ∈ L, q.1 ∈ S ∧ q.2 ∈ S := by
    intro q hq
    rw [hSdef]
    constructor
    · rw [List.mem_toFinset, List.mem_append]
      exact Or.inl (List.mem_map_of_mem hq)
    · rw [List.mem_toFinset, List.mem_append]
      exact Or.inr (List.mem_map_of_mem hq)
  obtain ⟨W, -, -⟩ := exists_arcWeakSolution_dipoleList 𝔇 S L hdisk hSmem
  exact ⟨hdiv ▸ W⟩

/-- **The §20 engine over E3 — E4 is the single remaining obligation.**  A chain with all
periods zero whose (E3-provided) weak-solution datum satisfies the E4 pairing identity
`∫_X σ∧α = 2πi·∫_c α` bounds a principal divisor.  Composition:
`ArcWeakSolution.toRaw` (E2 constructor, conditional on the pairing) →
`RawLogDbarDatum.toLogDbarDatum` (W1/W2 local analysis) →
`exists_meromorphic_of_logDbarDatum` (E5 assembly over P6 `∂̄`-solvability).

With `exists_arcWeakSolution_boundary` providing `W` unconditionally, discharging the
`hpair` hypothesis for the constructed datum (rung E4, the planar Stokes/residue
computation of Forster 20.3/20.5) makes the engine fully unconditional. -/
theorem exists_meromorphic_of_zeroPeriodChain_of_pairing (c : SmoothOneChain X)
    (W : ArcWeakSolution 𝔇 c.boundary)
    (hpair : ∀ α : HolomorphicOneForms X,
      FineResidue.pairOmega 𝔇 W.σ α = 2 * (Real.pi : ℂ) * Complex.I * c.period α)
    (hper : ∀ α : HolomorphicOneForms X, c.period α = 0) :
    ∃ f : MeromorphicFunction X, MeromorphicFunction.div X f = c.boundary :=
  exists_meromorphic_of_logDbarDatum 𝔇 c ((W.toRaw c rfl hpair).toLogDbarDatum) hper


/-! ### E4 COMPLETE: the pairing accumulator and the unconditional engine

The E4 discharge: `pairOmega` is linear in the `(0,1)` slot, the per-arc constructor
exposes its pairing value `π·segPeriod` (the planar atom), the chain fold adds the
`σ`'s, and inside each chart ball the chart-segment value is the line-integral piece
(`intervalIntegral_form_eq_segPeriod`).  Folding over the subdivided chain gives
`pairOmega 𝔇 W.σ α = π·∫_c α` — and with zero periods the E2 pairing field is met,
making `exists_meromorphic_of_zeroPeriodChain'` unconditional. -/

/-- `pairOmega` is additive in the `(0,1)` slot (`pairFormL` is linear). -/
theorem pairOmega_sigma_add (σ τ : ↥(OneFormsZeroOne X)) (α : HolomorphicOneForms X) :
    FineResidue.pairOmega 𝔇 (σ + τ) α
      = FineResidue.pairOmega 𝔇 σ α + FineResidue.pairOmega 𝔇 τ α := by
  unfold FineResidue.pairOmega
  exact map_add (FineResidue.pairFormL 𝔇 (FineResidue.isOneZeroCoeff_omegaCoeff 𝔇 α)) σ τ

/-- `pairOmega` vanishes on the zero `(0,1)` datum. -/
theorem pairOmega_sigma_zero (α : HolomorphicOneForms X) :
    FineResidue.pairOmega 𝔇 (0 : ↥(OneFormsZeroOne X)) α = 0 := by
  unfold FineResidue.pairOmega
  exact map_zero (FineResidue.pairFormL 𝔇 (FineResidue.isOneZeroCoeff_omegaCoeff 𝔇 α))

/-! #### Chart-tagged dipole lists

The tagged analogues of `consecPairs`/`nsmulList`/`zsmulList`: each (source, target)
pair carries the cover index of a disk containing both points, so the fold can
accumulate the per-arc pairing values `segPeriod` in the *chosen* charts. -/

section TaggedLists

variable {ι : Type*}

/-- Reverse the dipole of a tagged entry, keeping its chart tag. -/
def swapTag (q : (X × X) × ι) : (X × X) × ι := ((q.1.2, q.1.1), q.2)

@[simp] theorem swapTag_swapTag (q : (X × X) × ι) : swapTag (swapTag q) = q := rfl

/-- Tagged consecutive pairs `((p k, p (k+1)), j k)`, `k < N`. -/
def consecPairsTag (p : ℕ → X) (j : ℕ → ι) : ℕ → List ((X × X) × ι)
  | 0 => []
  | N + 1 => consecPairsTag p j N ++ [((p N, p (N + 1)), j N)]

/-- Tagged `k`-fold concatenation. -/
def nsmulListTag (L : List ((X × X) × ι)) : ℕ → List ((X × X) × ι)
  | 0 => []
  | k + 1 => L ++ nsmulListTag L k

/-- Tagged ℤ-scalar: `n ≥ 0` repeats, `n < 0` repeats the reversal. -/
def zsmulListTag (L : List ((X × X) × ι)) (n : ℤ) : List ((X × X) × ι) :=
  if 0 ≤ n then nsmulListTag L n.toNat else nsmulListTag (L.map swapTag) (-n).toNat

theorem map_fst_consecPairsTag (p : ℕ → X) (j : ℕ → ι) :
    ∀ N, (consecPairsTag p j N).map Prod.fst = consecPairs p N
  | 0 => rfl
  | N + 1 => by
    rw [consecPairsTag, consecPairs, List.map_append, map_fst_consecPairsTag p j N]
    rfl

theorem map_fst_nsmulListTag (L : List ((X × X) × ι)) :
    ∀ k, (nsmulListTag L k).map Prod.fst = nsmulList (L.map Prod.fst) k
  | 0 => rfl
  | k + 1 => by
    rw [nsmulListTag, nsmulList, List.map_append, map_fst_nsmulListTag L k]

theorem map_fst_swapTag (L : List ((X × X) × ι)) :
    (L.map swapTag).map Prod.fst = (L.map Prod.fst).map Prod.swap := by
  rw [List.map_map, List.map_map]
  rfl

theorem map_fst_zsmulListTag (L : List ((X × X) × ι)) (n : ℤ) :
    (zsmulListTag L n).map Prod.fst = zsmulList (L.map Prod.fst) n := by
  rw [zsmulListTag, zsmulList]
  split_ifs
  · exact map_fst_nsmulListTag L _
  · rw [map_fst_nsmulListTag, map_fst_swapTag]

theorem mem_consecPairsTag {p : ℕ → X} {j : ℕ → ι} {q : (X × X) × ι} :
    ∀ {N : ℕ}, q ∈ consecPairsTag p j N → ∃ k, k < N ∧ q = ((p k, p (k + 1)), j k)
  | 0, h => absurd h (List.not_mem_nil)
  | N + 1, h => by
    rw [consecPairsTag] at h
    rcases List.mem_append.mp h with h' | h'
    · obtain ⟨k, hk, hq⟩ := mem_consecPairsTag h'
      exact ⟨k, Nat.lt_succ_of_lt hk, hq⟩
    · rw [List.mem_singleton] at h'
      exact ⟨N, Nat.lt_succ_self N, h'⟩

theorem mem_nsmulListTag {L : List ((X × X) × ι)} {q : (X × X) × ι} :
    ∀ {k : ℕ}, q ∈ nsmulListTag L k → q ∈ L
  | 0, h => absurd h (List.not_mem_nil)
  | k + 1, h => by
    rw [nsmulListTag] at h
    rcases List.mem_append.mp h with h' | h'
    · exact h'
    · exact mem_nsmulListTag h'

theorem mem_zsmulListTag {L : List ((X × X) × ι)} {n : ℤ} {q : (X × X) × ι}
    (h : q ∈ zsmulListTag L n) : q ∈ L ∨ swapTag q ∈ L := by
  rw [zsmulListTag] at h
  split_ifs at h with hn
  · exact Or.inl (mem_nsmulListTag h)
  · obtain ⟨r, hr, hq⟩ := List.mem_map.mp (mem_nsmulListTag h)
    right
    rw [← hq, swapTag_swapTag]
    exact hr

/-- The mapped sum over tagged consecutive pairs is the range sum. -/
theorem sum_map_consecPairsTag (f : (X × X) × ι → ℂ) (p : ℕ → X) (j : ℕ → ι) :
    ∀ N, ((consecPairsTag p j N).map f).sum
      = ∑ k ∈ Finset.range N, f ((p k, p (k + 1)), j k)
  | 0 => by simp [consecPairsTag]
  | N + 1 => by
    rw [consecPairsTag, List.map_append, List.sum_append, sum_map_consecPairsTag f p j N,
      Finset.sum_range_succ]
    simp

theorem sum_map_nsmulListTag (f : (X × X) × ι → ℂ) (L : List ((X × X) × ι)) :
    ∀ k, ((nsmulListTag L k).map f).sum = k • (L.map f).sum
  | 0 => by simp [nsmulListTag]
  | k + 1 => by
    rw [nsmulListTag, List.map_append, List.sum_append, sum_map_nsmulListTag f L k,
      succ_nsmul]
    ring

theorem sum_map_neg_fun (f : (X × X) × ι → ℂ) (L : List ((X × X) × ι)) :
    (L.map fun q => -f q).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- The mapped sum over a tagged ℤ-scalar, for a swap-antisymmetric value. -/
theorem sum_map_zsmulListTag (f : (X × X) × ι → ℂ) (hf : ∀ q, f (swapTag q) = -f q)
    (L : List ((X × X) × ι)) (n : ℤ) :
    ((zsmulListTag L n).map f).sum = (n : ℂ) * (L.map f).sum := by
  rw [zsmulListTag]
  split_ifs with hn
  · rw [sum_map_nsmulListTag]
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [Int.toNat_natCast, nsmul_eq_mul]
    push_cast
    ring
  · rw [sum_map_nsmulListTag]
    have hswap : ((L.map swapTag).map f).sum = -(L.map f).sum := by
      rw [List.map_map, show f ∘ swapTag = fun q => -f q from funext hf, sum_map_neg_fun]
    rw [hswap, nsmul_eq_mul]
    have hk : (((-n).toNat : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      norm_cast
      exact Int.toNat_of_nonneg (by linarith [lt_of_not_ge hn])
    push_cast at hk ⊢
    rw [hk]
    ring

end TaggedLists

/-! #### The tagged master fold -/

/-- **The chain fold over a chart-tagged dipole list, with the pairing accumulator**:
the folded weak solution's `σ` pairs against every `α` to `π` times the sum of the
chart-segment values of the entries. -/
theorem exists_arcWeakSolution_dipoleListChart (S : Finset X)
    (L : List ((X × X) × 𝔇.toFiniteCover.ι))
    (hdisk : ∀ p ∈ L, p.1.1 ∈ (𝔇.U p.2 : Set X) ∧ p.1.2 ∈ (𝔇.U p.2 : Set X))
    (hS : ∀ p ∈ L, p.1.1 ∈ S ∧ p.1.2 ∈ S) :
    ∃ W : ArcWeakSolution 𝔇 (dipoleDiv (L.map Prod.fst)),
      (∀ α : HolomorphicOneForms X,
        FineResidue.pairOmega 𝔇 W.σ α
          = (Real.pi : ℂ) * (L.map fun p => segPeriod α (𝔇.center p.2)
              (chartMap 𝔇 p.2 p.1.1) (chartMap 𝔇 p.2 p.1.2)).sum) ∧
      (∀ x : X, dipoleDiv (L.map Prod.fst) x ≠ 0 → x ∈ S) ∧
      ∀ q ∈ S, dipoleDiv (L.map Prod.fst) q = 0 → W.TameAt q := by
  induction L with
  | nil =>
    rw [List.map_nil, dipoleDiv_nil]
    refine ⟨ArcWeakSolution.one 𝔇, ?_, fun x hx => (hx (by simp)).elim,
      fun q _ _ => ArcWeakSolution.one_tameAt 𝔇 q⟩
    intro α
    show FineResidue.pairOmega 𝔇 (0 : ↥(OneFormsZeroOne X)) α = _
    rw [pairOmega_sigma_zero]
    simp
  | cons hd tl ih =>
    obtain ⟨W₁, hval₁, hsupp₁, htame₁⟩ := ih
      (fun p hp => hdisk p (List.mem_cons_of_mem _ hp))
      (fun p hp => hS p (List.mem_cons_of_mem _ hp))
    by_cases hab : hd.1.1 = hd.1.2
    · -- degenerate dipole: zero divisor AND zero segment value
      have h0 : dipole hd.1 = 0 := by
        rw [dipole, hab, sub_self]
      rw [List.map_cons, dipoleDiv_cons, h0, zero_add]
      refine ⟨W₁, ?_, hsupp₁, htame₁⟩
      intro α
      rw [hval₁ α, List.map_cons, List.sum_cons]
      have hz : segPeriod α (𝔇.center hd.2) (chartMap 𝔇 hd.2 hd.1.1)
          (chartMap 𝔇 hd.2 hd.1.2) = 0 := by
        rw [hab, segPeriod, sub_self, zero_mul]
      rw [hz, zero_add]
    · obtain ⟨haU, hbU⟩ := hdisk hd List.mem_cons_self
      obtain ⟨haS, hbS⟩ := hS hd List.mem_cons_self
      obtain ⟨W₂, hval₂, hW₂⟩ := exists_arcWeakSolution_avoiding 𝔇 hd.2 S haU hbU hab
      have hW₂tame : ∀ q ∈ S, q ≠ hd.1.1 → W₂.TameAt q :=
        fun q hq hqa => ⟨(hW₂ q hq hqa).1, (hW₂ q hq hqa).2⟩
      have h₁ : ∀ x, dipoleDiv (tl.map Prod.fst) x ≠ 0 → dipole hd.1 x = 0 → W₂.TameAt x :=
        fun x hx hdx =>
          hW₂tame x (hsupp₁ x hx) (ne_fst_of_dipole_apply_eq_zero hab hdx)
      have h₂ : ∀ x, dipole hd.1 x ≠ 0 → dipoleDiv (tl.map Prod.fst) x = 0 → W₁.TameAt x := by
        intro x hx h0
        have hxS : x ∈ S := by
          rcases eq_fst_or_snd_of_dipole_ne_zero hx with rfl | rfl
          exacts [haS, hbS]
        exact htame₁ x hxS h0
      obtain ⟨W, hWσ, hWtame⟩ := ArcWeakSolution.exists_mul W₂ W₁ h₁ h₂
      rw [List.map_cons, dipoleDiv_cons]
      refine ⟨W, ?_, ?_, ?_⟩
      · intro α
        rw [hWσ, pairOmega_sigma_add, hval₂ α, hval₁ α, List.map_cons, List.sum_cons]
        ring
      · intro x hx
        by_cases hx1 : dipole hd.1 x = 0
        · refine hsupp₁ x fun h0 => hx ?_
          rw [Finsupp.add_apply, hx1, h0, add_zero]
        · rcases eq_fst_or_snd_of_dipole_ne_zero hx1 with rfl | rfl
          exacts [haS, hbS]
      · intro q hqS hq0
        exact hWtame q hq0
          (fun hd0 => hW₂tame q hqS (ne_fst_of_dipole_apply_eq_zero hab hd0))
          (fun ht0 => htame₁ q hqS ht0)

/-! #### Whole-piece chart-disk subdivision -/

/-- The chart ball of a cover disk lies inside the chart target. -/
theorem ball_subset_chartAt_target (j : 𝔇.toFiniteCover.ι) :
    Metric.ball (chartMap 𝔇 j (𝔇.center j)) (𝔇.radius j)
      ⊆ (chartAt ℂ (𝔇.center j)).target := by
  intro w hw
  have hyU : (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm w ∈ (𝔇.U j : Set X) :=
    symm_mem_U_of_mem_ball 𝔇 hw
  have h := (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hyU)
  rwa [show (chartAt ℂ (𝔇.center j)) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).symm w) = w from
    (extChartAt 𝓘(ℝ, ℂ) (𝔇.center j)).right_inv
      (𝔇.closedBall_subset_target j (Metric.ball_subset_closedBall hw))] at h

/-- **Whole-piece chart-disk subdivision**: parameter points `k/N` with each WHOLE piece
`γ([k/N, (k+1)/N])` inside one cover disk (Lebesgue number along the path; the piece has
diameter `1/N < δ`).  Strengthens `exists_subdivision` from endpoint to piece
containment, which is what the chart-ball period comparison consumes. -/
theorem exists_subdivision_pieces {P Q : X} {γ : ℝ → X} (h : IsSmoothPath P Q γ) :
    ∃ (N : ℕ) (j : ℕ → 𝔇.toFiniteCover.ι), 0 < N ∧
      ∀ k, k < N → ∀ t ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
        γ t ∈ (𝔇.U (j k) : Set X) := by
  classical
  have hcov : Set.Icc (0 : ℝ) 1 ⊆ ⋃ j : 𝔇.toFiniteCover.ι, γ ⁻¹' (𝔇.U j : Set X) := by
    intro t _
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (𝔇.toFiniteCover.covers ▸ Set.mem_univ (γ t) : γ t ∈ ⨆ i, 𝔇.toFiniteCover.U i)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun j => (𝔇.U j).isOpen.preimage h.cont) hcov
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNpos' : 0 < N := by exact_mod_cast hNpos
  have hsel : ∀ k : ℕ, k < N → ∃ j : 𝔇.toFiniteCover.ι,
      Metric.ball ((k : ℝ) / N) δ ⊆ γ ⁻¹' (𝔇.U j : Set X) := by
    intro k hk
    refine hball ((k : ℝ) / N) ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hk.le
  have hne : Nonempty 𝔇.toFiniteCover.ι := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (𝔇.toFiniteCover.covers ▸ Set.mem_univ x : x ∈ ⨆ i, 𝔇.toFiniteCover.U i)
    exact ⟨j⟩
  refine ⟨N, fun k => if hk : k < N then (hsel k hk).choose else hne.some, hNpos', ?_⟩
  intro k hk t ht
  have h1N : (1 : ℝ) / N < δ := by
    rw [div_lt_iff₀ hNpos]
    have h2 := (div_lt_iff₀ hδ).mp hN
    linarith [mul_comm δ (N : ℝ)]
  have hlen : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
    push_cast
    ring
  have htball : t ∈ Metric.ball ((k : ℝ) / N) δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  have hres := (hsel k hk).choose_spec htball
  simpa [dif_pos hk] using hres

/-! #### E4 COMPLETE: the boundary datum with its pairing value -/

/-- **E4, complete**: every smooth 1-chain admits an arc weak solution for its boundary
divisor whose `(0,1)` datum pairs against every holomorphic 1-form to `π·∫_c α` — the
honest pairing identity in the Lebesgue-area chart-coefficient convention
(`dz̄∧dz = 2i·dA`, so Forster's `∫∫ σ∧α = 2πi·∫_c α` reads `π·∫_c α`). -/
theorem exists_arcWeakSolution_boundary_pairing (c : SmoothOneChain X) :
    ∃ W : ArcWeakSolution 𝔇 c.boundary,
      ∀ α : HolomorphicOneForms X,
        FineResidue.pairOmega 𝔇 W.σ α = (Real.pi : ℂ) * c.period α := by
  classical
  choose N j hNpos hpiece using fun i : Fin c.n => exists_subdivision_pieces 𝔇 (c.smooth i)
  set p : Fin c.n → ℕ → X := fun i k => c.path i ((k : ℝ) / (N i)) with hp
  have hNR : ∀ i, (0 : ℝ) < ((N i : ℕ) : ℝ) := fun i => by exact_mod_cast hNpos i
  -- endpoint identification
  have hp0 : ∀ i, p i 0 = c.src i := by
    intro i
    show c.path i (((0 : ℕ) : ℝ) / (N i)) = c.src i
    rw [Nat.cast_zero, zero_div]
    exact (c.smooth i).start
  have hpN : ∀ i, p i (N i) = c.tgt i := by
    intro i
    show c.path i (((N i : ℕ) : ℝ) / (N i)) = c.tgt i
    rw [div_self (hNR i).ne']
    exact (c.smooth i).finish
  -- piece-parameter facts
  have hk_left : ∀ i (k : ℕ),
      (k : ℝ) / (N i) ∈ Set.Icc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)) := by
    intro i k
    refine ⟨le_rfl, ?_⟩
    gcongr
    linarith
  have hk_right : ∀ i (k : ℕ),
      ((k + 1 : ℕ) : ℝ) / (N i) ∈ Set.Icc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)) := by
    intro i k
    refine ⟨?_, le_rfl⟩
    gcongr
    linarith
  have hmem : ∀ i (k : ℕ), k < N i → p i k ∈ (𝔇.U (j i k) : Set X)
      ∧ p i (k + 1) ∈ (𝔇.U (j i k) : Set X) := fun i k hk =>
    ⟨hpiece i k hk _ (hk_left i k), hpiece i k hk _ (hk_right i k)⟩
  -- the tagged list
  set L : List ((X × X) × 𝔇.toFiniteCover.ι) :=
    (List.ofFn fun i : Fin c.n =>
      zsmulListTag (consecPairsTag (p i) (j i) (N i)) (c.coeff i)).flatten with hL
  -- divisor identification
  have hfst : L.map Prod.fst
      = (List.ofFn fun i : Fin c.n =>
          zsmulList (consecPairs (p i) (N i)) (c.coeff i)).flatten := by
    have hfun : (List.map (Prod.fst (β := 𝔇.toFiniteCover.ι)) ∘ fun i : Fin c.n =>
        zsmulListTag (consecPairsTag (p i) (j i) (N i)) (c.coeff i))
        = fun i : Fin c.n => zsmulList (consecPairs (p i) (N i)) (c.coeff i) := by
      funext i
      show (zsmulListTag (consecPairsTag (p i) (j i) (N i)) (c.coeff i)).map Prod.fst = _
      rw [map_fst_zsmulListTag, map_fst_consecPairsTag]
    rw [hL, List.map_flatten, List.map_ofFn, hfun]
  have hdiv : dipoleDiv (L.map Prod.fst) = c.boundary := by
    rw [hfst, dipoleDiv_flatten, List.map_ofFn, List.sum_ofFn, SmoothOneChain.boundary]
    refine Finset.sum_congr rfl fun i _ => ?_
    show dipoleDiv (zsmulList (consecPairs (p i) (N i)) (c.coeff i)) = _
    rw [dipoleDiv_zsmulList, dipoleDiv_consecPairs, hpN i, hp0 i]
  -- chart-disk membership of the tagged entries
  have hdiskL : ∀ q ∈ L, q.1.1 ∈ (𝔇.U q.2 : Set X) ∧ q.1.2 ∈ (𝔇.U q.2 : Set X) := by
    intro q hq
    rw [hL, List.mem_flatten] at hq
    obtain ⟨l, hl, hql⟩ := hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    rcases mem_zsmulListTag hql with hmem' | hmem'
    · obtain ⟨k, hk, rfl⟩ := mem_consecPairsTag hmem'
      exact ⟨(hmem i k hk).1, (hmem i k hk).2⟩
    · obtain ⟨k, hk, hswap⟩ := mem_consecPairsTag hmem'
      have hq' : q = ((p i (k + 1), p i k), j i k) := by
        have hss := congrArg swapTag hswap
        rwa [swapTag_swapTag] at hss
      rw [hq']
      exact ⟨(hmem i k hk).2, (hmem i k hk).1⟩
  -- the endpoint avoid set
  set S : Finset X :=
    ((L.map Prod.fst).map Prod.fst ++ (L.map Prod.fst).map Prod.snd).toFinset with hSdef
  have hSL : ∀ q ∈ L, q.1.1 ∈ S ∧ q.1.2 ∈ S := by
    intro q hq
    rw [hSdef]
    constructor
    · rw [List.mem_toFinset, List.mem_append]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hq))
    · rw [List.mem_toFinset, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (List.mem_map_of_mem hq))
  -- the tagged fold
  obtain ⟨W, hval, -, -⟩ := exists_arcWeakSolution_dipoleListChart 𝔇 S L hdiskL hSL
  -- per-path piece-sum identity: Σ segment values = line integral
  have hper_i : ∀ (α : HolomorphicOneForms X) (i : Fin c.n),
      ((consecPairsTag (p i) (j i) (N i)).map fun q => segPeriod α (𝔇.center q.2)
          (chartMap 𝔇 q.2 q.1.1) (chartMap 𝔇 q.2 q.1.2)).sum
        = lineIntegral α (c.path i) := by
    intro α i
    rw [sum_map_consecPairsTag]
    have hint01 : IntervalIntegrable
        (fun t => α.toFun (c.path i t) (pathSpeed (c.path i) t)) MeasureTheory.volume 0 1 :=
      intervalIntegrable_form_pathSpeed_of_velContinuous α (c.path i) (c.smooth i).velCont
    have hIccsub : ∀ k : ℕ, k < N i →
        Set.Icc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro k hk
      refine Set.Icc_subset_Icc (by positivity) ?_
      rw [div_le_one (hNR i)]
      exact_mod_cast hk
    have hle : ∀ k : ℕ, (k : ℝ) / (N i) ≤ ((k + 1 : ℕ) : ℝ) / (N i) := fun k =>
      (hk_left i k).2
    have huIcc_sub : ∀ k : ℕ, k < N i →
        Set.uIcc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)) ⊆ Set.uIcc (0 : ℝ) 1 := by
      intro k hk
      rw [Set.uIcc_of_le (hle k), Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hIccsub k hk
    have hpieceInt : ∀ k : ℕ, k < N i → IntervalIntegrable
        (fun t => α.toFun (c.path i t) (pathSpeed (c.path i) t)) MeasureTheory.volume
        ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)) := fun k hk =>
      hint01.mono_set (huIcc_sub k hk)
    calc ∑ k ∈ Finset.range (N i), segPeriod α (𝔇.center (j i k))
            (chartMap 𝔇 (j i k) (p i k)) (chartMap 𝔇 (j i k) (p i (k + 1)))
        = ∑ k ∈ Finset.range (N i), ∫ t in ((k : ℝ) / (N i))..(((k + 1 : ℕ) : ℝ) / (N i)),
            α.toFun (c.path i t) (pathSpeed (c.path i) t) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hsub := ball_subset_chartAt_target 𝔇 (j i k)
          have hγ_in : ∀ t ∈ Set.Icc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)),
              c.path i t ∈ (chartAt ℂ (𝔇.center (j i k))).source := fun t ht =>
            mem_chartSource_of_mem_U 𝔇 (hpiece i k hk t ht)
          have himg : ∀ t ∈ Set.Icc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)),
              (chartAt ℂ (𝔇.center (j i k))) (c.path i t)
                ∈ Metric.ball (chartMap 𝔇 (j i k) (𝔇.center (j i k))) (𝔇.radius (j i k)) := by
            intro t ht
            have hU := hpiece i k hk t ht
            rw [𝔇.isDisk (j i k)] at hU
            exact hU.1
          have hγ_diff : ∀ t ∈ Set.uIcc ((k : ℝ) / (N i)) (((k + 1 : ℕ) : ℝ) / (N i)),
              DifferentiableAt ℝ ((chartAt (H := ℂ) (𝔇.center (j i k))).toFun ∘ c.path i)
                t := by
            intro t ht
            rw [Set.uIcc_of_le (hle k)] at ht
            refine differentiableAt_chart_comp_transfer (𝔇.center (j i k)) ?_
              (c.smooth i).cont ?_
            · exact ((chartAt ℂ (𝔇.center (j i k))).open_source.preimage
                (c.smooth i).cont).mem_nhds (hγ_in t ht)
            · refine (c.smooth i).diff t ?_
              rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
              exact hIccsub k hk ht
          exact (intervalIntegral_form_eq_segPeriod α (𝔇.center (j i k)) (hle k) hsub
            hγ_in himg (c.smooth i).cont hγ_diff (hpieceInt k hk)).symm
      _ = ∫ t in (((0 : ℕ) : ℝ) / (N i))..(((N i : ℕ) : ℝ) / (N i)),
            α.toFun (c.path i t) (pathSpeed (c.path i) t) :=
          intervalIntegral.sum_integral_adjacent_intervals hpieceInt
      _ = lineIntegral α (c.path i) := by
          rw [lineIntegral, Nat.cast_zero, zero_div, div_self (hNR i).ne']
  -- assemble the chain value
  rw [← hdiv]
  refine ⟨W, ?_⟩
  intro α
  rw [hval α, SmoothOneChain.period]
  congr 1
  rw [hL]
  rw [List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((zsmulListTag (consecPairsTag (p i) (j i) (N i)) (c.coeff i)).map fun q =>
      segPeriod α (𝔇.center q.2) (chartMap 𝔇 q.2 q.1.1) (chartMap 𝔇 q.2 q.1.2)).sum = _
  rw [sum_map_zsmulListTag _ (fun q => segPeriod_swap α (𝔇.center q.2) _ _), hper_i α i]

include 𝔇 in
/-- **THE UNCONDITIONAL ENGINE** (Forster §20, E-block COMPLETE): a smooth 1-chain all of
whose periods vanish bounds a principal divisor.  E4 is discharged by
`exists_arcWeakSolution_boundary_pairing`: the constructed datum pairs to `π·∫_c α = 0`,
which (with the periods zero) meets the E2 pairing field `2πi·∫_c α = 0`. -/
theorem exists_meromorphic_of_zeroPeriodChain' (c : SmoothOneChain X)
    (hper : ∀ α : HolomorphicOneForms X, c.period α = 0) :
    ∃ f : MeromorphicFunction X, MeromorphicFunction.div X f = c.boundary := by
  obtain ⟨W, hW⟩ := exists_arcWeakSolution_boundary_pairing 𝔇 c
  refine exists_meromorphic_of_zeroPeriodChain_of_pairing 𝔇 c W ?_ hper
  intro α
  rw [hW α, hper α, mul_zero, mul_zero]


end ChainAssembly

end Jacobians.Dolbeault

end
