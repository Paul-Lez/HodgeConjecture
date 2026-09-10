/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.AbelSubsetEngine

/-!
# Abel ⊆ campaign, E-block: the W1/W2 local-analysis walls

The two local-analysis walls of `docs/planning/AB_E_ROUTE.md` §2, discharged:

* **W1** (`∂̄`-kernel ⟹ meromorphic): a corrected weak solution `F·e^{−u}` whose planar `∂̄`
  vanishes off the chain support is chart-holomorphic there (Wirtinger,
  `differentiableAt_of_dbar_eq_zero_local`), and its `z^{∂c(a)}·(continuous unit)` normal form
  at each support point upgrades to a meromorphic singularity by the removable-singularity
  theorem (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`).
* **W2** (normal form ⟹ order): the corrected function has `orderAtPoint = ∂c(a)` at support
  points (`meromorphicOrderAt_eq_int_iff`) and `orderAtPoint = 0` elsewhere (analytic
  nonvanishing), so its divisor is exactly `∂c`.

Both are packaged as the constructor `RawLogDbarDatum.toLogDbarDatum`: the **raw** datum
carries only the geometric output of the Forster 20.4/20.5 construction —

* the weak solution `F`, nonvanishing off the chain support, with planar
  `∂̄F = F·σ` in every cover chart off the support (`dbar_eq`),
* the local normal form `F = (z − a)^{∂c(a)}·(continuous unit)` at each support point
  (`norm_form`),
* the global `(0,1)` datum `σ` and the E4 pairing identity —

and the constructor discharges the two consequence fields (`mero_correction`,
`div_correction`) of the E2 interface `LogDbarDatum` from them.  The remaining E3
obligation is therefore exactly the raw geometric datum.

Supporting planar/chart toolkit added here:

* `dbarFun_neg` / `dbarFun_exp` — Wirtinger `∂̄` of negation and of `exp ∘ v`
  (holomorphic-outer chain rule).
* `analyticAt_atlasTransition` / `analyticAt_chartRead_transfer` — chart-transition
  analyticity (the `IsManifold 𝓘(ℂ) ω` coordinate-change brick, extracted from
  `Abel.lean`'s `orderAtPoint_chart_invariant`) and transport of chart-read analyticity
  between atlas members.
* `meromorphicAt_of_normalForm` — `MeromorphicAt` from an eventual `(z−a)^n·(analytic)`
  presentation.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §§20.4–20.5; Miranda,
*Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VIII §4.
-/

open Complex
open scoped Manifold ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Jacobians.Dolbeault

open FineResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Planar Wirtinger additions -/

/-- **Planar `∂̄` Leibniz rule** `∂̄(f·g) z = g z·∂̄f z + f z·∂̄g z` at a point where both
factors are real-differentiable.  Local re-proof of `dbarFun_mul` (`GluedDbarDatum.lean`),
which cannot be imported here: its import closure (via `CechFinitenessBallSolve`) collides
with `AbelSubsetPairing`'s (duplicate `rhoC` vs `DolbeaultComparisonInverse`). -/
theorem dbarFun_mul' {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x * g x) z
      = g z * DbarDisk.dbar f z + f z * DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`∂̄ = 0 ⇒ holomorphic`, local form (Wirtinger).**  A function `ℝ`-differentiable at `x`
with vanishing Wirtinger `∂̄` is `ℂ`-differentiable at `x`.  Local re-proof of
`differentiableAt_of_dbar_eq_zero_local` (`CechFinitenessBallSolve.lean`), which cannot be
imported here for the same `rhoC` collision. -/
private theorem differentiableAt_of_dbar_eq_zero_local' {g : ℂ → ℂ} {x : ℂ}
    (hg : DifferentiableAt ℝ g x) (hdb : DbarDisk.dbar g x = 0) : DifferentiableAt ℂ g x := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hg, ?_⟩
  have h2 : (fderiv ℝ g x) 1 + Complex.I * (fderiv ℝ g x) Complex.I = 0 := by
    have := hdb
    rw [DbarDisk.dbar] at this
    field_simp at this
    linear_combination this
  have hD1 : (fderiv ℝ g x) 1 = -(Complex.I * (fderiv ℝ g x) Complex.I) := by linear_combination h2
  rw [hD1, smul_eq_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring

/-- `∂̄` of a negation. -/
theorem dbarFun_neg {v : ℂ → ℂ} {z : ℂ} :
    DbarDisk.dbar (fun w => -(v w)) z = -DbarDisk.dbar v z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

/-- **Holomorphic-outer chain rule for `∂̄`**: `∂̄(exp ∘ v) = exp(v)·∂̄v` at a point where `v`
is real-differentiable.  (The outer `exp` is `ℂ`-differentiable, so its real Fréchet
derivative is `ℂ`-linear and factors out of the Wirtinger combination.) -/
theorem dbarFun_exp {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) :
    DbarDisk.dbar (fun w => Complex.exp (v w)) z
      = Complex.exp (v z) * DbarDisk.dbar v z := by
  have hexp : HasFDerivAt Complex.exp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp (v z))).restrictScalars ℝ)
      (v z) :=
    (Complex.hasDerivAt_exp (v z)).hasFDerivAt.restrictScalars ℝ
  have hcomp : HasFDerivAt (fun w => Complex.exp (v w))
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (Complex.exp (v z))).restrictScalars ℝ).comp (fderiv ℝ v z)) z :=
    hexp.comp z hv.hasFDerivAt
  unfold DbarDisk.dbar
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-- `∂̄(exp(−v)) = −exp(−v)·∂̄v` (the form the `F·e^{−u}` correction uses). -/
theorem dbarFun_exp_neg {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) :
    DbarDisk.dbar (fun w => Complex.exp (-(v w))) z
      = -(Complex.exp (-(v z)) * DbarDisk.dbar v z) := by
  have h := dbarFun_exp (v := fun w => -(v w)) (z := z) hv.neg
  rw [h, dbarFun_neg]
  ring

/-! ## Chart-transition analyticity and chart-read transport

The coordinate-change brick of `IsManifold 𝓘(ℂ) ω`, extracted (and generalized to two
arbitrary atlas members) from the proof of
`Jacobians.MeromorphicFunction.orderAtPoint_chart_invariant` (`Abel.lean`). -/

/-- The transition `e₂ ∘ e₁.symm` between two atlas charts is analytic at the `e₁`-coordinate
of any point in both sources. -/
theorem analyticAt_atlasTransition {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (h₁ : e₁ ∈ atlas ℂ X) (h₂ : e₂ ∈ atlas ℂ X) {y : X}
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) :
    AnalyticAt ℂ (e₂ ∘ e₁.symm) (e₁ y) := by
  have h₁max : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.subset_maximalAtlas h₁
  have h₂max : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.subset_maximalAtlas h₂
  have h_contDiffAt : ContDiffAt ℂ ω (↑(𝓘(ℂ).extendCoordChange e₁ e₂))
      (e₁.extend 𝓘(ℂ) y) := by
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange' h₁max h₂max hy₁ hy₂
    rwa [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  have h_analyticAt : AnalyticAt ℂ (↑(𝓘(ℂ).extendCoordChange e₁ e₂))
      (e₁.extend 𝓘(ℂ) y) := h_contDiffAt.analyticAt
  exact h_analyticAt

/-- **Chart-read transport of analyticity**: if `f ∘ e₂.symm` is analytic at `e₂ y`, then
`f ∘ e₁.symm` is analytic at `e₁ y`, for any two atlas charts containing `y`. -/
theorem analyticAt_chartRead_transfer {f : X → ℂ} {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (h₁ : e₁ ∈ atlas ℂ X) (h₂ : e₂ ∈ atlas ℂ X) {y : X}
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source)
    (h : AnalyticAt ℂ (f ∘ e₂.symm) (e₂ y)) :
    AnalyticAt ℂ (f ∘ e₁.symm) (e₁ y) := by
  have hτ : AnalyticAt ℂ (e₂ ∘ e₁.symm) (e₁ y) := analyticAt_atlasTransition h₁ h₂ hy₁ hy₂
  have hτy : (e₂ ∘ e₁.symm) (e₁ y) = e₂ y := by
    show e₂ (e₁.symm (e₁ y)) = e₂ y
    rw [e₁.left_inv hy₁]
  have hcomp : AnalyticAt ℂ ((f ∘ e₂.symm) ∘ (e₂ ∘ e₁.symm)) (e₁ y) := by
    refine AnalyticAt.comp ?_ hτ
    rw [hτy]
    exact h
  refine hcomp.congr ?_
  have hcont : ContinuousAt e₁.symm (e₁ y) := e₁.continuousAt_symm (e₁.map_source hy₁)
  have hmem : e₁.symm ⁻¹' e₂.source ∈ 𝓝 (e₁ y) := by
    refine hcont.preimage_mem_nhds ?_
    rw [e₁.left_inv hy₁]
    exact e₂.open_source.mem_nhds hy₂
  filter_upwards [hmem] with w hw
  show f (e₂.symm (e₂ (e₁.symm w))) = f (e₁.symm w)
  rw [e₂.left_inv hw]

/-- **`MeromorphicAt` from a normal form**: a function eventually equal (on a punctured
neighbourhood) to `(z − pt)^n · w` with `w` analytic is meromorphic at `pt`. -/
theorem meromorphicAt_of_normalForm {g : ℂ → ℂ} {pt : ℂ} {n : ℤ} {w : ℂ → ℂ}
    (hw : AnalyticAt ℂ w pt) (hev : ∀ᶠ z in 𝓝[≠] pt, g z = (z - pt) ^ n * w z) :
    MeromorphicAt g pt := by
  have hbase : MeromorphicAt (fun z => z - pt) pt :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hzp : MeromorphicAt (fun z => (z - pt) ^ n) pt := hbase.zpow n
  have hprod : MeromorphicAt (fun z => (z - pt) ^ n * w z) pt := hzp.mul hw.meromorphicAt
  refine hprod.congr ?_
  filter_upwards [hev] with z hz
  exact hz.symm

/-! ## The raw logarithmic-`∂̄` datum (the E3 construction target) -/

/-- **The raw logarithmic-`∂̄` datum of a chain** — the direct geometric output of the
Forster 20.4/20.5 per-arc weak-solution construction, *before* the W1/W2 local analysis:

* `F` — the weak solution, nonvanishing off the chain boundary support (`F_ne`);
* `σ` — the global smooth `(0,1)` datum `∂̄ log F`;
* `pairing` — the E4 identity `∫_X σ∧α = 2πi·∫_c α`;
* `diff_off`/`dbar_eq` — off the boundary support, the cover-chart read of `F` is
  real-differentiable with planar `∂̄F = F·σ̃` (`σ̃` the proven cutoff chart read of `σ`);
* `norm_form` — at each boundary point `a`, the own-chart read of `F` is eventually
  `(z − a)^{∂c(a)}·(continuous nonvanishing unit)` on a punctured neighbourhood.

`RawLogDbarDatum.toLogDbarDatum` below discharges the E2 consequence fields from these. -/
structure RawLogDbarDatum (𝔇 : ChartDiskCover X) (c : SmoothOneChain X) where
  /-- The weak solution. -/
  F : X → ℂ
  /-- The global smooth `(0,1)` logarithmic datum `σ = ∂̄ log F`. -/
  σ : ↥(OneFormsZeroOne X)
  /-- E4, the pairing identity: `∫_X σ∧α = 2πi·∫_c α` for every holomorphic 1-form. -/
  pairing : ∀ α : HolomorphicOneForms X,
    FineResidue.pairOmega 𝔇 σ α = 2 * (Real.pi : ℂ) * Complex.I * c.period α
  /-- `F` is nonvanishing off the boundary support. -/
  F_ne : ∀ x : X, c.boundary x = 0 → F x ≠ 0
  /-- Off the boundary support, the cover-chart read of `F` is real-differentiable. -/
  diff_off : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → c.boundary x = 0 →
    DifferentiableAt ℝ (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w))
      (chartMap 𝔇 j x)
  /-- Off the boundary support, the planar logarithmic `∂̄`-identity `∂̄F = F·σ̃` holds in
  every cover chart. -/
  dbar_eq : ∀ (j : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U j : Set X) → c.boundary x = 0 →
    DbarDisk.dbar (fun w => F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
      = F x * 𝔇.cutoffPullback j (σ : SmoothCOneForms X) (chartMap 𝔇 j x)
  /-- At each boundary point, the own-chart read of `F` has the local normal form
  `(z − a)^{∂c(a)}·(continuous nonvanishing unit)`. -/
  norm_form : ∀ a : X, c.boundary a ≠ 0 → ∃ w : ℂ → ℂ,
    ContinuousAt w ((chartAt (H := ℂ) a) a) ∧ w ((chartAt (H := ℂ) a) a) ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
      F ((chartAt (H := ℂ) a).symm z)
        = (z - (chartAt (H := ℂ) a) a) ^ (c.boundary a) * w z

namespace RawLogDbarDatum

variable {𝔇 : ChartDiskCover X} {c : SmoothOneChain X} (R : RawLogDbarDatum 𝔇 c)

/-- **W1, cover-chart form.**  Off the boundary support, the cover-chart read of the
corrected function `F·e^{−u}` is analytic: the Leibniz/chain-rule computation kills its
planar `∂̄` pointwise on the open off-support chart patch (`∂̄F = F·σ̃` against
`∂̄ũ = σ̃`, P4a `cutoffPullback_dbarL`), and Wirtinger upgrades to `ℂ`-differentiability,
hence analyticity on the open patch. -/
theorem analyticAt_corrected_coverRead {u : SmoothCFunctions X}
    (hu : dbarL u = (R.σ : SmoothCOneForms X)) {j : 𝔇.toFiniteCover.ι} {y : X}
    (hyU : y ∈ (𝔇.U j : Set X)) (hy0 : c.boundary y = 0) :
    AnalyticAt ℂ ((fun x => R.F x * Complex.exp (-(u x)))
        ∘ (chartAt (H := ℂ) (𝔇.center j)).symm) (chartMap 𝔇 j y) := by
  classical
  -- The open off-support patch of the chart image.
  have hSfin : (↑(c.boundary.support) : Set X).Finite := (c.boundary.support).finite_toSet
  have hUS_open : IsOpen ((𝔇.U j : Set X) \ ↑(c.boundary.support)) :=
    (𝔇.U j).isOpen.sdiff hSfin.isClosed
  have hUS_sub : ((𝔇.U j : Set X) \ ↑(c.boundary.support))
      ⊆ (chartAt (H := ℂ) (𝔇.center j)).source :=
    fun x hx => mem_chartSource_of_mem_U 𝔇 hx.1
  have hVopen : IsOpen ((chartAt (H := ℂ) (𝔇.center j))
      '' ((𝔇.U j : Set X) \ ↑(c.boundary.support))) :=
    (chartAt (H := ℂ) (𝔇.center j)).isOpen_image_of_subset_source hUS_open hUS_sub
  have hymem : chartMap 𝔇 j y ∈ (chartAt (H := ℂ) (𝔇.center j))
      '' ((𝔇.U j : Set X) \ ↑(c.boundary.support)) :=
    ⟨y, ⟨hyU, fun hyS => (Finsupp.mem_support_iff.mp hyS) hy0⟩, rfl⟩
  -- ℂ-differentiability on the patch, pointwise via Wirtinger.
  have hVdiff : DifferentiableOn ℂ ((fun x => R.F x * Complex.exp (-(u x)))
      ∘ (chartAt (H := ℂ) (𝔇.center j)).symm)
      ((chartAt (H := ℂ) (𝔇.center j)) '' ((𝔇.U j : Set X) \ ↑(c.boundary.support))) := by
    rintro z ⟨x, ⟨hxU, hxS⟩, rfl⟩
    have hx0 : c.boundary x = 0 := by
      by_contra h0
      exact hxS (Finsupp.mem_support_iff.mpr h0)
    have hxsrc : x ∈ (chartAt (H := ℂ) (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
    have hsx : (chartAt (H := ℂ) (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
      (chartAt (H := ℂ) (𝔇.center j)).left_inv hxsrc
    have hzt : chartMap 𝔇 j x ∈ (chartAt (H := ℂ) (𝔇.center j)).target :=
      (chartAt (H := ℂ) (𝔇.center j)).map_source hxsrc
    -- Real-differentiability of the three reads.
    have hFd : DifferentiableAt ℝ
        (fun w => R.F ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x) :=
      R.diff_off j x hxU hx0
    have hucd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => u ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x) :=
      contDiffAt_chartSymmRead u.contMDiff hzt
    have hud : DifferentiableAt ℝ
        (fun w => u ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x) :=
      hucd.differentiableAt (by simp)
    have hEd : DifferentiableAt ℝ
        (fun w => Complex.exp (-(u ((chartAt (H := ℂ) (𝔇.center j)).symm w))))
        (chartMap 𝔇 j x) := hud.neg.cexp
    -- The planar ∂̄ of the corrected read vanishes.
    have hu_dbar : DbarDisk.dbar
        (fun w => u ((chartAt (H := ℂ) (𝔇.center j)).symm w)) (chartMap 𝔇 j x)
          = 𝔇.cutoffPullback j (R.σ : SmoothCOneForms X) (chartMap 𝔇 j x) := by
      rw [← FineResidue.cutoffPullback_dbarL 𝔇 hxU, hu]
    have hE_dbar : DbarDisk.dbar
        (fun w => Complex.exp (-(u ((chartAt (H := ℂ) (𝔇.center j)).symm w))))
        (chartMap 𝔇 j x)
          = -(Complex.exp (-(u ((chartAt (H := ℂ) (𝔇.center j)).symm (chartMap 𝔇 j x))))
              * 𝔇.cutoffPullback j (R.σ : SmoothCOneForms X) (chartMap 𝔇 j x)) := by
      rw [dbarFun_exp_neg hud, hu_dbar]
    have hdbar0 : DbarDisk.dbar
        (fun w => R.F ((chartAt (H := ℂ) (𝔇.center j)).symm w)
          * Complex.exp (-(u ((chartAt (H := ℂ) (𝔇.center j)).symm w))))
        (chartMap 𝔇 j x) = 0 := by
      have hmul := dbarFun_mul' hFd hEd
      rw [hmul, hE_dbar, R.dbar_eq j x hxU hx0, hsx]
      ring
    -- Wirtinger.
    have hprod_d : DifferentiableAt ℝ
        (fun w => R.F ((chartAt (H := ℂ) (𝔇.center j)).symm w)
          * Complex.exp (-(u ((chartAt (H := ℂ) (𝔇.center j)).symm w))))
        (chartMap 𝔇 j x) := hFd.mul hEd
    exact (differentiableAt_of_dbar_eq_zero_local' hprod_d hdbar0).differentiableWithinAt
  exact hVdiff.analyticAt (hVopen.mem_nhds hymem)

/-- **W1 at an arbitrary atlas chart.**  Off the boundary support, the read of the corrected
function in *any* atlas chart containing the point is analytic (cover-chart analyticity +
chart-read transport). -/
theorem analyticAt_corrected_read {u : SmoothCFunctions X}
    (hu : dbarL u = (R.σ : SmoothCOneForms X)) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ atlas ℂ X) {y : X} (hy : y ∈ e.source) (hy0 : c.boundary y = 0) :
    AnalyticAt ℂ ((fun x => R.F x * Complex.exp (-(u x))) ∘ e.symm) (e y) := by
  obtain ⟨j, hyU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (𝔇.toFiniteCover.covers ▸ Set.mem_univ y : y ∈ ⨆ i, 𝔇.toFiniteCover.U i)
  exact analyticAt_chartRead_transfer he (chart_mem_atlas ℂ (𝔇.center j)) hy
    (mem_chartSource_of_mem_U 𝔇 hyU) (R.analyticAt_corrected_coverRead hu hyU hy0)

/-- **W1+W2 at a boundary point**: the own-chart read of the corrected function `F·e^{−u}`
has an eventual `(z − a)^{∂c(a)}·(analytic nonvanishing unit)` presentation.  The continuous
unit `w·e^{−ũ}` upgrades to an analytic one by the removable-singularity theorem, using the
punctured-neighbourhood holomorphy from W1 (nearby points are off the finite support). -/
theorem normalForm_corrected {u : SmoothCFunctions X}
    (hu : dbarL u = (R.σ : SmoothCOneForms X)) {a : X} (ha : c.boundary a ≠ 0) :
    ∃ w' : ℂ → ℂ, AnalyticAt ℂ w' ((chartAt (H := ℂ) a) a) ∧
      w' ((chartAt (H := ℂ) a) a) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
        ((fun x => R.F x * Complex.exp (-(u x))) ∘ (chartAt (H := ℂ) a).symm) z
          = (z - (chartAt (H := ℂ) a) a) ^ (c.boundary a) * w' z := by
  classical
  obtain ⟨w, hwc, hwne, hwev⟩ := R.norm_form a ha
  have hsymm_cont : ContinuousAt (chartAt (H := ℂ) a).symm ((chartAt (H := ℂ) a) a) :=
    (chartAt (H := ℂ) a).continuousAt_symm
      ((chartAt (H := ℂ) a).map_source (mem_chart_source ℂ a))
  have hEcont : ContinuousAt
      (fun z => Complex.exp (-(u ((chartAt (H := ℂ) a).symm z))))
      ((chartAt (H := ℂ) a) a) :=
    Complex.continuous_exp.continuousAt.comp
      ((u.contMDiff.continuous.continuousAt.comp hsymm_cont).neg)
  refine ⟨fun z => w z * Complex.exp (-(u ((chartAt (H := ℂ) a).symm z))), ?_, ?_, ?_⟩
  · -- Analyticity of the unit, via removable singularity.
    -- The corrected read is ℂ-differentiable on a punctured neighbourhood:
    have hSfin : ((↑(c.boundary.support) : Set X) \ {a}).Finite :=
      ((c.boundary.support).finite_toSet).subset Set.diff_subset
    have hWopen : IsOpen ((chartAt (H := ℂ) a).source
        \ ((↑(c.boundary.support) : Set X) \ {a})) :=
      (chartAt (H := ℂ) a).open_source.sdiff hSfin.isClosed
    have hWsub : ((chartAt (H := ℂ) a).source \ ((↑(c.boundary.support) : Set X) \ {a}))
        ⊆ (chartAt (H := ℂ) a).source := Set.diff_subset
    have hVWopen : IsOpen ((chartAt (H := ℂ) a)
        '' ((chartAt (H := ℂ) a).source \ ((↑(c.boundary.support) : Set X) \ {a}))) :=
      (chartAt (H := ℂ) a).isOpen_image_of_subset_source hWopen hWsub
    have hptVW : (chartAt (H := ℂ) a) a ∈ (chartAt (H := ℂ) a)
        '' ((chartAt (H := ℂ) a).source \ ((↑(c.boundary.support) : Set X) \ {a})) :=
      ⟨a, ⟨mem_chart_source ℂ a, fun h => h.2 rfl⟩, rfl⟩
    have hdiff_punct : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
        DifferentiableAt ℂ
          ((fun x => R.F x * Complex.exp (-(u x))) ∘ (chartAt (H := ℂ) a).symm) z := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVWopen.mem_nhds hptVW),
        self_mem_nhdsWithin] with z hzV hzne
      obtain ⟨y', hy'W, rfl⟩ := hzV
      have hy'ne : y' ≠ a := by
        intro h
        exact hzne (by rw [h]; rfl)
      have hy'0 : c.boundary y' = 0 := by
        by_contra h0
        exact hy'W.2 ⟨Finsupp.mem_support_iff.mpr h0, hy'ne⟩
      exact (R.analyticAt_corrected_read hu (chart_mem_atlas ℂ a) hy'W.1 hy'0).differentiableAt
    -- The corrected eventual normal form (needed to solve for the unit).
    have hgev : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
        ((fun x => R.F x * Complex.exp (-(u x))) ∘ (chartAt (H := ℂ) a).symm) z
          = (z - (chartAt (H := ℂ) a) a) ^ (c.boundary a)
              * (w z * Complex.exp (-(u ((chartAt (H := ℂ) a).symm z)))) := by
      filter_upwards [hwev] with z hz
      show R.F ((chartAt (H := ℂ) a).symm z) * _ = _
      rw [hz]
      ring
    -- The unit is ℂ-differentiable on the punctured neighbourhood (solve for it).
    have hw'diff : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
        DifferentiableAt ℂ
          (fun z => w z * Complex.exp (-(u ((chartAt (H := ℂ) a).symm z)))) z := by
      have hcomb := hgev.and hdiff_punct
      rw [eventually_nhdsWithin_iff] at hcomb
      obtain ⟨O, hO_sub, hOopen, hptO⟩ := mem_nhds_iff.mp hcomb
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hOopen.mem_nhds hptO] with z hzO hzne
      have hzne' : z ≠ (chartAt (H := ℂ) a) a := by simpa using hzne
      have hOpen' : IsOpen (O \ {(chartAt (H := ℂ) a) a}) := hOopen.sdiff isClosed_singleton
      have hmem' : z ∈ O \ {(chartAt (H := ℂ) a) a} := ⟨hzO, by simpa using hzne'⟩
      have hev_eq : (fun z => w z * Complex.exp (-(u ((chartAt (H := ℂ) a).symm z))))
          =ᶠ[𝓝 z] fun ζ => (ζ - (chartAt (H := ℂ) a) a) ^ (-(c.boundary a))
            * (((fun x => R.F x * Complex.exp (-(u x)))
                ∘ (chartAt (H := ℂ) a).symm) ζ) := by
        filter_upwards [hOpen'.mem_nhds hmem'] with ζ hζ
        have hζne : ζ ≠ (chartAt (H := ℂ) a) a := by simpa using hζ.2
        obtain ⟨heq, -⟩ := hO_sub hζ.1 (by simpa using hζne)
        have hbase : ζ - (chartAt (H := ℂ) a) a ≠ 0 := sub_ne_zero.mpr hζne
        rw [heq, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hbase), one_mul]
      obtain ⟨-, hdz⟩ := hO_sub hzO (by simpa using hzne')
      have hz1 : DifferentiableAt ℂ
          (fun ζ : ℂ => (ζ - (chartAt (H := ℂ) a) a) ^ (-(c.boundary a))) z :=
        (differentiableAt_id.sub_const _).zpow (Or.inl (sub_ne_zero.mpr hzne'))
      exact (hz1.mul hdz).congr_of_eventuallyEq hev_eq
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hw'diff (hwc.mul hEcont)
  · exact mul_ne_zero hwne (Complex.exp_ne_zero _)
  · filter_upwards [hwev] with z hz
    show R.F ((chartAt (H := ℂ) a).symm z) * _ = _
    rw [hz]
    ring

/-- **W1, assembled**: any global smooth `∂̄`-antiderivative of `σ` corrects `F` to a
meromorphic function. -/
theorem isMeromorphic_corrected {u : SmoothCFunctions X}
    (hu : dbarL u = (R.σ : SmoothCOneForms X)) :
    IsMeromorphic X fun x => R.F x * Complex.exp (-(u x)) := by
  intro y
  by_cases hy0 : c.boundary y = 0
  · exact (R.analyticAt_corrected_read hu (chart_mem_atlas ℂ y)
      (mem_chart_source ℂ y) hy0).meromorphicAt
  · obtain ⟨w', hw'an, hw'ne, hev⟩ := R.normalForm_corrected hu hy0
    exact meromorphicAt_of_normalForm hw'an hev

/-- **W1+W2, the constructor**: a raw logarithmic-`∂̄` datum yields the E2 interface — the
two consequence fields (`mero_correction`, `div_correction`) are discharged by the local
analysis above. -/
def toLogDbarDatum : LogDbarDatum 𝔇 c where
  F := R.F
  σ := R.σ
  pairing := R.pairing
  mero_correction := fun u hu => R.isMeromorphic_corrected hu
  div_correction := fun u hu => by
    refine Finsupp.ext fun a => ?_
    show (Finsupp.ofSupportFinite _ _) a = c.boundary a
    rw [Finsupp.ofSupportFinite_coe]
    by_cases ha : c.boundary a = 0
    · rw [ha]
      have han := R.analyticAt_corrected_read hu (chart_mem_atlas ℂ a)
        (mem_chart_source ℂ a) ha
      have hval : ((fun x => R.F x * Complex.exp (-(u x)))
          ∘ (chartAt (H := ℂ) a).symm) ((chartAt (H := ℂ) a) a) ≠ 0 := by
        show R.F ((chartAt (H := ℂ) a).symm ((chartAt (H := ℂ) a) a)) * _ ≠ 0
        rw [(chartAt (H := ℂ) a).left_inv (mem_chart_source ℂ a)]
        exact mul_ne_zero (R.F_ne a ha) (Complex.exp_ne_zero _)
      show (meromorphicOrderAt _ _).untop₀ = 0
      rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hval]
      rfl
    · obtain ⟨w', hw'an, hw'ne, hev⟩ := R.normalForm_corrected hu ha
      have hmero := meromorphicAt_of_normalForm hw'an hev
      have hord := (meromorphicOrderAt_eq_int_iff hmero).mpr
        ⟨w', hw'an, hw'ne, by
          filter_upwards [hev] with z hz
          rw [smul_eq_mul]
          exact hz⟩
      show (meromorphicOrderAt _ _).untop₀ = c.boundary a
      rw [hord]
      exact WithTop.untop₀_coe _

@[simp] theorem toLogDbarDatum_F : R.toLogDbarDatum.F = R.F := rfl

@[simp] theorem toLogDbarDatum_σ : R.toLogDbarDatum.σ = R.σ := rfl

end RawLogDbarDatum

end Jacobians.Dolbeault

end
