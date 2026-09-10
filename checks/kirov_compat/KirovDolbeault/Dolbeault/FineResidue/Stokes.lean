/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Integral
import KirovDolbeault.Dolbeault.ChartDiskFiniteness
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# R5a — the planar Stokes atom and the `∂̄`-packaging of the chart-pushed PoU weight

First half of lane-R rung R5 (S3 scoping §4.R5, `docs/planning/S3_FINESHEAF_RES_SCOPING.md`;
campaign `docs/planning/CAMPAIGN_KEYSTONE.md`).  Two independent deliverables:

1. **The planar Stokes atom** (`integral_dbar_eq_zero`):

     `∫_ℂ ∂̄g dA = 0`  for `g` smooth with compact support.

   This is the only genuinely *integral* input of the coboundary-vanishing assembly (R5b,
   `CoboundaryVanish.lean`): on a compact surface `∬_X ∂̄β = 0`, and in the chart-coefficient
   representation every global term is a compactly supported planar function, so the surface
   Stokes reduces to the planar one.  Route: `∂̄ = ½(∂ₓ + i·∂_y)` is a fixed combination of two
   directional derivatives, and `∫_ℂ ∂_v g = 0` for each direction `v` is integration by parts
   against the constant `1` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, the Fubini +
   line-FTC content prepackaged in Mathlib; the same divergence-theorem layer as the port's
   `greenOnUnitBox` precedent, with no boundary term because the support is compact).

2. **The `∂̄`-packaging of `pouCoeff`** — the gap flagged in the R4 handoff: R4 proved
   `contDiff_pouCoeff` but never computed its `∂̄`.  The two-case pattern of `contDiff_pouCoeff`
   yields the chart read of `∂̄ρ_j` (the manifold-level `dbarRho` of the backbone) through the
   indicator:

   * `dbar_pouCoeff_chartRead` — on the chart image of `U j`, `∂̄ρ̃_j` is the `∂̄` of the honest
     chart read `ρ_j ∘ (chart j).symm` (the indicator only removes zeros);
   * `dbar_pouCoeff_eq_zero_of_notMem_image_tsupport` — off the (compact) chart image of
     `tsupport ρ_j`, `∂̄ρ̃_j = 0` (the frontier case, killed by the compact-tsupport clearance).

   Plus the PoU-reinsertion identity `sum_dbar_rhoC_read` — the chart-read form of the backbone's
   `sum_dbarRho_eq_zero`: at any point of a chart target, `∑_j ∂̄(ρ_j ∘ (chart k).symm) = 0`,
   because `∑_j ρ_j = 1` *globally* (`sum_rhoC_apply`), so the sum of the reads is the constant
   `1`.  This is what kills the relocated `∑_j (∂̄ρ̃_j)·β_j` sum in R5b.

Supporting planar `∂̄`-calculus (`dbar_congr_of_eventuallyEq`, `dbar_eq_zero_of_eventuallyEq_zero`,
`dbar_finset_sum`) and the two-case globalization helpers (`contDiff_of_chartImage_clearance`,
`contDiff_pouCoeff_mul`) used throughout R5b's integrability bookkeeping.

The sign/normalization convention remains the **pinned** R0 gate (`SignTest.lean`):
`resNormalization = −π⁻¹` on Lebesgue-area integrals of `(1,1)` chart coefficients — cited,
never re-derived; nothing in this file touches it (the Stokes atom is normalization-free:
its right-hand side is `0`).
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`Integral` (the
-- `SmoothCFunctions` coercions of `rhoC` below need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

/-! ### The planar Stokes atom -/

/-- The integral of a single directional derivative of a compactly supported smooth function
vanishes: `∫_ℂ (∂_v g) dA = 0`.  Integration by parts against the constant function `1`
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` — Mathlib's Fubini + line-FTC layer),
whose derivative term vanishes identically. -/
theorem integral_fderiv_apply_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (v : ℂ) :
    ∫ z, fderiv ℝ g z v = 0 := by
  have hzero : (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) z v * g z) = fun _ => 0 := by
    funext z
    simp [fderiv_fun_const]
  have hf'g : Integrable (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) z v * g z) := by
    rw [hzero]
    exact integrable_zero _ _ _
  have hcont : Continuous fun z : ℂ => fderiv ℝ g z v :=
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp (hg.continuous_fderiv (by norm_num))
  have hint : Integrable fun z : ℂ => fderiv ℝ g z v :=
    hcont.integrable_of_hasCompactSupport (hgsupp.fderiv_apply ℝ v)
  have hfg' : Integrable (fun z : ℂ => (1 : ℂ) * fderiv ℝ g z v) := by
    simpa only [one_mul] using hint
  have hfg : Integrable (fun z : ℂ => (1 : ℂ) * g z) := by
    simpa only [one_mul] using hg.continuous.integrable_of_hasCompactSupport hgsupp
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => differentiableAt_const (1 : ℂ))
    (fun x _ => hg.differentiable (by norm_num) x)
  simpa [fderiv_fun_const] using key

/-- **The R5 planar Stokes atom**: `∫_ℂ ∂̄g dA = 0` for `g` smooth with compact support.
`∂̄g = ½(∂ₓg + i·∂_y g)` is a fixed ℂ-linear combination of two directional derivatives, each of
which integrates to zero (`integral_fderiv_apply_eq_zero`).  This is the well-definedness input
of the fine-sheaf residue functional: Forster §17.3 step 5, `∬_X ∂̄β = 0` on the compact surface,
in the chart-coefficient representation. -/
theorem integral_dbar_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) :
    ∫ z, DbarDisk.dbar g z = 0 := by
  have hcd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have h1 : Integrable fun z : ℂ => fderiv ℝ g z 1 :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp
      hcd).integrable_of_hasCompactSupport (hgsupp.fderiv_apply ℝ 1)
  have hI : Integrable fun z : ℂ => fderiv ℝ g z Complex.I :=
    ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp
      hcd).integrable_of_hasCompactSupport (hgsupp.fderiv_apply ℝ Complex.I)
  have key : ∫ z, ((2 : ℂ)⁻¹ * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)) = 0 := by
    rw [integral_const_mul, integral_add h1 (hI.const_mul _), integral_const_mul,
      integral_fderiv_apply_eq_zero hg hgsupp 1,
      integral_fderiv_apply_eq_zero hg hgsupp Complex.I, mul_zero, add_zero, mul_zero]
  exact key

/-! ### Planar `∂̄` plumbing -/

/-- `∂̄` only depends on the germ: functions agreeing near `z` have the same `∂̄` at `z`. -/
theorem dbar_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    DbarDisk.dbar f z = DbarDisk.dbar g z := by
  simp only [DbarDisk.dbar, h.fderiv_eq]

/-- A function vanishing near `z` has `∂̄ = 0` at `z`. -/
theorem dbar_eq_zero_of_eventuallyEq_zero {f : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] fun _ => (0 : ℂ)) : DbarDisk.dbar f z = 0 := by
  rw [dbar_congr_of_eventuallyEq h]
  exact DbarDisk.dbar_const 0 z

/-- `∂̄` of a finite sum is the sum of the `∂̄`s, at a point where every summand is
`ℝ`-differentiable. -/
theorem dbar_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    DbarDisk.dbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, DbarDisk.dbar (f i) z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_sum hf]
  simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]

/-! ### Chart reads of global smooth functions -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The chart read `F ∘ (chart c).symm` of a globally smooth `F : X → ℂ` is planar-smooth at
every point of the chart target (the `RealManifold` bridge through `contMDiffOn_chart_symm`). -/
theorem contDiffAt_chartSymmRead {F : X → ℂ}
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F) {c : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ c).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => F ((chartAt ℂ c).symm w)) z := by
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ c).symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := c) _ hz).contMDiffAt
      ((chartAt ℂ c).open_target.mem_nhds hz)
  exact contMDiffAt_iff_contDiffAt.1 ((hF _).comp z hsymm)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart read of a function vanishing near the read point has `∂̄ = 0`: junk values outside
the target never matter because the read is locally the zero function. -/
theorem dbar_chartSymmRead_eq_zero {F : X → ℂ} {c : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ c).target)
    (hF : ∀ᶠ y in 𝓝 ((chartAt ℂ c).symm z), F y = 0) :
    DbarDisk.dbar (fun w => F ((chartAt ℂ c).symm w)) z = 0 := by
  have hcont : ContinuousAt (chartAt ℂ c).symm z :=
    (chartAt ℂ c).symm.continuousAt (by rwa [(chartAt ℂ c).symm_source])
  exact dbar_eq_zero_of_eventuallyEq_zero (hcont.eventually hF)

variable (𝔇 : ChartDiskCover X)

omit [Nonempty X] in
/-- The chart image of `U j` lies in the chart target. -/
theorem chartMap_image_U_subset_target (j : 𝔇.toFiniteCover.ι) :
    chartMap 𝔇 j '' (𝔇.U j : Set X) ⊆ (chartAt ℂ (𝔇.center j)).target := by
  rintro z ⟨x, hx, rfl⟩
  exact (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hx)

/-- **PoU reinsertion in a chart** — the chart-read form of the backbone's
`sum_dbarRho_eq_zero`: at any point of the chart-`k` target, the `∂̄`s of the chart reads of the
PoU weights sum to zero, because `∑_j ρ_j = 1` holds *globally* on `X` (`sum_rhoC_apply`), so the
sum of the reads is the constant `1` even through the junk values of `(chart k).symm`. -/
theorem sum_dbar_rhoC_read (k : 𝔇.toFiniteCover.ι) {z : ℂ}
    (hz : z ∈ (chartAt ℂ (𝔇.center k)).target) :
    ∑ j, DbarDisk.dbar (fun w => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm w)) z = 0 := by
  have hdiff : ∀ j ∈ (Finset.univ : Finset 𝔇.toFiniteCover.ι),
      DifferentiableAt ℝ (fun w => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm w)) z := fun j _ =>
    (contDiffAt_chartSymmRead (rhoC 𝔇 j).contMDiff hz).differentiableAt (by simp)
  rw [← dbar_finset_sum Finset.univ hdiff]
  have hone : (fun w => ∑ j, rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm w))
      = fun _ => (1 : ℂ) := funext fun w => sum_rhoC_apply 𝔇 _
  rw [hone]
  exact DbarDisk.dbar_const 1 z

/-! ### `∂̄` of the chart-pushed PoU weight (the R4 packaging gap) -/

/-- **Frontier clearance**: off the (compact) chart image of `tsupport ρ_j`, the chart-pushed
PoU weight is locally identically zero, so its `∂̄` vanishes. -/
theorem dbar_pouCoeff_eq_zero_of_notMem_image_tsupport {j : 𝔇.toFiniteCover.ι} {z : ℂ}
    (hz : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)) :
    DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 := by
  refine dbar_eq_zero_of_eventuallyEq_zero ?_
  filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇 j).isClosed.isOpen_compl.mem_nhds hz]
    with w hw
  exact pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hw

/-- **`∂̄ρ̃_j` is the chart read of `∂̄ρ_j`**: on the (open) chart image of `U j` the indicator
cutoff of `pouCoeff` is locally invisible, so its `∂̄` is the `∂̄` of the honest chart read
`ρ_j ∘ (chart j).symm` — the planar coefficient of the backbone's `dbarRho 𝔇 j`. -/
theorem dbar_pouCoeff_chartRead {j : 𝔇.toFiniteCover.ι} {z : ℂ}
    (hz : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)) :
    DbarDisk.dbar (pouCoeff 𝔇 j) z
      = DbarDisk.dbar (fun w => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm w)) z := by
  refine dbar_congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_chartMap_image 𝔇 j (𝔇.U j).isOpen (subset_refl _)).mem_nhds hz]
    with w hw
  exact Set.indicator_of_mem hw _

/-! ### Two-case globalization helpers -/

/-- **Two-case globalization at cover index `j`**: a planar function smooth at every point of the
(open) chart image of `U j` and vanishing off the (compact, hence closed) chart image of
`tsupport ρ_j` is globally smooth — the `contDiff_pouCoeff` pattern, factored out for the R5b
integrability bookkeeping. -/
theorem contDiff_of_chartImage_clearance {j : 𝔇.toFiniteCover.ι} {F : ℂ → ℂ}
    (hsm : ∀ z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X), ContDiffAt ℝ (⊤ : ℕ∞) F z)
    (h0 : ∀ z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j), F z = 0) :
    ContDiff ℝ (⊤ : ℕ∞) F := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)
  · exact hsm z (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hz)
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇 j).isClosed.isOpen_compl.mem_nhds hz]
      with w hw
    exact h0 w hw

/-- The product of the chart-pushed PoU weight with any function smooth on the chart image of its
cover set is globally smooth (generalizes the `t j`-specific `continuous_pouCoeff_mul` of R4 to
`ContDiff`, for the Stokes atom's hypotheses). -/
theorem contDiff_pouCoeff_mul {j : 𝔇.toFiniteCover.ι} {u : ℂ → ℂ}
    (hu : ∀ z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X), ContDiffAt ℝ (⊤ : ℕ∞) u z) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => pouCoeff 𝔇 j z * u z := by
  refine contDiff_of_chartImage_clearance 𝔇
    (fun z hz => ((contDiff_pouCoeff 𝔇 j).contDiffAt).mul (hu z hz)) (fun z hz => ?_)
  rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul]

end Jacobians.Dolbeault.FineResidue
