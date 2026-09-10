/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Stokes

/-!
# R5b — coboundary Stokes: the residue functional kills coboundaries

Second half of lane-R rung R5 (S3 scoping §4.R5, Forster §17.3 step 5).  For **coboundary**
overlap data — `w i j = h j − h i` on overlaps, with `h` a per-chart holomorphic 0-cochain —
the glued `(1,1)` family `t = glueCoeff 𝔇 w g` integrates to zero:

  `resFunctional 𝔇 t = 0`   (`resFunctional_eq_zero_of_coboundary`).

This is the well-definedness of the fine-sheaf residue on Čech classes: combined with R4's
linearity it makes `resFunctional` descend to the `Z¹/B¹` quotient.  In the port's packaging
(`GlobalResidueConstruct.CousinResidueData`) the descent is `Submodule.liftQ` through the
`vanish_coboundary` field — this file provides exactly the statement that field needs, at the
chart-coefficient level; the R7 rung supplies the germ→coefficient extraction that connects a
Čech coboundary in `B¹(𝒪_K)` to the hypotheses here, and instantiates `liftQ`.

## The mathematics (Forster §17.3, step 5)

For `w = δh`, the PoU split collapses: `σ_i = ∑_k ρ_k·(h_i − h_k) = h_i − β` with
`β := ∑_k ρ_k·h_k` a **global** smooth scalar (`pouAverage`, `pouSplit_eq_of_coboundary`).
Since `h_i` is holomorphic, `∂̄σ_i = −∂̄β` in chart coordinates, so the Forster `(1,1)` density
is `τ = −∂̄(β·ω₀)` — exact.  Then

  `I(t) = ∑_j ∫ ρ̃_j·t_j = −∑_j ∫ ρ̃_j·∂̄B_j`,  `B_j := β̃_j·g_j` (the chart read of `β·ω₀`),

and the Leibniz rule `∂̄(ρ̃_j·B_j) = (∂̄ρ̃_j)·B_j + ρ̃_j·∂̄B_j` (R0's `dbar_mul`) splits each term:

* the total-derivative part dies **termwise** by the planar Stokes atom
  (`integral_dbar_eq_zero`, R5a): each `ρ̃_j·B_j` is globally smooth with compact support;
* the curvature part `∑_j ∫ (∂̄ρ̃_j)·B_j` dies by **PoU reinsertion + relocation**: insert
  `1 = ∑_k ρ_k` (`sum_rhoC_apply`), re-route each `(j,k)` term to chart `k` through R4's
  `setIntegral_overlap_relocate` (the `(1,1)` family for the relocation is
  `∂̄ρ_j ∧ (β·ω₀)` in chart coefficients, `isOneOneCoeff_dbarRead_mul`), and sum over `j`
  *at fixed chart `k`*: `∑_j ∂̄ρ̃_j = ∂̄(∑_j ρ_j) = ∂̄1 = 0` (`sum_dbar_rhoC_read`, the
  chart-read `sum_dbarRho_eq_zero`).

All integrability is the R4/R5a clearance bookkeeping (`contDiff_of_chartImage_clearance`,
compact supports from `pouCoeff`).  The normalization is the **pinned** R0 constant
`resNormalization = −π⁻¹` (`SignTest.lean`) — cited through `resFunctional`, never re-derived
(and irrelevant here: `resNormalization · 0 = 0`).

## Main declarations

* `SmoothOnSets` / `HolomorphicOnSets` — a per-chart 0-cochain `h`, smooth and chart-holomorphic
  on its own cover set (junk elsewhere, the germ discipline of R1/R2).
* `IsCoboundaryOn 𝔇 w h` — `w i j = h j − h i` pointwise **on overlaps** (membership-guarded:
  germ-representative noise off the overlaps never enters).
* `smoothOnOverlaps_of_coboundary` / `isOverlapCocycle_of_coboundary` /
  `holomorphicOnOverlaps_of_coboundary` — coboundary data satisfies all R2/R3 input predicates,
  so `glueCoeff 𝔇 w g ∈ oneOneCoeff 𝔇` comes from `glueCoeff_mem_oneOneCoeff` for free.
* `pouAverage` / `pouSplit_eq_of_coboundary` — the Forster collapse `σ_i = h_i − β`.
* `isOneOneCoeff_dbarRead_mul` — the relocation family `i ↦ ∂̄(F∘chartᵢ⁻¹)·(G∘chartᵢ⁻¹)·g_i`
  is a `(1,1)` chart-coefficient family for global smooth `F, G` and a `(1,0)` slot family `g`.
* `resIntegralFun_eq_zero_of_coboundary` — the unnormalized headline `I(δh·ω₀) = 0`.
* `resFunctional_eq_zero_of_coboundary` — **the R5 headline**: the residue functional kills
  coboundaries (the `vanish_coboundary` feeder for the R7 `Submodule.liftQ` descent).
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultComparisonInverse`/`Stokes` (the
-- `SmoothCFunctions` coercions of `rhoC` below need it).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### Per-chart holomorphic 0-cochains and the coboundary predicate -/

/-- A value family `h` is **smooth on its own cover sets** when each `h j` is `C^∞` (over `ℝ`)
at every point of `U j`.  Values outside `U j` are junk and never consumed. -/
def SmoothOnSets (h : 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ j, ∀ x ∈ (𝔇.U j : Set X), ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (h j) x

/-- A value family `h` is **holomorphic on its own cover sets** when the chart-`j` read of `h j`
is `ℂ`-differentiable at the chart image of every point of `U j` — the 0-cochain analogue of
`HolomorphicOnOverlaps`. -/
def HolomorphicOnSets (h : 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ j, ∀ x ∈ (𝔇.U j : Set X),
    DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center j)).symm z)) (chartMap 𝔇 j x)

/-- An overlap family `w` is **the coboundary of `h` on overlaps**: `w i j = h j − h i`
pointwise on every overlap `U i ⊓ U j`.  Membership-guarded (the R1/R2 germ discipline):
values of `w` off the overlaps are junk and never constrained — this is the shape in which
R7's germ→coefficient extraction of a Čech coboundary `δh ∈ B¹` delivers its function reps. -/
def IsCoboundaryOn (w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ)
    (h : 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ i j, ∀ x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X), w i j x = h j x - h i x

omit [Nonempty X] in
/-- Coboundary data is smooth on overlaps (each `h` factor is smooth on its own set, and the
overlap lies in both). -/
theorem smoothOnOverlaps_of_coboundary {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hsm : SmoothOnSets 𝔇 h) (hδ : IsCoboundaryOn 𝔇 w h) :
    SmoothOnOverlaps 𝔇 w := by
  intro i j x hx
  refine ((hsm j x hx.2).sub (hsm i x hx.1)).congr_of_eventuallyEq ?_
  filter_upwards [(𝔇.U i ⊓ 𝔇.U j : Opens X).isOpen.mem_nhds hx] with y hy
  exact hδ i j y hy

omit [Nonempty X] in
/-- Coboundary data is an overlap cocycle (the telescoping differences cancel). -/
theorem isOverlapCocycle_of_coboundary {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hδ : IsCoboundaryOn 𝔇 w h) :
    IsOverlapCocycle 𝔇 w := by
  intro a b c x hx
  rw [hδ b c x ⟨hx.1.2, hx.2⟩, hδ a c x ⟨hx.1.1, hx.2⟩, hδ a b x hx.1]
  ring

omit [Nonempty X] in
/-- The chart-`k` inverse relocates through the transition: near the chart-`j` coordinate of an
overlap point, `(chart k).symm ∘ φ_{jk} = (chart j).symm` — both read the same surface point. -/
theorem symm_transitionMap_eventuallyEq {j k : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X)) :
    (fun z => (chartAt ℂ (𝔇.center k)).symm (transitionMap 𝔇 j k z))
      =ᶠ[𝓝 (chartMap 𝔇 j x)] fun z => (chartAt ℂ (𝔇.center j)).symm z := by
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx.1
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
    (chartAt ℂ (𝔇.center j)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hov : ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact (𝔇.U j ⊓ 𝔇.U k : Opens X).isOpen.mem_nhds hx
  filter_upwards [hcont.preimage_mem_nhds hov] with z hz
  show (chartAt ℂ (𝔇.center k)).symm
      ((chartAt ℂ (𝔇.center k)) ((chartAt ℂ (𝔇.center j)).symm z)) = _
  rw [(chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hz.2)]

omit [Nonempty X] in
/-- Coboundary data is holomorphic on overlaps: each chart read is a difference of holomorphic
reads, the off-index one relocated through the holomorphic transition. -/
theorem holomorphicOnOverlaps_of_coboundary {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hhol : HolomorphicOnSets 𝔇 h)
    (hδ : IsCoboundaryOn 𝔇 w h) : HolomorphicOnOverlaps 𝔇 w := by
  intro i j x hx
  have hxi : x ∈ (𝔇.U i : Set X) := hx.1
  have hxj : x ∈ (𝔇.U j : Set X) := hx.2
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hxi
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hxsrc
  have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
    (chartAt ℂ (𝔇.center i)).map_source hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) :=
    (chartAt ℂ (𝔇.center i)).symm.continuousAt
      (by rwa [(chartAt ℂ (𝔇.center i)).symm_source])
  -- the i-read of `h j` is the j-read relocated through the transition, hence holomorphic
  have hcomp : DifferentiableAt ℂ
      (fun z => h j ((chartAt ℂ (𝔇.center j)).symm (transitionMap 𝔇 i j z)))
      (chartMap 𝔇 i x) := by
    have hbase : DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center j)).symm z))
        (transitionMap 𝔇 i j (chartMap 𝔇 i x)) := by
      rw [transitionMap_chartMap 𝔇 hxi]
      exact hhol j x hxj
    exact hbase.comp _ (transitionMap_analyticAt 𝔇 hxi hxj).differentiableAt
  have hread_j : DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center i)).symm z))
      (chartMap 𝔇 i x) := by
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with z hz
    rw [hz]
  have hov : ((𝔇.U i ⊓ 𝔇.U j : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x)) := by
    rw [hli]
    exact (𝔇.U i ⊓ 𝔇.U j : Opens X).isOpen.mem_nhds hx
  have hev : (fun z => w i j ((chartAt ℂ (𝔇.center i)).symm z))
      =ᶠ[𝓝 (chartMap 𝔇 i x)] fun z =>
        h j ((chartAt ℂ (𝔇.center i)).symm z) - h i ((chartAt ℂ (𝔇.center i)).symm z) := by
    filter_upwards [hcont.preimage_mem_nhds hov] with z hz
    exact hδ i j _ hz
  exact (hread_j.sub (hhol i x hxi)).congr_of_eventuallyEq hev

/-! ### The Forster collapse `σ_i = h_i − β` -/

/-- The **PoU average** `β := ∑_k ρ_k·h_k` — Forster's global smooth scalar against which a
coboundary split telescopes (`β·ω₀` is his global `(1,0)`-form `β`). -/
noncomputable def pouAverage (h : 𝔇.toFiniteCover.ι → X → ℂ) : X → ℂ :=
  fun x => ∑ k, rhoC 𝔇 k x * h k x

@[simp] theorem pouAverage_apply (h : 𝔇.toFiniteCover.ι → X → ℂ) (x : X) :
    pouAverage 𝔇 h x = ∑ k, rhoC 𝔇 k x * h k x := rfl

/-- The PoU average of a family smooth on its own cover sets is **globally** smooth (the
`gdTerm` support-aware gluing: off `tsupport ρ_k` the `k`-summand is locally zero). -/
theorem contMDiff_pouAverage {h : 𝔇.toFiniteCover.ι → X → ℂ} (hsm : SmoothOnSets 𝔇 h) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouAverage 𝔇 h) := by
  intro x
  refine ContMDiffAt.sum fun k _ => ?_
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
  · exact ((rhoC 𝔇 k).contMDiff x).mul (hsm k x (cechPoU_subordinate 𝔇 k hb))
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hb] with y hy
    have hr : rhoC 𝔇 k y = 0 := by
      simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hy]
      rfl
    simp only [hr, zero_mul]

/-- **The Forster collapse**: for coboundary data the PoU split telescopes against the global
average, `σ_i = h_i − β` on `U i`.  Termwise: either `ρ_k = 0` (both contributions die), or
subordination puts the point in `U k ⊓ U i` where `w k i = h i − h k`. -/
theorem pouSplit_eq_of_coboundary {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hδ : IsCoboundaryOn 𝔇 w h) {i : 𝔇.toFiniteCover.ι}
    {x : X} (hx : x ∈ (𝔇.U i : Set X)) :
    pouSplit 𝔇 w i x = h i x - pouAverage 𝔇 h x := by
  have hpt : ∀ k, rhoC 𝔇 k x * w k i x = rhoC 𝔇 k x * h i x - rhoC 𝔇 k x * h k x := by
    intro k
    by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
    · rw [hδ k i x ⟨cechPoU_subordinate 𝔇 k hb, hx⟩, mul_sub]
    · have hr : rhoC 𝔇 k x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hb]
        rfl
      simp only [hr, zero_mul, sub_zero]
  calc pouSplit 𝔇 w i x
      = ∑ k, (rhoC 𝔇 k x * h i x - rhoC 𝔇 k x * h k x) := by
        rw [pouSplit_apply]
        exact Finset.sum_congr rfl fun k _ => hpt k
    _ = (∑ k, rhoC 𝔇 k x) * h i x - pouAverage 𝔇 h x := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, pouAverage_apply]
    _ = h i x - pouAverage 𝔇 h x := by rw [sum_rhoC_apply, one_mul]

/-! ### The relocation family `∂̄F ∧ (G·ω₀)` in chart coefficients -/

omit [Nonempty X] in
/-- For globally smooth `F, G : X → ℂ` and a holomorphic `(1,0)` slot family `g`, the family

  `i ↦ ∂̄(F ∘ (chart i).symm) · (G ∘ (chart i).symm · g_i)`

is a `(1,1)` chart-coefficient family — the chart presentation of the global `(1,1)`-form
`∂̄F ∧ (G·ω₀)`.  The `(0,1)` factor `conj φ′` comes from the chain rule on the relocated read,
the scalar `G`-read is transition-invariant, and the `dz`-slot supplies `φ′`
(`Complex.mul_conj` reassembles R1's `normSq φ′`, exactly as in `glueCoeff_mem_oneOneCoeff`).
This is the family R5b relocates through `setIntegral_overlap_relocate` (with `F = ρ_j`,
`G = pouAverage`). -/
theorem isOneOneCoeff_dbarRead_mul {F G : X → ℂ}
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F)
    (hG : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) G)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => F ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (G ((chartAt ℂ (𝔇.center i)).symm z) * g i z) := by
  constructor
  · intro i x hx
    have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
      (chartAt ℂ (𝔇.center i)).map_source (mem_chartSource_of_mem_U 𝔇 hx)
    exact (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiffAt_chartSymmRead hF hzt)).mul
      ((contDiffAt_chartSymmRead hG hzt).mul
        (((hg.1 i x hx).restrictScalars (𝕜 := ℝ)).contDiffAt))
  · intro j k x hx
    have hxj : x ∈ (𝔇.U j : Set X) := hx.1
    have hxk : x ∈ (𝔇.U k : Set X) := hx.2
    have hzkt : chartMap 𝔇 k x ∈ (chartAt ℂ (𝔇.center k)).target :=
      (chartAt ℂ (𝔇.center k)).map_source (mem_chartSource_of_mem_U 𝔇 hxk)
    have htend : Tendsto (transitionMap 𝔇 j k) (𝓝 (chartMap 𝔇 j x))
        (𝓝 (chartMap 𝔇 k x)) := by
      have hc := (transitionMap_analyticAt 𝔇 hxj hxk).continuousAt
      rwa [ContinuousAt, transitionMap_chartMap 𝔇 hxj] at hc
    have hFev : (fun ζ => F ((chartAt ℂ (𝔇.center k)).symm (transitionMap 𝔇 j k ζ)))
        =ᶠ[𝓝 (chartMap 𝔇 j x)] fun ζ => F ((chartAt ℂ (𝔇.center j)).symm ζ) := by
      filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with ζ hζ
      rw [hζ]
    unfold OneOneLawAt
    filter_upwards [hFev.eventuallyEq_nhds, symm_transitionMap_eventuallyEq 𝔇 hx,
      (transitionMap_analyticAt 𝔇 hxj hxk).eventually_analyticAt,
      htend.eventually ((chartAt ℂ (𝔇.center k)).open_target.mem_nhds hzkt),
      hg.2 j k x hx] with z hzF hzsymm hzan hztgt hzg
    have h1 : DbarDisk.dbar (fun ζ => F ((chartAt ℂ (𝔇.center j)).symm ζ)) z
        = DbarDisk.dbar
            (fun ζ => F ((chartAt ℂ (𝔇.center k)).symm (transitionMap 𝔇 j k ζ))) z :=
      (dbar_congr_of_eventuallyEq hzF).symm
    have h2 := dbar_comp (f := fun ζ => F ((chartAt ℂ (𝔇.center k)).symm ζ))
      (φ := transitionMap 𝔇 j k)
      ((contDiffAt_chartSymmRead hF hztgt).differentiableAt (by simp))
      hzan.differentiableAt
    rw [Function.comp_def] at h2
    have hns : ((normSq (deriv (transitionMap 𝔇 j k) z) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 j k) z
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 j k) z) :=
      (Complex.mul_conj _).symm
    rw [h1, h2, hzg, ← hzsymm, hns]
    ring

/-! ### The Leibniz/Stokes step (per chart) -/

omit [Nonempty X] in
/-- The chart-`j` read of `β·ω₀` is smooth at the chart image of `U j`. -/
theorem contDiffAt_pouAverageRead_mul {β : X → ℂ}
    (hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) β) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (j : 𝔇.toFiniteCover.ι) :
    ∀ z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ζ => β ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) z := by
  rintro z ⟨x, hxU, rfl⟩
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hxU)
  exact (contDiffAt_chartSymmRead hβ hzt).mul
    (((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).contDiffAt)

/-- **The Leibniz/Stokes step**: for coboundary data, the `j`-th summand of the residue
integral is, after the Forster collapse `∂̄s_j = −∂̄β̃_j`, the Leibniz split

  `∫ ρ̃_j·t_j = −∫ ρ̃_j·∂̄B_j = ∫ (∂̄ρ̃_j)·B_j − ∫ ∂̄(ρ̃_j·B_j) = ∫ (∂̄ρ̃_j)·B_j`,

the total derivative dying by the planar Stokes atom; then PoU reinsertion `1 = ∑_k ρ_k`
unfolds the survivor into the `(j,k)` overlap terms ready for relocation. -/
theorem integral_pouCoeff_glueCoeff_of_coboundary
    {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hsm : SmoothOnSets 𝔇 h)
    (hhol : HolomorphicOnSets 𝔇 h) (hδ : IsCoboundaryOn 𝔇 w h) (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
  have hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouAverage 𝔇 h) :=
    contMDiff_pouAverage 𝔇 hsm
  have hBsm := contDiffAt_pouAverageRead_mul 𝔇 hβ hg j
  -- the everywhere pointwise Leibniz identity
  have hpt : ∀ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        - DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z := by
    intro z
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
      have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
        (chartAt ℂ (𝔇.center j)).map_source hxsrc
      have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
        (chartAt ℂ (𝔇.center j)).symm.continuousAt
          (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv hxsrc
      have hovU : ((𝔇.U j : Opens X) : Set X)
          ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
        rw [hli]
        exact (𝔇.U j).isOpen.mem_nhds hxU
      -- the Forster collapse, read in chart-`j` coordinates
      have hsplit_ev : splitCoeff 𝔇 w j =ᶠ[𝓝 (chartMap 𝔇 j x)]
          fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)
            - pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) := by
        filter_upwards [hcont.preimage_mem_nhds hovU] with ζ hζ
        rw [splitCoeff_apply, pouSplit_eq_of_coboundary 𝔇 hδ hζ]
      have hBd : DifferentiableAt ℝ
          (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) :=
        (contDiffAt_chartSymmRead hβ hzt).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        (((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt)
      have hdbar_split : DbarDisk.dbar (splitCoeff 𝔇 w j) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) := by
        rw [dbar_congr_of_eventuallyEq hsplit_ev,
          DbarOpenDisk.dbar_sub ((hhol j x hxU).restrictScalars ℝ) hBd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hhol j x hxU), zero_sub]
      have hdbarB : DbarDisk.dbar
            (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hBd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarPB : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _)
          ((hBsm _ ⟨x, hxU, rfl⟩).differentiableAt (by simp))
      rw [glueCoeff_apply, hdbar_split, hdbarPB, hdbarB]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hPB0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hP0, hD0, hPB0, zero_mul, zero_mul, sub_zero]
  -- integrability bookkeeping
  have hDBcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    contDiff_of_chartImage_clearance 𝔇
      (fun z hz => (ChartDiskCover.contDiffAt_dbar_chartDisk
        (contDiff_pouCoeff 𝔇 j).contDiffAt).mul (hBsm z hz))
      (fun z hz => by rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul])
  have hDBcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hI1 : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hDBcd.continuous.integrable_of_hasCompactSupport hDBcs
  have hPBcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    contDiff_pouCoeff_mul 𝔇 hBsm
  have hPBcs : HasCompactSupport fun ζ => pouCoeff 𝔇 j ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ) :=
    (hasCompactSupport_pouCoeff 𝔇 j).mul_right
  have hI2 : Integrable fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z :=
    (DbarDisk.continuous_dbar hPBcd).integrable_of_hasCompactSupport
      (DbarDisk.hasCompactSupport_dbar hPBcs)
  calc ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = ∫ z, (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
          - DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
          - ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z :=
        integral_sub hI1 hI2
    _ = ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
        rw [integral_dbar_eq_zero hPBcd hPBcs, sub_zero]
    _ = ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
    _ = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
        refine integral_finsetSum Finset.univ fun k _ => ?_
        have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
            rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
          contDiff_of_chartImage_clearance 𝔇
            (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
              (chartMap_image_U_subset_target 𝔇 j hz)).mul hDBcd.contDiffAt)
            (fun z hz => by
              rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
        exact hcd.continuous.integrable_of_hasCompactSupport hDBcs.mul_left

/-! ### The relocation step (per overlap pair) -/

/-- **The relocation step**: the `(j,k)` overlap term, read in chart `j`, equals its chart-`k`
read — restrict to the overlap image (everything vanishes outside: the weight `ρ_k` off `U k`,
the clearance `∂̄ρ̃_j = 0` off `tsupport ρ_j`), relocate through R4's
`setIntegral_overlap_relocate` applied to the `(1,1)` family `∂̄ρ_j ∧ (β·ω₀)`
(`isOneOneCoeff_dbarRead_mul`), and re-extend with the `pouCoeff` indicator. -/
theorem integral_overlapTerm_relocate {β : X → ℂ}
    (hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) β) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (j k : 𝔇.toFiniteCover.ι) :
    ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
  -- the relocation family `∂̄ρ_j ∧ (β·ω₀)` in chart coefficients
  have hu : IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (β ((chartAt ℂ (𝔇.center i)).symm z) * g i z) :=
    isOneOneCoeff_dbarRead_mul 𝔇 (rhoC 𝔇 j).contMDiff hβ hg
  -- step 1: the chart-`j` integrand vanishes off the overlap image
  have hvan1 : ∀ z, z ∉ overlapImage 𝔇 j k →
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    intro z hz
    by_cases hzs : z ∈ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)
    · obtain ⟨x, hxs, rfl⟩ := hzs
      have hxU : x ∈ (𝔇.U j : Set X) := cechPoU_subordinate 𝔇 j hxs
      have hxk : x ∉ (𝔇.U k : Set X) := fun hk => hz ⟨x, ⟨hxU, hk⟩, rfl⟩
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 k) := fun hs => hxk (cechPoU_subordinate 𝔇 k hs)
      have hr : rhoC 𝔇 k x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hxsupp]
        rfl
      rw [hli, hr, zero_mul]
    · rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs, zero_mul, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan1]
  -- step 2: on the overlap image, `∂̄ρ̃_j` is the `∂̄` of the honest chart read
  have hcongr1 : ∀ z ∈ overlapImage 𝔇 j k,
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    intro z hz
    rw [dbar_pouCoeff_chartRead 𝔇 (Set.image_mono (fun y hy => hy.1) hz)]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 j k).measurableSet hcongr1]
  -- step 3: relocate to chart `k` (the R4 lemma, with weight `ρ_k`)
  have hrel := setIntegral_overlap_relocate 𝔇 hu j k fun y => rhoC 𝔇 k y
  simp only [] at hrel
  rw [hrel]
  -- step 4: on the chart-`k` overlap image, the weight is the `pouCoeff` indicator
  have hcongr2 : ∀ z ∈ overlapImage 𝔇 k j,
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center k)).symm z)
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
      = pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    rintro z ⟨x, hx, rfl⟩
    have hli : (chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k x) = x :=
      (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.1)
    rw [pouCoeff_chartMap 𝔇 hx.1, hli]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 k j).measurableSet hcongr2]
  -- step 5: the chart-`k` integrand vanishes off the overlap image, re-extend to `ℂ`
  have hvan2 : ∀ z, z ∉ overlapImage 𝔇 k j →
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
    intro z hz
    by_cases hzU : z ∈ chartMap 𝔇 k '' (𝔇.U k : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxj : x ∉ (𝔇.U j : Set X) := fun hj => hz ⟨x, ⟨hxU, hj⟩, rfl⟩
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 j) := fun hs => hxj (cechPoU_subordinate 𝔇 j hs)
      have hzt : chartMap 𝔇 k x ∈ (chartAt ℂ (𝔇.center k)).target :=
        (chartAt ℂ (𝔇.center k)).map_source (mem_chartSource_of_mem_U 𝔇 hxU)
      have hli : (chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k x) = x :=
        (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hdz : DbarDisk.dbar
          (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) (chartMap 𝔇 k x) = 0 := by
        refine dbar_chartSymmRead_eq_zero hzt ?_
        rw [hli]
        filter_upwards [(isClosed_tsupport (cechPoU 𝔇 j)).isOpen_compl.mem_nhds hxsupp]
          with y hy
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hy]
        rfl
      rw [hdz, zero_mul, mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan2]

/-! ### The PoU-reinsertion kill (per chart) -/

/-- **The reinsertion kill**: at a fixed chart `k`, summing the relocated `(j,k)` terms over `j`
factors out `∑_j ∂̄ρ̃_j`, which vanishes identically on the chart image
(`sum_dbar_rhoC_read` — the chart read of `∑_j ρ_j = 1`); off the chart image the `pouCoeff`
indicator already kills every term. -/
theorem sum_integral_relocated_eq_zero {β : X → ℂ}
    (hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) β) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (k : 𝔇.toFiniteCover.ι) :
    ∑ j, ∫ z, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
  have hBsm := contDiffAt_pouAverageRead_mul 𝔇 hβ hg k
  have hint : ∀ j ∈ (Finset.univ : Finset 𝔇.toFiniteCover.ι), Integrable fun z =>
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    intro j _
    have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z => pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
      contDiff_pouCoeff_mul 𝔇 fun z hz =>
        (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiffAt_chartSymmRead
          (rhoC 𝔇 j).contMDiff (chartMap_image_U_subset_target 𝔇 k hz))).mul (hBsm z hz)
    exact hcd.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_pouCoeff 𝔇 k).mul_right
  rw [← integral_finsetSum Finset.univ hint]
  have hzero : (fun z => ∑ j, pouCoeff 𝔇 k z
      * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
          * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z))) = fun _ => (0 : ℂ) := by
    funext z
    have hfac : ∀ j, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
        = (pouCoeff 𝔇 k z * (β ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
            * DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hfac j, ← Finset.mul_sum]
    by_cases hzU : z ∈ chartMap 𝔇 k '' (𝔇.U k : Set X)
    · rw [sum_dbar_rhoC_read 𝔇 k (chartMap_image_U_subset_target 𝔇 k hzU), mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul, zero_mul]
  rw [hzero, integral_zero]

/-! ### The R5 headline -/

/-- **R5 headline (unnormalized) — the fine-sheaf surface integral kills coboundaries.**  For
coboundary overlap data `w i j = h j − h i` (on overlaps) with `h` a per-chart holomorphic
0-cochain, and any holomorphic `(1,0)` slot family `g`,

  `I(glueCoeff 𝔇 w g) = ∑_j ∫_ℂ ρ̃_j·t_j = 0`.

Forster §17.3 step 5 in chart coefficients: collapse (`pouSplit_eq_of_coboundary`), Leibniz +
planar Stokes (`integral_pouCoeff_glueCoeff_of_coboundary`), relocation
(`integral_overlapTerm_relocate`), and the PoU-reinsertion kill at fixed chart
(`sum_integral_relocated_eq_zero`), glued by `Finset.sum_comm`. -/
theorem resIntegralFun_eq_zero_of_coboundary
    {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hsm : SmoothOnSets 𝔇 h)
    (hhol : HolomorphicOnSets 𝔇 h) (hδ : IsCoboundaryOn 𝔇 w h) :
    resIntegralFun 𝔇 (glueCoeff 𝔇 w g) = 0 := by
  have hβ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouAverage 𝔇 h) :=
    contMDiff_pouAverage 𝔇 hsm
  calc resIntegralFun 𝔇 (glueCoeff 𝔇 w g)
      = ∑ j, ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := rfl
    _ = ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
        Finset.sum_congr rfl fun j _ =>
          integral_pouCoeff_glueCoeff_of_coboundary 𝔇 hg hsm hhol hδ j
    _ = ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
          integral_overlapTerm_relocate 𝔇 hβ hg j k
    _ = ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
        Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero 𝔇 hβ hg k

/-- **THE R5 HEADLINE — the residue functional kills coboundaries.**  For any `(1,1)` family
`t ∈ oneOneCoeff 𝔇` presented as the glue of coboundary data (`w i j = h j − h i` on overlaps,
`h` per-chart holomorphic) against a `(1,0)` slot family `g`,

  `resFunctional 𝔇 t = 0`.

With R4's ℂ-linearity this is exactly the `vanish_coboundary` field of the port's
`CousinResidueData` packaging (`GlobalResidueConstruct.lean`) at the chart-coefficient level:
the R7 descent applies `Submodule.liftQ` to it once the germ→coefficient extraction maps
`B¹(𝒪_K)` coboundaries onto `(w, h)` data of this shape, making `resFunctional` well-defined
on the Čech cohomology class.  The normalization `resNormalization = −π⁻¹` is the **pinned**
R0 constant (`SignTest.lean`) — cited, not re-derived (`0` is normalization-invariant). -/
theorem resFunctional_eq_zero_of_coboundary
    {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w g)
    (hg : IsOneZeroCoeff 𝔇 g) (hsm : SmoothOnSets 𝔇 h) (hhol : HolomorphicOnSets 𝔇 h)
    (hδ : IsCoboundaryOn 𝔇 w h) :
    resFunctional 𝔇 t = 0 := by
  have hI : resIntegral 𝔇 t = 0 := by
    have hfun : resIntegral 𝔇 t = resIntegralFun 𝔇 (glueCoeff 𝔇 w g) := by
      rw [← ht]
      rfl
    rw [hfun, resIntegralFun_eq_zero_of_coboundary 𝔇 hg hsm hhol hδ]
  rw [resFunctional_apply, hI, mul_zero]

end Jacobians.Dolbeault.FineResidue
