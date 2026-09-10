/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.MLTie

/-!
# R6b — the order-`m` vanish tie: coboundaries with isolated poles killed by slot zeros

The general-`K` residue-vanishing engine of the fine-sheaf ladder
(`docs/planning/R7_BLOCKER.md` §1, `docs/planning/R6_HANDOFF.md` Deliverable 2): R5's
coboundary Stokes (`resFunctional_eq_zero_of_coboundary`) generalized to 0-cochains `h` that
are smooth/holomorphic only **off a finite set `S` of isolated bad points** (each in a single
cover set — the K-point refinement discipline `MLIsolated`), provided at each bad point the
chart-read **product `h̃·g` with the `dz`-slot extends analytically** (`SlotProductExtendsAt`).

  `resFunctional 𝔇 (glueCoeff 𝔇 (δh) g) = 0`   (`resFunctional_eq_zero_of_mero_coboundary`)

## Why no higher-order Cauchy–Pompeiu is needed

The R7 blocker note asks for the order-`m` pole tie "one derivative order per pole order".
This file gets it for free: in the ML split `σ_j = h_j − β` (`pouSplit_eq_of_coboundary`,
`β = pouAverage h`), near an isolated bad point `a` every PoU weight is locally constant
(`ρ_k ≡ 0` for `k ≠ j₀`, `ρ_{j₀} ≡ 1`), so `β ≡ h_{j₀}` near `a` and the surviving chart-`j₀`
Stokes integrand `∂̄(ρ̃_{j₀}·β̃·g̃)` is — off the single bad coordinate — `∂̄` of a function that
**extends to a global C∞c function** (the slot zero of order `≥ m` cancels the pole of order
`≤ m`, the `SlotProductExtendsAt` hypothesis).  A finite limit-repair (`pointRepair`) makes the
extension honest, the planar Stokes atom (`integral_dbar_eq_zero`, R5a) kills the integral, and
the `∂̄`s agree a.e. (the bad coordinates are a finite, hence null, set).  The relocation and
PoU-reinsertion kills are the R5 mechanism verbatim, with the near-bad-point local constancy of
the weights supplying the smoothness clearance exactly as in the in-flight R6 `MLTie`.

The **order-`m` pole tie** itself (`resFunctional_poleCocycle_eq_zero_of_slot_vanishes`) is the
one-bad-point corollary: the cocycle of an explicit principal part `∑_{k<m} c_k (ζ−α)^{−(k+1)}`
glued against a slot vanishing to order `≥ m` at the pole evaluates to `0`.

Sign/normalization: the conclusion is `0`, so the pinned R0 constant `resNormalization = −π⁻¹`
(`SignTest.lean`) is cited only through `resFunctional` — never re-derived.

## Main declarations

* `SmoothOnSetsOff` / `HolomorphicOnSetsOff` — R5's 0-cochain predicates, off a bad set.
* `SlotProductExtendsAt 𝔇 h g j₀ a` — the chart-read product `h̃_{j₀}·g_{j₀}` extends
  analytically across the bad coordinate (the abstract "slot zero cancels the pole").
* `pointRepair` — finite limit-repair of a planar function.
* `meroGlue_mem_oneOneCoeff` — the glued family of bad-point coboundary data is `(1,1)`.
* `resFunctional_eq_zero_of_mero_coboundary` — **the engine headline**.
* `poleCocycle` / `resFunctional_poleCocycle_eq_zero_of_slot_extends` /
  `resFunctional_poleCocycle_eq_zero_of_slot_vanishes` — **the order-`m` pole tie** (D2a).
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical Real
open TopologicalSpace (Opens)

-- Same permissive transparency as the sibling FineResidue files (the `SmoothCFunctions`
-- coercions of `rhoC` below need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    (𝔇 : ChartDiskCover X)

/-! ### The bad-set 0-cochain predicates -/

/-- A value family `h` is **smooth on its own cover sets off the bad set `S`**: each `h j` is
real-`C^∞` at every point of `U j` not in `S`.  Values at bad points and outside `U j` are junk
and never consumed pointwise. -/
def SmoothOnSetsOff (S : Set X) (h : 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ j, ∀ x ∈ (𝔇.U j : Set X), x ∉ S →
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (h j) x

/-- A value family `h` is **holomorphic on its own cover sets off the bad set `S`** — the
off-`S` variant of R5's `HolomorphicOnSets`. -/
def HolomorphicOnSetsOff (S : Set X) (h : 𝔇.toFiniteCover.ι → X → ℂ) : Prop :=
  ∀ j, ∀ x ∈ (𝔇.U j : Set X), x ∉ S →
    DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center j)).symm z)) (chartMap 𝔇 j x)

/-- **The slot kills the pole**: at the isolated bad point `a` (distinguished index `j₀`), the
chart-`j₀` read of `h j₀` times the `dz`-slot `g j₀` agrees, on a punctured neighbourhood of
the bad coordinate, with a function analytic there.  For a pole of order `≤ m` against a slot
zero of order `≥ m` this is the Laurent cancellation; stated abstractly so the engine never
needs Laurent coefficients. -/
def SlotProductExtendsAt (h : 𝔇.toFiniteCover.ι → X → ℂ) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j₀ : 𝔇.toFiniteCover.ι) (a : X) : Prop :=
  ∃ q : ℂ → ℂ, AnalyticAt ℂ q (chartMap 𝔇 j₀ a) ∧
    (fun ζ => h j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ a)] q

/-! ### Near-isolated-point clearances (the MLTie local-constancy toolkit) -/

section Clearance

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X}

theorem rhoC_eq_zero_of_notMem_tsupport {k : 𝔇.toFiniteCover.ι} {y : X}
    (hy : y ∉ tsupport (cechPoU 𝔇 k)) : rhoC 𝔇 k y = 0 := by
  simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hy]
  rfl

/-- Near an isolated bad point, every off-index PoU weight vanishes identically. -/
theorem eventually_rhoC_eq_zero_near_iso (hiso : MLIsolated 𝔇 j₀ a)
    {k : 𝔇.toFiniteCover.ι} (hk : k ≠ j₀) : ∀ᶠ y in 𝓝 a, rhoC 𝔇 k y = 0 := by
  have hns : a ∉ tsupport (cechPoU 𝔇 k) := fun hs => hiso.2 k hk (cechPoU_subordinate 𝔇 k hs)
  filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hns] with y hy
  exact rhoC_eq_zero_of_notMem_tsupport hy

/-- Near an isolated bad point, `∑ρ = 1` forces the distinguished weight to be `≡ 1`. -/
theorem eventually_rhoC_eq_one_near_iso (hiso : MLIsolated 𝔇 j₀ a) :
    ∀ᶠ y in 𝓝 a, rhoC 𝔇 j₀ y = 1 := by
  have hall : ∀ᶠ y in 𝓝 a, ∀ k ∈ Finset.univ.erase j₀, rhoC 𝔇 k y = 0 :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      eventually_rhoC_eq_zero_near_iso hiso (Finset.ne_of_mem_erase hk)
  filter_upwards [hall] with y hy
  have hs := sum_rhoC_apply 𝔇 y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sum_eq_zero hy, add_zero] at hs
  exact hs

/-- Every PoU weight is locally constant near an isolated bad point. -/
theorem exists_rhoC_eventuallyEq_const_near_iso (hiso : MLIsolated 𝔇 j₀ a)
    (k : 𝔇.toFiniteCover.ι) : ∃ c : ℂ, (fun y => rhoC 𝔇 k y) =ᶠ[𝓝 a] fun _ => c := by
  by_cases hk : k = j₀
  · subst hk
    exact ⟨1, eventually_rhoC_eq_one_near_iso hiso⟩
  · exact ⟨0, eventually_rhoC_eq_zero_near_iso hiso hk⟩

/-- The chart-`j₀` reads of two functions locally equal at `a` are locally equal at the bad
coordinate. -/
theorem eventuallyEq_chartSymmRead_near_iso (hiso : MLIsolated 𝔇 j₀ a)
    {F G : X → ℂ} (hFG : F =ᶠ[𝓝 a] G) :
    (fun w => F ((chartAt ℂ (𝔇.center j₀)).symm w))
      =ᶠ[𝓝 (chartMap 𝔇 j₀ a)] fun w => G ((chartAt ℂ (𝔇.center j₀)).symm w) := by
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a) :=
    (chartAt ℂ (𝔇.center j₀)).symm.continuousAt
      (by rw [(chartAt ℂ (𝔇.center j₀)).symm_source]
          exact (chartAt ℂ (𝔇.center j₀)).map_source hsrc)
  have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ a) = a :=
    (chartAt ℂ (𝔇.center j₀)).left_inv hsrc
  rw [ContinuousAt, hli] at hcont
  exact hcont.eventually hFG

/-- `∂̄` of the chart-`j₀` read of a function locally constant at `a` vanishes identically near
the bad coordinate. -/
theorem eventually_dbar_chartSymmRead_zero_near_iso (hiso : MLIsolated 𝔇 j₀ a)
    {F : X → ℂ} {c : ℂ} (hF : F =ᶠ[𝓝 a] fun _ => c) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a),
      DbarDisk.dbar (fun ζ => F ((chartAt ℂ (𝔇.center j₀)).symm ζ)) w = 0 := by
  filter_upwards [(eventuallyEq_chartSymmRead_near_iso hiso hF).eventuallyEq_nhds] with w hw
  rw [dbar_congr_of_eventuallyEq hw]
  exact DbarDisk.dbar_const c w

/-- Near-bad-point clearance for the relocation weights: every chart-`j₀`-read `∂̄ρ̃_k` vanishes
identically near the bad coordinate. -/
theorem eventually_dbar_rhoC_read_zero_near_iso (hiso : MLIsolated 𝔇 j₀ a)
    (k : 𝔇.toFiniteCover.ι) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a),
      DbarDisk.dbar (fun ζ => rhoC 𝔇 k ((chartAt ℂ (𝔇.center j₀)).symm ζ)) w = 0 := by
  obtain ⟨c, hc⟩ := exists_rhoC_eventuallyEq_const_near_iso hiso k
  exact eventually_dbar_chartSymmRead_zero_near_iso hiso hc

/-- The chart-pushed PoU weight `ρ̃_{j₀}` is `≡ 1` near the bad coordinate. -/
theorem eventuallyEq_pouCoeff_one_near_iso (hiso : MLIsolated 𝔇 j₀ a) :
    pouCoeff 𝔇 j₀ =ᶠ[𝓝 (chartMap 𝔇 j₀ a)] fun _ => (1 : ℂ) := by
  have himg : chartMap 𝔇 j₀ a ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X) := ⟨a, hiso.1, rfl⟩
  filter_upwards [(isOpen_chartMap_image 𝔇 j₀ (𝔇.U j₀).isOpen (subset_refl _)).mem_nhds himg,
    eventuallyEq_chartSymmRead_near_iso hiso (eventually_rhoC_eq_one_near_iso hiso)]
    with w hw1 hw2
  rw [pouCoeff, Set.indicator_of_mem hw1]
  exact hw2

theorem eventually_dbar_pouCoeff_zero_near_iso (hiso : MLIsolated 𝔇 j₀ a) :
    ∀ᶠ w in 𝓝 (chartMap 𝔇 j₀ a), DbarDisk.dbar (pouCoeff 𝔇 j₀) w = 0 := by
  filter_upwards [(eventuallyEq_pouCoeff_one_near_iso hiso).eventuallyEq_nhds] with w hw
  rw [dbar_congr_of_eventuallyEq hw]
  exact DbarDisk.dbar_const 1 w

/-- The isolated index is unique: any cover set containing the bad point is the distinguished
one. -/
theorem eq_isolated_index (hiso : MLIsolated 𝔇 j₀ a) {i : 𝔇.toFiniteCover.ι}
    (hai : a ∈ (𝔇.U i : Set X)) : i = j₀ := by
  by_contra hne
  exact hiso.2 i hne hai

end Clearance

/-! ### The PoU average off the bad set -/

section Average

variable {𝔇} {S : Set X} {h : 𝔇.toFiniteCover.ι → X → ℂ}

/-- The PoU average of a family smooth off `S` is smooth at every point off `S` (the support-
aware gluing of R5's `contMDiff_pouAverage`, localized). -/
theorem contMDiffAt_pouAverage_off (hsm : SmoothOnSetsOff 𝔇 S h) {x : X}
    (hx : x ∉ S) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (pouAverage 𝔇 h) x := by
  refine ContMDiffAt.sum fun k _ => ?_
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
  · exact ((rhoC 𝔇 k).contMDiff x).mul (hsm k x (cechPoU_subordinate 𝔇 k hb) hx)
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hb] with y hy
    rw [rhoC_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- Near an isolated bad point the PoU average is the distinguished cochain component
(`ρ_{j₀} ≡ 1`, the others `≡ 0`). -/
theorem pouAverage_eventuallyEq_near_iso {j₀ : 𝔇.toFiniteCover.ι} {a : X}
    (hiso : MLIsolated 𝔇 j₀ a) (h : 𝔇.toFiniteCover.ι → X → ℂ) :
    pouAverage 𝔇 h =ᶠ[𝓝 a] h j₀ := by
  have hall : ∀ᶠ y in 𝓝 a, ∀ k ∈ Finset.univ.erase j₀, rhoC 𝔇 k y = 0 :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      eventually_rhoC_eq_zero_near_iso hiso (Finset.ne_of_mem_erase hk)
  filter_upwards [hall, eventually_rhoC_eq_one_near_iso hiso] with y hy h1
  rw [pouAverage_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), h1, one_mul,
    Finset.sum_eq_zero fun k hk => by rw [hy k hk, zero_mul], add_zero]

/-- Local variant of `contDiffAt_chartSymmRead`: the chart read of a function `ContMDiffAt` at
the read point is planar-smooth there. -/
theorem contDiffAt_chartSymmRead_of_contMDiffAt {F : X → ℂ} {c : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ c).target)
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F ((chartAt ℂ c).symm z)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => F ((chartAt ℂ c).symm w)) z := by
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ c).symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := c) _ hz).contMDiffAt
      ((chartAt ℂ c).open_target.mem_nhds hz)
  exact contMDiffAt_iff_contDiffAt.1 (hF.comp z hsymm)

/-- The chart-`i` read of the PoU average is planar-smooth at good chart points. -/
theorem contDiffAt_pouAverageRead_off (hsm : SmoothOnSetsOff 𝔇 S h)
    {i : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U i : Set X)) (hxS : x ∉ S) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center i)).symm w)) (chartMap 𝔇 i x) := by
  have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hsrc
  refine contDiffAt_chartSymmRead_of_contMDiffAt
    ((chartAt ℂ (𝔇.center i)).map_source hsrc) ?_
  rw [hli]
  exact contMDiffAt_pouAverage_off hsm hxS

/-- The `β̃·g` slot product is planar-smooth at good chart points. -/
theorem contDiffAt_pouAverageRead_mul_off {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hsm : SmoothOnSetsOff 𝔇 S h) (hg : IsOneZeroCoeff 𝔇 g) {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (hxS : x ∉ S) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center i)).symm ζ) * g i ζ)
      (chartMap 𝔇 i x) :=
  (contDiffAt_pouAverageRead_off hsm hx hxS).mul
    (((hg.1 i x hx).restrictScalars (𝕜 := ℝ)).contDiffAt)

/-- At an isolated bad point, the chart read of `β·g` inherits the analytic extension of the
distinguished `h̃_{j₀}·g_{j₀}` (the slot-kills-pole hypothesis transported to the average). -/
theorem pouAverageRead_mul_extends {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {j₀ : 𝔇.toFiniteCover.ι} {a : X} (hiso : MLIsolated 𝔇 j₀ a)
    (hext : SlotProductExtendsAt 𝔇 h g j₀ a) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (chartMap 𝔇 j₀ a) ∧
      (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
        =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ a)] q := by
  obtain ⟨q, hq, hpe⟩ := hext
  refine ⟨q, hq, ?_⟩
  have h1 := eventuallyEq_chartSymmRead_near_iso hiso (pouAverage_eventuallyEq_near_iso hiso h)
  have h2 : (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝 (chartMap 𝔇 j₀ a)]
        fun ζ => h j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ := by
    filter_upwards [h1] with ζ hζ
    rw [hζ]
  exact (h2.filter_mono nhdsWithin_le_nhds).trans hpe

end Average

/-! ### The finite limit-repair and the repaired Stokes atom -/

/-- **Finite limit-repair**: replace the values of a planar function on a finite set by its
punctured limits.  At a removable singularity this produces the honest analytic extension. -/
noncomputable def pointRepair (F : ℂ → ℂ) (T : Finset ℂ) : ℂ → ℂ :=
  fun ζ => if ζ ∈ T then limUnder (𝓝[≠] ζ) F else F ζ

theorem pointRepair_eq_off {F : ℂ → ℂ} {T : Finset ℂ} {ζ : ℂ} (h : ζ ∉ T) :
    pointRepair F T ζ = F ζ := if_neg h

theorem pointRepair_eventuallyEq_off {F : ℂ → ℂ} {T : Finset ℂ} {z : ℂ}
    (h : z ∉ T) : pointRepair F T =ᶠ[𝓝 z] F := by
  have hcl : IsClosed (T : Set ℂ) := T.finite_toSet.isClosed
  filter_upwards [hcl.isOpen_compl.mem_nhds h] with ζ hζ
  exact pointRepair_eq_off hζ

/-- At a repaired point with an analytic punctured extension, the repair agrees with the
extension on a whole neighbourhood. -/
theorem pointRepair_eventuallyEq_of_extends {F q : ℂ → ℂ} {T : Finset ℂ} {α : ℂ}
    (hα : α ∈ T) (hq : AnalyticAt ℂ q α) (hFq : F =ᶠ[𝓝[≠] α] q) :
    pointRepair F T =ᶠ[𝓝 α] q := by
  haveI : (𝓝[≠] α).NeBot := Module.punctured_nhds_neBot ℝ ℂ α
  have hlim : limUnder (𝓝[≠] α) F = q α := by
    have htq : Tendsto q (𝓝[≠] α) (𝓝 (q α)) :=
      hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact (htq.congr' hFq.symm).limUnder_eq
  have hpunct : ∀ᶠ ζ in 𝓝 α, ζ ≠ α → F ζ = q ζ := by
    have := hFq
    rw [EventuallyEq, eventually_nhdsWithin_iff] at this
    filter_upwards [this] with ζ hζ hne
    exact hζ hne
  have herase : ∀ᶠ ζ in 𝓝 α, ζ ∉ ((T.erase α : Finset ℂ) : Set ℂ) :=
    ((T.erase α).finite_toSet.isClosed.isOpen_compl).mem_nhds (by simp)
  filter_upwards [hpunct, herase] with ζ h1 h2
  by_cases hζα : ζ = α
  · subst hζα
    rw [pointRepair, if_pos hα, hlim]
  · have hζT : ζ ∉ T := fun hin => h2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hζα, hin⟩))
    rw [pointRepair_eq_off hζT, h1 hζα]

/-- **The repaired Stokes atom**: the planar Stokes integral of `∂̄(ρ̃_j·u)` vanishes when `u`
is smooth on the chart image off a finite repairable set — repair, note the `∂̄`s agree a.e.
(finite sets are null), and apply the R5a Stokes atom to the repaired C∞c function. -/
theorem integral_dbar_pouCoeff_repairable_eq_zero {u : ℂ → ℂ} {T : Finset ℂ}
    (j : 𝔇.toFiniteCover.ι)
    (hsm : ∀ z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X), z ∉ T → ContDiffAt ℝ (⊤ : ℕ∞) u z)
    (hT : ∀ α ∈ T, ∃ q : ℂ → ℂ, AnalyticAt ℂ q α ∧ u =ᶠ[𝓝[≠] α] q) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ * u ζ) z = 0 := by
  set u' : ℂ → ℂ := pointRepair u T with hu'def
  have hu' : ∀ z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X), ContDiffAt ℝ (⊤ : ℕ∞) u' z := by
    intro z hz
    by_cases hzT : z ∈ T
    · obtain ⟨q, hq, huq⟩ := hT z hzT
      exact ((hq.restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq
        (pointRepair_eventuallyEq_of_extends hzT hq huq)
    · exact (hsm z hz hzT).congr_of_eventuallyEq (pointRepair_eventuallyEq_off hzT)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j ζ * u' ζ :=
    contDiff_pouCoeff_mul 𝔇 hu'
  have hcs : HasCompactSupport fun ζ => pouCoeff 𝔇 j ζ * u' ζ :=
    (hasCompactSupport_pouCoeff 𝔇 j).mul_right
  have haway : ∀ᵐ z : ℂ ∂volume, z ∉ (T : Set ℂ) := by
    refine ae_iff.mpr ?_
    have hset : {z : ℂ | ¬ z ∉ (T : Set ℂ)} = (T : Set ℂ) := by
      ext z
      simp
    rw [hset]
    exact T.finite_toSet.measure_zero _
  have hae : (fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ * u ζ) z)
      =ᵐ[volume] fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ * u' ζ) z := by
    filter_upwards [haway] with z hz
    have hev : (fun ζ => pouCoeff 𝔇 j ζ * u ζ)
        =ᶠ[𝓝 z] fun ζ => pouCoeff 𝔇 j ζ * u' ζ := by
      filter_upwards [pointRepair_eventuallyEq_off (F := u) (T := T) hz] with ζ hζ
      rw [hu'def, hζ]
    exact dbar_congr_of_eventuallyEq hev
  rw [integral_congr_ae hae]
  exact integral_dbar_eq_zero hcd hcs

/-! ### Bad coordinates of a chart -/

/-- The bad coordinates of chart `j`: the chart-`j` images of the bad points lying in `U j`. -/
noncomputable def badCoords (S : Finset X) (j : 𝔇.toFiniteCover.ι) : Finset ℂ :=
  (S.filter fun a => a ∈ (𝔇.U j : Set X)).image (chartMap 𝔇 j)

theorem chartMap_mem_badCoords_iff {S : Finset X} {j : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U j : Set X)) : chartMap 𝔇 j x ∈ badCoords 𝔇 S j ↔ x ∈ S := by
  constructor
  · intro hmem
    obtain ⟨b, hb, hcb⟩ := Finset.mem_image.mp hmem
    obtain ⟨hbS, hbU⟩ := Finset.mem_filter.mp hb
    have hbx : b = x := (chartAt ℂ (𝔇.center j)).injOn
      (mem_chartSource_of_mem_U 𝔇 hbU) (mem_chartSource_of_mem_U 𝔇 hx) hcb
    exact hbx ▸ hbS
  · intro hxS
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hx⟩, rfl⟩

theorem exists_of_mem_badCoords {S : Finset X} {j : 𝔇.toFiniteCover.ι} {α : ℂ}
    (hα : α ∈ badCoords 𝔇 S j) :
    ∃ a, a ∈ S ∧ a ∈ (𝔇.U j : Set X) ∧ chartMap 𝔇 j a = α := by
  obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp hα
  obtain ⟨haS, haU⟩ := Finset.mem_filter.mp ha
  exact ⟨a, haS, haU, hca⟩

/-! ### The glued family of bad-point coboundary data is `(1,1)` -/

section Membership

variable {𝔇} {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- Off-diagonal overlap points are never bad (a bad point lies in a single cover set). -/
theorem notMem_S_of_mem_overlap (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    {i j : 𝔇.toFiniteCover.ι} (hij : i ≠ j) {x : X}
    (hx : x ∈ (𝔇.U i ⊓ 𝔇.U j : Opens X)) : x ∉ (S : Set X) := by
  intro hxS
  obtain ⟨j₀, hj₀⟩ := hiso x hxS
  have hi : i = j₀ := eq_isolated_index hj₀ hx.1
  have hj : j = j₀ := eq_isolated_index hj₀ hx.2
  exact hij (hi.trans hj.symm)

/-- Bad-point coboundary data is smooth on overlaps (off-diagonal overlaps avoid the bad set;
diagonal overlap functions vanish identically). -/
theorem smoothOnOverlaps_of_mero_coboundary (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h) :
    SmoothOnOverlaps 𝔇 w := by
  intro i j x hx
  by_cases hij : i = j
  · subst hij
    refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(𝔇.U i ⊓ 𝔇.U i : Opens X).isOpen.mem_nhds hx] with y hy
    rw [hδ i i y hy, sub_self]
  · have hxS := notMem_S_of_mem_overlap hiso hij hx
    refine ((hsm j x hx.2 hxS).sub (hsm i x hx.1 hxS)).congr_of_eventuallyEq ?_
    have hSopen : IsOpen ((S : Set X))ᶜ := S.finite_toSet.isClosed.isOpen_compl
    filter_upwards [(𝔇.U i ⊓ 𝔇.U j : Opens X).isOpen.mem_nhds hx] with y hy
    exact hδ i j y hy

/-- Bad-point coboundary data is holomorphic on overlaps. -/
theorem holomorphicOnOverlaps_of_mero_coboundary (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h) :
    HolomorphicOnOverlaps 𝔇 w := by
  intro i j x hx
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx.1
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) :=
    (chartAt ℂ (𝔇.center i)).symm.continuousAt
      (by rw [(chartAt ℂ (𝔇.center i)).symm_source]
          exact (chartAt ℂ (𝔇.center i)).map_source hxsrc)
  have hov : ((𝔇.U i ⊓ 𝔇.U j : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x)) := by
    rw [hli]
    exact (𝔇.U i ⊓ 𝔇.U j : Opens X).isOpen.mem_nhds hx
  by_cases hij : i = j
  · subst hij
    refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hcont.preimage_mem_nhds hov] with z hz
    rw [hδ i i _ hz, sub_self]
  · have hxS := notMem_S_of_mem_overlap hiso hij hx
    -- the i-read of `h j` is the j-read relocated through the transition, hence holomorphic
    have hcomp : DifferentiableAt ℂ
        (fun z => h j ((chartAt ℂ (𝔇.center j)).symm (transitionMap 𝔇 i j z)))
        (chartMap 𝔇 i x) := by
      have hbase : DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center j)).symm z))
          (transitionMap 𝔇 i j (chartMap 𝔇 i x)) := by
        rw [transitionMap_chartMap 𝔇 hx.1]
        exact hhol j x hx.2 hxS
      exact hbase.comp _ (transitionMap_analyticAt 𝔇 hx.1 hx.2).differentiableAt
    have hread_j : DifferentiableAt ℂ (fun z => h j ((chartAt ℂ (𝔇.center i)).symm z))
        (chartMap 𝔇 i x) := by
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with z hz
      rw [hz]
    have hev : (fun z => w i j ((chartAt ℂ (𝔇.center i)).symm z))
        =ᶠ[𝓝 (chartMap 𝔇 i x)] fun z =>
          h j ((chartAt ℂ (𝔇.center i)).symm z) - h i ((chartAt ℂ (𝔇.center i)).symm z) := by
      filter_upwards [hcont.preimage_mem_nhds hov] with z hz
      exact hδ i j _ hz
    exact (hread_j.sub (hhol i x hx.1 hxS)).congr_of_eventuallyEq hev

/-- **The glued family of bad-point coboundary data is a global `(1,1)` family** (the R3 glue
law applied to the verified off-`S` hypotheses). -/
theorem meroGlue_mem_oneOneCoeff (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h)
    (hδ : IsCoboundaryOn 𝔇 w h) (hg : IsOneZeroCoeff 𝔇 g) :
    glueCoeff 𝔇 w g ∈ oneOneCoeff 𝔇 :=
  glueCoeff_mem_oneOneCoeff 𝔇 (smoothOnOverlaps_of_mero_coboundary hiso hsm hδ)
    (isOverlapCocycle_of_coboundary 𝔇 hδ)
    (holomorphicOnOverlaps_of_mero_coboundary hiso hhol hδ) hg

end Membership

/-! ### The engine: relocation, reinsertion kill, repaired Stokes, Leibniz -/

section MeroEngine

variable {𝔇} {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- The relocation family `∂̄ρ_{jj} ∧ (β·ω₀)` is a `(1,1)` chart-coefficient family — R5's
`isOneOneCoeff_dbarRead_mul` with the bad-point PoU average in the scalar slot.  At a bad
chart point the `∂̄ρ̃_{jj}` factor vanishes on a whole neighbourhood (local constancy of the
weights near the isolated bad point); the overlap law never differentiates the scalar slot, so
the R5 proof applies verbatim. -/
theorem isOneOneCoeff_dbarRead_mul_mero (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hg : IsOneZeroCoeff 𝔇 g)
    (jj : 𝔇.toFiniteCover.ι) :
    IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center i)).symm z) * g i z) := by
  constructor
  · intro i x hx
    by_cases hxS : x ∈ (S : Set X)
    · obtain ⟨j₀, hj₀⟩ := hiso x hxS
      have hi : i = j₀ := eq_isolated_index hj₀ hx
      subst hi
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [eventually_dbar_rhoC_read_zero_near_iso hj₀ jj] with z hz
      rw [hz, zero_mul]
    · have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
        (chartAt ℂ (𝔇.center i)).map_source (mem_chartSource_of_mem_U 𝔇 hx)
      exact (ChartDiskCover.contDiffAt_dbar_chartDisk
        (contDiffAt_chartSymmRead (rhoC 𝔇 jj).contMDiff hzt)).mul
        (contDiffAt_pouAverageRead_mul_off hsm hg hx hxS)
  · intro p q x hx
    have hxp : x ∈ (𝔇.U p : Set X) := hx.1
    have hxq : x ∈ (𝔇.U q : Set X) := hx.2
    have hzqt : chartMap 𝔇 q x ∈ (chartAt ℂ (𝔇.center q)).target :=
      (chartAt ℂ (𝔇.center q)).map_source (mem_chartSource_of_mem_U 𝔇 hxq)
    have htend : Tendsto (transitionMap 𝔇 p q) (𝓝 (chartMap 𝔇 p x))
        (𝓝 (chartMap 𝔇 q x)) := by
      have hc := (transitionMap_analyticAt 𝔇 hxp hxq).continuousAt
      rwa [ContinuousAt, transitionMap_chartMap 𝔇 hxp] at hc
    have hFev : (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ)))
        =ᶠ[𝓝 (chartMap 𝔇 p x)] fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center p)).symm ζ) := by
      filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with ζ hζ
      rw [hζ]
    unfold OneOneLawAt
    filter_upwards [hFev.eventuallyEq_nhds, symm_transitionMap_eventuallyEq 𝔇 hx,
      (transitionMap_analyticAt 𝔇 hxp hxq).eventually_analyticAt,
      htend.eventually ((chartAt ℂ (𝔇.center q)).open_target.mem_nhds hzqt),
      hg.2 p q x hx] with z hzF hzsymm hzan hztgt hzg
    have h1 : DbarDisk.dbar (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center p)).symm ζ)) z
        = DbarDisk.dbar
            (fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ))) z :=
      (dbar_congr_of_eventuallyEq hzF).symm
    have h2 := dbar_comp (f := fun ζ => rhoC 𝔇 jj ((chartAt ℂ (𝔇.center q)).symm ζ))
      (φ := transitionMap 𝔇 p q)
      ((contDiffAt_chartSymmRead (rhoC 𝔇 jj).contMDiff hztgt).differentiableAt (by simp))
      hzan.differentiableAt
    rw [Function.comp_def] at h2
    have hns : ((normSq (deriv (transitionMap 𝔇 p q) z) : ℝ) : ℂ)
        = deriv (transitionMap 𝔇 p q) z
            * (starRingEnd ℂ) (deriv (transitionMap 𝔇 p q) z) :=
      (Complex.mul_conj _).symm
    rw [h1, h2, hzg, ← hzsymm, hns]
    ring

/-- **The relocation step** — `integral_overlapTerm_relocate` with the bad-point PoU average in
place of the globally smooth one (R4's `setIntegral_overlap_relocate` applied to the `(1,1)`
family `isOneOneCoeff_dbarRead_mul_mero`). -/
theorem integral_overlapTerm_relocate_mero
    (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hg : IsOneZeroCoeff 𝔇 g) (j k : 𝔇.toFiniteCover.ι) :
    ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∫ z, pouCoeff 𝔇 k z
          * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
  have hu : IsOneOneCoeff 𝔇 fun i z =>
      DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center i)).symm ζ)) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center i)).symm z) * g i z) :=
    isOneOneCoeff_dbarRead_mul_mero hiso hsm hg j
  -- step 1: the chart-`j` integrand vanishes off the overlap image
  have hvan1 : ∀ z, z ∉ overlapImage 𝔇 j k →
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    intro z hz
    by_cases hzs : z ∈ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j)
    · obtain ⟨x, hxs, rfl⟩ := hzs
      have hxU : x ∈ (𝔇.U j : Set X) := cechPoU_subordinate 𝔇 j hxs
      have hxk : x ∉ (𝔇.U k : Set X) := fun hk => hz ⟨x, ⟨hxU, hk⟩, rfl⟩
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hxU)
      have hxsupp : x ∉ tsupport (cechPoU 𝔇 k) := fun hs => hxk (cechPoU_subordinate 𝔇 k hs)
      rw [hli, rhoC_eq_zero_of_notMem_tsupport hxsupp, zero_mul]
    · rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs, zero_mul, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan1]
  -- step 2: on the overlap image, `∂̄ρ̃_j` is the `∂̄` of the honest chart read
  have hcongr1 : ∀ z ∈ overlapImage 𝔇 j k,
      rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center j)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
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
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
      = pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    rintro z ⟨x, hx, rfl⟩
    have hli : (chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k x) = x :=
      (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hx.1)
    rw [pouCoeff_chartMap 𝔇 hx.1, hli]
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_overlapImage 𝔇 k j).measurableSet hcongr2]
  -- step 5: the chart-`k` integrand vanishes off the overlap image, re-extend to `ℂ`
  have hvan2 : ∀ z, z ∉ overlapImage 𝔇 k j →
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
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
        exact rhoC_eq_zero_of_notMem_tsupport hy
      rw [hdz, zero_mul, mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan2]

/-- **The reinsertion kill**: at fixed chart `k`, the relocated curvature terms sum to zero
(`∑_j ∂̄ρ̃_j = 0` on the chart image); near each bad coordinate every `∂̄ρ̃_j`-read vanishes
identically, supplying the integrability clearance. -/
theorem sum_integral_relocated_eq_zero_mero
    (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hg : IsOneZeroCoeff 𝔇 g) (k : 𝔇.toFiniteCover.ι) :
    ∑ j, ∫ z, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) = 0 := by
  have hint : ∀ j ∈ (Finset.univ : Finset 𝔇.toFiniteCover.ι), Integrable fun z =>
      pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
    intro j _
    have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z => pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) := by
      refine contDiff_pouCoeff_mul 𝔇 ?_
      rintro z ⟨x, hxU, rfl⟩
      by_cases hxS : x ∈ (S : Set X)
      · obtain ⟨j₀, hj₀⟩ := hiso x hxS
        have hk : k = j₀ := eq_isolated_index hj₀ hxU
        subst hk
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_rhoC_read_zero_near_iso hj₀ j] with w hw
        rw [hw, zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk (contDiffAt_chartSymmRead
          (rhoC 𝔇 j).contMDiff (chartMap_image_U_subset_target 𝔇 k ⟨x, hxU, rfl⟩))).mul
          (contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS)
    exact hcd.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_pouCoeff 𝔇 k).mul_right
  rw [← integral_finsetSum Finset.univ hint]
  have hzero : (fun z => ∑ j, pouCoeff 𝔇 k z
      * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)))
      = fun _ => (0 : ℂ) := by
    funext z
    have hfac : ∀ j, pouCoeff 𝔇 k z
        * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
        = (pouCoeff 𝔇 k z * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z))
            * DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hfac j, ← Finset.mul_sum]
    by_cases hzU : z ∈ chartMap 𝔇 k '' (𝔇.U k : Set X)
    · rw [sum_dbar_rhoC_read 𝔇 k (chartMap_image_U_subset_target 𝔇 k hzU), mul_zero]
    · rw [show pouCoeff 𝔇 k z = 0 from Set.indicator_of_notMem hzU _, zero_mul, zero_mul]
  rw [hzero, integral_zero]

/-- **The repaired Stokes kill** — the surviving total-derivative term of each chart dies:
off the (finitely many) bad coordinates the integrand is `∂̄` of a smooth compactly supported
function, and at each bad coordinate the slot zero supplies the analytic extension
(`pouAverageRead_mul_extends`), so the finite limit-repair + R5a Stokes atom give `0`.  This
is where the in-flight R6's Cauchy–Pompeiu pole evaluation is replaced by a Stokes kill. -/
theorem integral_dbar_pouCoeff_pouAverage_eq_zero
    (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hg : IsOneZeroCoeff 𝔇 g)
    (hext : ∀ a ∈ S, ∀ j₀, MLIsolated 𝔇 j₀ a → SlotProductExtendsAt 𝔇 h g j₀ a)
    (j : 𝔇.toFiniteCover.ι) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
  refine integral_dbar_pouCoeff_repairable_eq_zero 𝔇 (T := badCoords 𝔇 S j) j ?_ ?_
  · rintro z ⟨x, hxU, rfl⟩ hzT
    have hxS : x ∉ (S : Set X) := fun hx =>
      hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
    exact contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS
  · intro α hα
    obtain ⟨a, haS, haU, hca⟩ := exists_of_mem_badCoords 𝔇 hα
    obtain ⟨j₀, hj₀⟩ := hiso a haS
    have hj : j = j₀ := eq_isolated_index hj₀ haU
    subst hj
    subst hca
    exact pouAverageRead_mul_extends hj₀ (hext a haS j hj₀)

/-- **The Leibniz step, Stokes term kept explicit** (per chart): the `j`-th summand of the
residue integral equals the PoU-reinserted curvature terms MINUS the surviving
total-derivative (Stokes) term.  A.e. version of R5's
`integral_pouCoeff_glueCoeff_of_coboundary`: the pointwise Leibniz identity holds off the
(finite, null) set of bad coordinates.  No slot-product hypothesis: the Stokes term is not
evaluated here (the vanish engine kills it via `SlotProductExtendsAt`, the evaluation engine
computes it via `SlotProductSimplePoleAt`). -/
theorem integral_pouCoeff_glueCoeff_mero_split
    (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h)
    (hg : IsOneZeroCoeff 𝔇 g)
    (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = (∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
        - ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z := by
  -- the a.e. pointwise Leibniz identity (off the bad coordinates)
  have hpt : ∀ z : ℂ, z ∉ badCoords 𝔇 S j →
      pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
        = DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
          - DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z := by
    intro z hzT
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxS : x ∉ (S : Set X) := fun hx =>
        hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
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
        (contDiffAt_pouAverageRead_off hsm hxU hxS).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      have hdbar_split : DbarDisk.dbar (splitCoeff 𝔇 w j) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) := by
        rw [dbar_congr_of_eventuallyEq hsplit_ev,
          DbarOpenDisk.dbar_sub ((hhol j x hxU hxS).restrictScalars ℝ) hBd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hhol j x hxU hxS), zero_sub]
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
          ((contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS).differentiableAt (by simp))
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
  have hIt : Integrable fun z => pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z :=
    integrable_pouCoeff_mul 𝔇 (meroGlue_mem_oneOneCoeff hiso hsm hhol hδ hg) j
  have hYcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    refine contDiff_of_chartImage_clearance 𝔇 (j := j) ?_ ?_
    · rintro z ⟨x, hxU, rfl⟩
      by_cases hxS : x ∈ (S : Set X)
      · obtain ⟨j₀, hj₀⟩ := hiso x hxS
        have hj : j = j₀ := eq_isolated_index hj₀ hxU
        subst hj
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_pouCoeff_zero_near_iso hj₀] with w' hw'
        rw [hw', zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk
          (contDiff_pouCoeff 𝔇 j).contDiffAt).mul
          (contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS)
    · intro z hz
      rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul]
  have hYcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hIY : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hYcd.continuous.integrable_of_hasCompactSupport hYcs
  -- the bad coordinates are volume-negligible
  have hane : ∀ᵐ z : ℂ ∂volume, z ∉ badCoords 𝔇 S j := by
    refine ae_iff.mpr ?_
    have hset : {z : ℂ | ¬ z ∉ badCoords 𝔇 S j} = ((badCoords 𝔇 S j : Finset ℂ) : Set ℂ) := by
      ext z
      simp
    rw [hset]
    exact (badCoords 𝔇 S j).finite_toSet.measure_zero _
  have hkey : ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
      = (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := by
    rw [← integral_sub hIY hIt]
    refine integral_congr_ae ?_
    filter_upwards [hane] with z hz
    linear_combination hpt z hz
  -- PoU reinsertion of the curvature term
  have hreins : (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    calc ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        = ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
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
                (chartMap_image_U_subset_target 𝔇 j hz)).mul hYcd.contDiffAt)
              (fun z hz => by
                rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
          exact hcd.continuous.integrable_of_hasCompactSupport hYcs.mul_left
  rw [← hreins]
  linear_combination hkey

/-- **The Leibniz/Stokes step** (per chart): the `j`-th summand of the residue integral equals
the PoU-reinserted curvature terms — the total-derivative term dies by the repaired Stokes
kill (the split step plus `integral_dbar_pouCoeff_pouAverage_eq_zero`). -/
theorem integral_pouCoeff_glueCoeff_mero
    (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h)
    (hg : IsOneZeroCoeff 𝔇 g)
    (hext : ∀ a ∈ S, ∀ j₀, MLIsolated 𝔇 j₀ a → SlotProductExtendsAt 𝔇 h g j₀ a)
    (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
  rw [integral_pouCoeff_glueCoeff_mero_split hiso hsm hhol hδ hg j,
    integral_dbar_pouCoeff_pouAverage_eq_zero hiso hsm hg hext j, sub_zero]

/-! ### The engine headline -/

/-- **THE R6b HEADLINE — the residue functional kills coboundaries with isolated bad points
whose poles the slot cancels.**  For any `(1,1)` family `t ∈ oneOneCoeff 𝔇` presented as the
glue of coboundary data `w i j = h j − h i` (on overlaps) against a `(1,0)` slot family `g`,
where `h` is smooth/holomorphic off a finite set `S` of cover-isolated bad points and at each
bad point the chart-read product `h̃·g` extends analytically (`SlotProductExtendsAt`),

  `resFunctional 𝔇 t = 0`.

This is R5's `resFunctional_eq_zero_of_coboundary` at `S = ∅` and the general-`K`
`vanish_coboundary` engine at `S = ` the K-points (`docs/planning/R7_BLOCKER.md` §1): the
order-`m` pole of a `sections0 K` scalar at a K-point is cancelled by the order-`K a` zero of
the `dz`-slot of `ω₀`, so the product extends and the contribution dies by Stokes — no
higher-order Cauchy–Pompeiu needed.  The pinned R0 normalization `resNormalization = −π⁻¹`
is cited only through `resFunctional` (`0` is normalization-invariant). -/
theorem resFunctional_eq_zero_of_mero_coboundary (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w g)
    (hg : IsOneZeroCoeff 𝔇 g) (hiso : ∀ a ∈ S, ∃ j₀, MLIsolated 𝔇 j₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h)
    (hδ : IsCoboundaryOn 𝔇 w h)
    (hext : ∀ a ∈ S, ∀ j₀, MLIsolated 𝔇 j₀ a → SlotProductExtendsAt 𝔇 h g j₀ a) :
    resFunctional 𝔇 t = 0 := by
  have hIfun : resIntegralFun 𝔇 (glueCoeff 𝔇 w g) = 0 := by
    calc resIntegralFun 𝔇 (glueCoeff 𝔇 w g)
        = ∑ j, ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := rfl
      _ = ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
          Finset.sum_congr rfl fun j _ =>
            integral_pouCoeff_glueCoeff_mero hiso hsm hhol hδ hg hext j
      _ = ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate_mero hiso hsm hg j k
      _ = ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero_mero hiso hsm hg k
  have hI : resIntegral 𝔇 t = 0 := by
    have hfun : resIntegral 𝔇 t = resIntegralFun 𝔇 (glueCoeff 𝔇 w g) := by
      rw [← ht]
      rfl
    rw [hfun, hIfun]
  rw [resFunctional_apply, hI, mul_zero]

end MeroEngine

/-! ### D2a — the order-`m` pole tie -/

/-- The one-point principal-part family of a planar principal part `P₀` read through the
distinguished chart (the order-`m` generalization of `MLTie.mlPart`). -/
noncomputable def polePart (j₀ : 𝔇.toFiniteCover.ι) (P₀ : ℂ → ℂ) :
    𝔇.toFiniteCover.ι → X → ℂ :=
  fun i x => if i = j₀ then P₀ (chartMap 𝔇 j₀ x) else 0

/-- The one-point principal-part overlap cocycle, in the MLTie orientation
(`w i j = p_i − p_j`). -/
noncomputable def poleCocycle (j₀ : 𝔇.toFiniteCover.ι) (P₀ : ℂ → ℂ) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j x => polePart 𝔇 j₀ P₀ i x - polePart 𝔇 j₀ P₀ j x

section PoleTie

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {P₀ : ℂ → ℂ}
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- The pole cocycle is the coboundary of the negated part family. -/
theorem isCoboundaryOn_poleCocycle :
    IsCoboundaryOn 𝔇 (poleCocycle 𝔇 j₀ P₀) (fun i x => -(polePart 𝔇 j₀ P₀ i x)) := by
  intro i j x _
  simp only [poleCocycle]
  ring

/-- The negated part family is smooth off the pole. -/
theorem smoothOnSetsOff_neg_polePart (hiso : MLIsolated 𝔇 j₀ a)
    (hP : ∀ z, z ≠ chartMap 𝔇 j₀ a → AnalyticAt ℂ P₀ z) :
    SmoothOnSetsOff 𝔇 (({a} : Finset X) : Set X) fun i x => -(polePart 𝔇 j₀ P₀ i x) := by
  intro j x hx hxa
  have hxa' : x ≠ a := by simpa using hxa
  refine ContMDiffAt.neg ?_
  unfold polePart
  by_cases hj : j = j₀
  · subst hj
    simp only []
    have hxj : x ∈ (𝔇.U j : Set X) := hx
    have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartMap 𝔇 j) x :=
      contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℂ)) (mem_chartSource_of_mem_U 𝔇 hxj)
    have hne : chartMap 𝔇 j x ≠ chartMap 𝔇 j a := fun hc =>
      hxa' ((chartAt ℂ (𝔇.center j)).injOn
        (mem_chartSource_of_mem_U 𝔇 hxj) (mem_chartSource_of_mem_U 𝔇 hiso.1) hc)
    have houter : ContDiffAt ℝ (⊤ : ℕ∞) P₀ (chartMap 𝔇 j x) :=
      ((hP _ hne).restrictScalars (𝕜 := ℝ)).contDiffAt
    exact (contMDiffAt_iff_contDiffAt.2 houter).comp x hchart
  · simp only [if_neg hj]
    exact contMDiffAt_const

/-- The negated part family is holomorphic off the pole. -/
theorem holomorphicOnSetsOff_neg_polePart (hiso : MLIsolated 𝔇 j₀ a)
    (hP : ∀ z, z ≠ chartMap 𝔇 j₀ a → AnalyticAt ℂ P₀ z) :
    HolomorphicOnSetsOff 𝔇 (({a} : Finset X) : Set X)
      fun i x => -(polePart 𝔇 j₀ P₀ i x) := by
  intro j x hx hxa
  have hxa' : x ≠ a := by simpa using hxa
  refine DifferentiableAt.neg ?_
  unfold polePart
  by_cases hj : j = j₀
  · subst hj
    simp only []
    have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
      (chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hx)
    have hev : (fun z => P₀ (chartMap 𝔇 j ((chartAt ℂ (𝔇.center j)).symm z)))
        =ᶠ[𝓝 (chartMap 𝔇 j x)] P₀ := by
      filter_upwards [(chartAt ℂ (𝔇.center j)).open_target.mem_nhds hzt] with z hz
      rw [show chartMap 𝔇 j ((chartAt ℂ (𝔇.center j)).symm z) = z from
        (chartAt ℂ (𝔇.center j)).right_inv hz]
    have hne : chartMap 𝔇 j x ≠ chartMap 𝔇 j a := fun hc =>
      hxa' ((chartAt ℂ (𝔇.center j)).injOn
        (mem_chartSource_of_mem_U 𝔇 hx) (mem_chartSource_of_mem_U 𝔇 hiso.1) hc)
    exact ((hP _ hne).differentiableAt).congr_of_eventuallyEq hev
  · simp only [if_neg hj]
    exact differentiableAt_const _

/-- The slot-product extension for the negated part family, from the planar extension of
`P₀·g`. -/
theorem slotProductExtendsAt_neg_polePart (hiso : MLIsolated 𝔇 j₀ a)
    {q : ℂ → ℂ} (hq : AnalyticAt ℂ q (chartMap 𝔇 j₀ a))
    (hpg : (fun ζ => P₀ ζ * g j₀ ζ) =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ a)] q) :
    SlotProductExtendsAt 𝔇 (fun i x => -(polePart 𝔇 j₀ P₀ i x)) g j₀ a := by
  refine ⟨fun ζ => -q ζ, hq.neg, ?_⟩
  have hsrc : a ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hiso.1
  have hzt : chartMap 𝔇 j₀ a ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hsrc
  have hev : ∀ᶠ ζ in 𝓝[≠] (chartMap 𝔇 j₀ a), ζ ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ (𝔇.center j₀)).open_target.mem_nhds hzt)
  filter_upwards [hev, hpg] with ζ hζ hpgζ
  simp only [polePart, if_true, neg_mul]
  rw [show chartMap 𝔇 j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) = ζ from
    (chartAt ℂ (𝔇.center j₀)).right_inv hζ, hpgζ]

/-- **The abstract one-pole vanish tie**: on an isolated bad point, the residue functional of
the glued principal-part cocycle vanishes whenever the planar product `P₀·g_{j₀}` extends
analytically across the pole coordinate. -/
theorem resFunctional_poleCocycle_eq_zero_of_slot_extends (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (hP : ∀ z, z ≠ chartMap 𝔇 j₀ a → AnalyticAt ℂ P₀ z)
    {q : ℂ → ℂ} (hq : AnalyticAt ℂ q (chartMap 𝔇 j₀ a))
    (hpg : (fun ζ => P₀ ζ * g j₀ ζ) =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ a)] q)
    (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 (poleCocycle 𝔇 j₀ P₀) g) :
    resFunctional 𝔇 t = 0 := by
  have hisoS : ∀ b ∈ ({a} : Finset X), ∃ i₀, MLIsolated 𝔇 i₀ b := by
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨j₀, hiso⟩
  refine resFunctional_eq_zero_of_mero_coboundary (S := {a})
    (h := fun i x => -(polePart 𝔇 j₀ P₀ i x)) t ht hg hisoS
    (smoothOnSetsOff_neg_polePart hiso hP) (holomorphicOnSetsOff_neg_polePart hiso hP)
    isCoboundaryOn_poleCocycle ?_
  intro b hb i₀ hi₀
  rw [Finset.mem_singleton] at hb
  subst hb
  have hi : i₀ = j₀ := eq_isolated_index hiso hi₀.1
  subst hi
  exact slotProductExtendsAt_neg_polePart hiso hq hpg

/-- The glued principal-part family is a global `(1,1)` family (companion membership lemma,
so callers can form the `oneOneCoeff` element). -/
theorem poleGlue_mem_oneOneCoeff (hiso : MLIsolated 𝔇 j₀ a) (hg : IsOneZeroCoeff 𝔇 g)
    (hP : ∀ z, z ≠ chartMap 𝔇 j₀ a → AnalyticAt ℂ P₀ z) :
    glueCoeff 𝔇 (poleCocycle 𝔇 j₀ P₀) g ∈ oneOneCoeff 𝔇 := by
  have hisoS : ∀ b ∈ ({a} : Finset X), ∃ i₀, MLIsolated 𝔇 i₀ b := by
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨j₀, hiso⟩
  exact meroGlue_mem_oneOneCoeff hisoS (smoothOnSetsOff_neg_polePart hiso hP)
    (holomorphicOnSetsOff_neg_polePart hiso hP) isCoboundaryOn_poleCocycle hg

/-- The standard order-`m` principal part `∑_{k<m} c_k·(ζ−α)^{−(k+1)}` at the pole
coordinate `α`. -/
noncomputable def stdPrincipalPart (α : ℂ) (m : ℕ) (c : ℕ → ℂ) : ℂ → ℂ :=
  fun ζ => ∑ k ∈ Finset.range m, c k * ((ζ - α) ^ (k + 1))⁻¹

theorem analyticAt_stdPrincipalPart {α z : ℂ} (hz : z ≠ α) (m : ℕ) (c : ℕ → ℂ) :
    AnalyticAt ℂ (stdPrincipalPart α m c) z := by
  unfold stdPrincipalPart
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
    (f := fun k ζ => c k * ((ζ - α) ^ (k + 1))⁻¹) _ fun k _ => ?_
  exact analyticAt_const.mul
    (((analyticAt_id.sub analyticAt_const).pow _).inv (pow_ne_zero _ (sub_ne_zero.mpr hz)))

/-- **D2a — THE ORDER-`m` POLE TIE** (the general-`K` vanish ingredient named in
`docs/planning/R7_BLOCKER.md` §1): the residue functional of the glued cocycle of a pole of
order `≤ m` at an isolated point, against a `dz`-slot vanishing there to order `≥ m`, is `0`.
The slot zero cancels the pole (`q` below is the polynomial-shifted Laurent product), so the
abstract slot-extends tie applies — one Stokes kill, no per-order Cauchy–Pompeiu ladder. -/
theorem resFunctional_poleCocycle_eq_zero_of_slot_vanishes (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (m : ℕ) (c : ℕ → ℂ) {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u (chartMap 𝔇 j₀ a))
    (hgv : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ a),
      g j₀ ζ = (ζ - chartMap 𝔇 j₀ a) ^ m * u ζ)
    (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ)
      = glueCoeff 𝔇 (poleCocycle 𝔇 j₀ (stdPrincipalPart (chartMap 𝔇 j₀ a) m c)) g) :
    resFunctional 𝔇 t = 0 := by
  set α := chartMap 𝔇 j₀ a with hα
  -- the cancelled product: `q ζ = (∑_{k<m} c_k (ζ−α)^{m−(k+1)}) · u ζ`
  set q : ℂ → ℂ := fun ζ => (∑ k ∈ Finset.range m, c k * (ζ - α) ^ (m - (k + 1))) * u ζ
    with hqdef
  have hq : AnalyticAt ℂ q α := by
    refine AnalyticAt.mul ?_ hu
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (f := fun k ζ => c k * (ζ - α) ^ (m - (k + 1))) _ fun k _ => ?_
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)
  have hpg : (fun ζ => stdPrincipalPart α m c ζ * g j₀ ζ) =ᶠ[𝓝[≠] α] q := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hgv,
      eventually_mem_nhdsWithin] with ζ hgζ hζ
    have hζne : ζ ≠ α := hζ
    have hζα : ζ - α ≠ 0 := sub_ne_zero.mpr hζne
    show stdPrincipalPart α m c ζ * g j₀ ζ = q ζ
    rw [hgζ, hqdef, stdPrincipalPart]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k + 1 ≤ m := Finset.mem_range.mp hk
    have hpow : (ζ - α) ^ (m - (k + 1)) = (ζ - α) ^ m / (ζ - α) ^ (k + 1) :=
      pow_sub₀ _ hζα hkm
    rw [hpow]
    field_simp
  exact resFunctional_poleCocycle_eq_zero_of_slot_extends hiso hg
    (fun z hz => analyticAt_stdPrincipalPart hz m c) hq hpg t ht

end PoleTie

/-! ### The EVALUATION engine — one marked simple-pole point (the nonzero direction)

The vanish engine above kills coboundaries whose slot-products *extend* at every bad point.
The §17.7 unwinding (`docs/planning/UNWIND_ROUTE.md`) needs the **nonzero direction**: at ONE
marked bad point the slot-product has a SIMPLE pole with residue `r`, and the functional
*evaluates* to `−r` (parts orientation `w i j = h j − h i`; against the MLTie orientation
`h = −mlPart` this reproduces `resFunctional_mlGlue`'s `+r·g(α)`).  No higher-order
Cauchy–Pompeiu ladder: the slot is analytic, so the Leibniz absorption turns the order-`m`
pole data into a planar simple pole, and the surviving Stokes term at the marked chart is the
R0 atom `integral_dbar_smearedSimplePole` plus the repaired-Stokes kill of the remainder. -/

/-- **The slot-product has a simple pole** at the marked bad point: the chart-`j₀` read of
`h j₀` times the `dz`-slot agrees, on a punctured neighbourhood of the marked coordinate, with
`r·(ζ−α)⁻¹ + q` for an analytic `q` — the "order-exactly-one-worse-than-the-slot-zero" shape
that survives the Stokes kill with residue `r`. -/
def SlotProductSimplePoleAt (h : 𝔇.toFiniteCover.ι → X → ℂ) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ)
    (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : Prop :=
  ∃ q : ℂ → ℂ, AnalyticAt ℂ q (chartMap 𝔇 j₀ a) ∧
    (fun ζ => h j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ a)] fun ζ => r * (ζ - chartMap 𝔇 j₀ a)⁻¹ + q ζ

section MeroEvalEngine

variable {𝔇} {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- At the marked isolated bad point, the chart read of `β·g` inherits the simple-pole shape of
the distinguished `h̃_{j₀}·g_{j₀}` (the average is locally the distinguished component). -/
theorem pouAverageRead_mul_simplePole {j₀ : 𝔇.toFiniteCover.ι} {b : X} {r : ℂ}
    (hb : MLIsolated 𝔇 j₀ b) (hpole : SlotProductSimplePoleAt 𝔇 h g j₀ b r) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (chartMap 𝔇 j₀ b) ∧
      (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
        =ᶠ[𝓝[≠] (chartMap 𝔇 j₀ b)] fun ζ => r * (ζ - chartMap 𝔇 j₀ b)⁻¹ + q ζ := by
  obtain ⟨q, hq, hpe⟩ := hpole
  refine ⟨q, hq, ?_⟩
  have h1 := eventuallyEq_chartSymmRead_near_iso hb (pouAverage_eventuallyEq_near_iso hb h)
  have h2 : (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝 (chartMap 𝔇 j₀ b)]
        fun ζ => h j₀ ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ := by
    filter_upwards [h1] with ζ hζ
    rw [hζ]
  exact (h2.filter_mono nhdsWithin_le_nhds).trans hpe

/-- **The off-marked-chart Stokes kill**: for every chart `j ≠ j₀` (the marked point's chart),
the total-derivative term dies — every bad coordinate of chart `j` comes from a bad point
OTHER than the marked one (isolation), where the slot-product extends. -/
theorem integral_dbar_pouCoeff_pouAverage_eq_zero_off
    (hiso : ∀ a ∈ S, ∃ i₀, MLIsolated 𝔇 i₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hg : IsOneZeroCoeff 𝔇 g) {b : X} {j₀ : 𝔇.toFiniteCover.ι} (hb : MLIsolated 𝔇 j₀ b)
    (hext : ∀ a ∈ S, a ≠ b → ∀ i₀, MLIsolated 𝔇 i₀ a → SlotProductExtendsAt 𝔇 h g i₀ a)
    {j : 𝔇.toFiniteCover.ι} (hj : j ≠ j₀) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
  refine integral_dbar_pouCoeff_repairable_eq_zero 𝔇 (T := badCoords 𝔇 S j) j ?_ ?_
  · rintro z ⟨x, hxU, rfl⟩ hzT
    have hxS : x ∉ (S : Set X) := fun hx =>
      hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
    exact contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS
  · intro α hα
    obtain ⟨a, haS, haU, hca⟩ := exists_of_mem_badCoords 𝔇 hα
    obtain ⟨i₀, hi₀⟩ := hiso a haS
    have hji : j = i₀ := eq_isolated_index hi₀ haU
    subst hji
    subst hca
    have hab : a ≠ b := fun hcontra => hj (eq_isolated_index hb (hcontra ▸ haU))
    exact pouAverageRead_mul_extends hi₀ (hext a haS hab j hi₀)

/-- **The marked-chart Stokes evaluation**: at the marked point's chart, the total-derivative
term is the R0 smeared simple pole — split off `χ·(ζ−α)⁻¹` with `χ = r·pouCoeff` (`∂̄χ ≡ 0`
near the marked coordinate, weights locally constant), repair-and-kill the remainder, and
evaluate the singular piece by `integral_dbar_smearedSimplePole`. -/
theorem integral_dbar_pouCoeff_pouAverage_eq_residue
    (hiso : ∀ a ∈ S, ∃ i₀, MLIsolated 𝔇 i₀ a) (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h)
    (hg : IsOneZeroCoeff 𝔇 g) {b : X} (hbS : b ∈ S) {j₀ : 𝔇.toFiniteCover.ι}
    (hb : MLIsolated 𝔇 j₀ b) {r : ℂ} (hpole : SlotProductSimplePoleAt 𝔇 h g j₀ b r)
    (hext : ∀ a ∈ S, a ≠ b → ∀ i₀, MLIsolated 𝔇 i₀ a → SlotProductExtendsAt 𝔇 h g i₀ a) :
    ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z = -π * r := by
  classical
  set α := chartMap 𝔇 j₀ b with hαdef
  set T := badCoords 𝔇 S j₀ with hTdef
  have hαT : α ∈ T := (chartMap_mem_badCoords_iff 𝔇 hb.1).mpr hbS
  set u : ℂ → ℂ := fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ
    with hudef
  set sing : ℂ → ℂ := fun ζ => r * (ζ - α)⁻¹ with hsingdef
  obtain ⟨q, hq, hpe⟩ := pouAverageRead_mul_simplePole hb hpole
  -- the repaired remainder `u − sing`
  set u' : ℂ → ℂ := pointRepair (fun ζ => u ζ - sing ζ) T with hu'def
  have hu' : ∀ z ∈ chartMap 𝔇 j₀ '' (𝔇.U j₀ : Set X), ContDiffAt ℝ (⊤ : ℕ∞) u' z := by
    intro z hz
    by_cases hzT : z ∈ T
    · obtain ⟨a, haS, haU, hca⟩ := exists_of_mem_badCoords 𝔇 hzT
      subst hca
      by_cases hab : a = b
      · -- the marked coordinate: the remainder extends to `q`
        have hzα : chartMap 𝔇 j₀ a = α := by rw [hab, hαdef]
        rw [hzα] at hzT ⊢
        have hFq : (fun ζ => u ζ - sing ζ) =ᶠ[𝓝[≠] α] q := by
          filter_upwards [hpe] with ζ hζ
          have hζ' : u ζ = r * (ζ - α)⁻¹ + q ζ := hζ
          simp only [hsingdef]
          rw [hζ']
          ring
        exact ((hq.restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq
          (pointRepair_eventuallyEq_of_extends hzT hq hFq)
      · -- an unmarked bad coordinate: the extension minus the (analytic there) singular part
        have hzα : chartMap 𝔇 j₀ a ≠ α := fun hc => hab
          ((chartAt ℂ (𝔇.center j₀)).injOn (mem_chartSource_of_mem_U 𝔇 haU)
            (mem_chartSource_of_mem_U 𝔇 hb.1) hc)
        obtain ⟨i₀, hi₀⟩ := hiso a haS
        have hji : j₀ = i₀ := eq_isolated_index hi₀ haU
        rw [← hji] at hi₀
        obtain ⟨q₁, hq₁, hpe₁⟩ := pouAverageRead_mul_extends hi₀ (hext a haS hab j₀ hi₀)
        have hsingan : AnalyticAt ℂ sing (chartMap 𝔇 j₀ a) := by
          simp only [hsingdef]
          exact analyticAt_const.mul
            ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzα))
        have hFq : (fun ζ => u ζ - sing ζ) =ᶠ[𝓝[≠] chartMap 𝔇 j₀ a]
            fun ζ => q₁ ζ - sing ζ := by
          filter_upwards [hpe₁] with ζ hζ
          rw [show u ζ = q₁ ζ from hζ]
        exact (((hq₁.sub hsingan).restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq
          (pointRepair_eventuallyEq_of_extends hzT (hq₁.sub hsingan) hFq)
    · -- a good coordinate: `u − sing` is smooth there (`z ≠ α` since `α ∈ T`)
      obtain ⟨x, hxU, rfl⟩ := hz
      have hxS : x ∉ (S : Set X) := fun hx =>
        hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
      have hzα : chartMap 𝔇 j₀ x ≠ α := fun hc => hzT (hc ▸ hαT)
      have hsing : ContDiffAt ℝ (⊤ : ℕ∞) sing (chartMap 𝔇 j₀ x) := by
        simp only [hsingdef]
        exact contDiffAt_const.mul
          ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzα))
      exact ((contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS).sub hsing).congr_of_eventuallyEq
        (pointRepair_eventuallyEq_off hzT)
  -- the repaired remainder is C∞c after the `pouCoeff` clearance
  have hcd' : ContDiff ℝ (⊤ : ℕ∞) fun ζ => pouCoeff 𝔇 j₀ ζ * u' ζ :=
    contDiff_pouCoeff_mul 𝔇 hu'
  have hcs' : HasCompactSupport fun ζ => pouCoeff 𝔇 j₀ ζ * u' ζ :=
    (hasCompactSupport_pouCoeff 𝔇 j₀).mul_right
  -- the singular piece `χ·(ζ−α)⁻¹`, `χ := r·pouCoeff`
  set χ : ℂ → ℂ := fun ζ => r * pouCoeff 𝔇 j₀ ζ with hχdef
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_const.mul (contDiff_pouCoeff 𝔇 j₀)
  have hχcs : HasCompactSupport χ := (hasCompactSupport_pouCoeff 𝔇 j₀).mul_left
  have hps : ∀ ζ, pouCoeff 𝔇 j₀ ζ * sing ζ = χ ζ * (ζ - α)⁻¹ := fun ζ => by
    simp only [hsingdef, hχdef]
    ring
  -- `∂̄χ ≡ 0` near the marked coordinate (the weights are locally constant there)
  have hχconst : χ =ᶠ[𝓝 α] fun _ => r := by
    filter_upwards [eventuallyEq_pouCoeff_one_near_iso hb] with ζ hζ
    simp only [hχdef]
    rw [hζ, mul_one]
  have hdχ0 : ∀ᶠ ζ in 𝓝 α, DbarDisk.dbar χ ζ = 0 := by
    filter_upwards [hχconst.eventuallyEq_nhds] with ζ hζ
    rw [dbar_congr_of_eventuallyEq hζ]
    exact DbarDisk.dbar_const r ζ
  -- the continuous a.e. representative of `∂̄(χ·(·−α)⁻¹)`
  set Gf : ℂ → ℂ := fun ζ => DbarDisk.dbar χ ζ * (ζ - α)⁻¹ with hGdef
  have hGzero : Gf =ᶠ[𝓝 α] fun _ => (0 : ℂ) := by
    filter_upwards [hdχ0] with ζ hζ
    simp only [hGdef]
    rw [hζ, zero_mul]
  have hGcont : Continuous Gf := by
    rw [continuous_iff_continuousAt]
    intro ζ
    by_cases hζα : ζ = α
    · subst hζα
      exact continuousAt_const.congr hGzero.symm
    · exact ((DbarDisk.continuous_dbar hχcd).continuousAt).mul
        ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hζα))
  have hGcs : HasCompactSupport Gf := (DbarDisk.hasCompactSupport_dbar hχcs).mul_right
  have hane : ∀ᵐ z : ℂ ∂volume, z ≠ α := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton _
  have hGae : (fun ζ => DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ) =ᵐ[volume] Gf := by
    filter_upwards [hane] with ζ hζ
    simp only [hGdef]
    rw [dbar_smul_inv_sub hχcd α hζ, div_eq_mul_inv]
  have hIsing : Integrable fun ζ => DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ :=
    (hGcont.integrable_of_hasCompactSupport hGcs).congr hGae.symm
  have hI1 : Integrable fun ζ => DbarDisk.dbar (fun ξ => pouCoeff 𝔇 j₀ ξ * u' ξ) ζ :=
    (DbarDisk.continuous_dbar hcd').integrable_of_hasCompactSupport
      (DbarDisk.hasCompactSupport_dbar hcs')
  -- the value of the singular integral: the R0 atom, `χ(α) = r`
  have hval : ∫ ζ, DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) ζ = -π * r := by
    rw [integral_dbar_smearedSimplePole hχcd hχcs α]
    have hpou1 : pouCoeff 𝔇 j₀ α = 1 := by
      rw [hαdef, pouCoeff_chartMap 𝔇 hb.1]
      exact (eventually_rhoC_eq_one_near_iso hb).self_of_nhds
    simp only [hχdef]
    rw [hpou1, mul_one]
  -- the a.e. split of the target integrand (off the finite bad set)
  have haneT : ∀ᵐ z : ℂ ∂volume, z ∉ T := by
    refine ae_iff.mpr ?_
    have hset : {z : ℂ | ¬ z ∉ T} = ((T : Finset ℂ) : Set ℂ) := by
      ext z
      simp
    rw [hset]
    exact T.finite_toSet.measure_zero _
  have hgoalEq : (fun ζ => pouCoeff 𝔇 j₀ ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ))
      = fun ζ => pouCoeff 𝔇 j₀ ζ * u ζ := rfl
  have hsplit : (fun z => DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ * u ζ) z)
      =ᵐ[volume] fun z => DbarDisk.dbar (fun ξ => pouCoeff 𝔇 j₀ ξ * u' ξ) z
        + DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z := by
    filter_upwards [haneT] with z hzT
    have hzα : z ≠ α := fun hc => hzT (hc ▸ hαT)
    have hev : (fun ζ => pouCoeff 𝔇 j₀ ζ * u ζ)
        =ᶠ[𝓝 z] fun ζ => pouCoeff 𝔇 j₀ ζ * u' ζ + χ ζ * (ζ - α)⁻¹ := by
      filter_upwards [pointRepair_eventuallyEq_off (F := fun ζ => u ζ - sing ζ)
        (T := T) hzT] with ζ hζ
      rw [← hps ζ]
      have hζ' : u' ζ = u ζ - sing ζ := hζ
      rw [hζ']
      ring
    rw [dbar_congr_of_eventuallyEq hev]
    have hd1 : DifferentiableAt ℝ (fun ξ => pouCoeff 𝔇 j₀ ξ * u' ξ) z :=
      (hcd'.differentiable (by simp)) z
    have hinvC : DifferentiableAt ℂ (fun ξ : ℂ => (ξ - α)⁻¹) z :=
      (differentiableAt_id.sub_const α).inv (sub_ne_zero.mpr hzα)
    have hd2 : DifferentiableAt ℝ (fun ξ => χ ξ * (ξ - α)⁻¹) z :=
      ((hχcd.differentiable (by simp)) z).mul (hinvC.restrictScalars ℝ)
    exact DbarOpenDisk.dbar_add hd1 hd2
  calc ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z
      = ∫ z, (DbarDisk.dbar (fun ξ => pouCoeff 𝔇 j₀ ξ * u' ξ) z
          + DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z) := by
        rw [hgoalEq]
        exact integral_congr_ae hsplit
    _ = (∫ z, DbarDisk.dbar (fun ξ => pouCoeff 𝔇 j₀ ξ * u' ξ) z)
        + ∫ z, DbarDisk.dbar (fun ξ => χ ξ * (ξ - α)⁻¹) z := integral_add hI1 hIsing
    _ = -π * r := by
        rw [integral_dbar_eq_zero hcd' hcs', hval, zero_add]

/-- **THE EVALUATION-ENGINE HEADLINE — the residue functional EVALUATES coboundaries with one
marked simple-pole bad point.**  Same data shape as `resFunctional_eq_zero_of_mero_coboundary`
(`w i j = h j − h i` on overlaps, `h` smooth/holomorphic off a finite cover-isolated bad set
`S`), but at the marked point `b ∈ S` the chart-read slot-product `h̃_{j₀}·g_{j₀}` has a SIMPLE
POLE with residue `r` (`SlotProductSimplePoleAt`), while at every other bad point it extends.
Then

  `resFunctional 𝔇 t = −r`.

This is the NONZERO direction of the order-`m` pole ladder (R6D2_BLOCKER §2 wall (a)),
obtained with no higher-order Cauchy–Pompeiu: the slot is analytic, so Leibniz absorption
reduces the marked Stokes term to the R0 atom.  Orientation check: for `h = −mlPart` (the
MLTie cocycle `w i j = p_i − p_j`) the slot-product residue is `−r₀·g(α)`, and
`−(−r₀·g(α)) = +r₀·g(α)` reproduces `resFunctional_mlGlue`. -/
theorem resFunctional_eq_neg_residue_of_mero_coboundary (t : oneOneCoeff 𝔇)
    (ht : (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) = glueCoeff 𝔇 w g)
    (hg : IsOneZeroCoeff 𝔇 g) (hiso : ∀ a ∈ S, ∃ i₀, MLIsolated 𝔇 i₀ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hhol : HolomorphicOnSetsOff 𝔇 (S : Set X) h)
    (hδ : IsCoboundaryOn 𝔇 w h) {b : X} (hbS : b ∈ S) {j₀ : 𝔇.toFiniteCover.ι}
    (hb : MLIsolated 𝔇 j₀ b) {r : ℂ} (hpole : SlotProductSimplePoleAt 𝔇 h g j₀ b r)
    (hext : ∀ a ∈ S, a ≠ b → ∀ i₀, MLIsolated 𝔇 i₀ a → SlotProductExtendsAt 𝔇 h g i₀ a) :
    resFunctional 𝔇 t = -r := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the relocated curvature double sum dies (R5 mechanism, verbatim from the vanish engine)
  have hcurv : ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
      * (DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) = 0 := by
    calc ∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        = ∑ j, ∑ k, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
            integral_overlapTerm_relocate_mero hiso hsm hg j k
      _ = ∑ k, ∑ j, ∫ z, pouCoeff 𝔇 k z
            * (DbarDisk.dbar (fun ζ => rhoC 𝔇 j ((chartAt ℂ (𝔇.center k)).symm ζ)) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center k)).symm z) * g k z)) :=
          Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun k _ => sum_integral_relocated_eq_zero_mero hiso hsm hg k
  -- the Stokes sum survives only at the marked chart, where it is the R0 atom
  have hstokes : ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = -π * r := by
    calc ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        = ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j₀ ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)) z :=
          Finset.sum_eq_single j₀
            (fun j _ hj =>
              integral_dbar_pouCoeff_pouAverage_eq_zero_off hiso hsm hg hb hext hj)
            (fun hmem => absurd (Finset.mem_univ j₀) hmem)
      _ = -π * r :=
          integral_dbar_pouCoeff_pouAverage_eq_residue hiso hsm hg hbS hb hpole hext
  have hIfun : resIntegralFun 𝔇 (glueCoeff 𝔇 w g) = (π : ℂ) * r := by
    calc resIntegralFun 𝔇 (glueCoeff 𝔇 w g)
        = ∑ j, ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := rfl
      _ = ∑ j, ((∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
            - ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z) :=
          Finset.sum_congr rfl fun j _ =>
            integral_pouCoeff_glueCoeff_mero_split hiso hsm hhol hδ hg j
      _ = (∑ j, ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
              * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                  * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
            - ∑ j, ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z := by
          rw [Finset.sum_sub_distrib]
      _ = (π : ℂ) * r := by
          rw [hcurv, hstokes]
          ring
  have hI : resIntegral 𝔇 t = (π : ℂ) * r := by
    have hfun : resIntegral 𝔇 t = resIntegralFun 𝔇 (glueCoeff 𝔇 w g) := by
      rw [← ht]
      rfl
    rw [hfun, hIfun]
  rw [resFunctional_apply, hI, resNormalization]
  field_simp

end MeroEvalEngine

end Jacobians.Dolbeault.FineResidue
