/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueInftyCoherence
import KirovDolbeault.Dolbeault.FormTraceBundleBridge
import KirovDolbeault.Dolbeault.MittagLeffler

/-!
# Gate A — the SOUND branch-value boundedness `hbnd` for a general meromorphic `α = ω₀·g`

This file discharges the branch-value boundedness `hbnd` of the kirovGenus-`0` simple-`∞` canonical
capstone `…_germ_CfullHreg_inftyClosed` **soundly**, for a general meromorphic numerator `g`, WITHOUT
the over-strong global-holomorphic-`αBr` route of `SerreResidueInftyClosedBnd.lean`.

## Why a new `hbnd` route (the `αBr` soundness finding)

`Jacobians.Dolbeault.SerreResidueTheorem.hbnd_canonical_of_offBranch` discharges `hbnd` via
`hbnd_of_eventual_sphereCoherence`, whose input `hαBrAgree` demands a **global** holomorphic 1-form
`αBr : HolomorphicOneForms X` agreeing with `ω₀·g` at **every** fibre point near each branch value
`b₀`.  Those fibre points sweep an **open** set `U = F⁻¹(punctured disk)`, so `αBr = ω₀·g` on `U`,
whence `αBr/ω₀ = g` GLOBALLY (identity theorem, `X` connected) — forcing every pole of `g` to sit at a
zero of `ω₀`.  For a general meromorphic `g` this is FALSE (the Serre-pairing consumer has `g = α/ω₀`
with poles wherever `α` has poles).  So that route is unsound for general `α`; see `human_input.md`
(2026-06-09, "8th bad field").

## The sound route (the `g`-weighted bundle SUM)

`hbnd` is genuinely TRUE (Miranda §VIII.3: the symmetric SUM extends across branch points).  The
geometric trace decomposes (`FormTraceBundleBridge.traceLocalCoeff_traceFun_eq_sheetSum`) as the
`g`-weighted fibre sum of the **global holomorphic** `ω₀`'s bundle summand:

> `valueChartTrace ω₀ f Φ z = ∑_{p ∈ F⁻¹(coe z)} g(p) · sheetPullback ω₀ p`.

We bound `(z − b₀)·[g-weighted sum] → 0` via a `g`-weighted analogue of
`TraceForm.traceLocalCoeff_mul_sub_tendsto_zero`: the per-preimage `ω₀`-summand boundedness
`TraceForm.traceSummand_localCoeff_mul_sub_tendsto` (applied to the GLOBAL HOLOMORPHIC `ω₀`, **not**
`ω₀·g`) times the BOUNDED weight `g(x)` (continuous at the fibre, since `b₀` is off the pole-values).
No global `αBr` — the form fed to the crux is `ω₀` itself.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y` — the `g`-weighted boundedness of the bundle SUM at
  a branch value, mirroring `traceLocalCoeff_mul_sub_tendsto_zero_Y` with the `g`-weight.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256.
* `Jacobians/TraceForm.lean` (`traceLocalCoeff_mul_sub_tendsto_zero_Y`, the un-weighted crux).
* `human_input.md` (2026-06-09 — the `αBr` soundness finding + this sound route).
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.TraceResidue

open Jacobians

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### The `g`-weighted per-preimage summand boundedness

Near a preimage `x₀` of the branch value `y₀`, the `g`-weighted bundle summand
`(c(fx) − c(y₀)) · g(x) · inCoordinates(traceSummand ω₀ x) 1 = g(x) · bigPhi f ω₀ y₀ x`
tends to `0`: `bigPhi → 0` (the un-weighted summand crux `traceSummand_localCoeff_mul_sub_tendsto`,
applied to the *global holomorphic* `ω₀`) and `g` is continuous at `x₀` (so bounded). -/

/-- **`g`-weighted per-preimage summand boundedness.**  For a global holomorphic `ω₀`, a weight `g`
continuous at a preimage `x₀` of `y₀ = f x₀`, the scaled `g`-weighted bundle summand tends to `0` as
`x → x₀` through the off-critical punctured neighbourhood. -/
theorem traceSummand_localCoeff_mul_sub_gWeighted_tendsto (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (ω₀ : HolomorphicOneForms X) (g : X → ℂ) {y₀ : Y} {x₀ : X} (hfx₀ : f x₀ = y₀)
    (hg : ContinuousAt g x₀) :
    Tendsto (fun x => g x * bigPhi f ω₀ y₀ x)
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) := by
  -- The un-weighted summand tends to 0 (the proven crux, applied to the global holomorphic ω₀).
  have hbig : Tendsto (fun x => bigPhi f ω₀ y₀ x)
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) :=
    traceSummand_localCoeff_mul_sub_tendsto f hf hnonconst ω₀ hfx₀
  -- g continuous (bounded) × bigPhi → 0, so g · bigPhi → 0.
  have hgc : Tendsto g (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 (g x₀)) :=
    hg.mono_left nhdsWithin_le_nhds
  have := hgc.mul hbig
  simpa using this

/-! ### The `g`-weighted bundle SUM boundedness at a branch value

Mirror of `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero_Y` with the `g`-weight inserted: in the
fixed chart `c := chartAt ℂ y₀`, the scaled `g`-weighted bundle local coefficient
`(c y − c y₀) · ∑ᶠ x ∈ f⁻¹{y}, g(x)·localCoeffLin(traceSummand ω₀ x) → 0`.  Each fibre term is
`g(x)·bigPhi f ω₀ y₀ x → 0` (the per-preimage `g`-weighted summand boundedness); the finite-subcover /
uniform off-branch card assembly is verbatim. -/

/-- **`g`-weighted bundle SUM boundedness (chart side).**  For a global holomorphic `ω₀` and a weight
`g` continuous at every preimage of the branch value `y₀`, the `g`-weighted bundle local coefficient
satisfies `(c y − c y₀) · ∑ᶠ x ∈ f⁻¹{y}, g(x)·localCoeffLin(traceSummand ω₀ x) → 0` as `y → y₀`
through `y ≠ y₀`.  No global `ω₀·g` form: the boundedness rides on the GLOBAL HOLOMORPHIC `ω₀` summand,
the `g` enters only as a bounded weight. -/
theorem traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f)
    (hg : ∀ x ∈ f ⁻¹' {y₀}, ContinuousAt g x) :
    Tendsto (fun y => ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)
        * ∑ᶠ x ∈ f ⁻¹' {y}, g x * localCoeffLin y₀ y (traceSummand f ω₀ x)) (𝓝[≠] y₀) (𝓝 0) := by
  classical
  set c := chartAt ℂ y₀ with hc
  -- Uniform off-branch fibre-cardinality bound near the branch point.
  obtain ⟨N, hN⟩ := fibre_ncard_bddAbove_near_branch f hf hnonconst hy₀
  -- Per-preimage open neighbourhood with the scaled `g`-weighted-coefficient bound.
  have hloc : ∀ (x₀ : X), f x₀ = y₀ → ∀ ε' : ℝ, 0 < ε' →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, x ∉ criticalSet f → x ≠ x₀ → ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
    intro x₀ hfx₀ ε' hε'
    have hgx₀ : ContinuousAt g x₀ := hg x₀ (by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfx₀)
    have htend := traceSummand_localCoeff_mul_sub_gWeighted_tendsto f hf hnonconst ω₀ g hfx₀ hgx₀
    have hev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
      have := htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hε')
      filter_upwards [this] with x hx
      simpa [Complex.dist_eq] using hx
    rw [eventually_nhdsWithin_iff] at hev
    rw [eventually_iff_exists_mem] at hev
    obtain ⟨V, hVnhd, hV⟩ := hev
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hVnhd
    refine ⟨U, hUopen, hxU, ?_⟩
    intro x hxU' hxcrit hxne
    exact hV x (hUsub hxU') ⟨hxcrit, hxne⟩
  have hproper : IsProperMap f := isProperMap_of_contMDiff f hf
  have hcompact : IsCompact (f ⁻¹' {y₀}) :=
    (isClosed_singleton.preimage hf.continuous).isCompact
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set ε' : ℝ := ε / (N + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  choose! U hUopen hUmem hUbnd using fun (p : X) (hp : f p = y₀) => hloc p hp ε' hε'
  obtain ⟨b, hbsub, hbfin, hbcover⟩ :=
    hcompact.elim_finite_subcover_image
      (b := f ⁻¹' {y₀}) (c := U)
      (fun i hi => hUopen i hi)
      (fun p hp => Set.mem_iUnion₂.mpr ⟨p, hp, hUmem p hp⟩)
  set V : Set X := ⋃ i ∈ b, U i with hVdef
  have hVopen : IsOpen V := isOpen_biUnion (fun i hi => hUopen i (hbsub hi))
  obtain ⟨W, hWopen, hWmem, hWsub⟩ := properNbhd hproper y₀ hVopen hbcover
  have hWnhd : W ∈ 𝓝[≠] y₀ := nhdsWithin_le_nhds (hWopen.mem_nhds hWmem)
  filter_upwards [hWnhd, hN, eventually_notMem_branchLocus f hf hnonconst y₀,
    self_mem_nhdsWithin] with y hyW hyN hybranch hyne
  have hynotbranch : y ∉ branchLocus f := hybranch
  have hyncard : (f ⁻¹' {y}).ncard ≤ N := hyN hynotbranch
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hynotbranch
  -- The `g`-weighted summand identity: `(c y − c y₀)·g(x)·localCoeffLin(traceSummand ω₀ x) = g(x)·bigPhi`.
  have hsummand : ∀ x ∈ f ⁻¹' {y},
      (c y - c y₀) * (g x * localCoeffLin y₀ y (traceSummand f ω₀ x)) = g x * bigPhi f ω₀ y₀ x := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [bigPhi, localCoeffLin, LinearMap.coe_mk, AddHom.coe_mk, hc]
    rw [hx]; ring
  have heq : (c y - c y₀) * ∑ᶠ x ∈ f ⁻¹' {y}, g x * localCoeffLin y₀ y (traceSummand f ω₀ x)
      = ∑ᶠ x ∈ f ⁻¹' {y}, g x * bigPhi f ω₀ y₀ x := by
    rw [mul_finsum_mem _ _]
    exact finsum_mem_congr rfl hsummand
  have hxbound : ∀ x ∈ f ⁻¹' {y}, ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
    intro x hx
    have hxy : f x = y := by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; exact hx
    have hxcrit : x ∉ criticalSet f := fun hmem => hynotbranch ⟨x, hmem, hxy⟩
    have hxW : x ∈ f ⁻¹' W := by rw [Set.mem_preimage, hxy]; exact hyW
    have hxV : x ∈ V := hWsub hxW
    rw [hVdef, Set.mem_iUnion₂] at hxV
    obtain ⟨i, hib, hiU⟩ := hxV
    have hfiy₀ : f i = y₀ := by
      have := hbsub hib; rw [Set.mem_preimage, Set.mem_singleton_iff] at this; exact this
    have hxne_i : x ≠ i := by
      intro hcontra; rw [hcontra, hfiy₀] at hxy; exact hyne (by rw [Set.mem_singleton_iff, hxy])
    exact hUbnd i hfiy₀ x hiU hxcrit hxne_i
  rw [heq, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hcardN : hfin.toFinset.card ≤ N := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]; exact hyncard
  calc ‖∑ x ∈ hfin.toFinset, g x * bigPhi f ω₀ y₀ x‖
      ≤ ∑ x ∈ hfin.toFinset, ‖g x * bigPhi f ω₀ y₀ x‖ := norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε' := by
        refine Finset.sum_le_card_nsmul _ _ _ (fun x hx => ?_)
        exact le_of_lt (hxbound x ((Set.Finite.mem_toFinset hfin).mp hx))
    _ = (hfin.toFinset.card : ℝ) * ε' := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ) * ε' := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hε')
        exact_mod_cast hcardN
    _ < ε := by
        rw [hε'def]
        calc (N : ℝ) * (ε / (N + 1)) = (N / (N + 1)) * ε := by ring
          _ < 1 * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              rw [div_lt_one (by positivity)]; linarith
          _ = ε := one_mul ε

end Jacobians.TraceResidue

namespace Jacobians.Dolbeault.FormTraceGlobal

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.SerreResidueTheorem

attribute [local instance] Classical.propDecidable

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The geometric trace as the `g`-weighted bundle finsum (αBr-FREE)

The sound bridge: at a regular value `coe z` with a sphere sheet system `S`, the geometric fibre trace
equals the `g`-weighted bundle finsum of the **global holomorphic** `ω₀` over the fibre — with **no**
auxiliary global form `αBr`.  This is the αBr-free analogue of `fibreTrace_traceCoeff_eq_traceLocalCoeff`
(whose αBr-naming step we drop), feeding the `g`-weighted boundedness crux directly. -/

/-- **Per-sheet frame identity.**  On `RiemannSphere`, the `coe b₀`-frame local coefficient of the
`ω₀`-trace summand at the sheet point `s (coe z)` equals the raw bundle summand `sheetPullback ω₀ s
(coe z) 1`.  Frame swap (`localCoeffLin_coe_base_swap`) to the self `coe z`-frame, then
`inCoordinates_center_self`, then `traceSummandAt_sheet_eq` (summand = `sheetPullback`). -/
theorem localCoeffLin_traceSummand_eq_sheetPullback (ω₀ : HolomorphicOneForms X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) (i : Fin S.n) :
    localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
        (traceSummand f.toRiemannSphere ω₀ (S.sheet i (((z : ℂ) : RiemannSphere))))
      = sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) := by
  -- `traceSummand F ω₀ (S.sheet i (coe z)) = sheetPullback ω₀ (S.sheet i)(coe z)`.
  have hsummand : traceSummand f.toRiemannSphere ω₀ (S.sheet i (((z : ℂ) : RiemannSphere)))
      = sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) := by
    have h := S.traceSummandAt_sheet_eq f.contMDiff_toRiemannSphere ω₀ i S.mem_V
    rw [traceSummandAt] at h; exact h
  rw [hsummand, localCoeffLin_coe_base_swap]
  -- Self-frame: `localCoeffLin (coe z)(coe z) φ = φ 1`.
  unfold localCoeffLin
  simp only [LinearMap.coe_mk, AddHom.coe_mk, inCoordinates_center_self]
  rfl

/-- **Geometric trace = `g`-weighted bundle finsum (αBr-FREE).**  At a regular value `coe z` with a
sphere sheet system `S` (regular fibre — `hderiv`, `hmero`), the geometric fibre trace coefficient
equals the `g`-weighted bundle finsum of `ω₀` over the fibre `F⁻¹(coe z)`, read in the `coe b₀`-frame:

> `(fibreTrace ω₀ f (ofSphereSheetSystem S hderiv hmero)).traceCoeff z
>    = ∑ᶠ x ∈ F⁻¹(coe z), g x · localCoeffLin (coe b₀) (coe z) (traceSummand F ω₀ x)`.

No global `αBr` — the boundedness rides on the global holomorphic `ω₀` summand weighted by `g`. -/
theorem fibreTrace_traceCoeff_eq_gWeighted_finsum (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere))))) :
    (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z
      = ∑ᶠ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
          g x * localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
            (traceSummand f.toRiemannSphere ω₀ x) := by
  -- The geometric side = `g`-weighted sheet sum (the proven αBr-free body via the moving sum).
  have hmoving := (fibreTrace_eventuallyEq_movingSum ω₀ f
    (FibreRegularData.ofSphereSheetSystem S hderiv hmero) (fun i => S.holoReprSheet i)
    (fun _ => rfl)
    (fun i => (S.holoReprSheet_contMDiffAt i).continuousAt)
    (fun i => S.holoReprSheet_section i)).self_of_nhds
  rw [hmoving]
  simp only []
  have hgeo : ∑ i, chartIntegrand ω₀ g ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i)
        ((chartAt ℂ ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i))
          (S.holoReprSheet i z))
        * deriv (fun w => (chartAt ℂ ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i))
            (S.holoReprSheet i w)) z
      = ∑ i, g (S.sheet i (((z : ℂ) : RiemannSphere)))
          * sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) :=
    Finset.sum_congr rfl (fun i _ =>
      movingSummand_eq_g_sheetPullback ω₀ g (S.sheet i) (S.sheet_mdifferentiableAt i S.mem_V))
  rw [hgeo]
  -- The `g`-weighted finsum side = `g`-weighted sheet sum (fibre = range of sheets + frame identity).
  rw [S.fibre_eq _ S.mem_V, finsum_mem_range (S.sheet_inj _ S.mem_V), finsum_eq_sum_of_fintype]
  exact (Finset.sum_congr rfl (fun i _ => by
    rw [localCoeffLin_traceSummand_eq_sheetPullback ω₀ S i])).symm

/-! ### The αBr-free eventual sphere-sheet coherence at a branch value

The first conjunct of `hev_canonical_of_offBranch` — `valueChartTrace = fibreTrace(ofSphereSheetSystem)`
near `b₀` — *without* any `αBr`.  Built from the canonical-selection regular-value data exactly as
`hev_canonical_of_offBranch`, but ending in `valueChartTrace_eq_sphereSheetFibreTrace` (αBr-free) rather
than the αBr-bundled `hevBr_of_regularData`. -/

/-- **αBr-free eventual sphere-sheet coherence at a branch value (canonical selection).**  For `b₀` off
the pole-centres `cs` (and `br ⊇ branchValues f`), eventually each `z` near `b₀` carries a sphere sheet
system `S_z` with `valueChartTrace ω₀ f (canonical) z = (fibreTrace ω₀ f (ofSphereSheetSystem S_z …))
.traceCoeff z` — the regular-value coherence (NO global form `αBr`). -/
theorem hev_coherence_canonical_of_offBranch (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ}
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j))) :
    ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z
          = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z := by
  classical
  -- The off-branch sphere system at each regular value `z` (off `image cs ∪ br`).
  set Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)) := fun z hz =>
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv)
      (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h)))).some with hSreg
  have hoff : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := fun z hz =>
    coe_notMem_branchLocus_of_notMem_branchValues f hdiv
      (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h))
  -- Each sheet point is a regular point of `f` (off-branch local injectivity).
  have hderivReg' : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0 := fun z hz i =>
    sheet_holoRepr_deriv_ne_zero f hdiv (hoff z hz)
      ((Sreg z hz).sheet_section i _ (Sreg z hz).mem_V)
  -- The sphere-sheet fibre point lies in the full fibre `F⁻¹(coe z)` (good value); `g`-data follows.
  have hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) := by
    intro z hz i
    have hfib : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (Sreg z hz).sheet_section i _ (Sreg z hz).mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv (hgood_reg z hz),
      canonicalFibreSelection_eq_ofFullFibre g f hdiv (hgood_reg z hz)] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv z j := hj.symm
    rw [hpt]; exact (hgood_reg z hz).2 j
  -- The canonical-fibre conditions near each regular `z` (same as `hev_canonical_of_offBranch`).
  have hΦinjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (canonicalFibreSelection g f hdiv b').xs := fun z hz =>
    canonicalFibreSelection_hΦinjReg g f hdiv (hoff z hz) (hgmero_reg z hz)
  have hΦrangeReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (canonicalFibreSelection g f hdiv b').xs
        = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} := fun z hz =>
    canonicalFibreSelection_hΦrangeReg g f hdiv (hoff z hz) (hgmero_reg z hz)
  have hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective
        (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))) := fun z hz => by
    have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' (Sreg z hz).V) ∈ 𝓝 z :=
      (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds
        ((Sreg z hz).isOpen_V.mem_nhds (Sreg z hz).mem_V)
    filter_upwards [hVnhds] with b' hb'
    exact (Sreg z hz).sheet_inj (((b' : ℂ) : RiemannSphere)) hb'
  have hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := fun z hz => by
    have hev : ∀ i : Fin (Sreg z hz).n, ∀ᶠ b' in 𝓝 z,
        (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
          (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := by
      intro i
      have hcont : ContinuousAt ((Sreg z hz).holoReprSheet i) z :=
        ((Sreg z hz).holoReprSheet_contMDiffAt i).continuousAt
      have hsrc : (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
          𝓝 ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))) :=
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).open_source.mem_nhds
          (mem_chart_source ℂ _)
      have := hcont.preimage_mem_nhds (show
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
          𝓝 ((Sreg z hz).holoReprSheet i z) from hsrc)
      filter_upwards [this] with b' hb' using hb'
    rw [eventually_all]; exact hev
  -- Eventually `z ∉ image cs ∪ br` on `𝓝[≠] b₀`: the finite bad set minus `{b₀}` is closed, avoids `b₀`.
  have hfin : (((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}).Finite :=
    ((Finset.univ.image cs ∪ br).finite_toSet).diff
  have hcompl : ((((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}))ᶜ ∈ 𝓝 b₀ :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with z hz_ne hz_compl
  have hzb : z ≠ b₀ := by simpa using hz_ne
  have hz : z ∉ Finset.univ.image cs ∪ br := by
    intro hmem
    exact hz_compl ⟨hmem, fun h => hzb (by simpa using h)⟩
  refine ⟨Sreg z hz, hderivReg' z hz, hmeroReg z hz, ?_⟩
  exact valueChartTrace_eq_sphereSheetFibreTrace ω₀ g f (canonicalFibreSelection g f hdiv)
    (Sreg z hz) (hderivReg' z hz) (hmeroReg z hz) (hΦinjReg z hz) (hΦrangeReg z hz)
    (hsheetInjReg z hz) (hsheetMemReg z hz)

/-! ### The SOUND branch-value boundedness `hbnd` (canonical selection, general `g`)

Assembling the sound `hbnd`: at a branch value `b₀` (off pole-centres), the geometric trace germ-equals
the `g`-weighted bundle finsum (αBr-free coherence + the finsum bridge), and the `g`-weighted bundle SUM
boundedness crux gives `(z − b₀)·trace → 0`.  The form fed to the crux is the GLOBAL HOLOMORPHIC `ω₀`;
`g` enters only as the bounded fibre weight (continuous at the branch fibre, off the pole-values). -/

/-- **The SOUND `hbnd` for the canonical selection at a branch value (general meromorphic `g`).**
For a genuine branch value `b₀ ∈ branchValues f` off the pole-centres `cs`, the canonical full-fibre
trace satisfies `(z − b₀)·valueChartTrace ω₀ f (canonical) z → 0`.  Discharged via:

* `hev_coherence_canonical_of_offBranch` — `valueChartTrace =ᶠ[𝓝[≠] b₀] fibreTrace(ofSphereSheetSystem)`
  (αBr-FREE);
* `fibreTrace_traceCoeff_eq_gWeighted_finsum` — `fibreTrace.traceCoeff z = ∑ᶠ g·localCoeffLin(traceSummand
  ω₀)`;
* `traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y` — the `g`-weighted bundle SUM boundedness (the form
  is the GLOBAL HOLOMORPHIC `ω₀`; `g` is the bounded weight, continuous at the branch fibre off the
  pole-values).

NO global `αBr` — the SOUND replacement of `hbnd_canonical_of_offBranch` for general `α = ω₀·g`. -/
theorem hbnd_canonical_sound (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ}
    (hb₀branch : b₀ ∈ branchValues f hdiv)
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_fibre : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((b₀ : ℂ) : RiemannSphere))}, ContinuousAt g x) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
      (𝓝[≠] b₀) (𝓝 0) := by
  classical
  -- `coe b₀ ∈ branchLocus`.
  have hbrloc : (((b₀ : ℂ) : RiemannSphere)) ∈ branchLocus f.toRiemannSphere :=
    (mem_branchValues f hdiv).mp hb₀branch
  -- The g-weighted bundle SUM boundedness (sphere side), read at `coe b₀`.
  have hcruxY := Jacobians.TraceResidue.traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y
    f.toRiemannSphere f.contMDiff_toRiemannSphere (hncF_of_div_ne_zero f hdiv) ω₀ g hbrloc hg_fibre
  -- Pull back along `coe : ℂ → RiemannSphere` (carries `𝓝[≠] b₀` to `𝓝[≠] (coe b₀)`).
  have hmap : Tendsto (fun z : ℂ => ((z : ℂ) : RiemannSphere)) (𝓝[≠] b₀)
      (𝓝[≠] (((b₀ : ℂ) : RiemannSphere))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(OnePoint.continuous_coe.continuousAt).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz_ne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcoe
    exact hz_ne (by rw [Set.mem_singleton_iff]; exact OnePoint.coe_injective hcoe)
  have hcrux := hcruxY.comp hmap
  -- Read in the affine value chart: `chart(coe b₀)(coe b₀) = b₀`, `coe z` is the sphere value.
  simp only [Function.comp_apply, RiemannSphere.chartAt_coe, RiemannSphere.chartCoe_apply_coe]
    at hcrux
  -- Transport along the eventual coherence + the g-weighted finsum bridge.
  refine hcrux.congr' ?_
  filter_upwards [hev_coherence_canonical_of_offBranch hdiv hbr hgood_reg hgmero_reg]
    with z hz
  obtain ⟨S, hderiv, hmero, hcoh⟩ := hz
  rw [hcoh, fibreTrace_traceCoeff_eq_gWeighted_finsum ω₀ g f S hderiv hmero (b₀ := b₀)]
  simp only [Function.comp_apply, RiemannSphere.chartCoe_apply_coe]

/-- **Trace analytic at a good value** (the non-branch `br`-value case, αBr-free).  At a good value `w`
with near-value `g`-meromorphy `hgmero_w` and fibre points non-poles (`hg_an`), the canonical full-fibre
trace is `AnalyticAt w` — the moving-datum coherence `analyticAt_valueChartTrace_of_movingDatum ∘
movingCoherenceDatum_canonical` (re-derived here so the file is independent of the unsound
`hbnd_canonical_of_offBranch`). -/
theorem hreg_canonical_at_goodValue_sound (hdiv : (f.div : Divisor X) ≠ 0) {w : ℂ}
    (hw_good : GoodValue g f hdiv w)
    (hgmero_w : ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an : ∀ y : X, f.toRiemannSphere y = (((w : ℂ) : RiemannSphere)) →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ y).symm z)) ((chartAt ℂ y) y)) :
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w := by
  classical
  set hoff := hw_good.1 with hoffdef
  set S : Jacobians.LocalSheetSystem f.toRiemannSphere (((w : ℂ) : RiemannSphere)) :=
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv) hoff).some with hS
  have hmeroS : ∀ k, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))) (S.sheet k (((w : ℂ) : RiemannSphere)))) := by
    intro k
    have hfib : S.sheet k (((w : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((w : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact S.sheet_section k _ S.mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv hw_good,
      canonicalFibreSelection_eq_ofFullFibre g f hdiv hw_good] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : S.sheet k (((w : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv w j := hj.symm
    rw [hpt]; exact hw_good.2 j
  set C : MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) w :=
    movingCoherenceDatum_canonical hdiv hoff S hmeroS hgmero_w with hC
  refine analyticAt_valueChartTrace_of_movingDatum C (fun k => ?_)
  have himg : Finset.univ.image C.D.xs
      = Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [hC]
    exact movingCoherenceDatum_canonical_D_image (ω₀ := ω₀) hdiv hoff S hmeroS hgmero_w hw_good
  have hmemImg : C.D.xs k ∈ Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [← himg]; exact Finset.mem_image_of_mem C.D.xs (Finset.mem_univ k)
  rw [Finset.mem_image] at hmemImg
  obtain ⟨j, _, hj⟩ := hmemImg
  have hfib : f.toRiemannSphere (C.D.xs k) = (((w : ℂ) : RiemannSphere)) := by
    rw [← hj]
    have : (canonicalFibreSelection g f hdiv w).xs j ∈
        Set.range (canonicalFibreSelection g f hdiv w).xs := ⟨j, rfl⟩
    rw [canonicalFibreSelection_xs_range g f hdiv hw_good] at this
    rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
  exact hg_an _ hfib

/-- **The SOUND `hbnd` for the canonical selection at a `br`-value off the pole-centres (general `g`).**
Both cases of the boundedness, αBr-FREE:

* `b₀ ∈ branchValues f` — the sound `g`-weighted bundle SUM route (`hbnd_canonical_sound`);
* `b₀ ∉ branchValues f` — the trace is analytic at `b₀` (`hreg_canonical_at_goodValue_sound`), hence
  continuous, so `(z − b₀)·trace → 0`.

This is the SOUND replacement of `hbnd_canonical_of_offBranch` — no global form `αBr`, no unsatisfiable
field; valid for a general meromorphic numerator `g`. -/
theorem hbnd_canonical_sound_full (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ} (_hb₀br : b₀ ∈ br)
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_fibre : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((b₀ : ℂ) : RiemannSphere))}, ContinuousAt g x)
    (hgood_b₀ : b₀ ∉ branchValues f hdiv → GoodValue g f hdiv b₀)
    (hgmero_b₀ : b₀ ∉ branchValues f hdiv → ∀ᶠ b' in 𝓝 b₀, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_b₀ : b₀ ∉ branchValues f hdiv → ∀ y : X,
      f.toRiemannSphere y = (((b₀ : ℂ) : RiemannSphere)) →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ y).symm z)) ((chartAt ℂ y) y)) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
      (𝓝[≠] b₀) (𝓝 0) := by
  by_cases hb₀branch : b₀ ∈ branchValues f hdiv
  · exact hbnd_canonical_sound hdiv hbr hb₀branch hgood_reg hgmero_reg hg_fibre
  · -- Regular `br`-value: trace analytic at `b₀`, hence `(z − b₀)·trace → 0` by continuity.
    have han : AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) b₀ :=
      hreg_canonical_at_goodValue_sound hdiv (hgood_b₀ hb₀branch) (hgmero_b₀ hb₀branch)
        (hg_an_b₀ hb₀branch)
    have hcont : ContinuousAt (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) b₀ :=
      han.continuousAt
    have hsub : Tendsto (fun z : ℂ => z - b₀) (𝓝[≠] b₀) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => z - b₀) (𝓝 b₀) (𝓝 0) := by
        have := (continuous_sub_right b₀).tendsto b₀; simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    have hmul := hsub.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    simpa using hmul

/-- **Manifold continuity from chart-pullback analyticity.**  If `g ∘ chart_x.symm` is analytic at
`chart_x x`, then `g : X → ℂ` is continuous at `x` (`g = (g ∘ chart.symm) ∘ chart` near `x`, both
factors continuous). -/
theorem continuousAt_of_chartPullback_analyticAt {x : X}
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ContinuousAt g x := by
  have h1 : ContinuousAt (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := hg.continuousAt
  have h2 : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have h3 : ContinuousAt ((fun z => g ((chartAt ℂ x).symm z)) ∘ (chartAt ℂ x)) x := h1.comp h2
  have heq : ((fun z => g ((chartAt ℂ x).symm z)) ∘ (chartAt ℂ x)) =ᶠ[𝓝 x] g := by
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    show g ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = g y
    rw [(chartAt ℂ x).left_inv hy]
  exact h3.congr heq

end Jacobians.Dolbeault.FormTraceGlobal

/-! ## The SOUND kirovGenus-`0` capstone — `hbnd` discharged via the `g`-weighted bundle SUM

Wiring the sound `hbnd_canonical_sound_full` into `…_germ_CfullHreg_inftyClosed`, replacing the unsound
αBr route of `…_inftyClosed_bnd`.  The two αBr-dependent hypotheses (`αBr`/`hαBrAgree`) are **GONE**: the
boundedness rides on the global holomorphic `ω₀` with `g` as a bounded weight, requiring only that `g` is
continuous (analytic) at the branch fibres — which follows from `hg_an_offpoles` (branch values are off
the pole-values).  This is the honest, satisfiable-for-general-`α` capstone. -/

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip RiemannSphere

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-- **Gate A `∑Res = 0` (kirovGenus `0`, simple `∞`-poles, canonical selection) — `hbnd` discharged SOUNDLY.**
Identical to `residueTheorem_ofCanonicalSimpleInfty_germ_CfullHreg_inftyClosed` with the branch-value
boundedness `hbnd` constructed via the **sound `g`-weighted bundle SUM** `hbnd_canonical_sound_full`
(form = global holomorphic `ω₀`, `g` the bounded fibre weight) — NOT the unsatisfiable global-holomorphic
`αBr` of `…_inftyClosed_bnd`.

The genuine branch values use the `g`-weighted boundedness crux; the non-branch `br`-values use the
good-value analyticity `hgood_brOff`/`hgmero_brOff` (vacuous when `br = branchValues f`).  `hg_fibre` at
the branch fibres and `hg_an` at the non-branch `br`-fibres are both derived internally from
`hg_an_offpoles` (a fibre point over a value off `image cs` is off `poles`).  This rests on **only the
discrete genericity bookkeeping** — no `αBr`, no false field. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed_soundBnd
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    -- The good-value `g`-data at the non-branch `br`-values (vacuous when `br = branchValues f`).
    (hgood_brOff : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs → b₀ ∉ branchValues f hdiv →
      GoodValue g f hdiv b₀)
    (hgmero_brOff : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs → b₀ ∉ branchValues f hdiv →
      ∀ᶠ b' in 𝓝 b₀, ∀ j,
        MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
          ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed hdiv hgood m cs ρ hcs_ball
    hcs_inj br hbr hcenters_cs hoff_cs hc_good hgmero hgood_reg hgmero_reg hg_an_offpoles hsimpleInf
    hmeroInf hnonpole_inf_an
    (fun b₀ hb₀br hb₀cs =>
      hbnd_canonical_sound_full hdiv hbr hb₀br hgood_reg hgmero_reg
        -- `hg_fibre`: `g` analytic (continuous) at each branch fibre point (off the pole-values).
        (fun x hx => continuousAt_of_chartPullback_analyticAt
          (hg_an_offpoles x (notMem_poles_of_fibrePoint_offCentres hcenters_cs hb₀cs
            (by rwa [Set.mem_preimage, Set.mem_singleton_iff] at hx))))
        (hgood_brOff b₀ hb₀br hb₀cs) (hgmero_brOff b₀ hb₀br hb₀cs)
        -- `hg_an` at the non-branch `br`-fibres: off `image cs` ⟹ non-pole-value ⟹ non-pole fibre.
        (fun _hbv y hy => hg_an_offpoles y
          (notMem_poles_of_fibrePoint_offCentres hcenters_cs hb₀cs hy)))

/-! ## The genericity bundle `AdaptedF` and the unconditional reduction

For a **genuine meromorphic** numerator `g : MeromorphicFunction X`, the `g`-meromorphy/holomorphy
hypotheses of the sound capstone are ALL automatic (`g` is meromorphic at every point, analytic off its
poles).  What remains is exactly the **generic-position data of the adapted cover `f`** — the pole-values
of `α = ω₀·g` off the branch locus, and the simple `∞`-poles.  We bundle that residual as `AdaptedF` and
reduce the unconditional `∑Res = 0` to `∃ f, AdaptedF`. -/

/-- **The adapted-cover genericity datum** for `α = ω₀·g` (genuine meromorphic `g`) over `poles`.  Bundles
*only* the generic-position facts about a single nonconstant `f` that the sound kirovGenus-`0` capstone
consumes; every `g`-meromorphy/holomorphy field is discharged automatically from `g`'s global meromorphy
(`hg_an_offpoles`/`hg_mero_pt`), so they are NOT fields here. -/
structure AdaptedF (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X) (poles : Finset X) where
  /-- The cover `f` is nonconstant. -/
  f : MeromorphicFunction X
  /-- `f.div ≠ 0`. -/
  hdiv : (f.div : Divisor X) ≠ 0
  /-- The enumeration `cs` of the finite pole-values of `α` (the `f`-images of `poles`, off `∞`). -/
  m : ℕ
  cs : Fin m → ℂ
  ρ : ℝ
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  hcs_inj : Function.Injective cs
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- **Genericity 1:** the finite pole-values of `α` lie off `f`'s branch locus (the pole fibres are
  unramified). -/
  hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere
  /-- **Genericity 2:** `f` has simple poles over `∞`. -/
  hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1
  /-- `poles` is exactly the pole set of `α = ω₀·g`: off `poles`, `g`'s chart-pullback is analytic (so
  `α` is holomorphic there).  This is the *definition* of `poles`, not a genericity demand. -/
  hg_an_offpoles : ∀ x : X, x ∉ poles →
    AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)

/-- **Unconditional Gate A `∑Res = 0` from an adapted cover.**  For a genuine meromorphic `g`, an
`AdaptedF` datum discharges the SOUND kirovGenus-`0` capstone: every `g`-meromorphy field is automatic from
`g.meromorphic` (g meromorphic at every point), the `g`-analyticity-off-poles is `hg_an_offpoles`, the
off-branch good-value conditions follow from `hoff_cs`/`hg_an_offpoles`, and `br := branchValues f` makes
the non-branch `br`-fields vacuous.  Hence `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`. -/
theorem residueTheorem_of_adaptedF (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) (A : AdaptedF ω₀ g poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 := by
  classical
  -- `GoodValue` at every value off the branch locus whose fibre is `g`-meromorphic — automatic for a
  -- genuine meromorphic `g` once the value is off the branch locus.
  have hmero_pt : ∀ y : X, MeromorphicAt (fun w => g.toFun ((chartAt ℂ y).symm w)) ((chartAt ℂ y) y) :=
    fun y => g.meromorphic y
  -- `GoodValue` from off-branch (the `g`-meromorphy of fibre points is free).
  have hgood_of_off : ∀ w, (((w : ℂ) : RiemannSphere)) ∉ branchLocus A.f.toRiemannSphere →
      GoodValue g.toFun A.f A.hdiv w := fun w hw =>
    ⟨hw, fun i => hmero_pt (fullFibreEnum A.f A.hdiv w i)⟩
  -- `hgmero`-style eventual fibre `g`-meromorphy: holds for ALL `b'` (genuine meromorphic `g`).
  have hgmero_all : ∀ w : ℂ, ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g.toFun ((chartAt ℂ (fullFibreEnum A.f A.hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum A.f A.hdiv b' j)) (fullFibreEnum A.f A.hdiv b' j)) := fun w =>
    Filter.Eventually.of_forall (fun b' j => hmero_pt (fullFibreEnum A.f A.hdiv b' j))
  -- A finite pole-value `coe p` (image of a pole `a`) is off the branch locus, via `hcenters_cs` +
  -- `hoff_cs`: `coe p ∈ (poles.image F).erase ∞ = (image cs).image coe`, so `coe p = coe (cs i)`.
  have hpoleval_off : ∀ p : ℂ, (∃ a ∈ poles, A.f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      (((p : ℂ) : RiemannSphere)) ∉ branchLocus A.f.toRiemannSphere := by
    intro p ⟨a, ha, hfa⟩
    have hmem : (((p : ℂ) : RiemannSphere)) ∈
        (poles.image A.f.toRiemannSphere).erase OnePoint.infty := by
      rw [Finset.mem_erase]
      exact ⟨OnePoint.coe_ne_infty p, hfa ▸ Finset.mem_image_of_mem _ ha⟩
    rw [← A.hcenters_cs, Finset.mem_image] at hmem
    obtain ⟨q, hq, hqp⟩ := hmem
    rw [Finset.mem_image] at hq
    obtain ⟨i, _, hi⟩ := hq
    have : (((A.cs i : ℂ) : RiemannSphere)) = (((p : ℂ) : RiemannSphere)) := by rw [hi, hqp]
    rw [← this]; exact A.hoff_cs i
  refine residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed_soundBnd
    A.hdiv (fun p hp => hgood_of_off p (hpoleval_off p hp)) A.m A.cs A.ρ A.hcs_ball A.hcs_inj
    (branchValues A.f A.hdiv) (Finset.Subset.refl _) A.hcenters_cs A.hoff_cs
    (fun i => hgood_of_off (A.cs i) (A.hoff_cs i)) (fun i => hgmero_all (A.cs i))
    (fun w hw => hgood_of_off w (coe_notMem_branchLocus_of_notMem_branchValues A.f A.hdiv
      (fun h => hw (Finset.mem_union_right _ h))))
    (fun w _ => hgmero_all w) A.hg_an_offpoles A.hsimpleInf
    (fun i => hmero_pt (inftyFibreEnum A.f i)) (fun k hk => A.hg_an_offpoles (inftyFibreEnum A.f k) hk)
    -- `hgood_brOff`/`hgmero_brOff`: vacuous (`br = branchValues f`, so `b₀ ∈ br ∧ b₀ ∉ branchValues f`).
    (fun b₀ hb₀br _ hb₀nbr => absurd hb₀br hb₀nbr)
    (fun b₀ hb₀br _ hb₀nbr => absurd hb₀br hb₀nbr)

/-- **`residueSum` form of the adapted-cover residue theorem.**  `residueSum ω₀ g.toFun poles = 0` for a
genuine meromorphic `g` with an adapted cover `A` — i.e. `MittagLefflerForm.res = 0`, the well-definedness
content `Res : H¹(X,Ω) → ℂ` (Forster 17.3) rests on. -/
theorem residueSum_of_adaptedF (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X) (A : AdaptedF ω₀ g poles) :
    residueSum ω₀ g.toFun poles = 0 :=
  residueTheorem_of_adaptedF ω₀ g poles A

/-! ### The unramified-route genericity `ExistsAdaptedF` (SUPERSEDED — Gate A closed)

The unramified route closes `∑Res = 0` via `residueTheorem_of_adaptedF` *given* the existence of an
adapted cover (`ExistsAdaptedF`, below).  That existence demand is now **superseded**: the ramified
route proves its genericity outright (`existsAdaptedFRamified`, `SerreResidueGateAGenericity.lean`)
and closes the residue theorem with **no hypothesis** (`residueTheorem_unconditional`,
`SerreResidueRamifiedRealSlitGeometry.lean`).  The definition is kept because
`ExistsAdaptedFRamified.of_existsAdaptedF` (`SerreResidueGateAInftyBuilder.lean`) records that the
proven ramified genericity is formally *weaker* (no harder) than this unramified one. -/

/-- **The unramified-route genericity (superseded; see the section header).**  An adapted cover exists
for `α = ω₀·g` over any finite `poles` off which `g`'s chart-pullback is analytic (so `poles ⊇` the
actual poles of `α`).

**Soundness (non-false).**  This is genuinely achievable for a general meromorphic `g`: take any
nonconstant meromorphic function (`exists_nonconstant_meromorphic`, the Riemann inequality) and replace
it by `f' = (f − a·1)⁻¹` for a value `a` that is *not* a critical value of `f` and is chosen so that the
finite pole-values of `α` under `f'` avoid `f'`'s (finite) branch values.  `a` not a critical value ⟹
`f'`'s poles (the simple zeros of `f − a`) are all SIMPLE (`hsimpleInf`); the finite "bad `a`" set
(critical values + the finitely many `a` making a pole-value collide with a branch value) is finite, so a
good `a` exists (Miranda p. 254 + generic position).  Hence `ExistsAdaptedF` is a TRUE existential, not a
disguised `False`. -/
def ExistsAdaptedF (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X) (poles : Finset X) : Prop :=
  (∀ x : X, x ∉ poles →
    AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) →
  Nonempty (AdaptedF ω₀ g poles)

end Jacobians.Dolbeault.SerreResidueTheorem
