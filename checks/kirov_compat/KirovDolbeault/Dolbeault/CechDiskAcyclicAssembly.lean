/-
  Dolbeault ladder — assembling `FunctionDiskAcyclic 𝔙 0` from the reused chart-transport bridge
  (`CechDiskAcyclicProof`) and the function-level finite-cover ball Čech split.

  This file imports `Jacobians.Dolbeault.CechDiskAcyclicProof` (the committed STEP-B chart-transport
  bridge `chartHoloRep` / `chartHoloRep_dbar_eq_zero`, the analytic representative `holoFn` +
  `toGerm_holoFn`, and the function-level ball split `ballSplit_glued` / `ballSplit_pou`).

  NOTE on the import situation (an empirical finding, correcting the task's premise): importing BOTH
  `CechDiskAcyclicProof` AND `DolbeaultComparisonInverse` is impossible — not because of a
  `NormedAddCommGroup (ℂ →L[ℝ] ℂ)` diamond, but because the two files define EIGHT identically-named
  declarations in the same `Jacobians.Dolbeault` namespace (`holoRep`, `holoRep_mem`,
  `toGerm_holoRep`, `gextLimRep_chart_analyticAt`, `holoFn`, `holoFn_eq_of_tendsto`,
  `holoFn_eq_holoRep_of_chart_analyticAt`, `toGerm_holoFn`).  `CechDiskAcyclicProof` deliberately
  re-derives that toolkit precisely so it need NOT import `DolbeaultComparisonInverse`; the cost is
  that the PoU primitives (`cechPoU` / `primFn` / `cechTerm`) of `DolbeaultComparisonInverse` are not
  importable here.  Per the task FALLBACK we therefore REUSE the `CechDiskAcyclicProof` machinery by
  import, and isolate the remaining ball-solve obligation as an honest hypothesis (never a gap tactic).
-/
import KirovDolbeault.Dolbeault.CechDiskAcyclicProof

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric Filter

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The cocycle-component membership

The `(i,j)` component of an `𝒪`-cocycle is a holomorphic (`OmegaDGerm 0`) germ-class on the overlap
`U_i ⊓ U_j` — its `sections1` part. (Port of `DolbeaultComparisonInverse.cocycle_mem`, available here
because `cocycles1`/`sections1` live in `CechComplex`, not in the un-importable file.) -/

/-- The `(i,j)` component of a `1`-cocycle `s` is an `OmegaDGerm 0`-germ on `U_i ⊓ U_j`. -/
theorem cocycleComp_mem (𝔙 : FiniteFamily X) (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (i j : 𝔙.ι) :
    (s : 𝔙.Cochain1) (i, j) ∈ OmegaDGerm (0 : Divisor X) (𝔙.U i ⊓ 𝔙.U j) :=
  (Submodule.mem_inf.1 s.2).2 (i, j)

/-! ### STEP B (reverse) — a chart-analytic ambient function restricts to a holomorphic section

The reverse of the imported forward bridge (`chartHoloRep_analyticAt`): an ambient `H : X → ℂ` whose
chart-read at every `y ∈ U` is `ℂ`-analytic at the chart centre restricts to a member of
`OmegaD 0 U` (holomorphic, order `≥ 0`).  Provable from the imported `CechH0` bridge
(`ordU_eq_orderAt_Gext`, `Gext_meromorphicAt`) without the un-importable file: analytic ⟹ meromorphic
with nonnegative order. -/

/-- **Chart-analytic ambient ⟹ holomorphic section (STEP B reverse).**  If `H : X → ℂ` reads
`ℂ`-analytically in the chart at every `y ∈ U`, then `H ∘ val ∈ OmegaD 0 U`. -/
theorem omegaD_zero_of_chart_analyticAt {U : Opens X} {H : X → ℂ}
    (hH : ∀ y ∈ U, AnalyticAt ℂ (H ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) :
    (H ∘ (Subtype.val : U → X)) ∈ OmegaD (0 : Divisor X) U := by
  -- `H ∘ val` and `Gext (H ∘ val)` agree on `U`, so `H ∘ val`'s intrinsic chart-read at `u` is
  -- analytic (it equals `H`'s, which is analytic by `hH`), giving meromorphy + order `≥ 0`.
  have hGext_eq : ∀ y ∈ U, ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y),
      (Gext (H ∘ (Subtype.val : U → X)) ∘ (chartAt (H := ℂ) y).symm) w = (H ∘ (chartAt (H := ℂ) y).symm) w := by
    intro y hy
    have hsrc : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
    have hcont : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
      (chartAt (H := ℂ) y).continuousAt_symm ((chartAt (H := ℂ) y).map_source hsrc)
    have hUnhds : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) y) y), (chartAt (H := ℂ) y).symm w ∈ U := by
      have : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) ∈ U := by
        rw [(chartAt (H := ℂ) y).left_inv hsrc]; exact hy
      exact hcont.preimage_mem_nhds (U.isOpen.mem_nhds this)
    filter_upwards [hUnhds] with w hw
    simp only [Function.comp_apply, Gext_apply_mem (H ∘ (Subtype.val : U → X)) hw]
  -- Membership: meromorphic on `↥U` + order `≥ 0 = -(0)` at each point.
  refine ⟨?_, ?_⟩
  · -- `IsMeromorphic` on `↥U`: at each `u`, the chart-read is analytic (hence meromorphic).
    intro u
    have hana : AnalyticAt ℂ (Gext (H ∘ (Subtype.val : U → X)) ∘ (chartAt (H := ℂ) u.1).symm)
        ((chartAt (H := ℂ) u.1) u.1) :=
      ((hH u.1 u.2).congr (Filter.EventuallyEq.symm (hGext_eq u.1 u.2)))
    -- restrict the ambient meromorphy to `↥U`'s chart at `u` via `ordU_eq_orderAt_Gext`-style bridge.
    have hmer : MeromorphicAt (Gext (H ∘ (Subtype.val : U → X)) ∘ (chartAt (H := ℂ) u.1).symm)
        ((chartAt (H := ℂ) u.1) u.1) := hana.meromorphicAt
    have hbridge := Gext_chart_bridge (H ∘ (Subtype.val : U → X)) u.2
    rw [← hbridge.1] at hmer
    exact hmer.congr (hbridge.2.filter_mono nhdsWithin_le_nhds).symm
  · intro u
    show (-(((0 : Divisor X) u.1)) : WithTop ℤ) ≤ ordU (H ∘ (Subtype.val : U → X)) u
    rw [ordU_eq_orderAt_Gext (H ∘ (Subtype.val : U → X)) u.2]
    have hana : AnalyticAt ℂ (Gext (H ∘ (Subtype.val : U → X)) ∘ (chartAt (H := ℂ) u.1).symm)
        ((chartAt (H := ℂ) u.1) u.1) :=
      ((hH u.1 u.2).congr (Filter.EventuallyEq.symm (hGext_eq u.1 u.2)))
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    exact hana.meromorphicOrderAt_nonneg

/-! ### STEP D — the function → germ descent

Given honest holomorphic correctors `η_i ∈ OmegaD 0 (U_i)` whose differences split the cocycle's
analytic representatives `holoFn (s_{ij})` off a discrete set on each overlap (the output of the
function-level ball solve, transported back through the cover's chart), the germ-class `0`-cochain
`i ↦ [η_i]` has Čech coboundary exactly `s`.  This is the complete germ-bookkeeping half of STEP D:
it turns the pointwise/`𝓝[≠]` splitting into the germ-class identity `δ⁰[η] = s`. -/

/-- **STEP D descent.**  Honest holomorphic correctors `η_i ∈ OmegaD 0 (U_i)` whose
extension-by-zero differences `Gext η_j − Gext η_i` agree off a discrete set with the cocycle's
analytic representative `holoFn (s_{ij})` near every overlap point yield `FunctionDiskAcyclic 𝔙 0`.

The germ-bookkeeping: on `U_i ⊓ U_j`, `(δ⁰[η])_{ij} = [η_j ∘ incl − η_i ∘ incl]`.  By
`toGerm_eq_iff` this germ equals `s_{ij}` once `η_j ∘ incl − η_i ∘ incl =ᶠ[𝓝[≠] u]` a representative
of `s_{ij}`; `toGerm_holoFn` gives `holoFn (s_{ij})` as such a representative, and the hypothesis
supplies the `𝓝[≠]`-agreement (pulled back to the overlap submanifold).  Reuses `holoFn` /
`toGerm_holoFn` from `CechDiskAcyclicProof`. -/
theorem functionDiskAcyclic_of_holoCorrectors (𝔙 : FiniteFamily X)
    (η : Π i, 𝔙.U i → ℂ) (_hη : ∀ i, η i ∈ OmegaD (0 : Divisor X) (𝔙.U i))
    (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (hsplit : ∀ i j, ∀ x : X, x ∈ (𝔙.U i ⊓ 𝔙.U j : Opens X) →
      (fun z => Gext (η j) z - Gext (η i) z)
        =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔙 s i j)) :
    𝔙.cechDelta0 (fun i => toGerm (𝔙.U i) (η i)) = (s : 𝔙.Cochain1) := by
  funext p
  obtain ⟨i, j⟩ := p
  -- `(δ⁰[η])_{ij} = toGerm (η_j ∘ incl) − toGerm (η_i ∘ incl) = toGerm (η_j ∘ incl − η_i ∘ incl)`.
  show (rawRestrictG (inf_le_right : 𝔙.U i ⊓ 𝔙.U j ≤ 𝔙.U j) (toGerm (𝔙.U j) (η j))
        - rawRestrictG (inf_le_left : 𝔙.U i ⊓ 𝔙.U j ≤ 𝔙.U i) (toGerm (𝔙.U i) (η i)))
      = (s : 𝔙.Cochain1) (i, j)
  rw [rawRestrictG_coe, rawRestrictG_coe, ← map_sub]
  -- Reduce to a germ equality against `holoFn (s_{ij})` and apply `toGerm_holoFn`.
  rw [← toGerm_holoFn (cocycleComp_mem 𝔙 s i j), toGerm_eq_iff]
  intro u
  -- Transport the ambient `𝓝[≠] u.1` splitting to the overlap submanifold `↥(U_i ⊓ U_j)`.
  have hamb := hsplit i j u.1 u.2
  have hpb := eventually_subtype_of_nhdsNE
    (V := 𝔙.U i ⊓ 𝔙.U j) (u := u)
    (fun z => Gext (η j) z - Gext (η i) z = holoFn (cocycleComp_mem 𝔙 s i j) z) hamb
  filter_upwards [hpb] with w hw
  -- On the overlap, `Gext (η k) w.1 = (η k ∘ incl) w` (membership of `w.1` in `U k`).
  simp only [Function.comp_apply, Pi.sub_apply, openIncl]
  rw [Gext_apply_mem (η j) w.2.2, Gext_apply_mem (η i) w.2.1] at hw
  exact hw

/-! ### The honest chart-disk-cover corrector input and the `FunctionDiskAcyclic` discharge

`FunctionDiskAcyclic 𝔙 0` is exactly: every `𝒪`-cocycle admits holomorphic correctors splitting it.
We package the remaining analytic obligation — producing those correctors via the function-level ball
solve over the cover's shared chart (OBSTRUCTION 3 / STEP C) — as a single honest predicate
`HasHoloCorrectors`, and discharge `FunctionDiskAcyclic` from it via the STEP-D descent.
Supplying `HasHoloCorrectors` (the ball-solve output) is the precise remaining gap; the germ-level
collapse `H¹(disk, 𝒪) = 0` then follows from `cechH1_subsingleton_of_isDiskAcyclic`. -/

/-- **The honest corrector input (the precise remaining analytic obligation).**  For every `𝒪`
1-cocycle `s` there exist holomorphic correctors `η_i ∈ OmegaD 0 (U_i)` whose `Gext`-differences split
the analytic representatives `holoFn (s_{ij})` off a discrete set on each overlap.  This is the
output of the function-level finite-cover ball Čech split (`CechDiskAcyclicProof.ballSplit_glued` +
`DbarDiskCohomology.dbar_solvable_ball`) transported back through the cover's shared chart — STEP C of
the obstruction map.  Isolated as a predicate so the discharge below is complete. -/
def HasHoloCorrectors (𝔙 : FiniteFamily X) : Prop :=
  ∀ s : ↥(𝔙.cocycles1 (0 : Divisor X)),
    ∃ η : Π i, 𝔙.U i → ℂ, (∀ i, η i ∈ OmegaD (0 : Divisor X) (𝔙.U i)) ∧
      ∀ i j, ∀ x : X, x ∈ (𝔙.U i ⊓ 𝔙.U j : Opens X) →
        (fun z => Gext (η j) z - Gext (η i) z)
          =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔙 s i j)

/-- **Ambient chart-analytic correctors (the natural ball-solve output).**  For every `𝒪` 1-cocycle
`s` there exist AMBIENT functions `H_i : X → ℂ`, each chart-analytic at every point of `U_i`, whose
differences `H_j − H_i` agree off a discrete set with `holoFn (s_{ij})` near every overlap point.

This is strictly more natural than `HasHoloCorrectors` as the output of STEPs C.1–C.4: the ball solve
(`ballSplit_glued`) produces the correctors as honest *functions* whose chart-reads are analytic, and
chart-analyticity (not an a-priori `OmegaD` membership) is exactly what it delivers.  The reverse
chart dictionary `omegaD_zero_of_chart_analyticAt` upgrades chart-analyticity to `OmegaD 0`-membership
of the restriction, so this implies `HasHoloCorrectors` (next lemma). -/
def HasChartAnalyticCorrectors (𝔙 : FiniteFamily X) : Prop :=
  ∀ s : ↥(𝔙.cocycles1 (0 : Divisor X)),
    ∃ H : 𝔙.ι → X → ℂ,
      (∀ i, ∀ y ∈ 𝔙.U i, AnalyticAt ℂ (H i ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) ∧
      ∀ i j, ∀ x : X, x ∈ (𝔙.U i ⊓ 𝔙.U j : Opens X) →
        (fun z => H j z - H i z) =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔙 s i j)

/-- **`HasChartAnalyticCorrectors ⟹ HasHoloCorrectors`.**  Restrict each ambient
chart-analytic corrector `H_i` to `η_i := H_i ∘ val ∈ OmegaD 0 (U_i)` (STEP-B reverse,
`omegaD_zero_of_chart_analyticAt`); near an overlap point `Gext (η_i) = H_i` (both equal `H_i` on the
open `U_i`), so the ambient splitting of the `H_i` transfers verbatim to the `Gext (η_i)`. -/
theorem hasHoloCorrectors_of_chartAnalytic (𝔙 : FiniteFamily X)
    (h : HasChartAnalyticCorrectors 𝔙) : HasHoloCorrectors 𝔙 := by
  intro s
  obtain ⟨H, hana, hsplit⟩ := h s
  refine ⟨fun i => H i ∘ (Subtype.val : 𝔙.U i → X), fun i => omegaD_zero_of_chart_analyticAt (hana i),
    fun i j x hx => ?_⟩
  -- Near every point of the open `U_k`, `Gext (H_k ∘ val) = H_k`.
  have hGextEq : ∀ (k : 𝔙.ι), x ∈ 𝔙.U k →
      Gext (H k ∘ (Subtype.val : 𝔙.U k → X)) =ᶠ[𝓝[≠] x] H k := by
    intro k hxk
    have hUk : ∀ᶠ z in 𝓝[≠] x, z ∈ 𝔙.U k :=
      eventually_nhdsWithin_of_eventually_nhds ((𝔙.U k).isOpen.mem_nhds hxk)
    filter_upwards [hUk] with z hz
    simp only [Function.comp_apply, Gext_apply_mem (H k ∘ (Subtype.val : 𝔙.U k → X)) hz]
  have hj := hGextEq j hx.2
  have hi := hGextEq i hx.1
  -- Transfer the ambient splitting of `H` to the `Gext (η)` splitting.
  refine (Filter.EventuallyEq.sub hj hi).trans (hsplit i j x hx)

/-- **`FunctionDiskAcyclic 𝔙 0` from the corrector input.**  The STEP-D descent
(`functionDiskAcyclic_of_holoCorrectors`) turns each cocycle's correctors into the matching germ-class
`0`-cochain primitive, witnessing `FunctionDiskAcyclic`. -/
theorem functionDiskAcyclic_of_hasHoloCorrectors (𝔙 : FiniteFamily X)
    (h : HasHoloCorrectors 𝔙) : FunctionDiskAcyclic 𝔙 (0 : Divisor X) := by
  intro s hs
  obtain ⟨η, hη, hsplit⟩ := h ⟨s, hs⟩
  exact ⟨η, hη, functionDiskAcyclic_of_holoCorrectors 𝔙 η hη ⟨s, hs⟩ hsplit⟩

/-- **The germ-level disk-acyclicity atom from the corrector input.**  `IsDiskAcyclic 𝔙 0` — every
`𝒪` 1-cocycle is a coboundary — via `CechDiskAcyclic.isDiskAcyclic_of_funcLevel`. -/
theorem isDiskAcyclic_of_hasHoloCorrectors (𝔙 : FiniteFamily X)
    (h : HasHoloCorrectors 𝔙) : IsDiskAcyclic 𝔙 (0 : Divisor X) :=
  isDiskAcyclic_of_funcLevel 𝔙 0 (functionDiskAcyclic_of_hasHoloCorrectors 𝔙 h)

/-- **`H¹(disk, 𝒪) = 0` from the corrector input.**  Every class of `𝔙.cechH1 0` is `0` — the
headline germ-level collapse the finiteness / Serre-D=0 consumers want — modulo the single honest
corrector obligation `HasHoloCorrectors` (the ball solve over the shared chart). -/
theorem cechH1_subsingleton_of_hasHoloCorrectors (𝔙 : FiniteFamily X)
    (h : HasHoloCorrectors 𝔙) (q : 𝔙.cechH1 (0 : Divisor X)) : q = 0 :=
  cechH1_subsingleton_of_isDiskAcyclic 𝔙 0 (isDiskAcyclic_of_hasHoloCorrectors 𝔙 h) q

/-- **`H¹(disk, 𝒪) = 0` from ambient chart-analytic correctors.**  The end-to-end
collapse modulo the natural ball-solve output `HasChartAnalyticCorrectors`: STEP-B reverse +
STEP D + the `IsDiskAcyclic`-collapse, all complete here. -/
theorem cechH1_subsingleton_of_chartAnalyticCorrectors (𝔙 : FiniteFamily X)
    (h : HasChartAnalyticCorrectors 𝔙) (q : 𝔙.cechH1 (0 : Divisor X)) : q = 0 :=
  cechH1_subsingleton_of_hasHoloCorrectors 𝔙 (hasHoloCorrectors_of_chartAnalytic 𝔙 h) q

end Jacobians.Dolbeault

/-! ## Status and the EXACT remaining goal

WHAT IS DELIVERED HERE (all complete; axiom-clean `[propext, Classical.choice, Quot.sound]`):

  * `cocycleComp_mem` — the `(i,j)` component of an `𝒪`-cocycle is an `OmegaDGerm 0`-germ on the
    overlap (port of `DolbeaultComparisonInverse.cocycle_mem`; the un-importable file is avoided —
    `cocycles1`/`sections1` live in `CechComplex`).
  * `omegaD_zero_of_chart_analyticAt` — **STEP B reverse** (genuinely new): an ambient
    `H : X → ℂ` whose chart-read is `ℂ`-analytic at every point of `U` restricts to a holomorphic
    section `H ∘ val ∈ OmegaD 0 U`.  The reverse of the imported forward bridge
    `chartHoloRep_analyticAt`, which the obstruction prose flagged as the missing dictionary entry;
    proven from the imported `CechH0` bridge (`Gext_chart_bridge`, `ordU_eq_orderAt_Gext`,
    `AnalyticAt.meromorphicOrderAt_nonneg`).
  * `functionDiskAcyclic_of_holoCorrectors` — **STEP D, the function → germ descent**:
    honest holomorphic correctors `η_i ∈ OmegaD 0 (U_i)` whose `Gext`-differences split the cocycle's
    analytic representatives `holoFn (s_{ij})` off a discrete set on each overlap give the matching
    germ-class `0`-cochain primitive with `δ⁰[η] = s`.  REUSES `holoFn` + `toGerm_holoFn` from the
    imported `CechDiskAcyclicProof`; the germ-bookkeeping is `toGerm_eq_iff` +
    `eventually_subtype_of_nhdsNE` + `Gext_apply_mem`.
  * `HasChartAnalyticCorrectors` / `hasHoloCorrectors_of_chartAnalytic` — the remaining analytic
    obligation packaged at its NATURAL level (ambient chart-analytic correctors + ambient splitting,
    i.e. the raw ball-solve output), reduced to `HasHoloCorrectors` via STEP-B reverse.
  * `HasHoloCorrectors` and the chain `functionDiskAcyclic_of_hasHoloCorrectors` /
    `isDiskAcyclic_of_hasHoloCorrectors` / `cechH1_subsingleton_of_hasHoloCorrectors` /
    `cechH1_subsingleton_of_chartAnalyticCorrectors` — the complete chain
    `HasChartAnalyticCorrectors ⟹ HasHoloCorrectors ⟹ FunctionDiskAcyclic ⟹ IsDiskAcyclic ⟹
    (H¹(disk, 𝒪) = 0)`, so the headline germ-level collapse follows the instant the ball-solve output
    is supplied.

IMPORT FINDING (corrects the task premise).  Importing BOTH `CechDiskAcyclicProof` AND
`DolbeaultComparisonInverse` is impossible: it is not a `NormedAddCommGroup (ℂ →L[ℝ] ℂ)` diamond but
EIGHT duplicate declaration names in the shared `Jacobians.Dolbeault` namespace (`holoRep`,
`holoRep_mem`, `toGerm_holoRep`, `gextLimRep_chart_analyticAt`, `holoFn`, `holoFn_eq_of_tendsto`,
`holoFn_eq_holoRep_of_chart_analyticAt`, `toGerm_holoFn` — `CechDiskAcyclicProof` re-derives that whole
toolkit).  The empirical error is `environment already contains
'Jacobians.Dolbeault.gextLimRep_chart_analyticAt'`.  We therefore REUSE `CechDiskAcyclicProof` BY
IMPORT (its STEP-B bridge + `ballSplit_glued`/`ballSplit_pou` + `holoFn`/`toGerm_holoFn`), and do NOT
import `DolbeaultComparisonInverse`; its PoU primitives (`cechPoU`/`primFn`/`cechTerm`) are thus
unavailable here and would need porting for the steps below.

THE EXACT REMAINING GOAL: discharge `HasChartAnalyticCorrectors 𝔙` for a chart-disk cover (every `U_i`
pulls back through a SINGLE shared chart `φ = chartAt c₀` to an open `Ω_i ⊆ B = ball c r ⊆ ℂ` covering
`B`).  STEP-B reverse (`omegaD_zero_of_chart_analyticAt`) and STEP D are already complete here, so
the obligation is now precisely STEPs C.1–C.4 — the PoU globalization of the cocycle + the ball solve.
The concrete route, on top of what is imported here:

  STEP C.1.  Push `holoFn (s_{ij})` through `φ` to `ĝ_{ij} : ℂ → ℂ`, holomorphic on `Ω_i ∩ Ω_j`
    (`= chartHoloRep (cocycleComp_mem 𝔙 s i j) (center)`); the cocycle relation gives
    `ĝ_{ik} = ĝ_{jk} + ĝ_{ij}` on triple overlaps.

  STEP C.2 (PoU primitives — needs porting; the documented ~400-LoC `primFn`/`cechTerm` step).  Port
    `exists_smoothPartitionOfUnity_subordinate`, `cechPoU`, the real-smooth bridge
    `contMDiffAt_real_of_chart_analyticAt` / `holoFn_contMDiffAt`, and `contMDiffMul_real_complex`
    from `DolbeaultComparisonInverse` (each is self-contained: needs only `CechDiskAcyclicProof`'s
    imports + `Mathlib.Geometry.Manifold.PartitionOfUnity` + form machinery from `DolbeaultComparison`,
    which does NOT name-clash with `CechDiskAcyclicProof` — verified empirically).  Build, in the chart
    coordinate, `ĥ_i := ∑ᶠ q, (ρ_q ∘ φ.symm) · (ĝ_{qi} ext 0)`; the per-summand global-`C^∞` 3-case
    `tsupport`/overlap argument is exactly `primFn`/`cechTerm`.

  STEP C.3 (glued `∂̄`-datum).  `ω := ∂̄ ĥ_i` on `Ω_i`; the cocycle relation + the imported
    `dbar_fun_sum` + `∑ ∂̄ρ = 0` make these glue to one global smooth `ω` on `B`.

  STEP C.4 (ball solve — IMPORTED engine).  Feed `{ĥ_i}`, `ω` to the imported
    `CechDiskAcyclicProof.ballSplit_glued` to get holomorphic `η̂_i` on `Ω_i ∩ B` with
    `η̂_j − η̂_i = ĝ_{ij}`.  Then set `H_i := η̂_i ∘ φ` (chart-analytic on `U_i` via the imported
    `transition_analyticAt` / `analyticAt_chart_change`) and `H_j − H_i =ᶠ holoFn (s_{ij})` near
    overlaps (from STEP C.1) — exactly the data of `HasChartAnalyticCorrectors`.

With STEP-B reverse, STEP D, and the chain above already complete, the moment
`HasChartAnalyticCorrectors` is produced (STEPs C.1–C.4), `FunctionDiskAcyclic 𝔙 0` — and the
germ-level `H¹(disk, 𝒪) = 0` (`cechH1_subsingleton_of_chartAnalyticCorrectors`) — follow immediately.
No gaps anywhere in this file: the remaining open obligation is the predicate `HasChartAnalyticCorrectors`,
written as an explicit hypothesis, not a gap tactic.
-/
