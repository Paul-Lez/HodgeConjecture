/-
  `HoloRep` — the canonical holomorphic-representative toolkit for `OmegaDGerm 0` classes.

  DEDUPLICATION (2026-06-04): `holoRep`/`holoFn`/`gextLimRep_chart_analyticAt` + the chart-analyticity
  lemmas were DUPLICATED, defined independently in BOTH `CechDiskAcyclicProof` AND
  `DolbeaultComparisonInverse` (the latter's docstring cites a since-resolved `dbar_add` name clash as
  the reason it couldn't be shared — only one `dbar_add` exists now, in `DolbeaultH01`, so the
  obstruction is gone).  This file is the single canonical home; both consumers import it.

  It is built on the LIGHT, comparison-free `CechH0` alone (NOT the `CechDiskAcyclic` combination, which
  trips a `ℂ →L[ℝ] ℂ`-norm diamond), so it does not pull the ~900s Dolbeault-comparison chain — keeping
  the model/finiteness branch that uses it cheap to build.

  Contents (all complete, axiom-clean): `nhdsNE_neBot`; `holoRep`/`holoRep_mem`/`toGerm_holoRep`
  (a chosen holomorphic representative of a germ class); `holoFn` (the limit-repaired analytic
  representative `x ↦ limUnder (𝓝[≠] x) (Gext (holoRep hg))`); its chart-analyticity
  (`gextLimRep_chart_analyticAt`, `holoFn_chart_analyticAt`); the value-reading lemmas
  (`holoFn_eq_of_tendsto`, `holoFn_eq_holoRep_of_chart_analyticAt`); and `toGerm_holoFn` (reads back the
  germ).  The `∂̄`/`ContMDiff`/algebra lemmas built on top stay with their analytic consumers.
-/
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.RealManifold
import KirovDolbeault.Dolbeault.RealForms

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The punctured neighbourhood of a point of a `ℂ`-manifold is `NeBot` (no isolated points). -/
theorem nhdsNE_neBot (x : X) : (𝓝[≠] x).NeBot := by
  have hsrc : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  exact ((chartAt (H := ℂ) x).symm.tendsto_nhdsNE (x := (chartAt (H := ℂ) x) x)
    (by simp [(chartAt (H := ℂ) x).map_source hsrc])).neBot.mono
    (by simp only [(chartAt (H := ℂ) x).left_inv hsrc]; exact le_rfl)

/-- A holomorphic representative function of an `OmegaDGerm 0`-class (chosen). -/
noncomputable def holoRep {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) : W → ℂ :=
  (Submodule.mem_map.mp hg).choose

theorem holoRep_mem {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) : holoRep hg ∈ OmegaD (0 : Divisor X) W :=
  (Submodule.mem_map.mp hg).choose_spec.1

theorem toGerm_holoRep {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) : toGerm W (holoRep hg) = g :=
  (Submodule.mem_map.mp hg).choose_spec.2

/-- The **analytic representative** `F = limit-repair(Gext (holoRep hg)) : X → ℂ`. -/
noncomputable def holoFn {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) : X → ℂ :=
  fun x => limUnder (𝓝[≠] x) (Gext (holoRep hg))

/-- **(Chart-analyticity of the analytic representative.)** For a holomorphic (`OmegaD 0`) function
`g` on `↥W`, the limit-repair `x ↦ limUnder (𝓝[≠] x) (Gext g)` is chart-analytic at every `y ∈ W`
(it discards the removable-singularity junk of `Gext g`, agreeing with the normal-form representative
`toMeromorphicNFOn` of the chart-read).  Re-derivation of
`DolbeaultComparisonInverse.gextLimRep_chart_analyticAt`. -/
theorem gextLimRep_chart_analyticAt {W : Opens X} {g : W → ℂ} (hg : g ∈ OmegaD 0 W)
    {y : X} (hy : y ∈ W) :
    AnalyticAt ℂ ((fun x => limUnder (𝓝[≠] x) (Gext g)) ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) := by
  set φ := chartAt (H := ℂ) y with hφ
  set F := Gext g ∘ φ.symm with hFdef
  have hmero₀ : MeromorphicAt F (φ y) := Gext_meromorphicAt hg.1 hy
  obtain ⟨V₀, hV₀open, hzV₀, hFV₀, hana₀⟩ :=
    Jacobians.MeromorphicAt.exists_isOpen_meromorphicOn hmero₀
  set W' := V₀ ∩ φ.target with hWdef
  have hW'open : IsOpen W' := hV₀open.inter φ.open_target
  have hzW' : φ y ∈ W' := ⟨hzV₀, φ.map_source (mem_chart_source ℂ y)⟩
  have hFW' : MeromorphicOn F W' := fun w hw => hFV₀ w hw.1
  have hana : ∀ w ∈ W', w ≠ φ y → AnalyticAt ℂ F w := fun w hw hwz => hana₀ w hw.1 hwz
  have hW'target : W' ⊆ φ.target := fun _ hw => hw.2
  have hord : ∀ w ∈ W', 0 ≤ meromorphicOrderAt F w := by
    intro w hw
    by_cases hwz : w = φ y
    · subst hwz
      have hord0 := (mem_OmegaD.1 hg).2 ⟨y, hy⟩
      rw [ordU_eq_orderAt_Gext g hy] at hord0
      simpa using hord0
    · exact (hana w hw hwz).meromorphicOrderAt_nonneg
  refine (Jacobians.analyticAt_toMeromorphicNFOn hFW' hord hzW').congr ?_
  filter_upwards [hW'open.mem_nhds hzW'] with w hw
  show toMeromorphicNFOn F W' w = limUnder (𝓝[≠] (φ.symm w)) (Gext g)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (hFW' w hw) (hord w hw)
  have hNFOn : toMeromorphicNFOn F W' w = c := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hFW' hw]
    exact Jacobians.toMeromorphicNFAt_self_eq_limUnder (hFW' w hw) (hord w hw) hc
  rw [hNFOn]
  have hys : φ.symm w ∈ φ.source := φ.map_target (hW'target hw)
  have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
    have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hW'target hw)
    simpa using this
  haveI hNeBot : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
  symm
  apply Filter.Tendsto.limUnder_eq
  have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] (φ (φ.symm w))) := φ.tendsto_nhdsNE hys
  have hwr : φ (φ.symm w) = w := φ.right_inv (hW'target hw)
  have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 c) := by
    rw [← hwr] at hc; exact hc.comp hfwd
  refine hcomp.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds hys)] with z hz
  simp [hFdef, Function.comp, φ.left_inv hz]

/-- The chart-read of the analytic representative `holoFn hg` is `AnalyticAt` at the chart centre. -/
theorem holoFn_chart_analyticAt {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {y : X} (hy : y ∈ W) :
    AnalyticAt ℂ (holoFn hg ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
  gextLimRep_chart_analyticAt (holoRep_mem hg) hy

/-- **Chart-analytic ⟹ real-smooth.** If a `ℂ`-valued function `h` read in the chart at `y` is
complex-analytic at the chart image, then `h` is real-`C^∞` at `y`. -/
theorem contMDiffAt_real_of_chart_analyticAt {h : X → ℂ} {y : X}
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) h y := by
  have hcd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (h ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) :=
    by
      set_option backward.isDefEq.respectTransparency false in
        exact ((ha.contDiffAt.restrict_scalars (𝕜 := ℝ)).contMDiffAt).of_le le_top
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt (H := ℂ) y) y :=
    (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := y)).contMDiffAt
      ((chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y))
  refine (hcd.comp y hchart).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y)] with z hz
  simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz]

/-- The analytic representative is real-smooth at every point of the open. -/
theorem holoFn_contMDiffAt {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {y : X} (hy : y ∈ W) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (holoFn hg) y :=
  contMDiffAt_real_of_chart_analyticAt (holoFn_chart_analyticAt hg hy)

/-- `proj01` annihilates the `ℝ`-restriction of a complex-linear map. -/
theorem proj01_restrictScalars_eq_zero (L : ℂ →L[ℂ] ℂ) : proj01 (L.restrictScalars ℝ) = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply]
  have hL : mulI (L (mulI v)) = -L v := by
    calc
      mulI (L (mulI v)) = Complex.I * (L (Complex.I * v)) := by rfl
      _ = Complex.I * (Complex.I * L v) := by
        simpa using congrArg (fun w => Complex.I * w) (L.map_smulₛₗ Complex.I v)
      _ = -L v := by
        have hi : (Complex.I : ℂ) * Complex.I = -1 := by
          exact Complex.I_mul_I
        calc
          Complex.I * (Complex.I * L v) = ((Complex.I : ℂ) * Complex.I) * L v := by
            rw [mul_assoc]
          _ = -L v := by
            rw [hi]
            simp
  simp [hL]

/-- **A holomorphic representative has vanishing `∂̄`.** For `g ∈ OmegaDGerm 0 W`, the intrinsic
`∂̄` of its analytic representative `holoFn hg` is `0` at every `x ∈ W`. -/
theorem holoFn_dbar_eq_zero {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {x : X} (hx : x ∈ W) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn hg) x) = 0 := by
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn hg) x :=
    (holoFn_contMDiffAt hg hx).mdifferentiableAt (by simp)
  have hpull : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn hg) x
      = fderiv ℝ (fun z => holoFn hg ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [hmdiff.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
    congr 1
  have hCdiff : DifferentiableAt ℂ (fun z => holoFn hg ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
      (extChartAt 𝓘(ℝ, ℂ) x x) :=
    (gextLimRep_chart_analyticAt (holoRep_mem hg) hx).differentiableAt
  rw [hpull, hCdiff.fderiv_restrictScalars ℝ]
  exact proj01_restrictScalars_eq_zero _

/-- **`holoFn` reads off a continuous representative's value.**  If the holomorphic germ class `g` has
a representative `F : ↥W → ℂ` (`toGerm W F = g`) whose extension `Gext F` has limit `c` along
`𝓝[≠] y`, then `holoFn hg y = c`. -/
theorem holoFn_eq_of_tendsto {W : Opens X} {g : MGerm W} (hg : g ∈ OmegaDGerm (0 : Divisor X) W)
    (F : W → ℂ) (hgF : toGerm W F = g) {y : X} (hy : y ∈ W) {c : ℂ}
    (hc : Tendsto (Gext F) (𝓝[≠] y) (𝓝 c)) : holoFn hg y = c := by
  haveI := nhdsNE_neBot y
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] y] Gext F := by
    have hmatch : rawRestrictG (inf_le_right : W ⊓ W ≤ W) (toGerm W F)
        = rawRestrictG (inf_le_left : W ⊓ W ≤ W) (toGerm W (holoRep hg)) := by
      rw [hgF, toGerm_holoRep]
    exact Gext_overlap_eventuallyEq (holoRep hg) F hmatch hy hy
  show limUnder (𝓝[≠] y) (Gext (holoRep hg)) = c
  exact (hc.congr' heq.symm).limUnder_eq

/-- **`holoFn` reads off `holoRep` at analytic points.**  If at `z ∈ W` the chart-read of
`Gext (holoRep hg)` is analytic at the chart image, the limit-repair recovers the genuine value
`holoFn hg z = holoRep hg ⟨z, hz⟩`. -/
theorem holoFn_eq_holoRep_of_chart_analyticAt {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {z : X} (hz : z ∈ W)
    (ha : AnalyticAt ℂ (Gext (holoRep hg) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)) :
    holoFn hg z = holoRep hg ⟨z, hz⟩ := by
  set φ := chartAt (H := ℂ) z with hφ
  have hsrc : z ∈ φ.source := mem_chart_source ℂ z
  have hcontAt : ContinuousAt (Gext (holoRep hg) ∘ φ.symm) (φ z) := ha.continuousAt
  have htend : Tendsto (Gext (holoRep hg)) (𝓝[≠] z) (𝓝 (Gext (holoRep hg) z)) := by
    have hval : (Gext (holoRep hg) ∘ φ.symm) (φ z) = Gext (holoRep hg) z := by
      simp only [Function.comp_apply, φ.left_inv hsrc]
    rw [← hval]
    refine (hcontAt.continuousWithinAt.tendsto.comp
      (φ.tendsto_nhdsNE (mem_chart_source ℂ z))).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds hsrc)] with w hw
    simp only [Function.comp_apply, φ.left_inv hw]
  rw [Gext_apply_mem (holoRep hg) hz] at htend
  exact holoFn_eq_of_tendsto hg (holoRep hg) (toGerm_holoRep hg) hz htend

/-- **The analytic representative reads back the germ.**  `toGerm W (holoFn hg ∘ val) = g`. -/
theorem toGerm_holoFn {W : Opens X} {g : MGerm W} (hg : g ∈ OmegaDGerm (0 : Divisor X) W) :
    toGerm W (fun v : W => holoFn hg v.1) = g := by
  refine Eq.trans ?_ (toGerm_holoRep hg)
  rw [toGerm_eq_iff]
  intro u
  show (fun v : W => holoFn hg v.1) =ᶠ[𝓝[≠] u] holoRep hg
  set y : X := u.1 with hy
  have hyW : y ∈ W := u.2
  set φ := chartAt (H := ℂ) y with hφ
  have hysrc : y ∈ φ.source := mem_chart_source ℂ y
  have hmer : MeromorphicAt (Gext (holoRep hg) ∘ φ.symm) (φ y) :=
    Gext_meromorphicAt (holoRep_mem hg).1 hyW
  have hana : ∀ᶠ w in 𝓝[≠] (φ y), AnalyticAt ℂ (Gext (holoRep hg) ∘ φ.symm) w :=
    hmer.eventually_analyticAt
  have htendφ : Tendsto φ (𝓝[≠] y) (𝓝[≠] (φ y)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(φ.continuousAt hysrc).continuousWithinAt.tendsto, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [φ.open_source.mem_nhds hysrc] with z hz hzne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hzne ⊢
    exact fun hc => hzne (φ.injOn hz hysrc hc)
  have hanaX : ∀ᶠ z in 𝓝[≠] y,
      AnalyticAt ℂ (Gext (holoRep hg) ∘ φ.symm) (φ z) := htendφ.eventually hana
  have hsrcX : ∀ᶠ z in 𝓝[≠] y, z ∈ φ.source :=
    eventually_nhdsWithin_of_eventually_nhds (φ.open_source.mem_nhds hysrc)
  have hambient : ∀ᶠ z in 𝓝[≠] y,
      ∀ (hzW : z ∈ W), holoFn hg z = holoRep hg ⟨z, hzW⟩ := by
    filter_upwards [hanaX, hsrcX] with z hzana hzsrc hzW
    exact holoFn_eq_holoRep_of_chart_analyticAt hg hzW (analyticAt_chart_change hzsrc hzana)
  have hpb := eventually_subtype_of_nhdsNE
    (V := W) (u := u) (fun z => ∀ (hzW : z ∈ W), holoFn hg z = holoRep hg ⟨z, hzW⟩) hambient
  filter_upwards [hpb] with w hw
  simpa using hw w.2

end Jacobians.Dolbeault
