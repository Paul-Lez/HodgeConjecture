/-
  Čech finiteness — instantiating the acyclic `exists_cechModel` via the completed disk-acyclicity.

  `CechFinitenessWiring.exists_cechModel` (Forster 14.9):
  every finite cover `𝔘` admits a chart-disk Leray model (`DiskOverlapData` + `Coboundaries`, including
  the `leray` disk-acyclicity field) whose sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine
  germ-class `𝔘.cechH1 D`.  As scoped in `CechRefinement.lean`'s `## PLAN`, the FULL statement
  (arbitrary `𝔘`, arbitrary `D`) is blocked by STEP B — Leray cover-INDEPENDENCE (`refineH1` being an
  iso for a strictly-finer Leray refinement), a greenfield ~several-hundred-LoC piece on top of the
  proven disk ∂̄-atoms.  That is NOT what the newly-completed disk-acyclicity unblocked.

  `CechFinitenessWiring` already provides the END-TO-END model assembly for the ACYCLIC case:
  `exists_cechModel_of_subsingleton` discharges `exists_cechModel 𝔘 D` whenever `𝔘.cechH1 D` is a
  SUBSINGLETON, via the trivial model `DiskOverlapData.empty.trivialCoboundaries` (whose `leray` field
  is discharged and whose `supH1 = 0`) and `LinearEquiv.ofSubsingleton`.

  THIS FILE supplies the geometric INSTANTIATION that the new disk-acyclicity makes possible
  (`exists_cechModel_of_sharedChart_zero`): for a `SharedChartCover 𝔇` at `D = 0`, the subsingleton
  hypothesis is discharged by the COMPLETED disk-acyclicity `SharedChartCover.hasGluedDbarDatum` (commit
  61484f5) — `H¹(disk, 𝒪) = 0` — so the disk `∂̄`-solvability engine is wired through the
  model-construction front door:
      `dbar_solvable_ball` ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ `exists_cechModel 𝔇 0`.
  (It lives here, not in `CechFinitenessWiring`, because it needs the `GluedDbarDatum` /
  `CechFinitenessBallSolve` closure, which imports — and so cannot be imported by — `CechComplex`'s
  downstream `CechFinitenessWiring`.)

  WHY THE GENERAL `exists_cechModel` STAYS A SORRY (the exact remaining obstruction):  an arbitrary
  Leray `𝔘` is NOT a `SharedChartCover` and its `cechH1 𝔘 D` is NOT a subsingleton (for high kirovGenus /
  general `D`), so the subsingleton route does not apply.  Closing the general statement needs the
  comparison `cechH1 𝔘 D ≃ₗ supH1` for a NON-acyclic `supH1` — the genuine Montel-model comparison +
  Leray cover-independence STEP B (`CechRefinement.lean`'s `## PLAN`, `CechRefinementLeray.lean`'s
  `## SURJECTIVITY`).  The forward `germ → BddHol` cochain map is built for `D = 0`
  (`CechModelCochain`/`CechModelDatum`); the inverse, the δ-square, and STEP B are not.

  All declarations here are complete, axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
-- Only the model TYPES / abstract spine (`DiskOverlapData`, `Coboundaries`, `supH1`,
-- `exists_cechModel_of_subsingleton`, `trivialCoboundaries`, `DiskOverlapData.empty`) are needed
-- here, so we import `CechModelBase` rather than `CechFinitenessWiring`.  This also keeps
-- `DolbeaultComparisonInverse` (pulled in by the now-`CechFinitenessDtwist`-importing
-- `CechFinitenessWiring`) out of this file's import closure, avoiding the ported-twin name
-- collisions with `CechFinitenessBallSolve` (imported below).
import KirovDolbeault.Dolbeault.CechModelBase
import KirovDolbeault.Dolbeault.CechModelDifferential
import KirovDolbeault.Dolbeault.GluedDbarDatum
import KirovDolbeault.Dolbeault.ChartCoverDbarGlue
import KirovDolbeault.Dolbeault.CechModelHolomorphic
import KirovDolbeault.Dolbeault.CechFinitenessBallSolve

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`exists_cechModel` for a shared-chart disk cover at `D = 0` (the disk-acyclicity wiring).**  For
any `SharedChartCover 𝔇` (a finite cover whose sets sit in one chart with chart-images in a fixed
ball), `exists_cechModel 𝔇.toFiniteCover 0` holds.  The subsingleton hypothesis of
`exists_cechModel_of_subsingleton` is discharged by the COMPLETED disk-acyclicity
`cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 (𝔇.hasGluedDbarDatum)` (commit 61484f5): every class of
`𝔇.toFiniteCover.cechH1 0` is `0`, so that `H¹` is a subsingleton.

This wires the newly-unblocked `leray`/disk-acyclicity piece through the model-construction front
door: the disk `∂̄`-solvability (`dbar_solvable_ball`) ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ the
assembled `exists_cechModel` on the shared-chart cover (the trivial acyclic model + the
`LinearEquiv.ofSubsingleton` comparison). -/
theorem exists_cechModel_of_sharedChart_zero (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔇.toFiniteFamily.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) := by
  haveI : Subsingleton (𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) :=
    subsingleton_iff.mpr fun a b => by
      rw [cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H a,
        cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H b]
  exact exists_cechModel_of_subsingleton 𝔇.toFiniteFamily 0

/-- **`exists_holomorphicCechModel` for a shared-chart disk cover at `D = 0` (the corrected branch).**
This is the same disk-acyclicity wiring as the older wrapper above, but routed to the corrected
holomorphic-shrinking model. -/
theorem exists_holomorphicCechModel_of_sharedChart_zero (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) :
    ∃ (d : HolomorphicDiskOverlapData) (c : HolomorphicCoboundaries d),
      Nonempty (𝔇.toFiniteFamily.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) := by
  haveI : Subsingleton (𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) :=
    subsingleton_iff.mpr fun a b => by
      rw [cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H a,
        cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H b]
  exact HolomorphicDiskOverlapData.exists_holomorphicCechModel_of_subsingleton 𝔇.toFiniteFamily 0

/-- The sound interior-core glued datum witness, re-exposed at the model-construction layer so the
rebased branch is available from the consumer side. -/
theorem hasGluedDbarDatumOnInteriorCore (𝔇 : SharedChartCover X) :
    ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
      ∃ dbarDatum : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) dbarDatum ∧
        ∀ i, ∀ z ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core),
          DbarDisk.dbar (chartPrim 𝔇 s i) z = dbarDatum z := by
  intro s
  refine ⟨𝔇.dbarDatum s, 𝔇.contDiff_dbarDatum s, ?_⟩
  intro i z hz
  have hzΩ : z ∈ 𝔇.Ω i := hz.1.2
  have hzcoreimg : z ∈ (𝔇.φ '' interior 𝔇.core) := hz.2
  rcases hzΩ with ⟨x₁, hxU, rfl⟩
  rcases hzcoreimg with ⟨x₂, hxcore, hφ⟩
  have hsrc₁ : x₁ ∈ (𝔇.φ).source := 𝔇.subset_source i hxU
  have hxunion : x₂ ∈ ⋃ i, (𝔇.U i : Set X) := 𝔇.core_subset (interior_subset hxcore)
  rcases Set.mem_iUnion.mp hxunion with ⟨j, hxj⟩
  have hsrc₂ : x₂ ∈ (𝔇.φ).source := 𝔇.subset_source j hxj
  have hxEq : x₁ = x₂ := by
    apply (𝔇.φ).injOn hsrc₁ hsrc₂
    simpa using hφ.symm
  subst hxEq
  exact 𝔇.dbarDatum_agrees_on_interiorCore s i hxU hxcore

/-- The consumer-side core-restricted chart-differentiable corrector bridge.  This is the downstream
hook for the new interior-core glued datum, and it keeps the sound branch visible without pretending
to discharge the full `HasChartAnalyticCorrectors` predicate. -/
def HasChartDifferentiableCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ H : 𝔇.toFiniteFamily.ι → X → ℂ,
      (∀ i, ∀ y : X, y ∈ 𝔇.toFiniteFamily.U i → y ∈ interior 𝔇.core →
        DifferentiableAt ℂ (fun z => H i ((chartAt (H := ℂ) y).symm z)) ((chartAt (H := ℂ) y) y)) ∧
      ∀ i j, ∀ x : X, x ∈ 𝔇.toFiniteFamily.U i → x ∈ 𝔇.toFiniteFamily.U j → x ∈ interior 𝔇.core →
        (fun z => H j z - H i z) =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j)

theorem hasChartDifferentiableCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) :
    HasChartDifferentiableCorrectorsOnInteriorCore 𝔇 := by
  intro s
  obtain ⟨dbarDatum, hdatum, hagree⟩ := hasGluedDbarDatumOnInteriorCore 𝔇 s
  obtain ⟨u, hu_smooth, hu_dbar⟩ :=
    DbarDiskCohomology.dbar_solvable_ball hdatum 𝔇.ballCenter 𝔇.radius_pos
  set ηhat : 𝔇.toFiniteFamily.ι → ℂ → ℂ := fun i => chartPrim 𝔇 s i - u with hηhatdef
  have hηdiff : ∀ i, ∀ y : X, y ∈ 𝔇.toFiniteFamily.U i → y ∈ interior 𝔇.core →
      DifferentiableAt ℂ (fun z => ηhat i (𝔇.φ ((chartAt (H := ℂ) y).symm z)))
        ((chartAt (H := ℂ) y) y) := by
    intro i y hyU hycore
    have hz : (𝔇.φ) y ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core) := by
      refine ⟨⟨𝔇.mem_ball hyU, 𝔇.mem_Ω hyU⟩, ?_⟩
      exact ⟨y, hycore, rfl⟩
    have hηcd : DifferentiableAt ℝ (ηhat i) (𝔇.φ y) := by
      have hĥ_cd : ContDiffAt ℝ (⊤ : ℕ∞) (chartPrim 𝔇 s i) (𝔇.φ y) := by
        simpa [chartPrim] using contDiffAt_coverPrim_chart 𝔇 s i hyU
      rw [hηhatdef]
      exact (hĥ_cd.differentiableAt (by norm_num)).sub
        (hu_smooth.differentiable (by norm_num) (𝔇.φ y))
    have hdb_eta : DbarDisk.dbar (ηhat i) (𝔇.φ y) = 0 := by
      have hsub0 : DbarDisk.dbar (fun w => chartPrim 𝔇 s i w - u w) (𝔇.φ y)
          = DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ y) - DbarDisk.dbar u (𝔇.φ y) := by
        have hprim_diff : DifferentiableAt ℝ (chartPrim 𝔇 s i) (𝔇.φ y) := by
          simpa [chartPrim] using (contDiffAt_coverPrim_chart 𝔇 s i hyU).differentiableAt
        have hu_diff : DifferentiableAt ℝ u (𝔇.φ y) :=
          hu_smooth.differentiable (by norm_num) (𝔇.φ y)
        exact dbarFun_sub hprim_diff hu_diff
      have hsub : DbarDisk.dbar (ηhat i) (𝔇.φ y)
          = DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ y) - DbarDisk.dbar u (𝔇.φ y) := by
        simpa [hηhatdef] using hsub0
      rcases hz with ⟨hzballΩ, hzimg⟩
      rcases hzballΩ with ⟨hzball, hzΩ⟩
      rw [hsub, hu_dbar (𝔇.φ y) hzball, hagree i (𝔇.φ y) ⟨⟨hzball, hzΩ⟩, hzimg⟩]; ring
    have hηc : DifferentiableAt ℂ (ηhat i) (𝔇.φ y) :=
      differentiableAt_of_dbar_eq_zero_local hηcd hdb_eta
    have htrans : DifferentiableAt ℂ (fun z => (𝔇.φ) ((chartAt (H := ℂ) y).symm z))
        ((chartAt (H := ℂ) y) y) :=
      (transition_analyticAt (y := 𝔇.center) (z := y) (𝔇.subset_source i hyU)).differentiableAt
    have hsymm : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y := by
      simp
    have hηc' : DifferentiableAt ℂ (ηhat i) ((𝔇.φ) ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y))) := by
      simpa [hsymm] using hηc
    simpa [ηhat, Function.comp_assoc] using hηc'.comp ((chartAt (H := ℂ) y) y) htrans
  refine ⟨fun i => ηhat i ∘ 𝔇.φ, hηdiff, ?_⟩
  intro i j x hxUi hxUj hxcore
  have hopen : IsOpen (((𝔇.toFiniteFamily.U i : Set X) ∩ (𝔇.toFiniteFamily.U j : Set X) ∩ interior 𝔇.core) : Set X) := by
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      ((𝔇.toFiniteFamily.U i).isOpen.inter ((𝔇.toFiniteFamily.U j).isOpen.inter isOpen_interior))
  have hUij : ∀ᶠ z in 𝓝[≠] x,
      z ∈ ((𝔇.toFiniteFamily.U i : Set X) ∩ (𝔇.toFiniteFamily.U j : Set X) ∩ interior 𝔇.core) := by
    exact eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds ⟨⟨hxUi, hxUj⟩, hxcore⟩)
  filter_upwards [hUij] with z hz
  rcases hz with ⟨hzIJ, hzcore⟩
  rcases hzIJ with ⟨hzUi, hzUj⟩
  show (ηhat j ∘ 𝔇.φ) z - (ηhat i ∘ 𝔇.φ) z = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) z
  have hzsrc : z ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hzUi
  have hsymm_eq : (𝔇.φ).symm (𝔇.φ z) = z := (𝔇.φ).left_inv hzsrc
  simp only [hηhatdef, Function.comp_apply, Pi.sub_apply, chartPrim, hsymm_eq]
  have hcd := coverPrim_diff 𝔇 s i j ⟨hzUi, hzUj⟩
  linear_combination hcd

/-- The core-restricted chart-analytic correctors, on the actual open locus controlled by the
current construction. -/
def HasChartAnalyticCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ H : 𝔇.toFiniteFamily.ι → X → ℂ,
      (∀ i, ∀ y : X, y ∈ 𝔇.toFiniteFamily.U i → y ∈ interior 𝔇.core →
        AnalyticAt ℂ (H i ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) ∧
      ∀ i j, ∀ x : X, x ∈ 𝔇.toFiniteFamily.U i → x ∈ 𝔇.toFiniteFamily.U j → x ∈ interior 𝔇.core →
        (fun z => H j z - H i z) =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j)

/-- The interior-core differentiable bridge upgrades to an interior-core analytic bridge on the
open locus where the construction actually proves differentiability. -/
theorem hasChartAnalyticCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) :
    HasChartAnalyticCorrectorsOnInteriorCore 𝔇 := by
  intro s
  obtain ⟨dbarDatum, hdatum, hagree⟩ := hasGluedDbarDatumOnInteriorCore 𝔇 s
  obtain ⟨u, hu_smooth, hu_dbar⟩ :=
    DbarDiskCohomology.dbar_solvable_ball hdatum 𝔇.ballCenter 𝔇.radius_pos
  set ηhat : 𝔇.toFiniteFamily.ι → ℂ → ℂ := fun i => chartPrim 𝔇 s i - u with hηhatdef
  have hcore_source : interior 𝔇.core ⊆ (𝔇.φ).source := by
    intro x hx
    have hxunion : x ∈ ⋃ i, (𝔇.U i : Set X) := 𝔇.core_subset (interior_subset hx)
    rcases Set.mem_iUnion.mp hxunion with ⟨j, hxj⟩
    exact 𝔇.subset_source j hxj
  have hcore_img_open : IsOpen (𝔇.φ '' interior 𝔇.core) :=
    (𝔇.φ).isOpen_image_of_subset_source isOpen_interior hcore_source
  have hηhol : ∀ i, DifferentiableOn ℂ (ηhat i)
      (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core)) := by
    intro i
    have hSopen : IsOpen (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core)) :=
      (Metric.isOpen_ball.inter (isOpen_Ω 𝔇 i)).inter hcore_img_open
    have hηR : DifferentiableOn ℝ (ηhat i)
        (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core)) := by
      intro z hz
      rcases hz with ⟨hzballΩ, hzimg⟩
      rcases hzballΩ with ⟨hzball, hzΩ⟩
      rcases hzimg with ⟨x, hxcore, rfl⟩
      rcases hzΩ with ⟨xU, hxU, hφ⟩
      have hηcd : DifferentiableAt ℝ (ηhat i) (𝔇.φ x) := by
        have hĥ_cd : ContDiffAt ℝ (⊤ : ℕ∞) (chartPrim 𝔇 s i) (𝔇.φ x) := by
          rw [← hφ]
          simpa [chartPrim] using contDiffAt_coverPrim_chart 𝔇 s i hxU
        rw [hηhatdef]
        exact (hĥ_cd.differentiableAt (by norm_num)).sub
          (hu_smooth.differentiable (by norm_num) (𝔇.φ x))
      exact hηcd.differentiableWithinAt
    have hdb_eta : ∀ z ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core),
        DbarDisk.dbar (ηhat i) z = 0 := by
      intro z hz
      rcases hz with ⟨hzballΩ, hzimg⟩
      rcases hzballΩ with ⟨hzball, hzΩ⟩
      rcases hzimg with ⟨x, hxcore, rfl⟩
      rcases hzΩ with ⟨xU, hxU, hφ⟩
      have hsub0 : DbarDisk.dbar (fun w => chartPrim 𝔇 s i w - u w) (𝔇.φ x)
          = DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ x) - DbarDisk.dbar u (𝔇.φ x) := by
        have hprim_diff : DifferentiableAt ℝ (chartPrim 𝔇 s i) (𝔇.φ x) := by
          rw [← hφ]
          simpa [chartPrim] using (contDiffAt_coverPrim_chart 𝔇 s i hxU).differentiableAt
        have hu_diff : DifferentiableAt ℝ u (𝔇.φ x) :=
          hu_smooth.differentiable (by norm_num) (𝔇.φ x)
        exact dbarFun_sub hprim_diff hu_diff
      have hsub : DbarDisk.dbar (ηhat i) (𝔇.φ x)
          = DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ x) - DbarDisk.dbar u (𝔇.φ x) := by
        simpa [hηhatdef] using hsub0
      have hzΩx : 𝔇.φ x ∈ 𝔇.Ω i := by
        simpa [hφ] using 𝔇.mem_Ω hxU
      rw [hsub, hu_dbar (𝔇.φ x) hzball,
        hagree i (𝔇.φ x) ⟨⟨hzball, hzΩx⟩, ⟨x, hxcore, rfl⟩⟩]; ring
    exact differentiableOn_complex_of_dbar_eq_zero_local hSopen hηR hdb_eta
  refine ⟨fun i => ηhat i ∘ 𝔇.φ, ?_, ?_⟩
  · intro i y hyU hycore
    have hopen : IsOpen (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core)) :=
      (Metric.isOpen_ball.inter (isOpen_Ω 𝔇 i)).inter hcore_img_open
    have hzopen : 𝔇.φ y ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core) := by
      refine ⟨⟨𝔇.mem_ball hyU, 𝔇.mem_Ω hyU⟩, ?_⟩
      exact ⟨y, hycore, rfl⟩
    have hηana : AnalyticAt ℂ (ηhat i) (𝔇.φ y) :=
      (hηhol i).analyticOnNhd hopen (𝔇.φ y) hzopen
    have hηana' : AnalyticAt ℂ (ηhat i)
        ((𝔇.φ) ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y))) := by
      simpa using hηana
    have htrans : AnalyticAt ℂ (fun z => (𝔇.φ) ((chartAt (H := ℂ) y).symm z))
        ((chartAt (H := ℂ) y) y) :=
      (transition_analyticAt (y := 𝔇.center) (z := y) (𝔇.subset_source i hyU))
    have hcomp : AnalyticAt ℂ (fun z => ηhat i ((𝔇.φ) ((chartAt (H := ℂ) y).symm z)))
        ((chartAt (H := ℂ) y) y) := by
      simpa [Function.comp_assoc] using
        (AnalyticAt.comp (g := ηhat i)
          (f := fun z => (𝔇.φ) ((chartAt (H := ℂ) y).symm z))
          (x := (chartAt (H := ℂ) y) y) hηana' htrans)
    simpa [Function.comp_assoc, hηhatdef] using hcomp
  · intro i j x hxUi hxUj hxcore
    have hopen : IsOpen (((𝔇.toFiniteFamily.U i : Set X) ∩ (𝔇.toFiniteFamily.U j : Set X) ∩ interior 𝔇.core) : Set X) := by
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
        ((𝔇.toFiniteFamily.U i).isOpen.inter ((𝔇.toFiniteFamily.U j).isOpen.inter isOpen_interior))
    have hUij : ∀ᶠ z in 𝓝[≠] x,
        z ∈ ((𝔇.toFiniteFamily.U i : Set X) ∩ (𝔇.toFiniteFamily.U j : Set X) ∩ interior 𝔇.core) := by
      exact eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds ⟨⟨hxUi, hxUj⟩, hxcore⟩)
    filter_upwards [hUij] with z hz
    rcases hz with ⟨hzIJ, hzcore⟩
    rcases hzIJ with ⟨hzUi, hzUj⟩
    show (ηhat j ∘ 𝔇.φ) z - (ηhat i ∘ 𝔇.φ) z = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) z
    have hzsrc : z ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hzUi
    have hsymm_eq : (𝔇.φ).symm (𝔇.φ z) = z := (𝔇.φ).left_inv hzsrc
    simp only [hηhatdef, Function.comp_apply, Pi.sub_apply, chartPrim, hsymm_eq]
    have hcd := coverPrim_diff 𝔇 s i j ⟨hzUi, hzUj⟩
    linear_combination hcd

/-- Core-restricted holomorphic correctors on the open locus where the construction is actually
available.  This is the holomorphic analogue of `HasChartAnalyticCorrectorsOnInteriorCore`, and it is
the honest bridge from the interior-core analytic output to the `OmegaD`-valued language used by the
germ descent side. -/
noncomputable def interiorCoreOpen (𝔇 : SharedChartCover X) : Opens X :=
  ⟨interior 𝔇.core, isOpen_interior⟩

noncomputable def interiorCoreU (𝔇 : SharedChartCover X) (i : 𝔇.toFiniteFamily.ι) : Opens X :=
  (𝔇.toFiniteFamily.U i) ⊓ interiorCoreOpen 𝔇

def HasHoloCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ η : Π i, interiorCoreU 𝔇 i → ℂ,
      (∀ i, η i ∈ OmegaD (0 : Divisor X) (interiorCoreU 𝔇 i)) ∧
      ∀ i j, ∀ x : X, x ∈ 𝔇.toFiniteFamily.U i → x ∈ 𝔇.toFiniteFamily.U j → x ∈ interior 𝔇.core →
        (fun z => Gext (η j) z - Gext (η i) z) =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j)

/-- The interior-core analytic bridge implies the corresponding interior-core holomorphic bridge. -/
theorem hasHoloCorrectorsOnInteriorCore_of_hasChartAnalyticCorrectorsOnInteriorCore
    (𝔇 : SharedChartCover X) :
    HasChartAnalyticCorrectorsOnInteriorCore 𝔇 →
      HasHoloCorrectorsOnInteriorCore 𝔇 := by
  intro h s
  rcases h s with ⟨H, hana, hsplit⟩
  refine ⟨fun i => H i ∘ (Subtype.val : interiorCoreU 𝔇 i → X), ?_, ?_⟩
  · intro i
    apply omegaD_zero_of_chart_analyticAt
    intro y hy
    exact hana i y hy.1 hy.2
  · intro i j x hxUi hxUj hxcore
    have hGextEq : ∀ (k : 𝔇.toFiniteFamily.ι),
        x ∈ 𝔇.toFiniteFamily.U k →
          Gext (fun y : interiorCoreU 𝔇 k =>
            H k y.1) =ᶠ[𝓝[≠] x] H k := by
      intro k hxk
      have hopen' : IsOpen (interiorCoreU 𝔇 k : Set X) := by
        simpa [interiorCoreU, interiorCoreOpen, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          using ((𝔇.toFiniteFamily.U k).isOpen.inter isOpen_interior)
      have hUk : ∀ᶠ z in 𝓝[≠] x,
          z ∈ (interiorCoreU 𝔇 k : Set X) := by
        exact eventually_nhdsWithin_of_eventually_nhds
          (hopen'.mem_nhds ⟨hxk, hxcore⟩)
      filter_upwards [hUk] with z hz
      simpa [Function.comp_apply] using
        Gext_apply_mem (H k ∘ (Subtype.val : interiorCoreU 𝔇 k → X)) hz
    have hj := hGextEq j hxUj
    have hi := hGextEq i hxUi
    exact (Filter.EventuallyEq.sub hj hi).trans (hsplit i j x hxUi hxUj hxcore)

/-- The interior-core analytic bridge immediately yields the interior-core differentiable bridge. -/
theorem hasChartDifferentiableCorrectorsOnInteriorCore_of_hasChartAnalyticCorrectorsOnInteriorCore
    (𝔇 : SharedChartCover X) :
    HasChartAnalyticCorrectorsOnInteriorCore 𝔇 →
      HasChartDifferentiableCorrectorsOnInteriorCore 𝔇 := by
  intro h s
  rcases h s with ⟨H, hana, hsplit⟩
  refine ⟨H, ?_, hsplit⟩
  intro i y hyU hycore
  exact (hana i y hyU hycore).differentiableAt

end Jacobians.Dolbeault
