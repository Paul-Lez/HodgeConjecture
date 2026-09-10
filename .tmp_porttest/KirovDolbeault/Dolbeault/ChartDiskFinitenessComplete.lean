/-
  Čech `H¹` finiteness on a CHART-DISK cover — the COMPLETE version.

  `ChartDiskFiniteness.lean` proves the analytic heart — the Forster 14.6 cover-level ∂̄-lift
  (`ChartDiskCover.forster146_lift`) — and the relatively-compact covering shrinking + the
  `HolomorphicDiskOverlapData` (`𝔇.overlapData`, with compact `ρ` for free, Montel).  The two pieces
  it does not build are the structural δ-complex `HolomorphicCoboundaries 𝔇.overlapData` and a
  comparison `cechH1 𝔇 0 ≃ₗ supH1`.

  This file builds that δ-complex + comparison, supplying the two pieces for the proven
  reduction `ChartDiskCover.finiteDimensional_cechH1_of_holomorphicModel`:

    * **(A) the δ-complex** `HolomorphicCoboundaries 𝔇.overlapData` (`holomorphicCoboundaries`) —
      mirroring `CechModelHolomorphicDelta.lean` (the MONTEL cover) but for `𝔇.overlapData`, the
      chart-disk ball-overlaps `𝔇.Uov`/`𝔇.Wov`.  ALL STRUCTURAL FIELDS are proven complete
      (`δ0`/`δ1`/`δ1cov`/`hδδ`/`hcomm`).

    * **(B) the comparison** `comparisonMap : cechH1 𝔇 0 →ₗ[ℂ] supH1` — PROVEN SORRY-FREE, AND
      INJECTIVE (`comparisonMap_injective`).  The forward germ→`BddHol` cochain map lands in the
      SHRINKING side `Cshr` (boundedness automatic on the relatively-compact `Wov`), is a cocycle
      (`cechToCshr_mem_Z1shr`), descends (well-definedness `coboundaries_le_ker_cechToSupH1`), and is
      injective by reduction to Forster 12.4 refinement-injectivity
      (`CechRefinementInjective.refinementDescend_unconditional`) along the shrinking cover `(V a)`.

  The `leray` field of `holomorphicCoboundaries` — the genuine analytic content (Forster 14.6) — is
  now PROVEN (§A2-* below), via the global Bott–Tu `(0,1)`-form route (NOT the cross-chart `∂̄g_a`
  gluing the earlier attempts hit): a shrinking cocycle `s : Cshr` is read back to germ sections `σ`
  (`shrinkGerm`); the global smooth form `ω̂ := ∑_{a,c} (ρ_a·holoFn σ_{ac})·∂̄ρ_c` (`glueForm`, shrinking
  PoU) is built directly; the PROVEN per-disk solve `dolbeaultToCechCocycle ω̂` gives a holomorphic
  cover cocycle on the FULL overlaps (`coverCochain`); the corrector `η_a := diskVal a ω̂ − G_a` is
  holomorphic (`etaCochain`); and `s = δ⁰η + ρx` holds (`leray_identity`).  The whole file — including
  `holomorphicCoboundaries` and `finiteDimensional_cechH1_chartDisk_complete` — is now COMPLETE
  (axioms: `propext, Classical.choice, Quot.sound`).

  Conventions follow `ChartDiskFiniteness.lean` / `CechModelHolomorphicDelta.lean`.  The lift reuses the
  proven Dolbeault-comparison machinery (`diskVal`/`planarPrimitive`/`dolbeaultToCechCocycle`,
  `DolbeaultComparisonProof`/`Inverse`/`Equiv`) and the shrinking-level PoU `shrinkPoU` (`ChartDiskLeray`).
-/
import KirovDolbeault.Dolbeault.ChartDiskFiniteness
import KirovDolbeault.Dolbeault.ChartDiskLeray
import KirovDolbeault.Dolbeault.CechModelHolomorphicDelta
import KirovDolbeault.Dolbeault.CechRefinementInjective

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Metric Complex Filter ContinuousLinearMap

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-- `𝔇.overlapData.Wov = 𝔇.Wov` (rfl) — exposed as a simp lemma so the `rhoRaw`-introduced
`overlapData.Wov` terms normalize to the `𝔇.Wov` used by the geometric witnesses. -/
@[simp] theorem overlapData_Wov_eq : 𝔇.overlapData.Wov = 𝔇.Wov := rfl

/-- `𝔇.overlapData.Uov = 𝔇.Uov` (rfl). -/
@[simp] theorem overlapData_Uov_eq : 𝔇.overlapData.Uov = 𝔇.Uov := rfl

/-! ## §A — The cross-chart Čech δ-complex on `𝔇.overlapData`

We build, for the chart-disk model `𝔇.overlapData` (whose `Uov`/`Wov` are the chart-`a` images of the
ball overlap `U a ∩ U b` resp. the shrinking overlap `V a ∩ V b`), the same data that
`CechModelHolomorphicDelta` builds for the Montel model: the cross-chart `δ⁰`/`δ¹`, the cover-side
`δ¹cov`, the cocycle identity `δ²=0`, and the commuting `hcomm` square.  The transport in each
differential is the analytic chart transition `𝔇.coverTransition a b`, analytic on the open `𝔇.Wov`
and mapping it into the `b`-side cover-open.

The geometry differs from Montel only in the concrete sets; the proofs are structurally identical, so
we re-derive the `coverTransition`/maps-to witnesses against `𝔇.Wov`/`𝔇.Uov`. -/

/-- The cover transition `τ_{ab}` is analytic on the OPEN shrinking overlap `𝔇.Wov (a,b)` (chart-`a`
image of `V a ∩ V b`): at each point it is analytic by `transition_analyticAt_of_mem`, both centres'
chart sources containing the overlap point (`V a, V b ⊆ closure ⊆ U ⊆ source`). -/
theorem analyticOn_coverTransition_Wov (a b : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.Wov (a, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa)))
    (𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)))

/-- The cover transition `τ_{ab}` maps the OPEN shrinking overlap `𝔇.Wov (a,b)` (chart-`a`
coordinates) into the `b`-side DIAGONAL shrinking `𝔇.Wov (b,b)` (chart-`b` image of `V b`).  A point
`φ_a x` with `x ∈ V a ∩ V b` maps to `φ_b x` with `x ∈ V b`, so `φ_b x ∈ φ_b '' (V b) = Wov (b,b)`.
(Using the diagonal SHRINKING `Wov (b,b)` rather than the full `Uov (b,b)` makes the 0-cochain space
`C0Holo` a SHRINKING space — bounded on a relatively-compact image — so the comparison descent of a
germ coboundary to a `δ⁰`-image is provable; cf. the Montel model's full-image `C0`.) -/
theorem mapsTo_coverTransition_Wov (a b : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.Wov (a, b)) (𝔇.Wov (b, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  refine ⟨x, ⟨hxb, hxb⟩, ?_⟩
  rw [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src]

/-- The shrinking overlap `𝔇.Wov (a,b)` lies in the `a`-side DIAGONAL shrinking `𝔇.Wov (a,a)` (chart-`a`
image of `V a ∩ V b ⊆ V a`), so the diagonal `a`-component restricts directly. -/
theorem Wov_subset_Wov_diag_fst (a b : 𝔇.ι) :
    𝔇.Wov (a, b) ⊆ 𝔇.Wov (a, a) :=
  Set.image_mono (fun _ hx => ⟨hx.1, hx.1⟩)

/-- **Sup-norm 0-cochains, holomorphic side** `C0Holo` — bounded-holomorphic on each DIAGONAL shrinking
`Wov (a,a) = chartAt (center a) '' (V a)`.  The shrinking (relatively-compact) image makes a germ
section's analytic representative bounded there (the descent of coboundaries needs this). -/
abbrev C0Holo (𝔇 : ChartDiskCover X) : Type _ :=
  ∀ a : 𝔇.ι, BddHol (𝔇.Wov (a, a))

noncomputable instance : NormedAddCommGroup 𝔇.C0Holo := inferInstance
noncomputable instance : NormedSpace ℂ 𝔇.C0Holo := inferInstance

noncomputable instance : CompleteSpace 𝔇.C0Holo := by
  haveI : ∀ a : 𝔇.ι, CompleteSpace (BddHol (𝔇.Wov (a, a))) := fun a =>
    BddHol.completeSpace (𝔇.isOpen_Wov (a, a))
  infer_instance

/-- **The cross-chart Čech `δ⁰`** of the chart-disk model: `c.Cshr`-valued from `C0Holo`.
Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f_b to chart-a) − (restriction of f_a)`   on the OPEN `Wov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through the holomorphic transition `τ_{ab}`.
Both pieces stay `BddHol` on the open `Wov`. -/
noncomputable def delta0Model :
    𝔇.C0Holo →L[ℂ] 𝔇.overlapData.Cshr :=
  ContinuousLinearMap.pi fun p =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_Wov p.1 p.2)
        (𝔇.mapsTo_coverTransition_Wov p.1 p.2)).comp (proj p.2)
      - (BddHol.restrictOpenCLM (𝔇.Wov_subset_Wov_diag_fst p.1 p.2)).comp (proj p.1)

theorem delta0Model_apply (f : 𝔇.C0Holo)
    (p : 𝔇.overlapData.J) :
    𝔇.delta0Model f p
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_Wov p.1 p.2)
          (𝔇.mapsTo_coverTransition_Wov p.1 p.2) (f p.2)
        - BddHol.restrictOpenCLM (𝔇.Wov_subset_Wov_diag_fst p.1 p.2) (f p.1) := rfl

theorem delta0Model_apply_apply (f : 𝔇.C0Holo)
    (p : 𝔇.overlapData.J) {z : ℂ} (hz : z ∈ 𝔇.Wov p) :
    (𝔇.delta0Model f p).toFun z
      = (f p.2).toFun (𝔇.coverTransition p.1 p.2 z) - (f p.1).toFun z := by
  obtain ⟨a, b⟩ := p
  rw [delta0Model_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The shrinking-side 2-cochains on OPEN triples `WovTriple`, and the `δ¹` -/

/-- Open chart-`a` image of the triple shrinking overlap `V a ∩ V b ∩ V c` — the shrinking-side
2-cochain domain. -/
noncomputable def WovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : Set ℂ :=
  (chartAt (H := ℂ) (𝔇.center t.1)) ''
    (𝔇.shrinkSet t.1 ∩ 𝔇.shrinkSet t.2.1 ∩ 𝔇.shrinkSet t.2.2)

theorem isOpen_WovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : IsOpen (𝔇.WovTriple t) := by
  refine (chartAt (H := ℂ) (𝔇.center t.1)).isOpen_image_of_subset_source
    (((𝔇.shrinkSet_isOpen t.1).inter (𝔇.shrinkSet_isOpen t.2.1)).inter
      (𝔇.shrinkSet_isOpen t.2.2)) ?_
  refine ((Set.inter_subset_left.trans Set.inter_subset_left).trans
    ((subset_closure).trans (𝔇.closure_shrinkSet_subset_U t.1))).trans ?_
  exact 𝔇.U_subset_chartAt_source t.1

/-- **Sup-norm 2-cochains, holomorphic shrinking side** `C2Holo` — bounded-holomorphic on each open
triple `WovTriple t`. -/
abbrev C2Holo (𝔇 : ChartDiskCover X) : Type _ :=
  ∀ t : 𝔇.ι × 𝔇.ι × 𝔇.ι, BddHol (𝔇.WovTriple t)

noncomputable instance : NormedAddCommGroup 𝔇.C2Holo := inferInstance
noncomputable instance : NormedSpace ℂ 𝔇.C2Holo := inferInstance

noncomputable instance : CompleteSpace 𝔇.C2Holo := by
  haveI : ∀ t, CompleteSpace (BddHol (𝔇.WovTriple t)) := fun t =>
    BddHol.completeSpace (𝔇.isOpen_WovTriple t)
  infer_instance

theorem analyticOn_coverTransition_WovTriple (a b c : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.WovTriple (a, b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa)))
    (𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)))

/-- `τ_{ab}` maps the OPEN triple `WovTriple (a,b,c)` (chart-`a` coords) into the shrinking
`Wov (b,c)` (chart-`b` image of `V b ∩ V c`).  A point `φ_a x` with `x ∈ V a ∩ V b ∩ V c` maps to
`φ_b x` with `x ∈ V b ∩ V c`. -/
theorem mapsTo_coverTransition_WovTriple_shrink (a b c : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.WovTriple (a, b, c)) (𝔇.Wov (b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, hxc⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  exact ⟨x, ⟨hxb, hxc⟩, by
    rw [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src]⟩

theorem WovTriple_subset_Wov_fst_snd (a b c : 𝔇.ι) :
    𝔇.WovTriple (a, b, c) ⊆ 𝔇.Wov (a, b) :=
  Set.image_mono Set.inter_subset_left

theorem WovTriple_subset_Wov_fst_trd (a b c : 𝔇.ι) :
    𝔇.WovTriple (a, b, c) ⊆ 𝔇.Wov (a, c) :=
  Set.image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

/-- **The cross-chart Čech `δ¹` on the shrinking side** `c.Cshr →L[ℂ] C2Holo`.
Componentwise on the triple `(a,b,c)`, `(δ¹s)_{abc} = (s_{bc} ∘ τ_{ab}) − s_{ac} + s_{ab}` on the
OPEN `WovTriple (a,b,c)`. -/
noncomputable def delta1Model :
    𝔇.overlapData.Cshr →L[ℂ] 𝔇.C2Holo :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
        (𝔇.mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

theorem delta1Model_apply (s : 𝔇.overlapData.Cshr) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.delta1Model s t
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
          (𝔇.mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2) (s (t.2.1, t.2.2))
        - BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2) (s (t.1, t.2.2))
        + BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)
            (s (t.1, t.2.1)) := rfl

theorem delta1Model_apply_apply (s : 𝔇.overlapData.Cshr) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.WovTriple t) :
    (𝔇.delta1Model s t).toFun z
      = (s (t.2.1, t.2.2)).toFun (𝔇.coverTransition t.1 t.2.1 z)
        - (s (t.1, t.2.2)).toFun z + (s (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1Model_apply, BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The cover-side 2-cochains, `δ¹cov`, and the cocycle identity `δ²=0` -/

/-- Open chart-`a` image of the triple cover overlap `U a ∩ U b ∩ U c` — the cover-side 2-cochain
domain. -/
noncomputable def UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : Set ℂ :=
  (chartAt (H := ℂ) (𝔇.center t.1)) ''
    ((𝔇.U t.1 ⊓ 𝔇.U t.2.1 ⊓ 𝔇.U t.2.2 : Opens X) : Set X)

theorem isOpen_UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : IsOpen (𝔇.UovTriple t) := by
  refine (chartAt (H := ℂ) (𝔇.center t.1)).isOpen_image_of_subset_source
    (𝔇.U t.1 ⊓ 𝔇.U t.2.1 ⊓ 𝔇.U t.2.2 : Opens X).isOpen ?_
  refine (Set.Subset.trans ?_ (𝔇.U_subset_chartAt_source t.1))
  exact (Set.inter_subset_left).trans (Set.inter_subset_left)

abbrev C2Cov (𝔇 : ChartDiskCover X) : Type _ :=
  ∀ t : 𝔇.ι × 𝔇.ι × 𝔇.ι, BddHol (𝔇.UovTriple t)

noncomputable instance : NormedAddCommGroup 𝔇.C2Cov := inferInstance
noncomputable instance : NormedSpace ℂ 𝔇.C2Cov := inferInstance

theorem analyticOn_coverTransition_UovTriple (a b c : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.UovTriple (a, b, c)) := by
  rintro w ⟨x, hx, rfl⟩
  apply AnalyticAt.analyticWithinAt
  have hxa : x ∈ ((𝔇.U a : Opens X) : Set X) := hx.1.1
  have hxb : x ∈ ((𝔇.U b : Opens X) : Set X) := hx.1.2
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a hxa) (𝔇.U_subset_chartAt_source b hxb)

/-- `τ_{ab}` maps the cover triple `UovTriple (a,b,c)` into the cover overlap `Uov (b,c)`. -/
theorem mapsTo_coverTransition_UovTriple (a b c : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.UovTriple (a, b, c)) (𝔇.Uov (b, c)) := by
  rintro w ⟨x, hx, rfl⟩
  have hxa : x ∈ ((𝔇.U a : Opens X) : Set X) := hx.1.1
  have hxb : x ∈ ((𝔇.U b : Opens X) : Set X) := hx.1.2
  have hxc : x ∈ ((𝔇.U c : Opens X) : Set X) := hx.2
  refine ⟨x, ⟨hxb, hxc⟩, ?_⟩
  rw [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv (𝔇.U_subset_chartAt_source a hxa)]

theorem UovTriple_subset_Uov_fst_snd (a b c : 𝔇.ι) :
    𝔇.UovTriple (a, b, c) ⊆ 𝔇.Uov (a, b) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' _
  exact Set.image_mono (fun x hx => ⟨hx.1.1, hx.1.2⟩)

theorem UovTriple_subset_Uov_fst_trd (a b c : 𝔇.ι) :
    𝔇.UovTriple (a, b, c) ⊆ 𝔇.Uov (a, c) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' _
  exact Set.image_mono (fun x hx => ⟨hx.1.1, hx.2⟩)

/-- **The cross-chart Čech `δ¹` on the COVER side** `c.Ccov →L[ℂ] C2Cov`.  Same shape as the shrinking
`δ¹`, on the full cover overlaps. -/
noncomputable def delta1CovModel :
    𝔇.overlapData.Ccov →L[ℂ] 𝔇.C2Cov :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_UovTriple t.1 t.2.1 t.2.2)
        (𝔇.mapsTo_coverTransition_UovTriple t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

theorem delta1CovModel_apply (s : 𝔇.overlapData.Ccov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.delta1CovModel s t
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_UovTriple t.1 t.2.1 t.2.2)
          (𝔇.mapsTo_coverTransition_UovTriple t.1 t.2.1 t.2.2) (s (t.2.1, t.2.2))
        - BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_trd t.1 t.2.1 t.2.2) (s (t.1, t.2.2))
        + BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_snd t.1 t.2.1 t.2.2)
            (s (t.1, t.2.1)) := rfl

theorem delta1CovModel_apply_apply (s : 𝔇.overlapData.Ccov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.UovTriple t) :
    (𝔇.delta1CovModel s t).toFun z
      = (s (t.2.1, t.2.2)).toFun (𝔇.coverTransition t.1 t.2.1 z)
        - (s (t.1, t.2.2)).toFun z + (s (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1CovModel_apply, BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-- **The chart-transition cocycle identity** on the OPEN triple `WovTriple`: `τ_{bc}(τ_{ab} z) =
τ_{ac} z` for `z ∈ WovTriple (a,b,c)`. -/
theorem coverTransition_cocycle_Wov (a b c : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.WovTriple (a, b, c)) :
    𝔇.coverTransition b c (𝔇.coverTransition a b z) = 𝔇.coverTransition a c z := by
  obtain ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩ := hz
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  have hxb_src : x ∈ (chartAt (H := ℂ) (𝔇.center b)).source :=
    𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb))
  simp only [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src,
    (chartAt (H := ℂ) (𝔇.center b)).left_inv hxb_src]

/-- **`δ¹ ∘ δ⁰ = 0` (the shrinking-side Čech `hδδ`).** -/
theorem delta1_comp_delta0 :
    (𝔇.delta1Model).comp 𝔇.delta0Model = 0 := by
  ext f t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.WovTriple t
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl]
    rw [delta1Model_apply_apply _ _ _ hz]
    obtain ⟨a, b, c⟩ := t
    rw [delta0Model_apply_apply _ _ _ (𝔇.mapsTo_coverTransition_WovTriple_shrink a b c hz),
      delta0Model_apply_apply _ _ _ (𝔇.WovTriple_subset_Wov_fst_trd a b c hz),
      delta0Model_apply_apply _ _ _ (𝔇.WovTriple_subset_Wov_fst_snd a b c hz)]
    rw [𝔇.coverTransition_cocycle_Wov a b c hz]
    ring
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl,
      (𝔇.delta1Model (𝔇.delta0Model f) t).zero_off z hz]

/-! ### The 2-cochain restriction `ρ²` cover → shrinking, and the `hcomm` square -/

theorem WovTriple_subset_UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.WovTriple t ⊆ 𝔇.UovTriple t := by
  show (chartAt (H := ℂ) (𝔇.center t.1)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center t.1)) '' _
  refine Set.image_mono (fun x hx => ?_)
  exact ⟨⟨𝔇.closure_shrinkSet_subset_U t.1 (subset_closure hx.1.1),
    𝔇.closure_shrinkSet_subset_U t.2.1 (subset_closure hx.1.2)⟩,
    𝔇.closure_shrinkSet_subset_U t.2.2 (subset_closure hx.2)⟩

/-- **The 2-cochain restriction `ρ² : C2Cov →L C2Holo`** (cover → shrinking). -/
noncomputable def rho2Model : 𝔇.C2Cov →L[ℂ] 𝔇.C2Holo :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_UovTriple t)).comp (proj t)

@[simp] theorem rho2Model_apply (g : 𝔇.C2Cov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.rho2Model g t = BddHol.restrictOpenCLM (𝔇.WovTriple_subset_UovTriple t) (g t) := by
  simp only [rho2Model, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **The commuting square** `δ¹_shr ∘ ρ = ρ² ∘ δ¹_cov`. -/
theorem delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov :
    (𝔇.delta1Model).comp 𝔇.overlapData.rhoRaw
      = (𝔇.rho2Model).comp 𝔇.delta1CovModel := by
  ext x t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.WovTriple t
  · rw [delta1Model_apply_apply _ _ _ hz]
    obtain ⟨a, b, c⟩ := t
    simp only [HolomorphicDiskOverlapData.rhoRaw_apply, overlapData_Wov_eq, overlapData_Uov_eq]
    rw [BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.mapsTo_coverTransition_WovTriple_shrink a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.WovTriple_subset_Wov_fst_trd a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.WovTriple_subset_Wov_fst_snd a b c hz)]
    rw [rho2Model_apply, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]
    rw [𝔇.delta1CovModel_apply_apply _ _ (𝔇.WovTriple_subset_UovTriple (a, b, c) hz)]
  · rw [(𝔇.delta1Model (𝔇.overlapData.rhoRaw x) t).zero_off z hz,
      (𝔇.rho2Model (𝔇.delta1CovModel x) t).zero_off z hz]

theorem hcomm (x : 𝔇.overlapData.Ccov) (hx : 𝔇.delta1CovModel x = 0) :
    𝔇.delta1Model (𝔇.overlapData.rhoRaw x) = 0 := by
  have h := congrArg (fun T => T x) 𝔇.delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, hx, map_zero]

/-! ## §A2 — The `HolomorphicCoboundaries` δ-data with the `leray` field

We package the δ-complex above into a `HolomorphicCoboundaries 𝔇.overlapData`.  The `C0` 0-cochain
space is `∀ a, BddHol (Uov (a,a))` (bounded-holomorphic on each diagonal cover-open), `C2`/`C2cov`
are the triple-overlap 2-cochains built above, and the δ's are the model differentials.

The `leray` field is the Forster 14.6 cover→shrinking lift; see the (corrected) `leray_diagnosis`.
The genuinely-new foundational input — a SHRINKING-level smooth partition of unity on `𝔇`, summing to
`1` on all of `X` — is built in `ChartDiskLeray.lean` (`ChartDiskCover.shrinkPoU`). -/

/-! ## §A2-pre — The shrinking opens `V_a` (foundational, used by the §A2 `leray` lift below). -/

/-- The shrinking sets `V a := shrinkSet a` as `Opens X`. -/
noncomputable def shrinkOpens (a : 𝔇.ι) : Opens X := ⟨𝔇.shrinkSet a, 𝔇.shrinkSet_isOpen a⟩

@[simp] theorem shrinkOpens_coe (a : 𝔇.ι) : ((𝔇.shrinkOpens a : Opens X) : Set X) = 𝔇.shrinkSet a :=
  rfl

/-- The **shrinking cover** `(V a)` — a `FiniteCover` (covers `X` by `iUnion_shrinkSet_eq_univ`). -/
noncomputable def shrinkCover : FiniteCover X where
  ι := 𝔇.ι
  fintype := inferInstance
  U := 𝔇.shrinkOpens
  covers := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    simpa only [shrinkOpens_coe] using 𝔇.iUnion_shrinkSet_eq_univ

@[simp] theorem shrinkCover_U (a : 𝔇.ι) : 𝔇.shrinkCover.U a = 𝔇.shrinkOpens a := rfl

/-- `V a ⊆ U a` (the shrinking sits in the cover set). -/
theorem shrinkOpens_le_U (a : 𝔇.ι) : 𝔇.shrinkOpens a ≤ 𝔇.U a := by
  intro x hx
  exact 𝔇.closure_shrinkSet_subset_U a (subset_closure hx)

/-- **The refinement** `shrinkCover ⪯ 𝔇` via the identity index map. -/
theorem isRefinement_shrinkCover :
    FiniteCover.IsRefinement 𝔇.shrinkCover 𝔇.toFiniteCover id :=
  fun a => 𝔇.shrinkOpens_le_U a

/-- `V a ⊆ (chartAt (center a)).source`. -/
theorem shrinkOpens_subset_source (a : 𝔇.ι) :
    ((𝔇.shrinkOpens a : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center a)).source :=
  fun _x hx => 𝔇.U_subset_chartAt_source a (𝔇.shrinkOpens_le_U a hx)

/-- `Wov (a,b)` is exactly the chart-`a` image of the open `shrinkOpens a ⊓ shrinkOpens b`. -/
theorem Wov_eq_chartImage_shrinkInter (a b : 𝔇.ι) :
    𝔇.Wov (a, b)
      = (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' (𝔇.shrinkSet a ∩ 𝔇.shrinkSet b) = _
  congr 1

/-- `V_a ∩ V_b ⊆ (chartAt (center a)).source`. -/
theorem shrinkInter_subset_source (a b : 𝔇.ι) :
    ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center a)).source := by
  intro x hx
  exact 𝔇.shrinkOpens_subset_source a hx.1

/-- The `BddHol` component `s_{ab}`, retyped to live on the exact chart image of `shrinkOpens a ⊓
shrinkOpens b` (which is `Wov (a,b)`), ready for `bddHolToOmegaDGerm_zero_image`. -/
noncomputable def shrinkBddHolRetype (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    BddHol ((chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X)) :=
  BddHol.restrictOpenCLM (𝔇.Wov_eq_chartImage_shrinkInter a b).ge (s (a, b))

theorem shrinkBddHolRetype_toFun_of_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {z : ℂ}
    (hz : z ∈ 𝔇.Wov (a, b)) :
    (𝔇.shrinkBddHolRetype s a b).toFun z = (s (a, b)).toFun z := by
  refine BddHol.restrictOpenCLM_toFun_of_mem _ _ ?_
  rw [← 𝔇.Wov_eq_chartImage_shrinkInter a b]; exact hz

/-- **The germ section `σ_{ab}` on `V_a ⊓ V_b`** read back from `s_{ab}` through chart `a`. -/
noncomputable def shrinkGerm (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    ↥(OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b)) :=
  bddHolToOmegaDGerm_zero_image (y := 𝔇.center a) (V := 𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b)
    (𝔇.shrinkInter_subset_source a b) (𝔇.shrinkBddHolRetype s a b)

theorem shrinkGerm_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    (𝔇.shrinkGerm s a b).1 ∈ OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) :=
  (𝔇.shrinkGerm s a b).2

/-- **The value of `holoFn σ_{ab}`** at `y ∈ V_a ∩ V_b` is `s_{ab}.toFun (φ_a y)`.  (Mirror of
`diagPullbackGerm_holoFn`.) -/
theorem shrinkGerm_holoFn (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X)) :
    holoFn (𝔇.shrinkGerm s a b).2 y = (s (a, b)).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) := by
  set g' := 𝔇.shrinkBddHolRetype s a b with hg'
  set F : ↥(𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) → ℂ :=
    fun x => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) x.1) with hF
  have hgerm : toGerm (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) F = (𝔇.shrinkGerm s a b).1 := rfl
  have hmemImg : (chartAt (H := ℂ) (𝔇.center a)) y
      ∈ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) :=
    ⟨y, hy, rfl⟩
  -- `g'.toFun (φ_a y) = s_{ab}.toFun (φ_a y)` (`shrinkBddHolRetype` agrees on `Wov`).
  have hzW : (chartAt (H := ℂ) (𝔇.center a)) y ∈ 𝔇.Wov (a, b) := by
    rw [𝔇.Wov_eq_chartImage_shrinkInter a b]; exact hmemImg
  have hval : g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y)
      = (s (a, b)).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) :=
    𝔇.shrinkBddHolRetype_toFun_of_mem s a b hzW
  -- `Gext F` is continuous at `y` (analytic `g'` ∘ chart), agreeing with `F`-value near `y`.
  have hcont : ContinuousAt (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) y := by
    refine (g'.analyticOn.continuousOn.continuousAt ?_).comp
      ((chartAt (H := ℂ) (𝔇.center a)).continuousAt (𝔇.shrinkInter_subset_source a b hy))
    exact ((chartAt (H := ℂ) (𝔇.center a)).isOpen_image_of_subset_source
      (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b).isOpen (𝔇.shrinkInter_subset_source a b)).mem_nhds hmemImg
  have hev : Gext F =ᶠ[nhds y]
      (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) := by
    filter_upwards [(𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b).isOpen.mem_nhds hy] with z hz
    rw [Gext_apply_mem F hz]
  have htend : Filter.Tendsto (Gext F) (𝓝[≠] y)
      (𝓝 (g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y))) :=
    Filter.Tendsto.congr' (hev.filter_mono nhdsWithin_le_nhds).symm
      ((hcont.tendsto).mono_left nhdsWithin_le_nhds)
  rw [← hval]
  exact holoFn_eq_of_tendsto (𝔇.shrinkGerm s a b).2 F hgerm hy htend

/-- `chart_i y ∈ WovTriple (i,j,k)` for `y ∈ V_i ∩ V_j ∩ V_k`. -/
theorem chart_mem_WovTriple (i j k : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.shrinkOpens i ⊓ 𝔇.shrinkOpens j ⊓ 𝔇.shrinkOpens k : Opens X)) :
    (chartAt (H := ℂ) (𝔇.center i)) y ∈ 𝔇.WovTriple (i, j, k) :=
  ⟨y, ⟨⟨hy.1.1, hy.1.2⟩, hy.2⟩, rfl⟩

/-- For `y ∈ V_i ∩ V_j ⊆ V_i ∩ V_j`, the transition point identity `(chart_j).symm (τ_{ij}(chart_i y))
= ...` collapses: `τ_{ij}(chart_i y) = chart_j y`. -/
theorem coverTransition_chart_shrink (i j : 𝔇.ι) {y : X}
    (hyi : y ∈ (𝔇.shrinkOpens i : Opens X)) (hyj : y ∈ (𝔇.shrinkOpens j : Opens X)) :
    𝔇.coverTransition i j ((chartAt (H := ℂ) (𝔇.center i)) y) = (chartAt (H := ℂ) (𝔇.center j)) y := by
  have hyiU : y ∈ ((𝔇.U i : Opens X) : Set X) := 𝔇.shrinkOpens_le_U i hyi
  have hyjU : y ∈ ((𝔇.U j : Opens X) : Set X) := 𝔇.shrinkOpens_le_U j hyj
  exact 𝔇.coverTransition_apply i j ⟨hyiU, hyjU⟩

/-- **The germ cocycle relation at the `holoFn` value level.**  For a `Cshr` cocycle `s` (i.e.
`δ¹s = 0`) and `y ∈ V_i ∩ V_j ∩ V_k`, `holoFn σ_{ik} y = holoFn σ_{ij} y + holoFn σ_{jk} y`.  Direct
from `delta1Model s = 0` evaluated at `chart_i y ∈ WovTriple (i,j,k)`, via `shrinkGerm_holoFn` and the
transition identity. -/
theorem shrinkGerm_cocycle_add (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0)
    (i j k : 𝔇.ι) {y : X} (hy : y ∈ (𝔇.shrinkOpens i ⊓ 𝔇.shrinkOpens j ⊓ 𝔇.shrinkOpens k : Opens X)) :
    holoFn (𝔇.shrinkGerm s i k).2 y
      = holoFn (𝔇.shrinkGerm s i j).2 y + holoFn (𝔇.shrinkGerm s j k).2 y := by
  have hyi : y ∈ (𝔇.shrinkOpens i : Opens X) := hy.1.1
  have hyj : y ∈ (𝔇.shrinkOpens j : Opens X) := hy.1.2
  have hyk : y ∈ (𝔇.shrinkOpens k : Opens X) := hy.2
  set z := (chartAt (H := ℂ) (𝔇.center i)) y with hz
  have hzW : z ∈ 𝔇.WovTriple (i, j, k) := 𝔇.chart_mem_WovTriple i j k hy
  -- `δ¹s = 0` value at `z`.
  have h0 : (𝔇.delta1Model s (i, j, k)).toFun z = 0 := by rw [hs]; rfl
  rw [𝔇.delta1Model_apply_apply s (i, j, k) hzW] at h0
  -- rewrite `s` components into `holoFn σ` via `shrinkGerm_holoFn` and the transition identity.
  rw [show 𝔇.coverTransition (i, j, k).1 (i, j, k).2.1 z = (chartAt (H := ℂ) (𝔇.center j)) y from
    𝔇.coverTransition_chart_shrink i j hyi hyj] at h0
  rw [← 𝔇.shrinkGerm_holoFn s i k ⟨hyi, hyk⟩,
    ← 𝔇.shrinkGerm_holoFn s i j ⟨hyi, hyj⟩, ← 𝔇.shrinkGerm_holoFn s j k ⟨hyj, hyk⟩] at h0
  linear_combination -h0

/-- `holoFn σ_{ii} y = 0` on `V_i` (diagonal vanishing).  From the cocycle relation with `j = k = i`:
`holoFn σ_{ii} = holoFn σ_{ii} + holoFn σ_{ii}`. -/
theorem shrinkGerm_diag_eq_zero (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0)
    (i : 𝔇.ι) {y : X} (hy : y ∈ (𝔇.shrinkOpens i : Opens X)) :
    holoFn (𝔇.shrinkGerm s i i).2 y = 0 := by
  have h := 𝔇.shrinkGerm_cocycle_add s hs i i i (y := y) ⟨⟨hy, hy⟩, hy⟩
  linear_combination -h

/-! ## §B — The global Bott–Tu `(0,1)`-form `ω̂` from `s`

`ω̂ := ∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`, with `ρ = shrinkPoU` (subordinate to `(V_a)`, sum-to-one
on `X`).  Each summand is a global smooth `(0,1)`-form by the confining 3-case `tsupport` argument
(mirrors `cechTerm` of `DolbeaultComparisonInverse`).  This is the global form whose chart-`a` read on
the FULL ball `U_a` is smooth — the input the per-disk solve consumes. -/

/-- `ρ_a` as a complex `SmoothCFunctions` (`ρ̃_a = ofReal ∘ shrinkPoU a`). -/
noncomputable def shrinkRhoC (a : 𝔇.ι) : SmoothCFunctions X :=
  ofRealCM.comp (𝔇.shrinkPoU a)

/-- `∂̄ρ_a` as a global `(0,1)`-form. -/
noncomputable def shrinkDbarRho (a : 𝔇.ι) : SmoothCOneForms X :=
  dbarL (𝔇.shrinkRhoC a)

theorem shrinkRhoC_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : 𝔇.shrinkRhoC a x = 0 := by
  simp only [shrinkRhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hx]; rfl

theorem shrinkDbarRho_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : (𝔇.shrinkDbarRho a) x = 0 := by
  refine dbarL_eq_zero_of_notMem_tsupport (𝔇.shrinkRhoC a) (fun hc => hx ?_)
  refine closure_mono (fun y hy => ?_) hc
  simp only [Function.mem_support, ne_eq] at hy ⊢
  exact fun h0 => hy (by simp only [shrinkRhoC, ContMDiffMap.comp_apply, ofRealCM, h0]; rfl)

theorem sum_shrinkRhoC (𝔇 : ChartDiskCover X) : ∑ a, 𝔇.shrinkRhoC a = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) = ∑ a, ⇑(𝔇.shrinkRhoC a) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ a, 𝔇.shrinkRhoC a) x = (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) x from rfl, h1,
    Finset.sum_apply, ContMDiffMap.coe_one, Pi.one_apply]
  show ∑ a, ((𝔇.shrinkPoU a x : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum, 𝔇.sum_shrinkPoU_eq_one x, Complex.ofReal_one]

theorem sum_shrinkRhoC_apply (𝔇 : ChartDiskCover X) (x : X) : ∑ a, (𝔇.shrinkRhoC a x) = 1 := by
  have h1 : (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) = ∑ a, ⇑(𝔇.shrinkRhoC a) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  have h2 : (∑ a, 𝔇.shrinkRhoC a) x = ∑ a, (𝔇.shrinkRhoC a x) := by
    rw [show ((∑ a, 𝔇.shrinkRhoC a) x : ℂ) = (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) x from rfl, h1,
      Finset.sum_apply]
  rw [← h2, sum_shrinkRhoC, ContMDiffMap.coe_one, Pi.one_apply]

theorem sum_shrinkDbarRho (𝔇 : ChartDiskCover X) : ∑ a, 𝔇.shrinkDbarRho a = 0 := by
  have h : ∑ a, 𝔇.shrinkDbarRho a = dbarL (∑ a, 𝔇.shrinkRhoC a) := (map_sum dbarL _ _).symm
  rw [h, sum_shrinkRhoC, dbarL_one_eq_zero]

theorem sum_shrinkDbarRho_apply (𝔇 : ChartDiskCover X) (x : X) :
    ∑ a, ((𝔇.shrinkDbarRho a) x) = 0 := by
  have h1 : (⇑(∑ a, 𝔇.shrinkDbarRho a)) = ∑ a, ⇑(𝔇.shrinkDbarRho a) :=
    map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
  have h2 : (∑ a, 𝔇.shrinkDbarRho a) x = ∑ a, ((𝔇.shrinkDbarRho a) x) := by
    rw [show ((∑ a, 𝔇.shrinkDbarRho a) x) = (⇑(∑ a, 𝔇.shrinkDbarRho a)) x from rfl, h1,
      Finset.sum_apply]
  rw [← h2, sum_shrinkDbarRho, ContMDiffSection.coe_zero, Pi.zero_apply]

/-- **The Bott–Tu double-sum term `(ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`** as a global smooth `(0,1)`-form.
Globally smooth by the 3-case `tsupport` argument: on `V_a ∩ V_c` (where `holoFn σ_{ac}` is smooth)
everything is smooth; off `tsupport ρ_a` the factor `ρ_a` vanishes; off `tsupport ρ_c` the factor
`∂̄ρ_c` vanishes. -/
noncomputable def shrinkTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) : SmoothCOneForms X where
  toFun := fun x => (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x)
  contMDiff_toFun := by
    intro x₀
    by_cases hba : x₀ ∈ tsupport (𝔇.shrinkPoU a)
    · by_cases hbc : x₀ ∈ tsupport (𝔇.shrinkPoU c)
      · have hxV : x₀ ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) :=
          ⟨𝔇.shrinkPoU_tsupport_subset a hba, 𝔇.shrinkPoU_tsupport_subset c hbc⟩
        have hmulrho : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
            (fun x => ContinuousLinearMap.mul ℝ ℂ (𝔇.shrinkRhoC a x)) x₀ :=
          ContMDiffAt.clm_apply contMDiffAt_const ((𝔇.shrinkRhoC a).contMDiff x₀)
        have hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
            (fun x => 𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) x₀ :=
          (hmulrho.clm_apply (holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxV)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun x => by simp [ContinuousLinearMap.mul_apply'])
        exact contMDiffAt_cSmul_section hG ((𝔇.shrinkDbarRho c).contMDiff_toFun x₀)
      · refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
          (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
        filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hbc] with x hx
        have hV : (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) = 0 := by
          rw [𝔇.shrinkDbarRho_eq_zero_of_notMem c hx]; module
        exact congrArg (Bundle.TotalSpace.mk x) hV
    · refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
      filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU a)).isOpen_compl.mem_nhds hba] with x hx
      have hV : (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) = 0 := by
        rw [𝔇.shrinkRhoC_eq_zero_of_notMem a hx, zero_mul]; module
      exact congrArg (Bundle.TotalSpace.mk x) hV

@[simp] theorem shrinkTerm_apply (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) (x : X) :
    (𝔇.shrinkTerm s a c) x
      = (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) := rfl

/-- Each Bott–Tu term is a `(0,1)`-form (`∂̄ρ_c` is, and ℂ-scaling preserves `(0,1)`). -/
theorem shrinkTerm_mem_zeroOne (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) :
    𝔇.shrinkTerm s a c ∈ OneFormsZeroOne X := by
  refine ⟨𝔇.shrinkTerm s a c, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 (𝔇.shrinkTerm s a c x) = 𝔇.shrinkTerm s a c x
  rw [shrinkTerm_apply, proj01_smul]
  have hfix : proj01 ((𝔇.shrinkDbarRho c) x) = (𝔇.shrinkDbarRho c x) := by
    show proj01 (dbarL (𝔇.shrinkRhoC c) x) = dbarL (𝔇.shrinkRhoC c) x
    rw [dbarL_eq_proj01L_differential]
    show proj01 (proj01 ((differential (𝔇.shrinkRhoC c)) x)) = proj01 ((differential (𝔇.shrinkRhoC c)) x)
    exact proj01_idempotent _
  rw [hfix]

/-- **The global Bott–Tu form `ω̂`** as a `(0,1)`-form: `∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`. -/
noncomputable def glueForm (s : 𝔇.overlapData.Cshr) : ↥(OneFormsZeroOne X) :=
  ∑ p : 𝔇.ι × 𝔇.ι, ⟨𝔇.shrinkTerm s p.1 p.2, 𝔇.shrinkTerm_mem_zeroOne s p.1 p.2⟩

/-- The underlying form of `glueForm` is the finite sum of `shrinkTerm`s. -/
theorem glueForm_val (s : 𝔇.overlapData.Cshr) :
    ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X)
      = ∑ p : 𝔇.ι × 𝔇.ι, 𝔇.shrinkTerm s p.1 p.2 := by
  show ((∑ p : 𝔇.ι × 𝔇.ι, (⟨𝔇.shrinkTerm s p.1 p.2, 𝔇.shrinkTerm_mem_zeroOne s p.1 p.2⟩ :
      ↥(OneFormsZeroOne X)) : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) = _
  rw [AddSubmonoidClass.coe_finsetSum]

/-! ## §C — The local smooth split `G_a` and its two key identities

`G_a(x) := ∑_c ρ_c(x) · holoFn σ_{ac}(x)` — a function smooth on `V_a` (each term confined to
`tsupport ρ_c ∩ V_a ⊆ V_c ∩ V_a`, where `holoFn σ_{ac}` is smooth).  Two identities drive the lift:
  * the **difference identity** `G_a(x) − G_b(x) = holoFn σ_{ab}(x) = s_{ab}.toFun(φ_a x)` on `V_a ∩ V_b`
    (cocycle telescoping `∑ ρ = 1`);
  * the **`∂̄` identity** `proj01(mfderiv G_a x) = ω̂ x` on `V_a` (Wirtinger product rule + cocycle
    telescoping `∑ ∂̄ρ = 0`), built in §D.
-/

/-- The chart-`a` smooth split `G_a := ∑_c ρ_c · holoFn σ_{ac}` (a function on `V_a`). -/
noncomputable def globalPrim (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  fun x => ∑ c, 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x

theorem globalPrim_apply (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) (x : X) :
    𝔇.globalPrim s a x = ∑ c, 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x := rfl

/-- **The difference identity** `G_a(x) − G_b(x) = holoFn σ_{ab}(x)` on `V_a ∩ V_b`.  Pointwise via the
cocycle relation `holoFn σ_{ac} = holoFn σ_{ab} + holoFn σ_{bc}` and `∑ ρ = 1`.  (Mirror of
`chartDiskCoverPrim_diff`.) -/
theorem globalPrim_diff (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a b : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X)) :
    𝔇.globalPrim s a x - 𝔇.globalPrim s b x = holoFn (𝔇.shrinkGerm s a b).2 x := by
  rw [globalPrim, globalPrim, ← Finset.sum_sub_distrib]
  have hpt : ∀ c : 𝔇.ι,
      𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x
        - 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s b c).2 x
      = 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a b).2 x := by
    intro c
    by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
    · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
      -- cocycle: `holoFn σ_{ac} = holoFn σ_{ab} + holoFn σ_{bc}` (middle `b`), on `V_a∩V_b∩V_c`.
      have htri : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b ⊓ 𝔇.shrinkOpens c : Opens X) :=
        ⟨⟨hx.1, hx.2⟩, hxc⟩
      rw [𝔇.shrinkGerm_cocycle_add s hs a b c htri]
      ring
    · rw [𝔇.shrinkRhoC_eq_zero_of_notMem c hb]; ring
  simp_rw [hpt, ← Finset.sum_mul, 𝔇.sum_shrinkRhoC_apply x, one_mul]

/-- A single summand `ρ_c · holoFn σ_{ac}` of `G_a`, as a bare function `X → ℂ`. -/
noncomputable def globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) : X → ℂ :=
  fun x => 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x

/-- Each summand of `G_a` is `MDifferentiableAt` at any point of `V_a` (in `tsupport ρ_c` both
factors are smooth — using `x ∈ V_a ∩ V_c`; off `tsupport ρ_c` the term is locally `0`). -/
theorem mdifferentiableAt_globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x := by
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    have hxac : x ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) := ⟨hxa, hxc⟩
    exact (((𝔇.shrinkRhoC c).contMDiff x).mul
      (holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxac)).mdifferentiableAt (by simp)
  · refine (mdifferentiableAt_const (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hb] with y hy
    simp only [globalPrimTerm, 𝔇.shrinkRhoC_eq_zero_of_notMem c hy, zero_mul]

/-- **The Wirtinger value of one summand** `proj01(mfderiv (ρ_c·holoFn σ_{ac}) x) = holoFn σ_{ac}(x) •
∂̄ρ_c x` at `x ∈ V_a` (product rule + `holoFn` holomorphic; off `tsupport ρ_c` both sides vanish). -/
theorem dbar_globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x)
      = holoFn (𝔇.shrinkGerm s a c).2 x • (𝔇.shrinkDbarRho c x) := by
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    have hxac : x ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) := ⟨hxa, hxc⟩
    have hr : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x) :=
      ((𝔇.shrinkRhoC c).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
    have hh : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn (𝔇.shrinkGerm s a c).2) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn (𝔇.shrinkGerm s a c).2) x) :=
      ((holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxac).mdifferentiableAt (by simp)).hasMFDerivAt
    show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x)
      = holoFn (𝔇.shrinkGerm s a c).2 x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x)
    rw [show (𝔇.globalPrimTerm s a c : X → ℂ)
        = ⇑(𝔇.shrinkRhoC c) * holoFn (𝔇.shrinkGerm s a c).2 from rfl,
      (hr.mul hh).mfderiv, map_add, proj01_smul, proj01_smul,
      holoFn_dbar_eq_zero (𝔇.shrinkGerm s a c).2 hxac]
    module
  · have hr0 : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x) = 0 := by
      have hconst : (𝔇.globalPrimTerm s a c) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hb] with y hy
        simp only [globalPrimTerm, 𝔇.shrinkRhoC_eq_zero_of_notMem c hy, zero_mul]
      rw [hconst.mfderiv_eq, mfderiv_const, map_zero]
    rw [hr0, 𝔇.shrinkDbarRho_eq_zero_of_notMem c hb]
    module

/-- Antisymmetry of `holoFn σ` (from diagonal vanishing + cocycle): `holoFn σ_{pa} = −holoFn σ_{ap}`
on `V_a ∩ V_p`. -/
theorem shrinkGerm_antisymm (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a p : 𝔇.ι) {y : X}
    (hya : y ∈ (𝔇.shrinkOpens a : Opens X)) (hyp : y ∈ (𝔇.shrinkOpens p : Opens X)) :
    holoFn (𝔇.shrinkGerm s p a).2 y = -holoFn (𝔇.shrinkGerm s a p).2 y := by
  have h := 𝔇.shrinkGerm_cocycle_add s hs p a p (y := y) ⟨⟨hyp, hya⟩, hyp⟩
  rw [𝔇.shrinkGerm_diag_eq_zero s hs p hyp] at h
  linear_combination -h

/-- **`glueForm` value telescopes on `V_a`**: `ω̂ x = ∑_c holoFn σ_{ac}(x) • ∂̄ρ_c(x)` for `x ∈ V_a`.
Via the cocycle substitution `holoFn σ_{pq} = holoFn σ_{aq} − holoFn σ_{ap}` (on `V_a`) and
`telescope_sum` (`∑ ρ = 1`, `∑ ∂̄ρ = 0`). -/
theorem glueForm_apply_on_V (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x
      = ∑ c, holoFn (𝔇.shrinkGerm s a c).2 x • (𝔇.shrinkDbarRho c x) := by
  rw [glueForm_val, section_finset_sum_apply]
  -- rewrite each term `(ρ_p·holoFn σ_{pq})•∂̄ρ_q` to `(ρ_p·(H_q − H_p))•∂̄ρ_q` with `H_q = holoFn σ_{aq}`.
  have hterm : ∀ p : 𝔇.ι × 𝔇.ι, (𝔇.shrinkTerm s p.1 p.2) x
      = (𝔇.shrinkRhoC p.1 x
          * (holoFn (𝔇.shrinkGerm s a p.2).2 x - holoFn (𝔇.shrinkGerm s a p.1).2 x))
        • (𝔇.shrinkDbarRho p.2 x) := by
    intro p
    obtain ⟨p, q⟩ := p
    rw [shrinkTerm_apply]
    by_cases hp : x ∈ tsupport (𝔇.shrinkPoU p)
    · by_cases hq : x ∈ tsupport (𝔇.shrinkPoU q)
      · have hxp : x ∈ (𝔇.shrinkOpens p : Opens X) := 𝔇.shrinkPoU_tsupport_subset p hp
        have hxq : x ∈ (𝔇.shrinkOpens q : Opens X) := 𝔇.shrinkPoU_tsupport_subset q hq
        -- cocycle `holoFn σ_{pq} = holoFn σ_{pa} + holoFn σ_{aq}` and antisymm `σ_{pa} = −σ_{ap}`.
        rw [𝔇.shrinkGerm_cocycle_add s hs p a q ⟨⟨hxp, hxa⟩, hxq⟩,
          𝔇.shrinkGerm_antisymm s hs a p hxa hxp]
        congr 2; ring
      · rw [𝔇.shrinkDbarRho_eq_zero_of_notMem q hq]; module
    · rw [𝔇.shrinkRhoC_eq_zero_of_notMem p hp]; module
  simp_rw [hterm]
  exact telescope_sum (fun p => 𝔇.shrinkRhoC p x) (fun q => holoFn (𝔇.shrinkGerm s a q).2 x)
    (fun q => 𝔇.shrinkDbarRho q x) (𝔇.sum_shrinkRhoC_apply x) (𝔇.sum_shrinkDbarRho_apply x)

/-- `G_a = ∑_c (ρ_c · holoFn σ_{ac})` as a sum of functions. -/
theorem globalPrim_eq_sum (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) :
    𝔇.globalPrim s a = ∑ c, 𝔇.globalPrimTerm s a c := by
  funext x
  rw [globalPrim_apply, Finset.sum_apply]
  rfl

/-- **The intrinsic `∂̄` identity** `proj01(mfderiv G_a x) = ω̂ x` for `x ∈ V_a`.  The per-term Wirtinger
values (`dbar_globalPrimTerm`) summed (`HasMFDerivAt.sum`), matched to `glueForm` by its `V_a`
telescoping. -/
theorem dbar_globalPrim (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x)
      = ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x := by
  -- `mfderiv G_a x = ∑_c mfderiv (term_c) x`.
  have hsum : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (∑ c, 𝔇.globalPrimTerm s a c) x
      (∑ c, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x) :=
    HasMFDerivAt.sum (fun c _ =>
      (𝔇.mdifferentiableAt_globalPrimTerm s a c hxa).hasMFDerivAt)
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x
      = ∑ c, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x := by
    rw [𝔇.globalPrim_eq_sum s a]; exact hsum.mfderiv
  rw [hmf, map_sum, 𝔇.glueForm_apply_on_V s hs a hxa]
  exact Finset.sum_congr rfl fun c _ => 𝔇.dbar_globalPrimTerm s a c hxa

/-! ## §D — The holomorphic corrector `η_a := u_a − G_a`

`u_a := diskVal a ω̂` is the per-disk `∂̄`-primitive (`proj01(mfderiv u_a) = ω̂` on `U_a`,
`dbar_diskValue_eq_g`).  Then `η_a := u_a − G_a` has `proj01(mfderiv η_a) = ω̂ − ω̂ = 0` on `V_a` —
holomorphic — and is bounded on `V_a` (`u_a` continuous on the compact `closure V_a ⊆ U_a`; `G_a`
bounded by `∑ ‖s_{·a}‖`).  So `η_a ∈ BddHol (Wov (a,a))`. -/

/-- The per-disk `∂̄`-primitive value `u_a := diskVal a ω̂` (a smooth function on `U_a`). -/
noncomputable def primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  diskVal 𝔇 a (𝔇.glueForm s)

/-- `proj01(mfderiv u_a x) = ω̂ x` on `U_a` (Forster 13.2 primitive; `dbar_diskValue_eq_g` upgraded to
the full CLM by `dbar_eq_of_apply_one'`). -/
theorem dbar_primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X} (hxa : x ∈ (𝔇.U a : Set X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x)
      = ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x :=
  dbar_eq_of_apply_one' (𝔇.glueForm s).2 (𝔇.dbar_diskValue_eq_g (𝔇.glueForm s).2 a hxa)

theorem mdifferentiableAt_primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.U a : Set X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x :=
  (contMDiffAt_diskVal 𝔇 a (𝔇.glueForm s) hxa).mdifferentiableAt (by simp)

/-- **Chart-`a` Wirtinger bridge from intrinsic vanishing.**  If `w` is `MDifferentiableAt y` with
intrinsic Wirtinger scalar `proj01(mfderiv w y)(1) = 0`, then for any chart `a` whose source contains
`y`, the chart-`a` planar `∂̄(w ∘ φ_a⁻¹)(φ_a y) = 0`.  Proof: `w∘φ_a⁻¹ = (w∘φ_y⁻¹)∘(φ_y∘φ_a⁻¹)`, the
inner map is holomorphic, so by the Wirtinger chain rule the chart-`a` `∂̄` is `conj(τ′)` times the
own-chart `∂̄(w∘φ_y⁻¹)(φ_y y) = proj01(mfderiv w y)(1) = 0`. -/
theorem dbar_chartFixed_of_intrinsic_zero {w : X → ℂ} {y : X} (a : 𝔇.ι)
    (hya : y ∈ (chartAt (H := ℂ) (𝔇.center a)).source)
    (hwmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w y)
    (hw0 : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w y) (1 : ℂ) = 0) :
    DbarDisk.dbar (fun z => w ((chartAt (H := ℂ) (𝔇.center a)).symm z))
      ((chartAt (H := ℂ) (𝔇.center a)) y) = 0 := by
  set φa := chartAt (H := ℂ) (𝔇.center a) with hφa
  set φy := chartAt (H := ℂ) y with hφy
  set τ : ℂ → ℂ := φy ∘ φa.symm with hτ
  have hyy : y ∈ φy.source := mem_chart_source ℂ y
  -- own-chart `∂̄(w∘φ_y.symm)(φ_y y) = proj01(mfderiv w y)(1) = 0`.
  have hown : DbarDisk.dbar (fun z => w (φy.symm z)) (φy y) = 0 := by
    have := dbar_apply_one_eq_dbarDisk' hwmd
    rw [hw0] at this
    -- `extChartAt 𝓘(ℝ,ℂ) y = chartAt ℂ y = φy` (identity model).
    simpa only [hφy, show (extChartAt 𝓘(ℝ, ℂ) y : X → ℂ) = (chartAt (H := ℂ) y : X → ℂ) from rfl,
      show ((extChartAt 𝓘(ℝ, ℂ) y) y : ℂ) = (chartAt (H := ℂ) y) y from rfl] using this.symm
  -- `τ` holomorphic at `φ_a y`, `τ (φ_a y) = φ_y y`.
  have hτdiff : DifferentiableAt ℂ τ (φa y) := by
    rw [hτ, hφy, hφa]
    exact (transition_analyticAt_of_mem (y := 𝔇.center a) (z := y) (x := y)
      hya hyy).differentiableAt
  have hτpt : τ (φa y) = φy y := by
    rw [hτ, Function.comp_apply, φa.left_inv hya]
  -- `w∘φ_y.symm` is `ℝ`-diff at `φ_y y` (= `τ(φ_a y)`).
  have hwsymm_md : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w (φy.symm (φy y)) := by
    rw [φy.left_inv hyy]; exact hwmd
  have hℝ : DifferentiableAt ℝ (fun z => w (φy.symm z)) (φy y) := by
    have hsymm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φy.symm (φy y) :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := y) _
        (φy.map_source hyy)).contMDiffAt
        (φy.open_target.mem_nhds (φy.map_source hyy)) |>.mdifferentiableAt (by simp)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z => w (φy.symm z)) (φy y) :=
      hwsymm_md.comp (φy y) hsymm
    have := hcomp.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, mfld_simps] using this
  -- Wirtinger chain rule: `∂̄((w∘φ_y.symm)∘τ)(φ_a y) = conj(τ′)·∂̄(w∘φ_y.symm)(φ_y y) = conj·0 = 0`.
  have hchain : DbarDisk.dbar ((fun z => w (φy.symm z)) ∘ τ) (φa y)
      = (starRingEnd ℂ) (deriv τ (φa y)) * DbarDisk.dbar (fun z => w (φy.symm z)) (τ (φa y)) :=
    dbarDisk_comp_holo (fun z => w (φy.symm z)) τ (φa y) (hτpt ▸ hℝ) hτdiff
  -- `w∘φ_a.symm = (w∘φ_y.symm)∘τ` on a NEIGHBOURHOOD of `φ_a y` (where `φ_a.symm ∈ φ_a.source`).
  have hcompfun : (fun z => w (φa.symm z)) =ᶠ[nhds (φa y)] ((fun z => w (φy.symm z)) ∘ τ) := by
    have hcont : ContinuousAt φa.symm (φa y) := φa.continuousAt_symm (φa.map_source hya)
    filter_upwards [hcont.preimage_mem_nhds (φy.open_source.mem_nhds (by
      rw [φa.left_inv hya]; exact hyy))] with z hz
    -- `hz : φa.symm z ∈ φy.source`; `τ z = φy (φa.symm z)`, `φy.symm (φy (φa.symm z)) = φa.symm z`.
    simp only [hτ, Function.comp_apply, φy.left_inv hz]
  rw [dbarDisk_congr hcompfun, hchain, hτpt, hown, mul_zero]

/-- **The corrector function** `η_a := u_a − G_a` (a bare `X → ℂ`, holomorphic on `V_a`). -/
noncomputable def etaFn (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  fun x => 𝔇.primVal s a x - 𝔇.globalPrim s a x

/-- `η_a` is `MDifferentiableAt` at `x ∈ V_a` (difference of two `MDifferentiableAt` functions). -/
theorem mdifferentiableAt_etaFn (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) x := by
  have hxaU : x ∈ (𝔇.U a : Set X) := 𝔇.shrinkOpens_le_U a hxa
  have hpu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x := 𝔇.mdifferentiableAt_primVal s a hxaU
  have hpg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x := by
    rw [𝔇.globalPrim_eq_sum s a]
    exact MDifferentiableAt.sum fun c _ => 𝔇.mdifferentiableAt_globalPrimTerm s a c hxa
  exact hpu.sub hpg

/-- The intrinsic Wirtinger scalar of `η_a` vanishes on `V_a`: `proj01(mfderiv η_a y)(1) = 0` (both
`u_a` and `G_a` have it `= (ω̂ y)(1)`). -/
theorem dbar1_etaFn (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {y : X}
    (hya : y ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) y) (1 : ℂ) = 0 := by
  have hyaU : y ∈ (𝔇.U a : Set X) := 𝔇.shrinkOpens_le_U a hya
  have hpu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) y := 𝔇.mdifferentiableAt_primVal s a hyaU
  have hpg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) y := by
    rw [𝔇.globalPrim_eq_sum s a]
    exact MDifferentiableAt.sum fun c _ => 𝔇.mdifferentiableAt_globalPrimTerm s a c hya
  -- own-chart planar `∂̄` of `η_a` = `∂̄(pu) − ∂̄(pg)` = `(ω̂)(1) − (ω̂)(1) = 0`; transfer back to scalar.
  set e := (extChartAt 𝓘(ℝ, ℂ) y) with he
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) y := 𝔇.mdifferentiableAt_etaFn s a hya
  rw [dbar_apply_one_eq_dbarDisk' hmd]
  have hpullEq : (fun z => 𝔇.etaFn s a (e.symm z))
      = fun z => 𝔇.primVal s a (e.symm z) - 𝔇.globalPrim s a (e.symm z) := by
    funext z; simp only [etaFn]
  have hℝu : DifferentiableAt ℝ (fun z => 𝔇.primVal s a (e.symm z)) (e y) := by
    have := hpu.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, he, mfld_simps] using this
  have hℝg : DifferentiableAt ℝ (fun z => 𝔇.globalPrim s a (e.symm z)) (e y) := by
    have := hpg.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, he, mfld_simps] using this
  rw [hpullEq, dbarFun_sub hℝu hℝg]
  rw [← dbar_apply_one_eq_dbarDisk' hpu, ← dbar_apply_one_eq_dbarDisk' hpg,
    𝔇.dbar_primVal s a hyaU, 𝔇.dbar_globalPrim s hs a hya, sub_self]

/-- **`η_a` chart-`a`-read is `AnalyticOn` `Wov (a,a)`.**  At each `z = φ_a y` (`y ∈ V_a`) the chart-`a`
planar `∂̄(η_a ∘ φ_a⁻¹) = 0` (`dbar_chartFixed_of_intrinsic_zero` + `dbar1_etaFn`), and the pullback is
`ℝ`-differentiable on the open `W = φ_a.target ∩ φ_a.symm⁻¹'(V_a)`; an open `DifferentiableOn ℂ` ⟹
`AnalyticOn`. -/
theorem etaFn_chartA_analyticOn (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) (𝔇.Wov (a, a)) := by
  set φa := chartAt (H := ℂ) (𝔇.center a) with hφa
  set W : Set ℂ := φa.target ∩ φa.symm ⁻¹' ((𝔇.shrinkOpens a : Opens X) : Set X) with hW
  have hWopen : IsOpen W := φa.isOpen_inter_preimage_symm (𝔇.shrinkOpens a).isOpen
  -- `DifferentiableOn ℂ (η_a∘φa.symm) W`.
  have hDiffOn : DifferentiableOn ℂ (𝔇.etaFn s a ∘ φa.symm) W := by
    intro z hz
    have hzV : φa.symm z ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hz.2
    have hzsrc : φa.symm z ∈ φa.source := φa.map_target hz.1
    have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) (φa.symm z) :=
      𝔇.mdifferentiableAt_etaFn s a hzV
    -- `ℝ`-differentiability of the chart-`a` pullback at `z = φa (φa.symm z)`.
    have hℝ : DifferentiableAt ℝ (𝔇.etaFn s a ∘ φa.symm) z := by
      have hsymm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φa.symm z :=
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center a) _ hz.1).contMDiffAt
          (φa.open_target.mem_nhds hz.1) |>.mdifferentiableAt (by simp)
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a ∘ φa.symm) z :=
        hmd.comp z hsymm
      have := hcomp.differentiableWithinAt_writtenInExtChartAt
      rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
        differentiableWithinAt_univ] at this
      simpa only [Function.comp, mfld_simps] using this
    -- chart-`a` planar `∂̄ = 0` (bridge from intrinsic zero).
    have hdb0 : DbarDisk.dbar (fun w => 𝔇.etaFn s a (φa.symm w)) z = 0 := by
      have hzz : φa (φa.symm z) = z := φa.right_inv hz.1
      have := 𝔇.dbar_chartFixed_of_intrinsic_zero a hzsrc hmd (𝔇.dbar1_etaFn s hs a hzV)
      rwa [hzz] at this
    exact (differentiableAt_of_dbar_eq_zero_chartDisk hℝ hdb0).differentiableWithinAt
  -- `AnalyticOn` on `Wov (a,a) = φ_a '' (V_a ∩ V_a) ⊆ W`-image.
  rintro w ⟨y, hyVV, rfl⟩
  have hyV : y ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hyVV.1
  have hysrc : y ∈ φa.source := 𝔇.shrinkOpens_subset_source a hyV
  have hwW : φa y ∈ W := ⟨φa.map_source hysrc, by
    simp only [Set.mem_preimage, φa.left_inv hysrc]; exact hyV⟩
  exact (hDiffOn.analyticOnNhd hWopen (φa y) hwW).analyticWithinAt

/-- `‖holoFn σ_{ac} x‖ ≤ ‖s_{ac}‖` on `V_a ∩ V_c` (the germ-section value is `s.toFun∘φ_a`, bounded by
the `BddHol` norm). -/
theorem norm_shrinkGerm_holoFn_le (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X)) :
    ‖holoFn (𝔇.shrinkGerm s a c).2 x‖ ≤ ‖s (a, c)‖ := by
  rw [𝔇.shrinkGerm_holoFn s a c hx]
  exact (s (a, c)).norm_toFun_le ⟨x, ⟨hx.1, hx.2⟩, rfl⟩

/-- `G_a` is bounded by `∑_c ‖s_{ac}‖` on `V_a`. -/
theorem norm_globalPrim_le (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    ‖𝔇.globalPrim s a x‖ ≤ ∑ c, ‖s (a, c)‖ := by
  rw [globalPrim_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (𝔇.norm_shrinkGerm_holoFn_le s a c ⟨hxa, hxc⟩)
    -- `‖ρ̃_c x‖ = |ρ_c x| ≤ 1` (nonneg + `∑ρ = 1`).
    show ‖((𝔇.shrinkPoU c x : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((𝔇.shrinkPoU).nonneg c x)]
    calc (𝔇.shrinkPoU c x : ℝ) ≤ ∑ d, 𝔇.shrinkPoU d x :=
          Finset.single_le_sum (fun d _ => (𝔇.shrinkPoU).nonneg d x) (Finset.mem_univ c)
      _ = 1 := 𝔇.sum_shrinkPoU_eq_one x
  · rw [𝔇.shrinkRhoC_eq_zero_of_notMem c hb, zero_mul, norm_zero]
    exact norm_nonneg _

/-- `primVal s a (φ_a.symm z) = planarPrimitive a ω̂ z` for `z ∈ φ_a.target` (chart round-trip). -/
theorem primVal_chartSymm (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (𝔇.center a)).target) :
    𝔇.primVal s a ((chartAt (H := ℂ) (𝔇.center a)).symm z)
      = 𝔇.planarPrimitive a (𝔇.glueForm s) z := by
  show 𝔇.planarPrimitive a (𝔇.glueForm s)
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center a)) ((chartAt (H := ℂ) (𝔇.center a)).symm z)) = _
  rw [show (extChartAt 𝓘(ℝ, ℂ) (𝔇.center a) : X → ℂ) = (chartAt (H := ℂ) (𝔇.center a) : X → ℂ) from rfl,
    (chartAt (H := ℂ) (𝔇.center a)).right_inv hz]

/-- **`η_a` chart-`a`-read is bounded on `Wov (a,a)`**: `‖planarPrimitive a ω̂ z‖` is bounded on the
compact `closure (Wov (a,a))` (`planarPrimitive` is globally continuous), and `‖G_a‖ ≤ ∑‖s_{a·}‖`. -/
theorem etaFn_chartA_bounded (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) :
    ∃ C, ∀ z ∈ 𝔇.Wov (a, a),
      ‖(𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) z‖ ≤ C := by
  obtain ⟨M, hM⟩ := (𝔇.isCompact_closure_Wov (a, a)).exists_bound_of_continuousOn
    (f := 𝔇.planarPrimitive a (𝔇.glueForm s))
    (𝔇.contDiff_planarPrimitive a (𝔇.glueForm s)).continuous.continuousOn
  refine ⟨M + ∑ c, ‖s (a, c)‖, fun z hz => ?_⟩
  obtain ⟨y, hyVV, rfl⟩ := hz
  have hyV : y ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hyVV.1
  have hysrc : y ∈ (chartAt (H := ℂ) (𝔇.center a)).source := 𝔇.shrinkOpens_subset_source a hyV
  have htgt : (chartAt (H := ℂ) (𝔇.center a)) y ∈ (chartAt (H := ℂ) (𝔇.center a)).target :=
    (chartAt (H := ℂ) (𝔇.center a)).map_source hysrc
  -- value: `η_a∘φa.symm (φa y) = planarPrimitive a ω̂ (φa y) − G_a y`.
  have hval : (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) ((chartAt (H := ℂ) (𝔇.center a)) y)
      = 𝔇.planarPrimitive a (𝔇.glueForm s) ((chartAt (H := ℂ) (𝔇.center a)) y) - 𝔇.globalPrim s a y := by
    simp only [Function.comp_apply, etaFn, (chartAt (H := ℂ) (𝔇.center a)).left_inv hysrc]
    -- `primVal s a y = planarPrimitive a ω̂ (extChartAt(center a) y) = planarPrimitive a ω̂ (φa y)`.
    rfl
  rw [hval]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (𝔇.norm_globalPrim_le s a hyV))
  exact hM _ (subset_closure ⟨y, hyVV, rfl⟩)

/-- **The holomorphic corrector `η_a ∈ BddHol (Wov (a,a))`** (`C0Holo`'s `a`-component). -/
noncomputable def etaBddHol (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) :
    BddHol (𝔇.Wov (a, a)) :=
  BddHol.ofAnalyticOn (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm)
    (𝔇.etaFn_chartA_analyticOn s hs a) (𝔇.etaFn_chartA_bounded s a)

theorem etaBddHol_toFun_of_mem (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.Wov (a, a)) :
    (𝔇.etaBddHol s hs a).toFun z = 𝔇.etaFn s a ((chartAt (H := ℂ) (𝔇.center a)).symm z) :=
  BddHol.ofAnalyticOn_toFun_of_mem _ _ _ hz

/-- `η : C0Holo` — the holomorphic 0-cochain. -/
noncomputable def etaCochain (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) : 𝔇.C0Holo :=
  fun a => 𝔇.etaBddHol s hs a

/-! ## §A2-x — The holomorphic COVER cocycle `x : Ccov` (Forster 14.6 per-disk solve)

`x'_{ab} := dolbeaultToCechCocycle 𝔇 ω̂` (the PROVEN per-disk ∂̄-solve via the Cauchy transform on each
ball, `DolbeaultComparisonProof`) is a germ Čech cocycle, holomorphic on the FULL overlaps, with
component value `holoFn(x'_{ab}) = u_b − u_a` (`u_a := diskVal a ω̂`).  We package each component as a
`BddHol (Uov (a,b))` (analytic via `analyticOn_pullback_of_holo`; bounded since `u_a = planarPrimitive
a ω̂ ∘ φ_a` and `planarPrimitive a ω̂` is continuous on the compact `closedBall ⊇ φ_a '' U_a`). -/

/-- The germ cover cocycle `x' := dolbeaultToCechCocycle 𝔇 ω̂` (an element of `cocycles1`). -/
noncomputable def coverCocycleGerm (s : 𝔇.overlapData.Cshr) :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) :=
  dolbeaultToCechCocycle 𝔇 (𝔇.glueForm s)

/-- The `(a,b)`-component germ is `cechDelta0 (rawCochain ω̂)` — its representative on `U_a ⊓ U_b` is
`diskSection b ω̂ − diskSection a ω̂`. -/
theorem coverCocycleGerm_component (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    ((𝔇.coverCocycleGerm s : 𝔇.toFiniteCover.Cochain1)) (a, b)
      = toGerm (𝔇.U a ⊓ 𝔇.U b)
          (𝔇.diskSection b (𝔇.glueForm s) ∘ openIncl inf_le_right
            - 𝔇.diskSection a (𝔇.glueForm s) ∘ openIncl inf_le_left) := by
  show 𝔇.toFiniteCover.cechDelta0 (𝔇.rawCochain (𝔇.glueForm s)) (a, b) = _
  simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  rw [show 𝔇.rawCochain (𝔇.glueForm s) b = toGerm (𝔇.U b) (𝔇.diskSection b (𝔇.glueForm s)) from rfl,
    show 𝔇.rawCochain (𝔇.glueForm s) a = toGerm (𝔇.U a) (𝔇.diskSection a (𝔇.glueForm s)) from rfl,
    rawRestrictG_coe, rawRestrictG_coe, ← map_sub]

/-- **`holoFn(x'_{ab}) y = u_b y − u_a y`** on `U_a ∩ U_b` (`u := diskVal ω̂`).  The germ's
representative `diskSection b − diskSection a` extends continuously to `diskVal b − diskVal a`. -/
theorem coverCocycleGerm_holoFn (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.U a ⊓ 𝔇.U b : Opens X)) :
    holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b) y
      = diskVal 𝔇 b (𝔇.glueForm s) y - diskVal 𝔇 a (𝔇.glueForm s) y := by
  set F : ↥(𝔇.U a ⊓ 𝔇.U b) → ℂ :=
    𝔇.diskSection b (𝔇.glueForm s) ∘ openIncl inf_le_right
      - 𝔇.diskSection a (𝔇.glueForm s) ∘ openIncl inf_le_left with hF
  have hgermeq : toGerm (𝔇.U a ⊓ 𝔇.U b) F
      = ((𝔇.coverCocycleGerm s : 𝔇.toFiniteCover.Cochain1)) (a, b) :=
    (𝔇.coverCocycleGerm_component s a b).symm
  -- `Gext F` agrees with the continuous `diskVal b − diskVal a` near `y`, and is continuous there.
  have hcont : ContinuousAt (fun z : X => diskVal 𝔇 b (𝔇.glueForm s) z - diskVal 𝔇 a (𝔇.glueForm s) z) y :=
    ((contMDiffAt_diskVal 𝔇 b (𝔇.glueForm s) hy.2).continuousAt).sub
      ((contMDiffAt_diskVal 𝔇 a (𝔇.glueForm s) hy.1).continuousAt)
  have hFval : ∀ w : ↥(𝔇.U a ⊓ 𝔇.U b),
      F w = diskVal 𝔇 b (𝔇.glueForm s) w.1 - diskVal 𝔇 a (𝔇.glueForm s) w.1 := by
    intro w; simp only [hF, Pi.sub_apply, Function.comp_apply, openIncl, diskSection, diskVal]
  have hev : Gext F =ᶠ[nhds y]
      (fun z : X => diskVal 𝔇 b (𝔇.glueForm s) z - diskVal 𝔇 a (𝔇.glueForm s) z) := by
    filter_upwards [(𝔇.U a ⊓ 𝔇.U b).isOpen.mem_nhds hy] with z hz
    rw [Gext_apply_mem F hz, hFval ⟨z, hz⟩]
  have htend : Filter.Tendsto (Gext F) (𝓝[≠] y)
      (𝓝 (diskVal 𝔇 b (𝔇.glueForm s) y - diskVal 𝔇 a (𝔇.glueForm s) y)) :=
    Filter.Tendsto.congr' (hev.filter_mono nhdsWithin_le_nhds).symm
      ((hcont.tendsto).mono_left nhdsWithin_le_nhds)
  exact holoFn_eq_of_tendsto (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b) F hgermeq hy htend

/-- `φ_a.symm z ∈ U_a ∩ U_b` for `z ∈ Uov (a,b)`. -/
theorem chartSymm_mem_Uov (a b : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Uov (a, b)) :
    (chartAt (H := ℂ) (𝔇.center a)).symm z ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [(chartAt (H := ℂ) (𝔇.center a)).left_inv
    ((Set.inter_subset_left).trans (𝔇.U_subset_chartAt_source a) hx)]

/-- `‖diskVal a ω̂ x‖` is bounded (uniformly in `x`) by the sup of `planarPrimitive a ω̂` on the compact
`closedBall (e a) (radius a)` (`diskVal a ω̂ x = planarPrimitive a ω̂ (φ_a x)`). -/
theorem exists_bound_diskVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) :
    ∃ C, ∀ x : X, x ∈ (𝔇.U a : Set X) → ‖diskVal 𝔇 a (𝔇.glueForm s) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (𝔇.e a) (𝔇.radius a)).exists_bound_of_continuousOn
    (f := 𝔇.planarPrimitive a (𝔇.glueForm s))
    (𝔇.contDiff_planarPrimitive a (𝔇.glueForm s)).continuous.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  show ‖𝔇.planarPrimitive a (𝔇.glueForm s) ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center a)) x)‖ ≤ C
  refine hC _ (Metric.ball_subset_closedBall ?_)
  rw [← 𝔇.image_U_eq_ball a]; exact ⟨x, hx, rfl⟩

/-- **The cover-cochain analyticity input**: `holoFn(x'_{ab}) ∘ φ_a⁻¹` is `AnalyticOn (Uov (a,b))`. -/
theorem coverCocycle_analyticOn (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    AnalyticOn ℂ (holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b)
      ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) (𝔇.Uov (a, b)) := by
  have : AnalyticOn ℂ (holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b)
      ∘ (chartAt (H := ℂ) (𝔇.center a)).symm)
      ((chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X)) :=
    analyticOn_pullback_of_holo ((Set.inter_subset_left).trans (𝔇.U_subset_chartAt_source a))
      (fun x hx => gextLimRep_chart_analyticAt
        (holoRep_mem (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b)) hx)
  exact this

/-- **The cover cochain component** `x_{ab} ∈ BddHol (Uov (a,b))` (analytic + bounded by `2·max diskVal`). -/
noncomputable def coverBddHol (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) : BddHol (𝔇.Uov (a, b)) :=
  BddHol.ofAnalyticOn
    (holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b) ∘ (chartAt (H := ℂ) (𝔇.center a)).symm)
    (𝔇.coverCocycle_analyticOn s a b)
    (by
      obtain ⟨Cb, hCb⟩ := 𝔇.exists_bound_diskVal s b
      obtain ⟨Ca, hCa⟩ := 𝔇.exists_bound_diskVal s a
      refine ⟨Cb + Ca, fun z hz => ?_⟩
      have hxmem : (chartAt (H := ℂ) (𝔇.center a)).symm z ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) :=
        𝔇.chartSymm_mem_Uov a b hz
      rw [Function.comp_apply, 𝔇.coverCocycleGerm_holoFn s a b hxmem]
      refine (norm_sub_le _ _).trans (add_le_add (hCb _ hxmem.2) (hCa _ hxmem.1)))

theorem coverBddHol_toFun_of_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {z : ℂ}
    (hz : z ∈ 𝔇.Uov (a, b)) :
    (𝔇.coverBddHol s a b).toFun z
      = holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b) ((chartAt (H := ℂ) (𝔇.center a)).symm z) :=
  BddHol.ofAnalyticOn_toFun_of_mem _ _ _ hz

/-- `x : Ccov` — the holomorphic cover cocycle (the NEGATED per-disk cocycle: the boundary-map sign
convention `(δ⁰c)(a,b) = c_b − c_a` makes the lift `s = δ⁰η + ρx` come out with `x = −x'`). -/
noncomputable def coverCochain (s : 𝔇.overlapData.Cshr) : 𝔇.overlapData.Ccov :=
  fun p => -(𝔇.coverBddHol s p.1 p.2)

theorem coverCochain_toFun_of_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {z : ℂ}
    (hz : z ∈ 𝔇.Uov (a, b)) :
    (𝔇.coverCochain s (a, b)).toFun z
      = -holoFn (cocycle_mem 𝔇 (𝔇.coverCocycleGerm s) a b) ((chartAt (H := ℂ) (𝔇.center a)).symm z) := by
  show (-(𝔇.coverBddHol s a b)).toFun z = _
  rw [BddHol.toFun_neg, Pi.neg_apply, 𝔇.coverBddHol_toFun_of_mem s a b hz]

/-! ## §A2-leray — the cocycle property of `x` and the lift identity `s = δ⁰η + ρx` -/

/-- `chart_a w ∈ UovTriple (a,b,c)` for `w ∈ U_a ∩ U_b ∩ U_c`. -/
theorem chart_mem_UovTriple (a b c : 𝔇.ι) {w : X}
    (hw : w ∈ (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c : Opens X)) :
    (chartAt (H := ℂ) (𝔇.center a)) w ∈ 𝔇.UovTriple (a, b, c) :=
  ⟨w, hw, rfl⟩

/-- **`δ¹cov x = 0`** — the cover cochain `x` is a cocycle.  Pointwise on `UovTriple`, the three
`holoFn(x'_{··})` values obey the cocycle relation `holoFn_cocycle_add` (`x' ∈ cocycles1`). -/
theorem coverCochain_mem_Z1cov (s : 𝔇.overlapData.Cshr) :
    𝔇.delta1CovModel (𝔇.coverCochain s) = 0 := by
  ext t
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.UovTriple t
  · rw [show ((0 : 𝔇.C2Cov) t).toFun z = 0 from rfl,
      𝔇.delta1CovModel_apply_apply (𝔇.coverCochain s) t hz]
    obtain ⟨a, b, c⟩ := t
    obtain ⟨w, hw, hwz⟩ := id hz
    -- chart round-trips: `chart_a.symm z = w`, `chart_b.symm (τ_{ab} z) = w`, `chart_a.symm z = w`.
    have hwa : (chartAt (H := ℂ) (𝔇.center a)).symm z = w := by
      rw [← hwz, (chartAt (H := ℂ) (𝔇.center a)).left_inv (𝔇.U_subset_chartAt_source a hw.1.1)]
    have hτw : 𝔇.coverTransition a b z = (chartAt (H := ℂ) (𝔇.center b)) w := by
      rw [← hwz]; exact 𝔇.coverTransition_apply a b ⟨hw.1.1, hw.1.2⟩
    have hwb : (chartAt (H := ℂ) (𝔇.center b)).symm (𝔇.coverTransition a b z) = w := by
      rw [hτw, (chartAt (H := ℂ) (𝔇.center b)).left_inv (𝔇.U_subset_chartAt_source b hw.1.2)]
    -- evaluate the three negated `holoFn(x')` components.
    rw [𝔇.coverCochain_toFun_of_mem s b c (𝔇.mapsTo_coverTransition_UovTriple a b c hz),
      𝔇.coverCochain_toFun_of_mem s a c (𝔇.UovTriple_subset_Uov_fst_trd a b c hz),
      𝔇.coverCochain_toFun_of_mem s a b (𝔇.UovTriple_subset_Uov_fst_snd a b c hz), hwa, hwb]
    -- cocycle relation `holoFn x'_{ac} = holoFn x'_{ab} + holoFn x'_{bc}`.
    rw [holoFn_cocycle_add 𝔇 (𝔇.coverCocycleGerm s) a b c hw]
    ring
  · rw [show ((0 : 𝔇.C2Cov) t).toFun z = 0 from rfl,
      (𝔇.delta1CovModel (𝔇.coverCochain s) t).zero_off z hz]

/-- **The lift identity** `s = δ⁰ η + ρ x` on each `Wov (a,b)`.  Pointwise at `z = φ_a x`
(`x ∈ V_a ∩ V_b`):
`(δ⁰η + ρx)_{ab}(z) = (η_b(x) − η_a(x)) + (−(u_b(x) − u_a(x)))`
`= ((u_b − G_b) − (u_a − G_a)) − (u_b − u_a) = G_a(x) − G_b(x) = holoFn σ_{ab}(x) = s_{ab}(z)`. -/
theorem leray_identity (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) :
    s = 𝔇.delta0Model (𝔇.etaCochain s hs) + 𝔇.overlapData.rhoRaw (𝔇.coverCochain s) := by
  ext p
  apply BddHol.toFun_injective
  funext z
  obtain ⟨a, b⟩ := p
  by_cases hz : z ∈ 𝔇.Wov (a, b)
  · obtain ⟨x, ⟨hxa, hxb⟩, hxz⟩ := id hz
    have hxab : x ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) := ⟨hxa, hxb⟩
    have hxaU : x ∈ ((𝔇.U a : Opens X) : Set X) := 𝔇.shrinkOpens_le_U a hxa
    have hxbU : x ∈ ((𝔇.U b : Opens X) : Set X) := 𝔇.shrinkOpens_le_U b hxb
    have hxUov : x ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) := ⟨hxaU, hxbU⟩
    -- chart round-trips.
    have hwa : (chartAt (H := ℂ) (𝔇.center a)).symm z = x := by
      rw [← hxz, (chartAt (H := ℂ) (𝔇.center a)).left_inv (𝔇.U_subset_chartAt_source a hxaU)]
    have hτz : 𝔇.coverTransition a b z = (chartAt (H := ℂ) (𝔇.center b)) x := by
      rw [← hxz]; exact 𝔇.coverTransition_apply a b ⟨hxaU, hxbU⟩
    have hwb : (chartAt (H := ℂ) (𝔇.center b)).symm (𝔇.coverTransition a b z) = x := by
      rw [hτz, (chartAt (H := ℂ) (𝔇.center b)).left_inv (𝔇.U_subset_chartAt_source b hxbU)]
    have hzWaa : z ∈ 𝔇.Wov (a, a) := by rw [← hxz]; exact ⟨x, ⟨hxa, hxa⟩, rfl⟩
    have hτzWbb : 𝔇.coverTransition a b z ∈ 𝔇.Wov (b, b) := by
      rw [hτz]; exact ⟨x, ⟨hxb, hxb⟩, rfl⟩
    have hzUov : z ∈ 𝔇.Uov (a, b) := ⟨x, hxUov, hxz⟩
    -- LHS `s_{ab}(z) = holoFn σ_{ab}(x)`.
    have hLHS : (s (a, b)).toFun z = holoFn (𝔇.shrinkGerm s a b).2 x := by
      rw [𝔇.shrinkGerm_holoFn s a b hxab, hxz]
    rw [hLHS]
    -- RHS.
    show holoFn (𝔇.shrinkGerm s a b).2 x
      = (𝔇.delta0Model (𝔇.etaCochain s hs) (a, b)
          + 𝔇.overlapData.rhoRaw (𝔇.coverCochain s) (a, b)).toFun z
    rw [BddHol.toFun_add, Pi.add_apply]
    -- `(δ0 η)(a,b)(z) = η_b(τ z) − η_a(z)`.
    rw [𝔇.delta0Model_apply_apply (𝔇.etaCochain s hs) (a, b) hz]
    show holoFn (𝔇.shrinkGerm s a b).2 x
      = ((𝔇.etaCochain s hs b).toFun (𝔇.coverTransition a b z)
          - (𝔇.etaCochain s hs a).toFun z)
        + (𝔇.overlapData.rhoRaw (𝔇.coverCochain s) (a, b)).toFun z
    rw [show 𝔇.etaCochain s hs b = 𝔇.etaBddHol s hs b from rfl,
      show 𝔇.etaCochain s hs a = 𝔇.etaBddHol s hs a from rfl,
      𝔇.etaBddHol_toFun_of_mem s hs b hτzWbb, 𝔇.etaBddHol_toFun_of_mem s hs a hzWaa,
      hwb, hwa]
    -- `(ρ x)(a,b)(z) = x(a,b)(z) = −(u_b(x) − u_a(x))`.
    simp only [HolomorphicDiskOverlapData.rhoRaw_apply, overlapData_Wov_eq, overlapData_Uov_eq]
    rw [BddHol.restrictOpenCLM_toFun_of_mem _ _ hz,
      𝔇.coverCochain_toFun_of_mem s a b hzUov, hwa, 𝔇.coverCocycleGerm_holoFn s a b hxUov]
    -- `η_a x = u_a x − G_a x`, `η_b x = u_b x − G_b x`; assemble to `G_a − G_b = holoFn σ_{ab}`.
    show holoFn (𝔇.shrinkGerm s a b).2 x
      = (𝔇.etaFn s b x - 𝔇.etaFn s a x)
        + -(diskVal 𝔇 b (𝔇.glueForm s) x - diskVal 𝔇 a (𝔇.glueForm s) x)
    simp only [etaFn, primVal]
    have hdiff := 𝔇.globalPrim_diff s hs a b hxab
    linear_combination -hdiff
  · show (s (a, b)).toFun z
      = (𝔇.delta0Model (𝔇.etaCochain s hs) (a, b)
          + 𝔇.overlapData.rhoRaw (𝔇.coverCochain s) (a, b)).toFun z
    rw [(s (a, b)).zero_off z hz, BddHol.toFun_add, Pi.add_apply,
      (𝔇.delta0Model (𝔇.etaCochain s hs) (a, b)).zero_off z hz,
      (𝔇.overlapData.rhoRaw (𝔇.coverCochain s) (a, b)).zero_off z hz, add_zero]


/-- **The structural δ-complex on `𝔇.overlapData`, with the `leray` field** — all fields PROVEN.
`δ0`/`δ1`/`δ1cov`/`hδδ`/`hcomm` are the model differentials of §A; `leray` (Forster 14.6) is
discharged by the global Bott–Tu form route of §A2-*:

  Given a shrinking cocycle `s : Cshr` (`δ¹s = 0`):
  * `σ := shrinkGerm s` reads each `s_{ab}` back to an `𝒪_0` germ on `V_a ⊓ V_b`, a germ cocycle.
  * `ω̂ := glueForm s = ∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c` (shrinking PoU `shrinkPoU`) is a GLOBAL
    smooth `(0,1)`-form, built directly (NO cross-chart `∂̄g_a` gluing).
  * `x := coverCochain s` is the per-disk ∂̄-solve cocycle `dolbeaultToCechCocycle ω̂` (PROVEN, the
    no-cutoff ball solve), holomorphic on the FULL overlaps `Uov`; `δ¹cov x = 0`
    (`coverCochain_mem_Z1cov`).
  * `η := etaCochain s` has `η_a = diskVal a ω̂ − G_a` (`G_a := ∑_c ρ_c · holoFn σ_{ac}`, the local
    split), holomorphic on `V_a` since both `diskVal a ω̂` and `G_a` have intrinsic ∂̄ `= ω̂` there
    (`dbar_globalPrim`/`dbar_diskValue_eq_g`).
  * `s = δ⁰η + ρx` (`leray_identity`): the `diskVal` terms cancel, leaving `G_a − G_b = holoFn σ_{ab}`
    (`globalPrim_diff`, cocycle telescoping `∑ρ = 1`).

This is the ball geometry's genuine unblock over the Montel cover: the global form has a smooth
full-ball chart read, so the per-disk solve produces a cover cocycle on the FULL overlap. -/
noncomputable def holomorphicCoboundaries : HolomorphicCoboundaries 𝔇.overlapData where
  C0 := 𝔇.C0Holo
  C2 := 𝔇.C2Holo
  C2cov := 𝔇.C2Cov
  δ0 := 𝔇.delta0Model
  δ1 := 𝔇.delta1Model
  δ1cov := 𝔇.delta1CovModel
  hδδ := 𝔇.delta1_comp_delta0
  hcomm := 𝔇.hcomm
  leray := fun s hs => by
    -- The global Bott–Tu form route, fully discharged (§A2-* above): `η := etaCochain` (the
    -- holomorphic corrector `u_a − G_a`), `x := coverCochain` (the per-disk ∂̄-solve cocycle,
    -- `dolbeaultToCechCocycle`), `δ¹cov x = 0` (`coverCochain_mem_Z1cov`), and the lift identity
    -- `s = δ⁰η + ρx` (`leray_identity`).
    have hs' : 𝔇.delta1Model s = 0 := hs
    exact ⟨𝔇.etaCochain s hs', 𝔇.coverCochain s, 𝔇.coverCochain_mem_Z1cov s,
      𝔇.leray_identity s hs'⟩

/-! ## §B — The comparison `cechH1 𝔇 0 ↪ supH1`

For FINITENESS a linear INJECTION `cechH1 𝔇 0 ↪ c.supH1` suffices (`FiniteDimensional.of_injective`).
We build the FORWARD germ→`BddHol` cochain map landing in the SHRINKING side `Cshr` (where boundedness
is automatic on the relatively-compact `Wov`), show it is a cocycle (lands in `Z1shr`) and kills
coboundaries (descends to `cechH1 → supH1`), and prove injectivity by the germ-class `𝒪_D`
sheaf-gluing (`omegaDGerm_separated`/`omegaDGerm_glue`).

The per-overlap atom reads a germ section `g (a,b) ∈ OmegaDGerm 0 (U a ⊓ U b)` through chart `center a`
and restricts it to the relatively-compact `Wov (a,b)` (whose closure lies in `Uov (a,b) = chartAt ''
(U a ⊓ U b)`, i.e. `closure_Wov_subset_Uov`).  This is the `holoSectionToBddHol` K-bridge atom; it is
re-derived inline (the packaged `CechModelCochain.germSectionToBddHolCLM` is import-incompatible with
`ChartDiskFiniteness` — the `dbarRho_eq_zero_of_notMem` duplicate-def collision). -/

variable (D : Divisor X)

/-- The per-overlap holomorphy domain for the forward map: the ball overlap `U a ⊓ U b`, read in chart
`center a`.  `U a ⊓ U b ⊆ (chartAt (center a)).source`. -/
theorem overlap_subset_source (a b : 𝔇.ι) :
    ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center a)).source :=
  (Set.inter_subset_left).trans (𝔇.U_subset_chartAt_source a)

/-- `closure (Wov (a,b)) ⊆ chartAt (center a) '' (U a ⊓ U b)` — the relatively-compact nesting that
makes the analytic representative bounded on `Wov`.  This is `closure_Wov_subset_Uov` read against the
defining `Uov = chartAt '' (U a ⊓ U b)`. -/
theorem closure_Wov_subset_chartImage_overlap (a b : 𝔇.ι) :
    closure (𝔇.Wov (a, b)) ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) :=
  𝔇.closure_Wov_subset_Uov (a, b)

/-- **The per-overlap atom** (inline `germSectionToBddHol` on the shrinking `Wov`).  A germ section
`g ∈ OmegaDGerm 0 (U a ⊓ U b)`, read through chart `center a` and restricted to `Wov (a,b)`, is a
`BddHol (Wov (a,b))`.  Value: `holoFn hg ∘ (chartAt (center a)).symm`. -/
noncomputable def overlapAtom (a b : 𝔇.ι) {g : MGerm (𝔇.U a ⊓ 𝔇.U b)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) :
    BddHol (𝔇.Wov (a, b)) :=
  holoSectionToBddHol (𝔇.overlap_subset_source a b)
    (fun _x hx => gextLimRep_chart_analyticAt (holoRep_mem hg) hx)
    (𝔇.closure_Wov_subset_chartImage_overlap a b) (𝔇.isCompact_closure_Wov (a, b))

@[simp] theorem overlapAtom_toFun_of_mem (a b : 𝔇.ι) {g : MGerm (𝔇.U a ⊓ 𝔇.U b)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, b)) :
    (𝔇.overlapAtom a b hg).toFun z = holoFn hg ((chartAt (H := ℂ) (𝔇.center a)).symm z) :=
  holoSectionToBddHol_toFun_of_mem _ _ _ _ hz

/-- For `z ∈ Wov (a,b)`, the chart-`a` preimage `(chartAt (center a)).symm z` lies in the overlap
`U a ⊓ U b` — so `holoFn` (germ-invariant, additive, …) applies there. -/
theorem chartSymm_mem_overlap (a b : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, b)) :
    (chartAt (H := ℂ) (𝔇.center a)).symm z ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) := by
  obtain ⟨w, hwUV, hwz⟩ := 𝔇.closure_Wov_subset_chartImage_overlap a b (subset_closure hz)
  have hsrc : w ∈ (chartAt (H := ℂ) (𝔇.center a)).source := 𝔇.overlap_subset_source a b hwUV
  rwa [← hwz, (chartAt (H := ℂ) (𝔇.center a)).left_inv hsrc]

theorem overlapAtom_add (a b : 𝔇.ι) {g₁ g₂ : MGerm (𝔇.U a ⊓ 𝔇.U b)}
    (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b))
    (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) :
    𝔇.overlapAtom a b (Submodule.add_mem _ hg₁ hg₂)
      = 𝔇.overlapAtom a b hg₁ + 𝔇.overlapAtom a b hg₂ := by
  refine BddHol.toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ 𝔇.Wov (a, b)
  · rw [BddHol.toFun_add, Pi.add_apply,
      overlapAtom_toFun_of_mem _ _ _ (Submodule.add_mem _ hg₁ hg₂) hz,
      overlapAtom_toFun_of_mem _ _ _ hg₁ hz, overlapAtom_toFun_of_mem _ _ _ hg₂ hz]
    exact holoFn_add hg₁ hg₂ (Submodule.add_mem _ hg₁ hg₂) (𝔇.chartSymm_mem_overlap a b hz)
  · rw [BddHol.toFun_add, Pi.add_apply,
      (𝔇.overlapAtom a b (Submodule.add_mem _ hg₁ hg₂)).zero_off z hz,
      (𝔇.overlapAtom a b hg₁).zero_off z hz,
      (𝔇.overlapAtom a b hg₂).zero_off z hz, add_zero]

theorem overlapAtom_smul (a b : 𝔇.ι) (c : ℂ) {g : MGerm (𝔇.U a ⊓ 𝔇.U b)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) :
    𝔇.overlapAtom a b (Submodule.smul_mem _ c hg) = c • 𝔇.overlapAtom a b hg := by
  refine BddHol.toFun_injective (funext fun z => ?_)
  by_cases hz : z ∈ 𝔇.Wov (a, b)
  · rw [BddHol.toFun_smul, Pi.smul_apply,
      overlapAtom_toFun_of_mem _ _ _ (Submodule.smul_mem _ c hg) hz,
      overlapAtom_toFun_of_mem _ _ _ hg hz]
    exact holoFn_smul c hg (Submodule.smul_mem _ c hg) (𝔇.chartSymm_mem_overlap a b hz)
  · rw [BddHol.toFun_smul, Pi.smul_apply,
      (𝔇.overlapAtom a b (Submodule.smul_mem _ c hg)).zero_off z hz,
      (𝔇.overlapAtom a b hg).zero_off z hz, smul_zero]

/-- **The per-overlap atom as a `ℂ`-linear map** `OmegaDGerm 0 (U a ⊓ U b) →ₗ[ℂ] BddHol (Wov (a,b))`. -/
noncomputable def overlapAtomCLM (a b : 𝔇.ι) :
    (OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) →ₗ[ℂ] BddHol (𝔇.Wov (a, b)) where
  toFun g := 𝔇.overlapAtom a b g.2
  map_add' g₁ g₂ := 𝔇.overlapAtom_add a b g₁.2 g₂.2
  map_smul' c g := 𝔇.overlapAtom_smul a b c g.2

@[simp] theorem overlapAtomCLM_apply (a b : 𝔇.ι) {g : MGerm (𝔇.U a ⊓ 𝔇.U b)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a ⊓ 𝔇.U b)) :
    𝔇.overlapAtomCLM a b ⟨g, hg⟩ = 𝔇.overlapAtom a b hg := rfl

/-! ### The forward cochain map `↥(cocycles1 0) → Cshr`, and its image in `Z1shr` -/

/-- **The forward germ→`BddHol` cochain map** `↥(cocycles1 0) →ₗ[ℂ] Cshr`.  Componentwise the
per-overlap atom: a Čech germ cocycle `g`'s `(a,b)`-component (an `OmegaDGerm 0 (U a ⊓ U b)` section,
`cocycle_mem`) becomes a `BddHol (Wov (a,b))` via its analytic representative restricted to the
relatively-compact `Wov (a,b)`.  `ℂ`-linear (each component is, `overlapAtomCLM`). -/
noncomputable def cechToCshr :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) →ₗ[ℂ] 𝔇.overlapData.Cshr where
  toFun g := fun p => 𝔇.overlapAtom p.1 p.2 (cocycle_mem 𝔇 g p.1 p.2)
  map_add' g₁ g₂ := by
    funext p
    exact 𝔇.overlapAtom_add p.1 p.2 (cocycle_mem 𝔇 g₁ p.1 p.2) (cocycle_mem 𝔇 g₂ p.1 p.2)
  map_smul' c g := by
    funext p
    exact 𝔇.overlapAtom_smul p.1 p.2 c (cocycle_mem 𝔇 g p.1 p.2)

theorem cechToCshr_apply_toFun (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (p : 𝔇.overlapData.J) {z : ℂ} (hz : z ∈ 𝔇.Wov p) :
    (𝔇.cechToCshr g p).toFun z
      = holoFn (cocycle_mem 𝔇 g p.1 p.2) ((chartAt (H := ℂ) (𝔇.center p.1)).symm z) := by
  obtain ⟨a, b⟩ := p
  exact 𝔇.overlapAtom_toFun_of_mem a b (cocycle_mem 𝔇 g a b) hz

/-- The transition point identity for a triple-overlap chart point: for `x ∈ U a ⊓ U b ⊓ U c`,
`(chart_b).symm (τ_{ab} (chart_a x)) = x`.  (`τ_{ab} (chart_a x) = chart_b x` by
`coverTransition_apply`, then `(chart_b).symm (chart_b x) = x`.) -/
theorem chartSymm_coverTransition_eq (a b c : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c : Opens X)) :
    (chartAt (H := ℂ) (𝔇.center b)).symm
        (𝔇.coverTransition a b ((chartAt (H := ℂ) (𝔇.center a)) x)) = x := by
  rw [𝔇.coverTransition_apply a b ⟨hx.1.1, hx.1.2⟩,
    (chartAt (H := ℂ) (𝔇.center b)).left_inv (𝔇.U_subset_chartAt_source b hx.1.2)]

/-- **The forward map lands in `Z1shr`** (`δ¹` vanishes).  Pointwise on `WovTriple t`, the three terms
reduce — via the transition point identity and the cocycle relation at the `holoFn` level
(`holoFn_cocycle_add`) — to `0`. -/
theorem cechToCshr_mem_Z1shr (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    𝔇.cechToCshr g ∈ (𝔇.holomorphicCoboundaries).Z1shr := by
  rw [HolomorphicCoboundaries.Z1shr, LinearMap.mem_ker]
  show 𝔇.delta1Model (𝔇.cechToCshr g) = 0
  ext t
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.WovTriple t
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl, delta1Model_apply_apply _ _ _ hz]
    obtain ⟨a, b, c⟩ := t
    -- the base point `x ∈ U a ⊓ U b ⊓ U c`, with `z = chart_a x`
    obtain ⟨x, hx, hxz⟩ := id hz
    have hxmem : x ∈ (𝔇.U a ⊓ 𝔇.U b ⊓ 𝔇.U c : Opens X) :=
      ⟨⟨𝔇.closure_shrinkSet_subset_U a (subset_closure hx.1.1),
        𝔇.closure_shrinkSet_subset_U b (subset_closure hx.1.2)⟩,
        𝔇.closure_shrinkSet_subset_U c (subset_closure hx.2)⟩
    -- evaluate the three components
    rw [𝔇.cechToCshr_apply_toFun _ _ (𝔇.mapsTo_coverTransition_WovTriple_shrink a b c hz),
      𝔇.cechToCshr_apply_toFun _ _ (𝔇.WovTriple_subset_Wov_fst_trd a b c hz),
      𝔇.cechToCshr_apply_toFun _ _ (𝔇.WovTriple_subset_Wov_fst_snd a b c hz)]
    -- rewrite the chart-symm of each point to `x`
    have hza : (chartAt (H := ℂ) (𝔇.center a)).symm z = x := by
      rw [← hxz, (chartAt (H := ℂ) (𝔇.center a)).left_inv
        (𝔇.U_subset_chartAt_source a hxmem.1.1)]
    have hzb : (chartAt (H := ℂ) (𝔇.center b)).symm
        (𝔇.coverTransition a b z) = x := by
      rw [← hxz]; exact 𝔇.chartSymm_coverTransition_eq a b c hxmem
    rw [hza, hzb]
    -- `holoFn (g(b,c)) x - holoFn (g(a,c)) x + holoFn (g(a,b)) x = 0`
    rw [holoFn_cocycle_add 𝔇 g a b c hxmem]
    ring
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl,
      (𝔇.delta1Model (𝔇.cechToCshr g) t).zero_off z hz]

/-- **The forward map corestricted to `Z1shr`** `↥(cocycles1 0) →ₗ[ℂ] Z1shr`. -/
noncomputable def cechToZ1shr :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) →ₗ[ℂ] (𝔇.holomorphicCoboundaries).Z1shr :=
  (𝔇.cechToCshr).codRestrict (𝔇.holomorphicCoboundaries).Z1shr 𝔇.cechToCshr_mem_Z1shr

@[simp] theorem cechToZ1shr_coe (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    ((𝔇.cechToZ1shr g : (𝔇.holomorphicCoboundaries).Z1shr) : 𝔇.overlapData.Cshr)
      = 𝔇.cechToCshr g := rfl

/-! ### The diagonal atom and the descent of coboundaries to `range δ` -/

/-- `U a ⊆ (chartAt (center a)).source`. -/
theorem U_subset_source (a : 𝔇.ι) :
    ((𝔇.U a : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center a)).source :=
  𝔇.U_subset_chartAt_source a

/-- `closure (Wov (a,a)) ⊆ chartAt (center a) '' (U a)` — the diagonal relatively-compact nesting. -/
theorem closure_Wov_diag_subset_chartImage_U (a : 𝔇.ι) :
    closure (𝔇.Wov (a, a)) ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.U a : Opens X) : Set X) := by
  refine (𝔇.closure_Wov_subset_Uov (a, a)).trans ?_
  show 𝔇.Uov (a, a) ⊆ _
  exact Set.image_mono (fun _ hx => hx.1)

/-- **The diagonal atom.**  A germ section `η ∈ OmegaDGerm 0 (U a)`, read through chart `center a` and
restricted to the diagonal shrinking `Wov (a,a)`, is a `BddHol (Wov (a,a))`.  Value:
`holoFn hη ∘ (chartAt (center a)).symm`. -/
noncomputable def diagAtom (a : 𝔇.ι) {η : MGerm (𝔇.U a)}
    (hη : η ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a)) :
    BddHol (𝔇.Wov (a, a)) :=
  holoSectionToBddHol (𝔇.U_subset_source a)
    (fun _x hx => gextLimRep_chart_analyticAt (holoRep_mem hη) hx)
    (𝔇.closure_Wov_diag_subset_chartImage_U a) (𝔇.isCompact_closure_Wov (a, a))

@[simp] theorem diagAtom_toFun_of_mem (a : 𝔇.ι) {η : MGerm (𝔇.U a)}
    (hη : η ∈ OmegaDGerm (0 : Divisor X) (𝔇.U a)) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, a)) :
    (𝔇.diagAtom a hη).toFun z = holoFn hη ((chartAt (H := ℂ) (𝔇.center a)).symm z) :=
  holoSectionToBddHol_toFun_of_mem _ _ _ _ hz

/-- For `z ∈ Wov (a,b)`, the chart-`a` preimage lies in `U a` (the `a`-side ball). -/
theorem chartSymm_mem_U_fst (a b : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, b)) :
    (chartAt (H := ℂ) (𝔇.center a)).symm z ∈ ((𝔇.U a : Opens X) : Set X) :=
  (𝔇.chartSymm_mem_overlap a b hz).1

/-- For `z ∈ Wov (a,b)`, the chart-`b` preimage of `τ_{ab} z` lies in `U b` (the `b`-side ball). -/
theorem chartSymm_coverTransition_mem_U_snd (a b : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, b)) :
    (chartAt (H := ℂ) (𝔇.center b)).symm (𝔇.coverTransition a b z)
      ∈ ((𝔇.U b : Opens X) : Set X) := by
  obtain ⟨x, ⟨hxa, hxb⟩, rfl⟩ := hz
  have hxbU : x ∈ ((𝔇.U b : Opens X) : Set X) :=
    𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  rw [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src,
    (chartAt (H := ℂ) (𝔇.center b)).left_inv (𝔇.U_subset_chartAt_source b hxbU)]
  exact hxbU

/-- The `b`-side transition point `(chart_b).symm (τ_{ab} z)` equals the `a`-side preimage
`(chart_a).symm z` for `z ∈ Wov (a,b)` (both `= x`). -/
theorem chartSymm_coverTransition_eq_chartSymm (a b : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Wov (a, b)) :
    (chartAt (H := ℂ) (𝔇.center b)).symm (𝔇.coverTransition a b z)
      = (chartAt (H := ℂ) (𝔇.center a)).symm z := by
  obtain ⟨x, ⟨hxa, hxb⟩, rfl⟩ := hz
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  have hxbU : x ∈ ((𝔇.U b : Opens X) : Set X) :=
    𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)
  have hxaU : x ∈ ((𝔇.U a : Opens X) : Set X) :=
    𝔇.closure_shrinkSet_subset_U a (subset_closure hxa)
  rw [𝔇.coverTransition_apply a b ⟨hxaU, hxbU⟩,
    (chartAt (H := ℂ) (𝔇.center b)).left_inv (𝔇.U_subset_chartAt_source b hxbU),
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src]

/-- **The forward map sends a germ coboundary to `δ⁰` of a diagonal `C0Holo` cochain.**  If `g` is the
germ coboundary `cechDelta0 η₀` of a germ 0-cochain `η₀ ∈ sections0 0`, then
`cechToCshr g = δ0 (fun a => diagAtom a (η₀ a))` — so `cechToCshr g ∈ range δ`.

Pointwise on `Wov (a,b)`: `(cechToCshr g)_{ab}(z) = holoFn(g_{ab}) x = holoFn(η₀ b) x − holoFn(η₀ a) x`
(`holoFn_restrict` + `holoFn_sub`, `x = (chart_a).symm z`), and `(δ0 f)_{ab}(z) = f_b(τ z) − f_a(z) =
holoFn(η₀ b)((chart_b).symm (τ z)) − holoFn(η₀ a) x = holoFn(η₀ b) x − holoFn(η₀ a) x` (the transition
point identity). -/
theorem cechToCshr_coboundary_eq_delta0 (η₀ : 𝔇.toFiniteCover.Cochain0)
    (hη₀ : η₀ ∈ 𝔇.toFiniteCover.sections0 (0 : Divisor X))
    (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (hgeq : (g : 𝔇.toFiniteCover.Cochain1) = 𝔇.toFiniteCover.cechDelta0 η₀) :
    𝔇.cechToCshr g
      = (𝔇.holomorphicCoboundaries).δ0 (fun a => 𝔇.diagAtom a (hη₀ a)) := by
  ext p
  apply BddHol.toFun_injective
  funext z
  obtain ⟨a, b⟩ := p
  by_cases hz : z ∈ 𝔇.Wov (a, b)
  · -- LHS
    rw [𝔇.cechToCshr_apply_toFun _ _ hz]
    -- the cocycle component is the germ coboundary `rawRestrictG (η₀ b) − rawRestrictG (η₀ a)`
    have hcomp : (g : 𝔇.toFiniteCover.Cochain1) (a, b)
        = rawRestrictG inf_le_right (η₀ b) - rawRestrictG inf_le_left (η₀ a) := by
      rw [hgeq]; rfl
    -- so `holoFn (g_{ab}) x = holoFn(η₀ b restricted) x − holoFn(η₀ a restricted) x`
    have hx : (chartAt (H := ℂ) (𝔇.center a)).symm z ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) :=
      𝔇.chartSymm_mem_overlap a b hz
    rw [holoFn_congr (cocycle_mem 𝔇 g a b)
      (sub_mem (rawRestrictG_omegaDGerm inf_le_right (hη₀ b))
        (rawRestrictG_omegaDGerm inf_le_left (hη₀ a))) hcomp hx,
      holoFn_sub (rawRestrictG_omegaDGerm inf_le_right (hη₀ b))
        (rawRestrictG_omegaDGerm inf_le_left (hη₀ a)) _ hx,
      holoFn_restrict inf_le_right (hη₀ b) hx, holoFn_restrict inf_le_left (hη₀ a) hx]
    -- RHS: `δ0 (diagAtom ...) = diagAtom_b(τ z) − diagAtom_a(z)`
    show _ = (𝔇.delta0Model (fun a => 𝔇.diagAtom a (hη₀ a)) (a, b)).toFun z
    rw [𝔇.delta0Model_apply_apply _ _ hz,
      𝔇.diagAtom_toFun_of_mem b (hη₀ b) (𝔇.mapsTo_coverTransition_Wov a b hz),
      𝔇.diagAtom_toFun_of_mem a (hη₀ a) (𝔇.Wov_subset_Wov_diag_fst a b hz),
      𝔇.chartSymm_coverTransition_eq_chartSymm a b hz]
  · -- off `Wov (a,b)` both sides are `0`
    rw [(𝔇.cechToCshr g (a, b)).zero_off z hz]
    show _ = (𝔇.delta0Model (fun a => 𝔇.diagAtom a (hη₀ a)) (a, b)).toFun z
    rw [(𝔇.delta0Model (fun a => 𝔇.diagAtom a (hη₀ a)) (a, b)).zero_off z hz]

/-! ### The descended comparison map `cechH1 𝔇 0 → supH1` and injectivity -/

/-- The composite `↥(cocycles1 0) → Z1shr → supH1` (the forward map followed by the `supH1`
quotient). -/
noncomputable def cechToSupH1 :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) →ₗ[ℂ] (𝔇.holomorphicCoboundaries).supH1 :=
  (Submodule.mkQ _).comp 𝔇.cechToZ1shr

theorem cechToSupH1_apply (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    𝔇.cechToSupH1 g = Submodule.Quotient.mk (𝔇.cechToZ1shr g) := rfl

/-- **The forward map kills germ coboundaries** (well-definedness of the descent): the submodule of
cocycles that are germ coboundaries is contained in `ker cechToSupH1`.  An element is a germ coboundary
`cechDelta0 η₀`, so its forward image is `δ0 (diagAtom ...) ∈ range δ`
(`cechToCshr_coboundary_eq_delta0`), hence `0` in `supH1`. -/
theorem coboundaries_le_ker_cechToSupH1 :
    (𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
        (𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) ≤ LinearMap.ker 𝔇.cechToSupH1 := by
  intro g hg
  -- `g`'s underlying cochain is a germ coboundary `cechDelta0 η₀`, `η₀ ∈ sections0 0`
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    FiniteFamily.coboundaries1, Submodule.mem_map] at hg
  obtain ⟨η₀, hη₀, hηeq⟩ := hg
  rw [LinearMap.mem_ker, cechToSupH1_apply, Submodule.Quotient.mk_eq_zero]
  -- `cechToZ1shr g = δ (diagAtom ...)`, which lies in `range δ`
  refine ⟨fun a => 𝔇.diagAtom a (hη₀ a), ?_⟩
  apply Subtype.ext
  show (𝔇.holomorphicCoboundaries).δ (fun a => 𝔇.diagAtom a (hη₀ a)) = 𝔇.cechToCshr g
  rw [HolomorphicCoboundaries.δ, ContinuousLinearMap.coe_codRestrict_apply]
  exact (𝔇.cechToCshr_coboundary_eq_delta0 η₀ hη₀ g hηeq.symm).symm

/-- **The descended comparison map** `cechH1 𝔇 0 →ₗ[ℂ] supH1` (the forward germ→`BddHol` cochain map,
descended to the cohomology quotients via `coboundaries_le_ker_cechToSupH1`). -/
noncomputable def comparisonMap :
    𝔇.toFiniteCover.cechH1 (0 : Divisor X) →ₗ[ℂ] (𝔇.holomorphicCoboundaries).supH1 :=
  Submodule.liftQ _ 𝔇.cechToSupH1 𝔇.coboundaries_le_ker_cechToSupH1

theorem comparisonMap_mk (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    𝔇.comparisonMap (Submodule.Quotient.mk g) = 𝔇.cechToSupH1 g :=
  Submodule.liftQ_apply _ _ _

/-! #### The shrinking cover `(V a)` and Forster-12.4 injectivity

`comparisonMap` injectivity reduces, by germ-class `𝒪_D` sheaf-gluing (Forster 12.4), to: a germ
cocycle `g` whose forward `BddHol` image is a `supH1`-coboundary `δ0 f` (`f : C0Holo`,
bounded-holomorphic on the diagonal shrinkings `Wov (a,a) = chartAt (center a) '' (V a)`) is a germ
coboundary.  The shrinking sets `V a := shrinkSet a` form a `FiniteCover` refining `𝔇`
(`iUnion_shrinkSet_eq_univ` + `shrinkSet ⊆ U`), and `f` pulls back to a germ 0-cochain `η a = [ζ_a]`
(`bddHolToOmegaDGerm`) on `V a` with `refineC1 g = δ⁰_𝔙 η` (pointwise via `holoFn`/`toGerm_holoFn` and
the transition point identity).  Then `refinementDescend_unconditional` (Forster 12.4) gives
`g ∈ coboundaries1 𝔇`. -/

/-- `Wov (a,a) = chartAt (center a) '' (V a)` (the diagonal shrinking IS the chart-image of `V a`). -/
theorem Wov_diag_eq_chartImage_shrinkOpens (a : 𝔇.ι) :
    𝔇.Wov (a, a) = (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a : Opens X) : Set X) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' (𝔇.shrinkSet a ∩ 𝔇.shrinkSet a) = _
  rw [Set.inter_self, shrinkOpens_coe]

/-- `chart_a '' (V a) ⊆ Wov (a,a)` (in fact equal). -/
theorem chartImage_shrinkOpens_subset_Wov_diag (a : 𝔇.ι) :
    (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a : Opens X) : Set X) ⊆ 𝔇.Wov (a, a) :=
  (𝔇.Wov_diag_eq_chartImage_shrinkOpens a).ge

/-- The diagonal `C0Holo` element `f a`, restricted to the exact chart-image `chart_a '' (V a)` (which
equals `Wov (a,a)`).  Avoids a propositional set-equality cast in `diagPullbackGerm`. -/
noncomputable def diagRestrict (f : 𝔇.C0Holo) (a : 𝔇.ι) :
    BddHol ((chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a : Opens X) : Set X)) :=
  BddHol.restrictOpenCLM (𝔇.chartImage_shrinkOpens_subset_Wov_diag a) (f a)

theorem diagRestrict_toFun_of_mem (f : 𝔇.C0Holo) (a : 𝔇.ι) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a : Opens X) : Set X)) :
    (𝔇.diagRestrict f a).toFun z = (f a).toFun z :=
  BddHol.restrictOpenCLM_toFun_of_mem _ _ hz

/-- The germ section `ζ_a := [f_a ∘ chart_a]` on `V a` from a diagonal `C0Holo` element `f`
(`bddHolToOmegaDGerm` on the exact chart-image `chart_a '' (V a)`). -/
noncomputable def diagPullbackGerm (f : 𝔇.C0Holo) (a : 𝔇.ι) :
    ↥(OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a)) :=
  bddHolToOmegaDGerm_zero_image (y := 𝔇.center a) (V := 𝔇.shrinkOpens a)
    (𝔇.shrinkOpens_subset_source a) (𝔇.diagRestrict f a)

theorem diagPullbackGerm_holoFn (f : 𝔇.C0Holo) (a : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.shrinkOpens a : Opens X)) :
    holoFn (𝔇.diagPullbackGerm f a).2 y
      = (f a).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) := by
  -- the representative `F` of `diagPullbackGerm` is `(diagRestrict f a) ∘ chart_a`
  set g' := 𝔇.diagRestrict f a with hg'
  set F : ↥(𝔇.shrinkOpens a) → ℂ :=
    fun x => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) x.1) with hF
  have hgerm : toGerm (𝔇.shrinkOpens a) F = (𝔇.diagPullbackGerm f a).1 := rfl
  have hmem : (chartAt (H := ℂ) (𝔇.center a)) y
      ∈ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a : Opens X) : Set X) := ⟨y, hy, rfl⟩
  -- `g'.toFun (chart_a y) = (f a).toFun (chart_a y)` (`diagRestrict` agrees on the image)
  have hval : g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y)
      = (f a).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) :=
    𝔇.diagRestrict_toFun_of_mem f a hmem
  -- `Gext F` is continuous at `y` (analytic `g'` ∘ chart), agreeing with `F`-value near `y`
  have hcont : ContinuousAt (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) y := by
    refine (g'.analyticOn.continuousOn.continuousAt ?_).comp
      ((chartAt (H := ℂ) (𝔇.center a)).continuousAt (𝔇.shrinkOpens_subset_source a hy))
    exact ((chartAt (H := ℂ) (𝔇.center a)).isOpen_image_of_subset_source
      (𝔇.shrinkOpens a).isOpen (𝔇.shrinkOpens_subset_source a)).mem_nhds hmem
  have hev : Gext F =ᶠ[nhds y]
      (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) := by
    filter_upwards [(𝔇.shrinkOpens a).isOpen.mem_nhds hy] with z hz
    rw [Gext_apply_mem F hz]
  have htend : Filter.Tendsto (Gext F) (𝓝[≠] y)
      (𝓝 (g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y))) :=
    Filter.Tendsto.congr' (hev.filter_mono nhdsWithin_le_nhds).symm
      ((hcont.tendsto).mono_left nhdsWithin_le_nhds)
  rw [← hval]
  exact holoFn_eq_of_tendsto (𝔇.diagPullbackGerm f a).2 F hgerm hy htend

/-- The germ section `diagPullbackGerm f a` is `𝒪_0` on `V a`. -/
theorem diagPullbackGerm_mem (f : 𝔇.C0Holo) (a : 𝔇.ι) :
    (𝔇.diagPullbackGerm f a).1 ∈ OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a) :=
  (𝔇.diagPullbackGerm f a).2

/-- For `v ∈ V a ⊓ V b`, the chart-`a` value `chartAt (center a) v ∈ Wov (a,b)`. -/
theorem chart_mem_Wov_of_shrinkInter (a b : 𝔇.ι) {v : X}
    (hv : v ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X)) :
    (chartAt (H := ℂ) (𝔇.center a)) v ∈ 𝔇.Wov (a, b) :=
  ⟨v, ⟨hv.1, hv.2⟩, rfl⟩

/-- **The key germ identity for injectivity.**  If `δ0 f = cechToCshr g`, then on each shrinking
overlap `V a ⊓ V b` the germ `g_{ab}` (restricted) equals `[ζ_b] − [ζ_a]` (the diagonal pullback
germs), i.e. `refineC1 g = δ⁰_𝔙 (diagPullbackGerm f)`.  Pointwise via `holoFn`/`diagPullbackGerm_holoFn`
and the transition point identity. -/
theorem refineC1_eq_delta0_shrink (g : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (f : 𝔇.C0Holo) (hf : (𝔇.holomorphicCoboundaries).δ0 f = 𝔇.cechToCshr g) :
    (𝔇.isRefinement_shrinkCover).refineC1 (g : 𝔇.toFiniteCover.Cochain1)
      = 𝔇.shrinkCover.cechDelta0 (fun a => (𝔇.diagPullbackGerm f a).1) := by
  funext p
  obtain ⟨a, b⟩ := p
  -- both sides are germs on `V a ⊓ V b`; reduce to a pointwise function identity via `toGerm_holoFn`
  rw [FiniteCover.IsRefinement.refineC1_apply]
  show rawRestrictG (𝔇.isRefinement_shrinkCover.pair_le a b) ((g : 𝔇.toFiniteCover.Cochain1) (a, b))
      = (rawRestrictG inf_le_right ((𝔇.diagPullbackGerm f b).1)
          - rawRestrictG inf_le_left ((𝔇.diagPullbackGerm f a).1))
  -- LHS = germ of `holoFn(g_{ab})` restricted to `V a ⊓ V b`
  rw [← toGerm_holoFn (cocycle_mem 𝔇 g a b)]
  -- RHS = germ of `ζ_b − ζ_a` (= `holoFn(diagPullbackGerm f ·)`) restricted to `V a ⊓ V b`
  rw [← toGerm_holoFn (𝔇.diagPullbackGerm_mem f b), ← toGerm_holoFn (𝔇.diagPullbackGerm_mem f a)]
  simp only [rawRestrictG_coe, id_eq, shrinkCover_U]
  rw [← map_sub, toGerm_eq_iff]
  -- the two representatives are EQUAL at every point of `V a ⊓ V b`, hence germ-equal at each `u`
  intro _u
  refine Filter.Eventually.of_forall ?_
  rintro ⟨v, hv⟩
  show holoFn (cocycle_mem 𝔇 g a b) ((openIncl _ ⟨v, hv⟩ : ↥(𝔇.U a ⊓ 𝔇.U b)) : X)
      = (fun w : ↥(𝔇.shrinkOpens b) => holoFn (𝔇.diagPullbackGerm_mem f b) w.1)
          (openIncl inf_le_right ⟨v, hv⟩)
        - (fun w : ↥(𝔇.shrinkOpens a) => holoFn (𝔇.diagPullbackGerm_mem f a) w.1)
          (openIncl inf_le_left ⟨v, hv⟩)
  simp only [openIncl]
  -- `v ∈ V a ⊓ V b`, hence in `U a ⊓ U b` and in each `V a`, `V b`
  have hva : v ∈ (𝔇.shrinkOpens a : Opens X) := hv.1
  have hvb : v ∈ (𝔇.shrinkOpens b : Opens X) := hv.2
  have hvU : v ∈ ((𝔇.U a ⊓ 𝔇.U b : Opens X) : Set X) :=
    ⟨𝔇.shrinkOpens_le_U a hva, 𝔇.shrinkOpens_le_U b hvb⟩
  -- evaluate `holoFn(ζ_a)`, `holoFn(ζ_b)`
  rw [𝔇.diagPullbackGerm_holoFn f a hva, 𝔇.diagPullbackGerm_holoFn f b hvb]
  -- the `δ0 f = cechToCshr g` identity at `z = chart_a v ∈ Wov (a,b)`
  have hzW : (chartAt (H := ℂ) (𝔇.center a)) v ∈ 𝔇.Wov (a, b) :=
    𝔇.chart_mem_Wov_of_shrinkInter a b hv
  have hδ := congrFun (congrArg (fun (s : 𝔇.overlapData.Cshr) => (s (a, b)).toFun) hf)
    ((chartAt (H := ℂ) (𝔇.center a)) v)
  simp only [show (𝔇.holomorphicCoboundaries).δ0 f = 𝔇.delta0Model f from rfl] at hδ
  -- LHS of `hδ`: `(δ0 f)_{ab}(z) = f_b(τ z) − f_a(z)`; RHS: `holoFn(g_{ab})((chart_a).symm z)`
  rw [𝔇.delta0Model_apply_apply f (a, b) hzW, 𝔇.cechToCshr_apply_toFun g (a, b) hzW,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv (𝔇.U_subset_source a hvU.1),
    𝔇.coverTransition_apply a b ⟨hvU.1, hvU.2⟩] at hδ
  -- assemble: `holoFn(g_{ab}) v = (f b).toFun(chart_b v) − (f a).toFun(chart_a v)`
  rw [← hδ]

/-- **Injectivity of the comparison map** (Forster 12.4 sheaf-gluing).  `comparisonMap (mk g) = 0`
gives `δ0 f = cechToCshr g` for some `f : C0Holo`; then `refineC1 g = δ⁰_𝔙 (diagPullbackGerm f)`
(`refineC1_eq_delta0_shrink`) so `refineC1 g` is a `𝔙`-coboundary, and Forster 12.4
(`refinementDescend_unconditional`) gives `g ∈ coboundaries1 𝔇`, i.e. `mk g = 0`. -/
theorem comparisonMap_injective : Function.Injective 𝔇.comparisonMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro fcl hfcl
  -- write `fcl = mk g`
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ fcl
  rw [LinearMap.mem_ker, comparisonMap_mk, cechToSupH1_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range] at hfcl
  obtain ⟨f, hf⟩ := hfcl
  -- `δ f = cechToZ1shr g`, i.e. `δ0 f = cechToCshr g`
  have hf0 : (𝔇.holomorphicCoboundaries).δ0 f = 𝔇.cechToCshr g := by
    have hval := congrArg (Subtype.val) hf
    rw [𝔇.cechToZ1shr_coe g] at hval
    simpa only [HolomorphicCoboundaries.δ, ContinuousLinearMap.coe_codRestrict_apply] using hval
  -- `refineC1 g` is a `𝔙`-coboundary
  have hcob : (𝔇.isRefinement_shrinkCover).refineC1 (g : 𝔇.toFiniteCover.Cochain1)
      ∈ 𝔇.shrinkCover.coboundaries1 (0 : Divisor X) := by
    rw [FiniteFamily.coboundaries1, Submodule.mem_map]
    exact ⟨fun a => (𝔇.diagPullbackGerm f a).1, fun a => (𝔇.diagPullbackGerm f a).2,
      (𝔇.refineC1_eq_delta0_shrink g f hf0).symm⟩
  -- Forster 12.4: `g ∈ coboundaries1 𝔇`
  have hgcob : (g : 𝔇.toFiniteCover.Cochain1) ∈ 𝔇.toFiniteCover.coboundaries1 (0 : Divisor X) :=
    FiniteCover.IsRefinement.refinementDescend_unconditional (0 : Divisor X)
      𝔇.isRefinement_shrinkCover g hcob
  -- hence `mk g = 0`
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  exact hgcob

/-! ## §C — The finiteness reduction (injective variant) and the COMPLETE theorem -/

/-- **The finiteness reduction via a linear INJECTION** (lighter than the full iso of
`finiteDimensional_cechH1_of_holomorphicModel`).  Given a `HolomorphicCoboundaries` model `c` for the
chart-disk cover with its `supH1` finite (via `leray`), a linear injection `cechH1 𝔇 0 ↪ c.supH1`
suffices to conclude `cechH1 𝔇 0` finite (`FiniteDimensional.of_injective`). -/
theorem finiteDimensional_cechH1_of_holomorphicModel_inj
    (c : HolomorphicCoboundaries 𝔇.overlapData)
    (f : 𝔇.toFiniteCover.cechH1 (0 : Divisor X) →ₗ[ℂ] c.supH1) (hf : Function.Injective f) :
    FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) := by
  haveI : FiniteDimensional ℂ c.supH1 :=
    c.finiteDimensional_supH1 (HolomorphicCoboundaries.leray_surjective 𝔇.overlapData c)
  exact FiniteDimensional.of_injective f hf

/-- **`H¹` finiteness on a chart-disk cover (Forster 14.9) — the COMPLETE statement.**
`FiniteDimensional ℂ (cechH1 𝔇 0)` for a `ChartDiskCover 𝔇`.

The δ-complex + comparison that `ChartDiskFiniteness.lean` leaves open are BUILT here: the model
`𝔇.holomorphicCoboundaries` (δ-data of §A; the `leray` field discharged in §A2-*) and
the injection `𝔇.comparisonMap` (forward germ→`BddHol` cochain map of §B).

This theorem is SORRY-FREE and axiom-clean (`propext, Classical.choice, Quot.sound`): the entire
δ-complex, the `leray` lift (Forster 14.6, global Bott–Tu form route — see `holomorphicCoboundaries`),
the comparison `comparisonMap` and its injectivity (Forster 12.4 sheaf-gluing), and this assembly are
all proven. -/
theorem finiteDimensional_cechH1_chartDisk_complete [Nonempty X] :
    FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) :=
  𝔇.finiteDimensional_cechH1_of_holomorphicModel_inj 𝔇.holomorphicCoboundaries
    𝔇.comparisonMap 𝔇.comparisonMap_injective

end ChartDiskCover

end Jacobians.Dolbeault
