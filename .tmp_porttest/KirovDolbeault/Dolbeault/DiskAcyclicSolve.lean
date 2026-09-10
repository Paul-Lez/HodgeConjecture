/-
  Dolbeault ladder — **Forster 13.4**: genuine disk-acyclicity `H¹(disk, 𝒪) = 0` for a shared-chart
  cover whose chart-images fill the ball, built from the open-disk ∂̄-solver (Forster 13.2,
  `DbarOpenDisk.dbar_solvable_open_disk`).

  This is the sound replacement for the stalled `HasGluedDbarDatum` route: instead of a Bott–Tu
  partition-of-unity datum (which sums to `1` only on a closed core), we use the **open-union**
  partition of unity `coverOpenUnionPoU` (which sums to `1` on all of `↥(⋃Uᵢ)`), whose chart-read
  primitive `openChartPrim` therefore telescopes on EVERY overlap. Its `∂̄` glues to a datum smooth on
  the union's chart-image; when that image is the full ball, Forster 13.2 solves `∂̄u = ω` there, and
  `η̂ᵢ = openChartPrimᵢ − u` are the holomorphic correctors that `analyticAt_compChart_of_differentiableOn`
  turns into `HasChartAnalyticCorrectors` ⟹ `H¹(disk,𝒪)=0`.
-/
import KirovDolbeault.Dolbeault.CechFinitenessBallSolve
import KirovDolbeault.Dolbeault.DbarOpenDisk

open scoped Manifold ContDiff Topology
open Complex Metric Filter
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault
namespace SharedChartCover

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- If `z` is in the chart-image of the open union, its chart-preimage lands in the open union. -/
theorem symm_mem_openUnionU (𝔇 : SharedChartCover X) {z : ℂ} (hz : z ∈ openUnionChartImage 𝔇) :
    (𝔇.φ).symm z ∈ openUnionU 𝔇 := by
  rcases hz with ⟨x, hxU, hxz⟩
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := by
    rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩; exact 𝔇.subset_source j hxj
  have hsymm : (chartAt (H := ℂ) 𝔇.center).symm z = x := by
    simpa [hxz] using (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  show (chartAt (H := ℂ) 𝔇.center).symm z ∈ (openUnionU 𝔇 : Set X)
  rw [hsymm]; exact hxU

/-- The chart-read of the open-union primitive (`ℂ → ℂ`, junk off the union's chart-image). -/
noncomputable def openChartPrim (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) : ℂ → ℂ := by
  classical
  exact fun z => if h : z ∈ openUnionChartImage 𝔇 then
    openUnionCoverPrim 𝔇 s i ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 h⟩ else 0

/-- On the union's chart-image, `openChartPrim` reads the open-union primitive. -/
theorem openChartPrim_apply_mem (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) {z : ℂ}
    (hz : z ∈ openUnionChartImage 𝔇) :
    openChartPrim 𝔇 s i z = openUnionCoverPrim 𝔇 s i ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 hz⟩ := by
  simp only [openChartPrim, hz, dif_pos]

/-- **The chart-read difference identity** (holds on EVERY overlap, since the open-union PoU sums to
`1` everywhere — no closed-core restriction).  For `x ∈ Uᵢ ⊓ Uⱼ`,
`openChartPrimⱼ(φx) − openChartPrimᵢ(φx) = holoFn(sᵢⱼ) x`. -/
theorem openChartPrim_diff (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i j : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X)) :
    openChartPrim 𝔇 s j (𝔇.φ x) - openChartPrim 𝔇 s i (𝔇.φ x)
      = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) x := by
  have hxU : x ∈ ⋃ k, (𝔇.U k : Set X) := Set.mem_iUnion.mpr ⟨i, hx.1⟩
  have hxim : 𝔇.φ x ∈ openUnionChartImage 𝔇 := ⟨x, hxU, rfl⟩
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hx.1
  have hsymm : (𝔇.φ).symm (𝔇.φ x) = x := (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  rw [openChartPrim_apply_mem 𝔇 s j hxim, openChartPrim_apply_mem 𝔇 s i hxim]
  have hpt : (⟨(𝔇.φ).symm (𝔇.φ x), symm_mem_openUnionU 𝔇 hxim⟩ : ↥(openUnionU 𝔇))
      = ⟨x, hxU⟩ := Subtype.ext hsymm
  rw [hpt]
  exact openUnionCoverPrim_diff 𝔇 s i j (x := ⟨x, hxU⟩) hx

/-! ## Step 1 — `openChartPrim` is real-`C^∞` on `Ω_i`

The chart-read open-union primitive is `ContDiffAt ℝ ⊤` at every point of `Ω_i = φ '' U_i`.  We
transfer the manifold smoothness `contMDiffAt_openUnionCoverPrim` (on the open submanifold
`↥(openUnionU 𝔇)`) through the chart `φ.symm` and the open-submanifold inclusion: the lift
`z ↦ ⟨φ.symm z, _⟩` is `ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ)` (its `Subtype.val`-composition is `φ.symm`, smooth
by `contMDiffOn_chart_symm`, so `contMDiffAt_subtype_iff` lifts it into the subtype), and `openChartPrim`
equals `openUnionCoverPrim ∘ lift` near `φ x` (where `φ x ∈ openUnionChartImage`, an open set). -/

/-- The chart-image of the open union is open in `ℂ` (`φ` is an `OpenPartialHomeomorph` and
`openUnionU 𝔇 ⊆ φ.source`). -/
theorem isOpen_openUnionChartImage (𝔇 : SharedChartCover X) :
    IsOpen (openUnionChartImage 𝔇) := by
  refine (chartAt (H := ℂ) 𝔇.center).isOpen_image_of_subset_source (openUnionU 𝔇).isOpen ?_
  rintro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  exact 𝔇.subset_source j hxj

/-- The chart-image of the open union sits inside the chart target. -/
theorem openUnionChartImage_subset_target (𝔇 : SharedChartCover X) :
    openUnionChartImage 𝔇 ⊆ (𝔇.φ).target := by
  rintro z ⟨x, hxU, rfl⟩
  rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩
  exact (𝔇.φ).map_source (𝔇.subset_source j hxj)

/-- The lift `ℂ → ↥(openUnionU 𝔇)`, `z ↦ ⟨φ.symm z, _⟩` on the open-union chart image, junking to a
supplied basepoint `p` elsewhere.  Only its germ near a point of `openUnionChartImage` is used; the
basepoint makes it total without a separate inhabitation argument. -/
noncomputable def liftSymm (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) (z : ℂ) :
    ↥(openUnionU 𝔇) := by
  classical
  exact if h : z ∈ openUnionChartImage 𝔇 then ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 h⟩ else p

/-- On the open-union chart image, `liftSymm` is the genuine chart-preimage lift. -/
theorem liftSymm_apply_mem (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) {z : ℂ}
    (hz : z ∈ openUnionChartImage 𝔇) :
    liftSymm 𝔇 p z = ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 hz⟩ := by
  simp only [liftSymm, hz, dif_pos]

/-- **`liftSymm` is `ContMDiffAt`** at every point of the (open) open-union chart image.  Its
`Subtype.val`-composition equals `φ.symm` near `z₀` (`liftSymm_apply_mem` on the open
`openUnionChartImage`), which is `ContMDiffAt` (chart-symm smoothness); `contMDiffAt_subtype_iff`
lifts it into the subtype. -/
theorem contMDiffAt_liftSymm (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ openUnionChartImage 𝔇) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (liftSymm 𝔇 p) z₀ := by
  have hz₀tgt : z₀ ∈ (𝔇.φ).target := openUnionChartImage_subset_target 𝔇 hz₀
  -- `φ.symm` is `ContMDiffAt` at `z₀`.
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (𝔇.φ).symm z₀ :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center) _ hz₀tgt).contMDiffAt
      ((𝔇.φ).open_target.mem_nhds hz₀tgt)
  -- `Subtype.val ∘ liftSymm =ᶠ[𝓝 z₀] φ.symm` (on the open chart image).
  have hval : (Subtype.val ∘ liftSymm 𝔇 p) =ᶠ[𝓝 z₀] (𝔇.φ).symm := by
    filter_upwards [(isOpen_openUnionChartImage 𝔇).mem_nhds hz₀] with z hz
    simp only [Function.comp_apply, liftSymm_apply_mem 𝔇 p hz]
  have hval' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (Subtype.val ∘ liftSymm 𝔇 p) z₀ :=
    hsymm.congr_of_eventuallyEq hval
  exact (ContMDiffAt.subtypeVal_comp_iff (openUnionU 𝔇) (liftSymm 𝔇 p) z₀).1 hval'

/-- **Step 1 — `openChartPrim 𝔇 s i` is `ContDiffAt ℝ ⊤` on `Ω_i`.**  For `x ∈ U_i`, the chart point
`φ x` lies in `openUnionChartImage`, where `openChartPrim 𝔇 s i = openUnionCoverPrim 𝔇 s i ∘ liftSymm`;
the lift is `ContMDiffAt` (`contMDiffAt_liftSymm`) and the open-union primitive is `ContMDiffAt` over
`U_i` (`contMDiffAt_openUnionCoverPrim`), so the composite is, and `contMDiffAt_iff_contDiffAt`
bridges to `ContDiffAt ℝ`. -/
theorem contDiffAt_openChartPrim (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) {x : X} (hx : x ∈ 𝔇.U i) :
    ContDiffAt ℝ (⊤ : ℕ∞) (openChartPrim 𝔇 s i) (𝔇.φ x) := by
  have hxU : (x : X) ∈ ⋃ k, (𝔇.U k : Set X) := Set.mem_iUnion.mpr ⟨i, hx⟩
  set p : ↥(openUnionU 𝔇) := ⟨x, hxU⟩ with hpdef
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hx
  have hxim : 𝔇.φ x ∈ openUnionChartImage 𝔇 := ⟨x, hxU, rfl⟩
  -- The lift `liftSymm 𝔇 p` is `ContMDiffAt` at `φ x`.
  have hlift : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (liftSymm 𝔇 p) (𝔇.φ x) :=
    contMDiffAt_liftSymm 𝔇 p hxim
  -- `liftSymm 𝔇 p (φ x) = ⟨x, hxU⟩ = p` (so the open-union primitive is smooth at the lift value).
  have hsymm_pt : (𝔇.φ).symm (𝔇.φ x) = x := (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  have hlift_pt : liftSymm 𝔇 p (𝔇.φ x) = p := by
    rw [liftSymm_apply_mem 𝔇 p hxim]; exact Subtype.ext hsymm_pt
  -- The open-union primitive is `ContMDiffAt` at `p` (point over `U_i`).
  have hprim : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (openUnionCoverPrim 𝔇 s i) p :=
    contMDiffAt_openUnionCoverPrim 𝔇 s i (x₀ := p) hx
  -- Compose, then read `openChartPrim = openUnionCoverPrim ∘ liftSymm` near `φ x`.
  have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (openUnionCoverPrim 𝔇 s i ∘ liftSymm 𝔇 p) (𝔇.φ x) :=
    (hlift_pt ▸ hprim).comp (𝔇.φ x) hlift
  have heq : openChartPrim 𝔇 s i =ᶠ[𝓝 (𝔇.φ x)] (openUnionCoverPrim 𝔇 s i ∘ liftSymm 𝔇 p) := by
    filter_upwards [(isOpen_openUnionChartImage 𝔇).mem_nhds hxim] with z hz
    rw [openChartPrim_apply_mem 𝔇 s i hz, Function.comp_apply, liftSymm_apply_mem 𝔇 p hz]
  exact contMDiffAt_iff_contDiffAt.1 (hcomp.congr_of_eventuallyEq heq)

/-! ## Step 2 — `∂̄ openChartPrim` agrees on overlaps

On `Ω_i ∩ Ω_j` the two chart-read primitives have the same `∂̄`: their difference equals the chart-read
`holoFn(s_{ij}) ∘ φ.symm`, which is holomorphic there (its `∂̄` vanishes).  We first record that
chart-read analytic representatives are `AnalyticAt ℂ` (replicating the `GluedDbarDatum.analyticAt_holoHat`
argument over the bare composite, since that file is not in this import cone), then conclude via
`dbar_sub` + `dbar_eq_zero_of_differentiableAt`. -/

/-- **The chart-read analytic representative is `AnalyticAt ℂ`.**  For `x ∈ U_a ⊓ U_b`,
`holoFn(s_{a,b}) ∘ φ.symm` is `AnalyticAt ℂ` at `φ x`: `holoFn(s_{a,b})` is chart-analytic in `x`'s own
chart (`holoFn_chart_analyticAt`); transport to the shared chart `φ` by the analytic transition map. -/
theorem analyticAt_holoFn_comp_symm (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (a b : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U a ⊓ 𝔇.toFiniteFamily.U b : Opens X)) :
    AnalyticAt ℂ (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) ∘ (𝔇.φ).symm) (𝔇.φ x) := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  have hsrc : x ∈ φ.source := 𝔇.subset_source a hx.1
  set h := holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) with hh
  -- `h` read in `x`'s OWN chart is analytic at `(chartAt x) x`.
  have hown : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x) :=
    holoFn_chart_analyticAt (cocycleComp_mem 𝔇.toFiniteFamily s a b) hx
  have hsymm_pt : φ.symm (φ x) = x := φ.left_inv hsrc
  have hxtgt : φ x ∈ φ.target := φ.map_source hsrc
  -- The transition `(chartAt x) ∘ φ.symm` is `AnalyticAt ℂ` at `φ x` (it maps `φ x ↦ (chartAt x) x`).
  have h_symm_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ.symm (φ x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := 𝔇.center)) _ hxtgt).contMDiffAt
      (φ.open_target.mem_nhds hxtgt)
  have h_cx_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) x) (φ.symm (φ x)) := by
    rw [hsymm_pt]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x)) _ (mem_chart_source ℂ x)).contMDiffAt
      ((chartAt (H := ℂ) x).open_source.mem_nhds (mem_chart_source ℂ x))
  have htrans_ana : AnalyticAt ℂ ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) :=
    (contMDiffAt_iff_contDiffAt.1 (h_cx_cmd.comp (φ x) h_symm_cmd)).analyticAt
  have htrans_pt : ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) = (chartAt (H := ℂ) x) x := by
    simp only [Function.comp_apply, hsymm_pt]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) (φ x) :=
    AnalyticAt.comp (htrans_pt ▸ hown) htrans_ana
  -- Near `φ x`, `h ∘ φ.symm` equals that composite (where `φ.symm` lands in `(chartAt x).source`).
  have hmem : ∀ᶠ w in 𝓝 (φ x), φ.symm w ∈ (chartAt (H := ℂ) x).source := by
    have hcont : ContinuousAt φ.symm (φ x) := φ.continuousAt_symm hxtgt
    have hh0 : φ.symm (φ x) ∈ (chartAt (H := ℂ) x).source := by
      rw [hsymm_pt]; exact mem_chart_source ℂ x
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hh0)
  have heq : (h ∘ φ.symm) =ᶠ[𝓝 (φ x)]
      ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
  exact (analyticAt_congr heq).2 hcomp

/-- If `z` lies in both chart-images `Ω_i` and `Ω_j`, its chart-preimage lands in the overlap
`U_i ⊓ U_j` (`φ` is injective on its source). -/
theorem symm_mem_overlap_of_mem_Ω (𝔇 : SharedChartCover X) {i j : 𝔇.ι} {z : ℂ}
    (hzi : z ∈ 𝔇.Ω i) (hzj : z ∈ 𝔇.Ω j) :
    (𝔇.φ).symm z ∈ (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X) := by
  obtain ⟨xi, hxi, hxiz⟩ := hzi
  obtain ⟨xj, hxj, hxjz⟩ := hzj
  have hsrci : xi ∈ (𝔇.φ).source := 𝔇.subset_source i hxi
  have hsrcj : xj ∈ (𝔇.φ).source := 𝔇.subset_source j hxj
  have hsymmi : (𝔇.φ).symm z = xi := by rw [← hxiz]; exact (𝔇.φ).left_inv hsrci
  have hsymmj : (𝔇.φ).symm z = xj := by rw [← hxjz]; exact (𝔇.φ).left_inv hsrcj
  refine ⟨?_, ?_⟩
  · rw [hsymmi]; exact hxi
  · rw [hsymmj]; exact hxj

/-- **Step 2 — `∂̄ openChartPrim` agrees on overlaps.**  For `z ∈ Ω_i ∩ Ω_j`,
`∂̄(openChartPrim s i) z = ∂̄(openChartPrim s j) z`.  The difference `openChartPrim j − openChartPrim i`
equals `holoFn(s_{ij}) ∘ φ.symm` near `z` (from `openChartPrim_diff`, read at `φ.symm`), which is
holomorphic there (`analyticAt_holoFn_comp_symm`), so its `∂̄` vanishes (`dbar_sub` +
`dbar_eq_zero_of_differentiableAt`). -/
theorem dbar_openChartPrim_agree (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i j : 𝔇.ι) {z : ℂ}
    (hzi : z ∈ 𝔇.Ω i) (hzj : z ∈ 𝔇.Ω j) :
    DbarDisk.dbar (openChartPrim 𝔇 s i) z = DbarDisk.dbar (openChartPrim 𝔇 s j) z := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  -- `x := φ.symm z ∈ U_i ⊓ U_j`, and `φ x = z`.
  set x : X := φ.symm z with hxdef
  have hxov : x ∈ (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X) :=
    symm_mem_overlap_of_mem_Ω 𝔇 hzi hzj
  obtain ⟨xi, hxi, hxiz⟩ := hzi
  have hsrc : xi ∈ φ.source := 𝔇.subset_source i hxi
  have hztgt : z ∈ φ.target := by rw [← hxiz]; exact φ.map_source hsrc
  have hφx : φ x = z := by rw [hxdef]; exact φ.right_inv hztgt
  -- `openChartPrim j w − openChartPrim i w = holoFn(s_{ij})(φ.symm w)` for `w` near `z`.
  have hdiffEq : (fun w => openChartPrim 𝔇 s j w - openChartPrim 𝔇 s i w)
      =ᶠ[𝓝 z] (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) ∘ φ.symm) := by
    -- Near `z`: `w ∈ φ.target` and `φ.symm w ∈ U_i ⊓ U_j` (both open conditions holding at `z`).
    have hcont : ContinuousAt φ.symm z := φ.continuousAt_symm hztgt
    have hovnhds : ∀ᶠ w in 𝓝 z, φ.symm w ∈
        (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X) :=
      hcont.preimage_mem_nhds
        ((𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X).isOpen.mem_nhds hxov)
    have htgtnhds : ∀ᶠ w in 𝓝 z, w ∈ φ.target := φ.open_target.mem_nhds hztgt
    filter_upwards [hovnhds, htgtnhds] with w hwov hwtgt
    -- `openChartPrim k w = openChartPrim k (φ (φ.symm w))`, then `openChartPrim_diff` at `φ.symm w`.
    have hwback : φ (φ.symm w) = w := φ.right_inv hwtgt
    have hd := openChartPrim_diff 𝔇 s i j (x := φ.symm w) hwov
    rw [hwback] at hd
    simpa only [Function.comp_apply] using hd
  -- `holoFn(s_{ij}) ∘ φ.symm` is `DifferentiableAt ℂ` at `z` (analytic), so its `∂̄` is `0`.
  have hana : AnalyticAt ℂ (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) ∘ φ.symm) z := by
    have := analyticAt_holoFn_comp_symm 𝔇 s i j hxov
    rwa [hφx] at this
  have hdiffC : DifferentiableAt ℂ (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) ∘ φ.symm) z :=
    hana.differentiableAt
  -- `openChartPrim k` is `ℝ`-differentiable at `z = φ x` (Step 1, `x ∈ U_k`).
  have hdi : DifferentiableAt ℝ (openChartPrim 𝔇 s i) z :=
    (hφx ▸ contDiffAt_openChartPrim 𝔇 s i (x := x) hxov.1).differentiableAt (by norm_num)
  have hdj : DifferentiableAt ℝ (openChartPrim 𝔇 s j) z :=
    (hφx ▸ contDiffAt_openChartPrim 𝔇 s j (x := x) hxov.2).differentiableAt (by norm_num)
  -- `∂̄(holoFn ∘ φ.symm) z = 0` (holomorphic), and `∂̄` of the difference equals it (`=ᶠ` congr).
  have hdb_holo : DbarDisk.dbar (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) ∘ φ.symm) z = 0 :=
    DbarDisk.dbar_eq_zero_of_differentiableAt hdiffC
  have hdb_diff_eq :
      DbarDisk.dbar (fun w => openChartPrim 𝔇 s j w - openChartPrim 𝔇 s i w) z
        = DbarDisk.dbar (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) ∘ φ.symm) z := by
    simp only [DbarDisk.dbar, hdiffEq.fderiv_eq]
  -- Assemble: `∂̄(openChartPrim i) z = ∂̄(openChartPrim j) z`.
  have hsubeq : DbarDisk.dbar (openChartPrim 𝔇 s j) z - DbarDisk.dbar (openChartPrim 𝔇 s i) z = 0 := by
    rw [← DbarOpenDisk.dbar_sub hdj hdi, hdb_diff_eq, hdb_holo]
  exact (sub_eq_zero.1 hsubeq).symm

/-! ## Step 3 — The glued `∂̄`-datum `ω`

`ω z = ∂̄(openChartPrim s i₀) z` for any `i₀` with `z ∈ Ω i₀` (well-defined by Step 2), junk off the
union's chart-image.  It is `ContDiffOn ℝ ⊤` on the ball: at `z₀ ∈ ball = openUnionChartImage = ⋃ Ω i`,
`z₀ ∈ Ω i₀`, and `ω =ᶠ[𝓝 z₀] ∂̄(openChartPrim i₀)` (Step 2 on the open `Ω i₀`), which is `ContDiffAt`
(∂̄ of the `C^∞` `openChartPrim i₀`, Step 1). -/

/-- **`∂̄` of a `C^∞`-at-`z` function is `C^∞` at `z`** (`∂̄g` is a fixed CLM-combination of `fderiv ℝ g`
evaluated at `1, I`; `fderiv ℝ g` is `C^∞` near `z`).  Local port of `GluedDbarDatum.contDiffAt_dbar`
(that file is not in this import cone). -/
theorem contDiffAt_dbar_local {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℝ (⊤ : ℕ∞) g z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (DbarDisk.dbar g) z := by
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ g) z :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (fderiv ℝ g w) (1 : ℂ)) z :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff.contDiffAt.comp z hfd
  have hI : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (fderiv ℝ g w) Complex.I) z :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.contDiffAt.comp z hfd
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (2 : ℂ)⁻¹ * ((fderiv ℝ g w) (1 : ℂ) + Complex.I * (fderiv ℝ g w) Complex.I)) z :=
    contDiffAt_const.mul (h1.add (contDiffAt_const.mul hI))
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by rw [DbarDisk.dbar])

/-- The open-union chart image is the union of the chart-images `Ω_i` (`φ '' (⋃ Uᵢ) = ⋃ (φ '' Uᵢ)`). -/
theorem openUnionChartImage_eq_iUnion_Ω (𝔇 : SharedChartCover X) :
    openUnionChartImage 𝔇 = ⋃ i, 𝔇.Ω i := by
  simp only [openUnionChartImage, openUnionU, Ω, Opens.coe_mk, Set.image_iUnion]

/-- **The glued `∂̄`-datum** `ω : ℂ → ℂ` — equals `∂̄(openChartPrim s i)` on each `Ω_i`, junk off the
union's chart-image. -/
noncomputable def gluedDatum (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) : ℂ → ℂ := by
  classical
  exact fun z => if h : ∃ i, z ∈ 𝔇.Ω i then
    DbarDisk.dbar (openChartPrim 𝔇 s h.choose) z else 0

/-- **`gluedDatum` reads `∂̄(openChartPrim s i)` on `Ω_i`** (well-defined by the Step-2 overlap
agreement). -/
theorem gluedDatum_apply (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.Ω i) :
    gluedDatum 𝔇 s z = DbarDisk.dbar (openChartPrim 𝔇 s i) z := by
  have hex : ∃ i, z ∈ 𝔇.Ω i := ⟨i, hz⟩
  simp only [gluedDatum, hex, dif_pos]
  exact dbar_openChartPrim_agree 𝔇 s hex.choose i hex.choose_spec hz

/-- **`gluedDatum` is `ContDiffOn ℝ ⊤` on the ball** (assuming the chart-images fill the ball).  At
`z₀ ∈ ball = openUnionChartImage = ⋃ Ω i`, `z₀ ∈ Ω i₀`, and `gluedDatum =ᶠ[𝓝 z₀] ∂̄(openChartPrim i₀)`
(Step 2 on the open `Ω i₀`), which is `ContDiffAt` (Step 1 + `contDiffAt_dbar_local`). -/
theorem contDiffOn_gluedDatum (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)))
    (hunion : openUnionChartImage 𝔇 = Metric.ball 𝔇.ballCenter 𝔇.radius) :
    ContDiffOn ℝ (⊤ : ℕ∞) (gluedDatum 𝔇 s) (Metric.ball 𝔇.ballCenter 𝔇.radius) := by
  intro z₀ hz₀
  -- `z₀ ∈ openUnionChartImage = ⋃ Ω i`, so `z₀ ∈ Ω i₀` for some `i₀`.
  have hz₀union : z₀ ∈ openUnionChartImage 𝔇 := by rw [hunion]; exact hz₀
  rw [openUnionChartImage_eq_iUnion_Ω] at hz₀union
  obtain ⟨i₀, hz₀Ω⟩ := Set.mem_iUnion.mp hz₀union
  obtain ⟨x₀, hx₀U, hx₀z⟩ := hz₀Ω
  -- `openChartPrim i₀` is `C^∞` at `z₀ = φ x₀` (Step 1), so `∂̄(openChartPrim i₀)` is `C^∞` at `z₀`.
  have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (DbarDisk.dbar (openChartPrim 𝔇 s i₀)) z₀ := by
    refine contDiffAt_dbar_local ?_
    rw [← hx₀z]; exact contDiffAt_openChartPrim 𝔇 s i₀ hx₀U
  -- `gluedDatum =ᶠ[𝓝 z₀] ∂̄(openChartPrim i₀)` (on the open `Ω i₀`, by `gluedDatum_apply`).
  have heq : gluedDatum 𝔇 s =ᶠ[𝓝 z₀] DbarDisk.dbar (openChartPrim 𝔇 s i₀) := by
    filter_upwards [(isOpen_Ω 𝔇 i₀).mem_nhds (hx₀z ▸ 𝔇.mem_Ω hx₀U)] with z hz
    exact gluedDatum_apply 𝔇 s i₀ hz
  exact (hcd.congr_of_eventuallyEq heq).contDiffWithinAt

/-! ## Steps 4–7 — Solve, holomorphic correctors, and the disk-acyclicity conclusion

Solve `∂̄u = ω` on the open ball (Forster 13.2, `dbar_solvable_open_disk`).  Then `η̂ᵢ := openChartPrimᵢ − u`
is holomorphic on `ball ∩ Ω_i` (its `∂̄` is `ω − ω = 0`), so `Hᵢ := η̂ᵢ ∘ φ` are chart-analytic correctors
(`analyticAt_compChart_of_differentiableOn`) whose differences split `holoFn(s_{ij})` on overlaps
(`openChartPrim_diff`, the `u`-terms cancel) — exactly `HasChartAnalyticCorrectors`.  The imported
`cechH1_subsingleton_of_chartAnalyticCorrectors` then collapses every class of `cechH1 0`. -/

/-- Each chart-image `Ω_i` lies inside the ball (so `ball ∩ Ω_i = Ω_i`). -/
theorem Ω_subset_ball (𝔇 : SharedChartCover X) (i : 𝔇.ι) :
    𝔇.Ω i ⊆ Metric.ball 𝔇.ballCenter 𝔇.radius :=
  𝔇.image_subset_ball i

/-- **`HasChartAnalyticCorrectors` for a shared-chart cover whose chart-images fill the ball.**  Steps
4–6 assembled: solve `∂̄u = ω` on the ball, set `η̂ᵢ := openChartPrimᵢ − u` (holomorphic on `ball ∩ Ω_i`,
`∂̄η̂ᵢ = ω − ω = 0`), `Hᵢ := η̂ᵢ ∘ φ` chart-analytic with `Hⱼ − Hᵢ =ᶠ holoFn(s_{ij})`. -/
theorem hasChartAnalyticCorrectors_of_unionBall (𝔇 : SharedChartCover X)
    (hunion : openUnionChartImage 𝔇 = Metric.ball 𝔇.ballCenter 𝔇.radius) :
    HasChartAnalyticCorrectors 𝔇.toFiniteFamily := by
  intro s
  -- **Step 4.** Solve `∂̄u = ω` on the open ball (Forster 13.2).
  obtain ⟨u, hu_smooth, hu_dbar⟩ :=
    DbarOpenDisk.dbar_solvable_open_disk 𝔇.ballCenter 𝔇.radius_pos (contDiffOn_gluedDatum 𝔇 s hunion)
  -- **Step 5.** The holomorphic chart correctors `η̂ᵢ := openChartPrimᵢ − u` on `ball ∩ Ω_i`.
  set ηhat : 𝔇.ι → ℂ → ℂ := fun i => openChartPrim 𝔇 s i - u with hηhatdef
  have hηhol : ∀ i, DifferentiableOn ℂ (ηhat i)
      (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i) := by
    intro i z hz
    obtain ⟨x, hxU, hxz⟩ := hz.2
    -- `openChartPrimᵢ` is `C^∞` at `z = φ x` (Step 1, `x ∈ U_i`); `u` is `C^∞` at `z ∈ ball`.
    have hĥ_cd : ContDiffAt ℝ (⊤ : ℕ∞) (openChartPrim 𝔇 s i) z := by
      rw [← hxz]; exact contDiffAt_openChartPrim 𝔇 s i hxU
    have hu_cd : ContDiffAt ℝ (⊤ : ℕ∞) u z :=
      (hu_smooth z hz.1).contDiffAt (Metric.isOpen_ball.mem_nhds hz.1)
    -- `∂̄η̂ᵢ z = ∂̄(openChartPrimᵢ) z − ∂̄u z = ω z − ω z = 0`.
    have hdb_eta : DbarDisk.dbar (ηhat i) z = 0 := by
      have hsub : DbarDisk.dbar (fun w => openChartPrim 𝔇 s i w - u w) z
          = DbarDisk.dbar (openChartPrim 𝔇 s i) z - DbarDisk.dbar u z :=
        DbarOpenDisk.dbar_sub (hĥ_cd.differentiableAt (by norm_num))
          (hu_cd.differentiableAt (by norm_num))
      rw [hηhatdef]
      show DbarDisk.dbar (fun w => openChartPrim 𝔇 s i w - u w) z = 0
      rw [hsub, hu_dbar z hz.1, gluedDatum_apply 𝔇 s i hz.2, sub_self]
    -- `∂̄η̂ᵢ = 0` + `η̂ᵢ` `ℝ`-differentiable ⟹ `ℂ`-differentiable (Wirtinger), on the open set.
    have hηcd : DifferentiableAt ℝ (ηhat i) z := by
      rw [hηhatdef]
      exact (hĥ_cd.differentiableAt (by norm_num)).sub (hu_cd.differentiableAt (by norm_num))
    exact (differentiableAt_of_dbar_eq_zero_local hηcd hdb_eta).differentiableWithinAt
  -- **Step 6.** The ambient correctors `H_i := η̂_i ∘ φ`.
  refine ⟨fun i => ηhat i ∘ 𝔇.φ, fun i y hy => ?_, fun i j x hx => ?_⟩
  · -- Chart-analytic on `U_i` (`analyticAt_compChart_of_differentiableOn`).
    exact analyticAt_compChart_of_differentiableOn 𝔇 i (hηhol i) hy
  · -- Difference identity, pointwise on the open overlap (gives the `𝓝[≠]`-eventual form).
    have hUij : ∀ᶠ z in 𝓝[≠] x, z ∈ (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X) :=
      eventually_nhdsWithin_of_eventually_nhds
        ((𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X).isOpen.mem_nhds hx)
    filter_upwards [hUij] with z hz
    -- `(η̂_j ∘ φ) z − (η̂_i ∘ φ) z = openChartPrim_j(φz) − openChartPrim_i(φz) = holoFn(s_{ij}) z`.
    show (ηhat j ∘ 𝔇.φ) z - (ηhat i ∘ 𝔇.φ) z = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) z
    simp only [hηhatdef, Function.comp_apply, Pi.sub_apply]
    -- The `u`-terms cancel; the rest is `openChartPrim_diff`.
    have hd := openChartPrim_diff 𝔇 s i j hz
    linear_combination hd

/-- **`H¹(disk, 𝒪) = 0` for a shared-chart cover whose chart-images fill the ball (Forster 13.4).**
The genuine disk-acyclicity: every class of `cechH1 0` is `0`.  Built from the open-disk ∂̄-solver
(Forster 13.2) via the open-union partition of unity — the sound replacement for the dead closed-core
`HasGluedDbarDatum` route. -/
theorem cechH1_subsingleton_of_unionBall (𝔇 : SharedChartCover X)
    (hunion : openUnionChartImage 𝔇 = Metric.ball 𝔇.ballCenter 𝔇.radius)
    (q : 𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) : q = 0 :=
  cechH1_subsingleton_of_chartAnalyticCorrectors 𝔇.toFiniteFamily
    (hasChartAnalyticCorrectors_of_unionBall 𝔇 hunion) q

end SharedChartCover
end Jacobians.Dolbeault
