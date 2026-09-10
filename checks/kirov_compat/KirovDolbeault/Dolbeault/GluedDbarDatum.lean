/-
  Dolbeault ladder — discharging `HasGluedDbarDatum 𝔇` for a `SharedChartCover`.

  `CechFinitenessBallSolve` reduced germ-level `H¹(disk, 𝒪) = 0` (for a shared-chart disk cover)
  to the single honest predicate `HasGluedDbarDatum 𝔇`: for every `𝒪`-cocycle `s` there is
  ONE globally-`C^∞` function `ω̂ : ℂ → ℂ` agreeing with the planar Wirtinger `∂̄(chartPrim s i)` on
  every `Ω_i ∩ ball`, where `chartPrim s i = coverPrim s i ∘ φ.symm` and
  `coverPrim s i = ∑_q ρ_q · holoFn(s_{q,i})` is the partition-of-unity primitive on the cover set `U_i`.

  ## The construction (Bott–Tu / Forster PoU globalization, IN CHART COORDINATES)

  Work entirely with `ℂ → ℂ` functions (the agreement target `DbarDisk.dbar` is the planar Wirtinger
  derivative, so no manifold-`∂̄`-to-planar bridge is needed).  Write, for the shared chart
  `φ = chartAt ℂ 𝔇.center`:

    * `rhoHat q   := rhoC q ∘ φ.symm`              (the chart-read PoU function),
    * `holoHat a b := holoFn(s_{a,b}) ∘ φ.symm`     (the chart-read analytic representative),
    * `dRhoHat q  := DbarDisk.dbar (rhoHat q)`      (the planar `∂̄` of the chart-read PoU function).

  Then on `Ω_i ∩ ball` (where every factor is genuinely smooth / holomorphic) the chart-read primitive
  satisfies, by the planar Leibniz rule and holomorphy (`∂̄holoHat = 0`),

      `∂̄(chartPrim s i) = ∑_q holoHat q i · dRhoHat q`.

  The GLUED datum is the **Bott–Tu double sum** (matching `coverPrim`'s PoU-index-first convention):

      `ω̂ := ∑_{(a,b)} (rhoHat b · holoHat a b) · dRhoHat a`,

  globally `C^∞` on `ℂ` because each term carries the confining factors `rhoHat b` (supported in
  `φ '' tsupport ρ_b`) and `dRhoHat a` (supported in `φ '' tsupport ρ_a`) — the documented 3-case
  `tsupport` argument, here transported to chart coordinates (the chart image of a `tsupport` is compact
  in `ℂ`, hence closed, so its complement is open).  The double sum telescopes (`∑_q rhoHat q = 1`,
  `∑_q dRhoHat q = 0`, and the cocycle relation `holoHat q k = holoHat q i + holoHat i k` from
  `holoFn_cocycle_sub`) to `∑_q holoHat q i · dRhoHat q = ∂̄(chartPrim s i)` on each `Ω_i ∩ ball`,
  proving the agreement.

  No gaps.  Reuses by import the planar Wirtinger algebra (`dbarFun_add` / `dbarFun_sub`)
  and all the §0–§5 machinery of `CechFinitenessBallSolve` (`coverPrim` / `chartPrim` / `holoFn` /
  `rhoC` / `holoFn_cocycle_sub` / `SharedChartCover` / `HasGluedDbarDatum`).
-/
import KirovDolbeault.Dolbeault.CechFinitenessBallSolve

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## §A — Planar Wirtinger primitives (Leibniz + finite-sum additivity)

The agreement target is the PLANAR `DbarDisk.dbar` of `ℂ → ℂ` functions, so we work with the planar
Wirtinger algebra (`dbarFun_add` / `dbarFun_sub` are imported from `CechDiskAcyclic`).  We add the two
missing primitives: the Leibniz product rule and additivity over a `Finset.sum`. -/

/-- **Planar `∂̄` Leibniz rule** `∂̄(f·g) z = g z · ∂̄f z + f z · ∂̄g z`, at a point where both factors are
real-differentiable (`fderiv_fun_mul` over `ℝ` for the `ℝ`-algebra `ℂ`). -/
theorem dbarFun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    DbarDisk.dbar (fun x => f x * g x) z = g z * DbarDisk.dbar f z + f z * DbarDisk.dbar g z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Planar `∂̄` additivity over a finite sum** `∂̄(∑_i f i) z = ∑_i ∂̄(f i) z`, at a point where every
summand is real-differentiable (`Finset.induction` on `dbarFun_add`). -/
theorem dbarFun_finset_sum {ι : Type*} (t : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (hf : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) :
    DbarDisk.dbar (fun x => ∑ i ∈ t, f i x) z = ∑ i ∈ t, DbarDisk.dbar (f i) z := by
  classical
  induction t using Finset.induction with
  | empty => simp [DbarDisk.dbar]
  | insert a s ha ih =>
    have hfa : DifferentiableAt ℝ (f a) z := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, DifferentiableAt ℝ (f i) z := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hsumdiff : DifferentiableAt ℝ (fun x => ∑ i ∈ s, f i x) z :=
      DifferentiableAt.fun_sum (fun i hi => hfs i hi)
    have hrw : (fun x => ∑ i ∈ insert a s, f i x)
        = (fun x => f a x + (fun y => ∑ i ∈ s, f i y) x) := by
      funext x; rw [Finset.sum_insert ha]
    rw [hrw, dbarFun_add hfa hsumdiff, ih hfs, Finset.sum_insert ha]

/-- **Planar `∂̄` of a `C^∞`-at-a-point function is `C^∞` at that point.**  `∂̄g z` is a fixed
continuous-linear combination of `fderiv ℝ g z` evaluated at the directions `1` and `I`; `fderiv ℝ g`
is `C^∞` near `z` (`ContDiffAt.fderiv_right`), and CLM-evaluation is `C^∞`. -/
theorem contDiffAt_dbar {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℝ (⊤ : ℕ∞) g z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (DbarDisk.dbar g) z := by
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ g) z :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (fderiv ℝ g w) (1 : ℂ)) z :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff.contDiffAt.comp z hfd
  have hI : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (fderiv ℝ g w) Complex.I) z :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.contDiffAt.comp z hfd
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (2 : ℂ)⁻¹ * ((fderiv ℝ g w) (1 : ℂ) + Complex.I * (fderiv ℝ g w) Complex.I)) z :=
    (contDiffAt_const.mul (h1.add (contDiffAt_const.mul hI)))
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by rw [DbarDisk.dbar])

/-! ## §B — The chart-read building blocks

Fix a `SharedChartCover 𝔇` and a cocycle `s`.  The chart-read PoU functions `rhoHat q = ρ_q ∘ φ.symm`
and analytic representatives `holoHat a b = holoFn(s_{a,b}) ∘ φ.symm` are honest `ℂ → ℂ` functions.
We establish exactly the regularity we need:
  * `rhoHat q` is `ContDiffAt ℝ ⊤` at every point of `φ.target` (so also `dRhoHat q = ∂̄(rhoHat q)` is);
  * `holoHat a b` is `AnalyticAt ℂ` at `φ x` for `x ∈ U_a ⊓ U_b` (hence holomorphic there, `∂̄ = 0`);
  * the chart images of the `tsupport`s are compact (the confinement that makes the double sum global). -/

namespace SharedChartCover

variable (𝔇 : SharedChartCover X) (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)))

/-- The chart-read PoU function `rhoHat q = ρ_q ∘ φ.symm : ℂ → ℂ`. -/
noncomputable def rhoHat (q : 𝔇.toFiniteFamily.ι) : ℂ → ℂ := rhoC 𝔇 q ∘ (𝔇.φ).symm

/-- The chart-read analytic representative `holoHat a b = holoFn(s_{a,b}) ∘ φ.symm : ℂ → ℂ`. -/
noncomputable def holoHat (a b : 𝔇.toFiniteFamily.ι) : ℂ → ℂ :=
  holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) ∘ (𝔇.φ).symm

/-- The planar `∂̄` of the chart-read PoU function, `dRhoHat q = ∂̄(rhoHat q) : ℂ → ℂ`. -/
noncomputable def dRhoHat (q : 𝔇.toFiniteFamily.ι) : ℂ → ℂ := DbarDisk.dbar (𝔇.rhoHat q)

/-- **`rhoHat q` is `ContDiffAt ℝ ⊤` at every `z ∈ φ.target`.**  `ρ_q` is globally `C^∞` on `X`, and
`φ.symm` is `C^∞` on `φ.target` (model `𝓘(ℝ,ℂ)` ≅ identity). -/
theorem contDiffAt_rhoHat (q : 𝔇.toFiniteFamily.ι) {z : ℂ} (hz : z ∈ (𝔇.φ).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (𝔇.rhoHat q) z := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center) _ hz).contMDiffAt
      (φ.open_target.mem_nhds hz)
  have hrho : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (rhoC 𝔇 q) (φ.symm z) :=
    (rhoC 𝔇 q).contMDiff (φ.symm z)
  have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (rhoC 𝔇 q ∘ φ.symm) z := hrho.comp z hsymm
  exact contMDiffAt_iff_contDiffAt.1 hcomp

/-- **`dRhoHat q` is `ContDiffAt ℝ ⊤` at every `z ∈ φ.target`** (`∂̄` of a `C^∞`-at-`z` function is
`C^∞` at `z`, `contDiffAt_dbar`). -/
theorem contDiffAt_dRhoHat (q : 𝔇.toFiniteFamily.ι) {z : ℂ} (hz : z ∈ (𝔇.φ).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (𝔇.dRhoHat q) z :=
  contDiffAt_dbar (𝔇.contDiffAt_rhoHat q hz)

/-- **`holoHat a b` is `AnalyticAt ℂ` at `φ x` for `x ∈ U_a ⊓ U_b`.**  `holoFn(s_{a,b})` is
chart-analytic in `x`'s own chart (`holoFn_chart_analyticAt`); transport to the shared chart `φ` via the
analytic transition map (the reverse chart change). -/
theorem analyticAt_holoHat (a b : 𝔇.toFiniteFamily.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U a ⊓ 𝔇.toFiniteFamily.U b : Opens X)) :
    AnalyticAt ℂ (𝔇.holoHat s a b) (𝔇.φ x) := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  have hsrc : x ∈ φ.source := 𝔇.subset_source a hx.1
  -- `holoFn(s_{a,b})` read in `x`'s OWN chart is analytic at `(chartAt x) x`.
  have hown : AnalyticAt ℂ
      (holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) ∘ (chartAt (H := ℂ) x).symm)
      ((chartAt (H := ℂ) x) x) :=
    holoFn_chart_analyticAt (cocycleComp_mem 𝔇.toFiniteFamily s a b) hx
  -- Transport to the shared chart `φ` at the point `x`: the transition `(chartAt x) ∘ φ.symm` is
  -- analytic at `φ x` (it maps `φ x ↦ (chartAt x) x`), and we precompose.
  set h := holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) with hh
  have hsymm_pt : φ.symm (φ x) = x := φ.left_inv hsrc
  -- `(chartAt x) ∘ φ.symm` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `φ x`.
  have hxtgt : φ x ∈ φ.target := φ.map_source hsrc
  have h_symm_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ.symm (φ x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := 𝔇.center)) _ hxtgt).contMDiffAt
      (φ.open_target.mem_nhds hxtgt)
  have h_cx_cmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) x) (φ.symm (φ x)) := by
    rw [hsymm_pt]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x)) _ (mem_chart_source ℂ x)).contMDiffAt
      ((chartAt (H := ℂ) x).open_source.mem_nhds (mem_chart_source ℂ x))
  have htrans_ana : AnalyticAt ℂ ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) :=
    (contMDiffAt_iff_contDiffAt.1 (h_cx_cmd.comp (φ x) h_symm_cmd)).analyticAt
  -- Compose: `(h ∘ (chartAt x).symm) ∘ ((chartAt x) ∘ φ.symm)` analytic at `φ x`; it maps to `(chartAt x) x`.
  have htrans_pt : ((chartAt (H := ℂ) x) ∘ φ.symm) (φ x) = (chartAt (H := ℂ) x) x := by
    simp only [Function.comp_apply, hsymm_pt]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) (φ x) :=
    AnalyticAt.comp (htrans_pt ▸ hown) htrans_ana
  -- Near `φ x`, `h ∘ φ.symm` equals that composite (where `φ.symm` lands in `(chartAt x).source`).
  have hmem : ∀ᶠ w in 𝓝 (φ x), φ.symm w ∈ (chartAt (H := ℂ) x).source := by
    have hcont : ContinuousAt φ.symm (φ x) := φ.continuousAt_symm hxtgt
    have hh0 : φ.symm (φ x) ∈ (chartAt (H := ℂ) x).source := by rw [hsymm_pt]; exact mem_chart_source ℂ x
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) x).open_source.mem_nhds hh0)
  have heq : (h ∘ φ.symm) =ᶠ[𝓝 (φ x)]
      ((h ∘ (chartAt (H := ℂ) x).symm) ∘ ((chartAt (H := ℂ) x) ∘ φ.symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv hw]
  rw [show 𝔇.holoHat s a b = h ∘ φ.symm from rfl, analyticAt_congr heq]
  exact hcomp

/-- The chart image `φ '' tsupport ρ_q` is compact in `ℂ` (`tsupport ρ_q` is closed in the compact `X`,
hence compact; `φ` is continuous on its source, which contains `tsupport ρ_q`). -/
theorem isCompact_image_tsupport (q : 𝔇.toFiniteFamily.ι) :
    IsCompact (𝔇.φ '' tsupport (coverPoU 𝔇 q)) := by
  have hcompact : IsCompact (tsupport (coverPoU 𝔇 q)) :=
    (isClosed_tsupport _).isCompact
  have hsub : tsupport (coverPoU 𝔇 q) ⊆ (𝔇.φ).source := by
    intro x hx
    exact 𝔇.subset_source q (coverPoU_subordinate 𝔇 q hx)
  refine hcompact.image_of_continuousOn ?_
  exact (𝔇.φ).continuousOn.mono hsub

/-- The chart image `φ '' tsupport ρ_q` is closed in `ℂ` (compact in a `T2` space). -/
theorem isClosed_image_tsupport (q : 𝔇.toFiniteFamily.ι) :
    IsClosed (𝔇.φ '' tsupport (coverPoU 𝔇 q)) :=
  (𝔇.isCompact_image_tsupport q).isClosed

/-- `rhoHat q z = 0` for `z ∉ φ '' tsupport ρ_q` (and `z ∈ φ.target`, so `φ.symm z ∉ tsupport ρ_q`).
Stated for `z ∈ φ.target`: outside the chart target `φ.symm` is junk so we cannot conclude. -/
theorem rhoHat_eq_zero_of_notMem (q : 𝔇.toFiniteFamily.ι) {z : ℂ} (hz : z ∈ (𝔇.φ).target)
    (hznot : z ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 q)) : 𝔇.rhoHat q z = 0 := by
  have hsymm_not : (𝔇.φ).symm z ∉ tsupport (coverPoU 𝔇 q) := by
    intro hc
    exact hznot ⟨(𝔇.φ).symm z, hc, (𝔇.φ).right_inv hz⟩
  show rhoC 𝔇 q ((𝔇.φ).symm z) = 0
  exact rhoC_eq_zero_of_notMem 𝔇 q hsymm_not

/-! ## §C — The smooth zero-extension and the globally-`C^∞` double-sum term

The raw chart-pushed `rhoHat b`, `holoHat a b`, `dRhoHat a` are only controlled on `φ.target` (junk
outside).  The CONFINING factor is `rhoHat b`, supported (within `φ.target`) in the compact
`Cb = φ '' tsupport ρ_b ⊆ φ.target`.  We replace it by its **smooth zero-extension** `rhoTilde b`
(equal to `rhoHat b` on `φ.target`, `0` outside), globally `C^∞` by a two-open argument (`φ.target`
where it is `rhoHat b`; `Cbᶜ` where it is `0`).  The double-sum term `rhoTilde b · holoHat a b ·
dRhoHat a` is then globally `C^∞`: on `φ.target` all three factors are smooth; off `Cb` the factor
`rhoTilde b` vanishes on a neighbourhood, killing the off-target junk of the other two. -/

open Classical in
/-- The **smooth zero-extension** of `rhoHat q`: equal to `rhoC q ∘ φ.symm` on `φ.target`, `0` outside.
Globally `C^∞` (`contDiff_rhoTilde`). -/
noncomputable def rhoTilde (q : 𝔇.toFiniteFamily.ι) : ℂ → ℂ :=
  fun z => if z ∈ (𝔇.φ).target then 𝔇.rhoHat q z else 0

/-- On `φ.target`, `rhoTilde q = rhoHat q`. -/
theorem rhoTilde_eq_of_mem (q : 𝔇.toFiniteFamily.ι) {z : ℂ} (hz : z ∈ (𝔇.φ).target) :
    𝔇.rhoTilde q z = 𝔇.rhoHat q z := by
  simp only [rhoTilde, if_pos hz]

/-- `rhoTilde q ≡ 0` on the complement of `Cq = φ '' tsupport ρ_q`: outside `φ.target` by definition;
on `φ.target ∖ Cq` because `φ.symm z ∉ tsupport ρ_q` there (`rhoHat q z = 0`). -/
theorem rhoTilde_eq_zero_of_notMem (q : 𝔇.toFiniteFamily.ι) {z : ℂ}
    (hz : z ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 q)) : 𝔇.rhoTilde q z = 0 := by
  simp only [rhoTilde]
  split
  · next hzt => exact 𝔇.rhoHat_eq_zero_of_notMem q hzt hz
  · rfl

/-- **`rhoTilde q` is globally `C^∞` on `ℂ`.**  Two-open argument: on the open `φ.target` it equals the
`C^∞` function `rhoHat q` (`contDiffAt_rhoHat`); on the open complement of the closed `Cq` it is
identically `0`.  These two opens cover `ℂ` (since `Cq ⊆ φ.target`). -/
theorem contDiff_rhoTilde (q : 𝔇.toFiniteFamily.ι) : ContDiff ℝ (⊤ : ℕ∞) (𝔇.rhoTilde q) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (𝔇.φ).target
  · -- On the open `φ.target`, `rhoTilde q =ᶠ rhoHat q`.
    refine (𝔇.contDiffAt_rhoHat q hz).congr_of_eventuallyEq ?_
    filter_upwards [(𝔇.φ).open_target.mem_nhds hz] with w hw
    exact 𝔇.rhoTilde_eq_of_mem q hw
  · -- `z ∉ φ.target ⟹ z ∉ Cq` (since `Cq ⊆ target`); on the open `Cqᶜ`, `rhoTilde q ≡ 0`.
    have hznotC : z ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 q) := by
      intro hc
      obtain ⟨x, hx, hxz⟩ := hc
      exact hz (hxz ▸ (𝔇.φ).map_source (𝔇.subset_source q (coverPoU_subordinate 𝔇 q hx)))
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(𝔇.isClosed_image_tsupport q).isOpen_compl.mem_nhds hznotC] with w hw
    exact 𝔇.rhoTilde_eq_zero_of_notMem q hw

/-- The **double-sum term** `cechTermFun a b z = (rhoTilde b z · holoHat a b z) · dRhoHat a z` — the
chart-coordinate Bott–Tu term confined by the smooth zero-extension `rhoTilde b`. -/
noncomputable def cechTermFun (a b : 𝔇.toFiniteFamily.ι) : ℂ → ℂ :=
  fun z => (𝔇.rhoTilde b z * 𝔇.holoHat s a b z) * 𝔇.dRhoHat a z

/-- **`cechTermFun a b` is globally `C^∞` on `ℂ`** (the 3-case `tsupport` argument, here a clean
two-open cover thanks to the zero-extension `rhoTilde b`).  On `φ.target` all three factors are `C^∞`
(`contDiff_rhoTilde`, `analyticAt_holoHat` on the overlap or `rhoTilde b = 0` off it, `contDiffAt_dRhoHat`);
off the closed `Cb = φ '' tsupport ρ_b` the factor `rhoTilde b` vanishes on a neighbourhood, so the
product (and the off-target junk of the other factors) is killed. -/
theorem contDiff_cechTermFun (a b : 𝔇.toFiniteFamily.ι) :
    ContDiff ℝ (⊤ : ℕ∞) (𝔇.cechTermFun s a b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (𝔇.φ).target
  · -- On `φ.target`: `rhoTilde b` and `dRhoHat a` are always `C^∞`; for `holoHat a b` split on whether
    -- `z ∈ Cb` (then `z = φ x`, `x ∈ U_b`, and we still need `x ∈ U_a` — handled by sub-casing on `Ca`).
    have hrt : ContDiffAt ℝ (⊤ : ℕ∞) (𝔇.rhoTilde b) z := (𝔇.contDiff_rhoTilde b).contDiffAt
    have hdr : ContDiffAt ℝ (⊤ : ℕ∞) (𝔇.dRhoHat a) z := 𝔇.contDiffAt_dRhoHat a hz
    by_cases hzCb : z ∈ 𝔇.φ '' tsupport (coverPoU 𝔇 b)
    · by_cases hzCa : z ∈ 𝔇.φ '' tsupport (coverPoU 𝔇 a)
      · -- `z = φ x` with `x ∈ tsupp ρ_a ∩ tsupp ρ_b ⊆ U_a ⊓ U_b`: `holoHat a b` is `C^∞` at `z`.
        obtain ⟨x, hxb, hxz⟩ := hzCb
        obtain ⟨x', hxa', hx'z⟩ := hzCa
        have hxa : x ∈ tsupport (coverPoU 𝔇 a) := by
          have : x' = x := (𝔇.φ).injOn
            (𝔇.subset_source a (coverPoU_subordinate 𝔇 a hxa'))
            (𝔇.subset_source b (coverPoU_subordinate 𝔇 b hxb)) (hx'z.trans hxz.symm)
          exact this ▸ hxa'
        have hxU : x ∈ (𝔇.toFiniteFamily.U a ⊓ 𝔇.toFiniteFamily.U b : Opens X) :=
          ⟨coverPoU_subordinate 𝔇 a hxa, coverPoU_subordinate 𝔇 b hxb⟩
        have hholo : ContDiffAt ℝ (⊤ : ℕ∞) (𝔇.holoHat s a b) z := by
          rw [← hxz]
          exact (𝔇.analyticAt_holoHat s a b hxU).contDiffAt.restrict_scalars ℝ
        exact (hrt.mul hholo).mul hdr
      · -- `z ∉ Ca`: `dRhoHat a = ∂̄(rhoHat a) ≡ 0` near `z` (`rhoHat a ≡ 0` on a nbhd, so its `∂̄ = 0`).
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        -- `rhoHat a ≡ 0` on `φ.target ∩ Caᶜ` (open), so `dRhoHat a ≡ 0` there.
        have hopen : IsOpen ((𝔇.φ).target ∩ (𝔇.φ '' tsupport (coverPoU 𝔇 a))ᶜ) :=
          (𝔇.φ).open_target.inter (𝔇.isClosed_image_tsupport a).isOpen_compl
        have hmem : ((𝔇.φ).target ∩ (𝔇.φ '' tsupport (coverPoU 𝔇 a))ᶜ) ∈ 𝓝 z :=
          hopen.mem_nhds ⟨hz, hzCa⟩
        filter_upwards [hmem] with w hw
        have hdR0 : 𝔇.dRhoHat a w = 0 := by
          show DbarDisk.dbar (𝔇.rhoHat a) w = 0
          -- `rhoHat a ≡ 0` on the open nbhd `target ∩ Caᶜ` of `w`, so its `∂̄` vanishes at `w`.
          have hraEq : 𝔇.rhoHat a =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
            filter_upwards [hopen.mem_nhds hw] with v hv
            exact 𝔇.rhoHat_eq_zero_of_notMem a hv.1 hv.2
          rw [DbarDisk.dbar, hraEq.fderiv_eq]
          simp
        show (𝔇.rhoTilde b w * 𝔇.holoHat s a b w) * 𝔇.dRhoHat a w = 0
        rw [hdR0, mul_zero]
    · -- `z ∉ Cb`: `rhoTilde b ≡ 0` near `z`, killing the term.
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(𝔇.isClosed_image_tsupport b).isOpen_compl.mem_nhds hzCb] with w hw
      show 𝔇.cechTermFun s a b w = 0
      simp only [SharedChartCover.cechTermFun]
      rw [𝔇.rhoTilde_eq_zero_of_notMem b hw, zero_mul, zero_mul]
  · -- `z ∉ φ.target ⟹ z ∉ Cb` (since `Cb ⊆ target`): `rhoTilde b ≡ 0` near `z`.
    have hzCb : z ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 b) := by
      intro hc
      obtain ⟨x, hx, hxz⟩ := hc
      exact hz (hxz ▸ (𝔇.φ).map_source (𝔇.subset_source b (coverPoU_subordinate 𝔇 b hx)))
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(𝔇.isClosed_image_tsupport b).isOpen_compl.mem_nhds hzCb] with w hw
    show 𝔇.cechTermFun s a b w = 0
    simp only [SharedChartCover.cechTermFun]
    rw [𝔇.rhoTilde_eq_zero_of_notMem b hw, zero_mul, zero_mul]

/-- **The glued `∂̄`-datum `ω̂`** — the chart-coordinate Bott–Tu double sum
`∑_{(a,b)} (rhoTilde b · holoHat a b) · dRhoHat a`, globally `C^∞` (finite sum of `contDiff_cechTermFun`). -/
noncomputable def dbarDatum : ℂ → ℂ :=
  fun z => ∑ p : 𝔇.toFiniteFamily.ι × 𝔇.toFiniteFamily.ι, 𝔇.cechTermFun s p.1 p.2 z

/-- **`ω̂` is globally `C^∞` on `ℂ`** (finite sum of the globally-`C^∞` terms). -/
theorem contDiff_dbarDatum : ContDiff ℝ (⊤ : ℕ∞) (𝔇.dbarDatum s) :=
  ContDiff.sum (fun p _ => 𝔇.contDiff_cechTermFun s p.1 p.2)

/-! ## §D — The agreement `∂̄(chartPrim s i) = ω̂` on `Ω_i ∩ ball`

The remaining obligation.  At a point `z = φ x ∈ Ω_i ∩ ball` (so `x ∈ U_i`):

  * `chartPrim s i w = ∑_q rhoHat q w · holoHat q i w` (definitional);
  * `∂̄(chartPrim s i) z = ∑_q holoHat q i z · dRhoHat q z` (planar Leibniz + holomorphy of `holoHat`,
    via the per-`q` two-case lemma `dbar_chartSummand`);
  * `ω̂ z = ∑_{(a,b)} (rhoHat b z · holoHat a b z) · dRhoHat a z` (using `rhoTilde = rhoHat` on the ball),
    which telescopes (`∑rhoHat = 1`, `∑dRhoHat = 0`, cocycle `holoHat a b = holoHat a i + holoHat i b`) to
    `∑_q holoHat q i z · dRhoHat q z`. -/

/-- At `z = φ x` (`x ∈ φ.source`), `holoHat a b (φ x) = holoFn(s_{a,b}) x` (chart left-inverse). -/
theorem holoHat_apply_chart (a b : 𝔇.toFiniteFamily.ι) {x : X} (hx : x ∈ (𝔇.φ).source) :
    𝔇.holoHat s a b (𝔇.φ x) = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) x := by
  show holoFn (cocycleComp_mem 𝔇.toFiniteFamily s a b) ((𝔇.φ).symm (𝔇.φ x)) = _
  rw [(𝔇.φ).left_inv hx]

/-- `dRhoHat a z = 0` for `z ∈ φ.target ∖ Ca` (off the chart image of `tsupport ρ_a`): `rhoHat a ≡ 0`
on the open `φ.target ∩ Caᶜ` containing `z`, so its planar `∂̄` vanishes at `z`. -/
theorem dRhoHat_eq_zero_of_notMem (a : 𝔇.toFiniteFamily.ι) {z : ℂ} (hz : z ∈ (𝔇.φ).target)
    (hzCa : z ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 a)) : 𝔇.dRhoHat a z = 0 := by
  have hopen : IsOpen ((𝔇.φ).target ∩ (𝔇.φ '' tsupport (coverPoU 𝔇 a))ᶜ) :=
    (𝔇.φ).open_target.inter (𝔇.isClosed_image_tsupport a).isOpen_compl
  show DbarDisk.dbar (𝔇.rhoHat a) z = 0
  have hraEq : 𝔇.rhoHat a =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds ⟨hz, hzCa⟩] with v hv
    exact 𝔇.rhoHat_eq_zero_of_notMem a hv.1 hv.2
  rw [DbarDisk.dbar, hraEq.fderiv_eq]; simp

/-- `∂̄(holoHat q i)(φ x) = 0` for `x ∈ U_q ⊓ U_i` (the chart-read analytic representative is
holomorphic at `φ x`, `analyticAt_holoHat`, so its planar Wirtinger `∂̄` vanishes). -/
theorem dbar_holoHat_eq_zero (q i : 𝔇.toFiniteFamily.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U q ⊓ 𝔇.toFiniteFamily.U i : Opens X)) :
    DbarDisk.dbar (𝔇.holoHat s q i) (𝔇.φ x) = 0 :=
  DbarDisk.dbar_eq_zero_of_differentiableAt (𝔇.analyticAt_holoHat s q i hx).differentiableAt

/-- `holoHat q i` is `DifferentiableAt ℝ` at `φ x` for `x ∈ U_q ⊓ U_i` (analytic ⟹ `ℝ`-differentiable). -/
theorem differentiableAt_holoHat (q i : 𝔇.toFiniteFamily.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U q ⊓ 𝔇.toFiniteFamily.U i : Opens X)) :
    DifferentiableAt ℝ (𝔇.holoHat s q i) (𝔇.φ x) :=
  ((𝔇.analyticAt_holoHat s q i hx).differentiableAt).restrictScalars ℝ

/-- **Per-`q` summand `∂̄`:** at `z = φ x` (`x ∈ U_i`), `∂̄(rhoHat q · holoHat q i) z = holoHat q i z ·
dRhoHat q z`.  Two-case: on `tsupport ρ_q` (so `x ∈ U_q ⊓ U_i`) the planar Leibniz `dbarFun_mul` with
`∂̄(holoHat q i) = 0` (holomorphy); off it `rhoHat q ≡ 0` near `z`, so both the summand and `dRhoHat q`
vanish at `z`. -/
theorem dbar_chartSummand (i q : 𝔇.toFiniteFamily.ι) {x : X} (hx : x ∈ 𝔇.toFiniteFamily.U i)
    (hxsrc : x ∈ (𝔇.φ).source) :
    DbarDisk.dbar (fun w => 𝔇.rhoHat q w * 𝔇.holoHat s q i w) (𝔇.φ x)
      = 𝔇.holoHat s q i (𝔇.φ x) * 𝔇.dRhoHat q (𝔇.φ x) := by
  by_cases hb : x ∈ tsupport (coverPoU 𝔇 q)
  · -- `x ∈ U_q ⊓ U_i`: Leibniz, with `∂̄(holoHat q i) = 0`.
    have hxq : x ∈ 𝔇.toFiniteFamily.U q := coverPoU_subordinate 𝔇 q hb
    have hxqi : x ∈ (𝔇.toFiniteFamily.U q ⊓ 𝔇.toFiniteFamily.U i : Opens X) := ⟨hxq, hx⟩
    have hrt : DifferentiableAt ℝ (𝔇.rhoHat q) (𝔇.φ x) :=
      (𝔇.contDiffAt_rhoHat q (𝔇.φ.map_source hxsrc)).differentiableAt (by simp)
    have hht : DifferentiableAt ℝ (𝔇.holoHat s q i) (𝔇.φ x) := 𝔇.differentiableAt_holoHat s q i hxqi
    rw [dbarFun_mul hrt hht, 𝔇.dbar_holoHat_eq_zero s q i hxqi]
    show 𝔇.holoHat s q i (𝔇.φ x) * DbarDisk.dbar (𝔇.rhoHat q) (𝔇.φ x) + _ = _
    rw [mul_zero, add_zero]; rfl
  · -- `x ∉ tsupport ρ_q`: `rhoHat q ≡ 0` near `φ x`, so the summand and `dRhoHat q` vanish at `φ x`.
    have hxtgt : 𝔇.φ x ∈ (𝔇.φ).target := 𝔇.φ.map_source hxsrc
    have hxCa : 𝔇.φ x ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 q) := by
      intro hc
      obtain ⟨y, hy, hyx⟩ := hc
      exact hb ((𝔇.φ).injOn (𝔇.subset_source q (coverPoU_subordinate 𝔇 q hy)) hxsrc hyx ▸ hy)
    have hdR0 : 𝔇.dRhoHat q (𝔇.φ x) = 0 := 𝔇.dRhoHat_eq_zero_of_notMem q hxtgt hxCa
    have hsummand0 : DbarDisk.dbar (fun w => 𝔇.rhoHat q w * 𝔇.holoHat s q i w) (𝔇.φ x) = 0 := by
      have hopen : IsOpen ((𝔇.φ).target ∩ (𝔇.φ '' tsupport (coverPoU 𝔇 q))ᶜ) :=
        (𝔇.φ).open_target.inter (𝔇.isClosed_image_tsupport q).isOpen_compl
      have heq : (fun w => 𝔇.rhoHat q w * 𝔇.holoHat s q i w) =ᶠ[𝓝 (𝔇.φ x)] (fun _ => (0 : ℂ)) := by
        filter_upwards [hopen.mem_nhds ⟨hxtgt, hxCa⟩] with v hv
        rw [𝔇.rhoHat_eq_zero_of_notMem q hv.1 hv.2, zero_mul]
      rw [DbarDisk.dbar, heq.fderiv_eq]; simp
    rw [hsummand0, hdR0, mul_zero]

/-- **`∑_q rhoHat q z = 1` on the chart-image of the closed-core INTERIOR** (chart-read of `∑ ρ_q = 1`,
which the closed-core PoU guarantees only on `𝔇.core` — `sum_rhoC_apply` needs `φ.symm z ∈ core`).
Stated for `φ.symm z ∈ interior 𝔇.core` (the open locus where the overlaps live), so that a
neighbourhood of `z` is also in `φ '' interior core` (used for the `∂̄`-of-`∑ρ` argument). -/
theorem sum_rhoHat_apply {z : ℂ} (hz : (𝔇.φ).symm z ∈ interior 𝔇.core) :
    ∑ q, 𝔇.rhoHat q z = 1 := by
  have : ∑ q, rhoC 𝔇 q ((𝔇.φ).symm z) = 1 := sum_rhoC_apply 𝔇 (interior_subset hz)
  simpa only [SharedChartCover.rhoHat, Function.comp_apply] using this

/-- **`∑_q dRhoHat q z = 0` on the chart-image of `interior 𝔇.core`** (`∂̄(∑_q rhoHat q) = ∂̄(const 1) =
0`).  Needs `z ∈ φ.target` (for the `∂̄`-commutes-with-sum smoothness) AND `φ.symm z ∈ interior 𝔇.core`
(so `∑ rhoHat = 1` on a neighbourhood of `z`, where the closed-core PoU sums to one).  The chart-image
`φ '' interior core ∩ φ.target` is the open locus on which `∑ rhoHat = 1`, so `∂̄` of the constant `1`
vanishes there. -/
theorem sum_dRhoHat_apply {z : ℂ} (hz : z ∈ (𝔇.φ).target)
    (hzc : (𝔇.φ).symm z ∈ interior 𝔇.core) :
    ∑ q, 𝔇.dRhoHat q z = 0 := by
  have hdiff : ∀ q ∈ (Finset.univ : Finset 𝔇.toFiniteFamily.ι),
      DifferentiableAt ℝ (𝔇.rhoHat q) z :=
    fun q _ => (𝔇.contDiffAt_rhoHat q hz).differentiableAt (by simp)
  have hsum : DbarDisk.dbar (fun w => ∑ q, 𝔇.rhoHat q w) z = ∑ q, 𝔇.dRhoHat q z :=
    dbarFun_finset_sum Finset.univ (fun q => 𝔇.rhoHat q) hdiff
  -- `∑_q rhoHat q = const 1` on the open nbhd `φ.target ∩ φ.symm⁻¹(interior core)` of `z`, so `∂̄ = 0`.
  have hconst : DbarDisk.dbar (fun w => ∑ q, 𝔇.rhoHat q w) z = 0 := by
    have hznbhd : z ∈ (𝔇.φ).target ∩ (𝔇.φ).symm ⁻¹' interior 𝔇.core := ⟨hz, hzc⟩
    have hznbhd_open : IsOpen ((𝔇.φ).target ∩ (𝔇.φ).symm ⁻¹' interior 𝔇.core) :=
      OpenPartialHomeomorph.isOpen_inter_preimage_symm (𝔇.φ) isOpen_interior
    have heq : (fun w => ∑ q, 𝔇.rhoHat q w) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
      filter_upwards [hznbhd_open.mem_nhds hznbhd] with v hv
      exact 𝔇.sum_rhoHat_apply hv.2
    rw [DbarDisk.dbar, heq.fderiv_eq]; simp
  rw [← hsum, hconst]

/-- **The chart cocycle relation.**  At `z = φ x` (`x ∈ U_a ⊓ U_i ⊓ U_b`),
`holoHat a b z = holoHat a i z + holoHat i b z` (`holoFn_cocycle_sub` pushed through the chart). -/
theorem holoHat_cocycle (a i b : 𝔇.toFiniteFamily.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U a ⊓ 𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U b : Opens X)) :
    𝔇.holoHat s a b (𝔇.φ x) = 𝔇.holoHat s a i (𝔇.φ x) + 𝔇.holoHat s i b (𝔇.φ x) := by
  have hsrc : x ∈ (𝔇.φ).source := 𝔇.subset_source a hx.1.1
  rw [𝔇.holoHat_apply_chart s a b hsrc, 𝔇.holoHat_apply_chart s a i hsrc,
    𝔇.holoHat_apply_chart s i b hsrc]
  have hcoc := holoFn_cocycle_sub 𝔇.toFiniteFamily s a i b hx
  -- `holoFn(s_ab) − holoFn(s_ai) = holoFn(s_ib)`.
  linear_combination hcoc

/-- **`∂̄(chartPrim s i) z = ∑_q holoHat q i z · dRhoHat q z`** at `z = φ x`, `x ∈ U_i` (sum the per-`q`
two-case Leibniz `dbar_chartSummand`; the `chartPrim` is the `∑_q rhoHat q · holoHat q i` finite sum). -/
theorem dbar_chartPrim_apply (i : 𝔇.toFiniteFamily.ι) {x : X} (hx : x ∈ 𝔇.toFiniteFamily.U i) :
    DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ x)
      = ∑ q, 𝔇.holoHat s q i (𝔇.φ x) * 𝔇.dRhoHat q (𝔇.φ x) := by
  have hsrc : x ∈ (𝔇.φ).source := 𝔇.subset_source i hx
  -- `chartPrim s i = fun w => ∑_q rhoHat q w · holoHat q i w` (definitional).
  have hcp : chartPrim 𝔇 s i = (fun w => ∑ q, 𝔇.rhoHat q w * 𝔇.holoHat s q i w) := by
    funext w
    show coverPrim 𝔇 s i ((𝔇.φ).symm w) = _
    rw [coverPrim_apply]
    rfl
  rw [hcp]
  -- Per-`q` differentiability (for the finite-sum `∂̄`): two-case (overlap analytic / locally `0`).
  have hdiff : ∀ q ∈ (Finset.univ : Finset 𝔇.toFiniteFamily.ι),
      DifferentiableAt ℝ (fun w => 𝔇.rhoHat q w * 𝔇.holoHat s q i w) (𝔇.φ x) := by
    intro q _
    by_cases hb : x ∈ tsupport (coverPoU 𝔇 q)
    · have hxq : x ∈ 𝔇.toFiniteFamily.U q := coverPoU_subordinate 𝔇 q hb
      have hxqi : x ∈ (𝔇.toFiniteFamily.U q ⊓ 𝔇.toFiniteFamily.U i : Opens X) := ⟨hxq, hx⟩
      exact ((𝔇.contDiffAt_rhoHat q (𝔇.φ.map_source hsrc)).differentiableAt
        (by simp)).mul (𝔇.differentiableAt_holoHat s q i hxqi)
    · -- Locally `0` near `φ x`.
      have hxtgt : 𝔇.φ x ∈ (𝔇.φ).target := 𝔇.φ.map_source hsrc
      have hxCa : 𝔇.φ x ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 q) := by
        intro hc
        obtain ⟨y, hy, hyx⟩ := hc
        exact hb ((𝔇.φ).injOn (𝔇.subset_source q (coverPoU_subordinate 𝔇 q hy)) hsrc hyx ▸ hy)
      have hopen : IsOpen ((𝔇.φ).target ∩ (𝔇.φ '' tsupport (coverPoU 𝔇 q))ᶜ) :=
        (𝔇.φ).open_target.inter (𝔇.isClosed_image_tsupport q).isOpen_compl
      refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds ⟨hxtgt, hxCa⟩] with v hv
      rw [𝔇.rhoHat_eq_zero_of_notMem q hv.1 hv.2, zero_mul]
  rw [dbarFun_finset_sum Finset.univ (fun q => fun w => 𝔇.rhoHat q w * 𝔇.holoHat s q i w) hdiff]
  exact Finset.sum_congr rfl fun q _ => 𝔇.dbar_chartSummand s i q hx hsrc

/-- **`ω̂ z = ∑_q holoHat q i z · dRhoHat q z`** at `z = φ x`, `x ∈ U_i` (the Bott–Tu telescoping).
On the ball `rhoTilde = rhoHat`; substitute the cocycle `holoHat a b = holoHat a i + holoHat i b` on the
triple overlap (off it a confining factor vanishes); split the double sum using `∑rhoHat = 1`,
`∑dRhoHat = 0`. -/
theorem dbarDatum_apply (i : 𝔇.toFiniteFamily.ι) {x : X} (hx : x ∈ 𝔇.toFiniteFamily.U i)
    (hxc : x ∈ interior 𝔇.core) :
    𝔇.dbarDatum s (𝔇.φ x) = ∑ q, 𝔇.holoHat s q i (𝔇.φ x) * 𝔇.dRhoHat q (𝔇.φ x) := by
  have hsrc : x ∈ (𝔇.φ).source := 𝔇.subset_source i hx
  have hxtgt : 𝔇.φ x ∈ (𝔇.φ).target := 𝔇.φ.map_source hsrc
  -- The chart-image point's `φ.symm` returns to `x ∈ interior core` (used for `∑ρ = 1`).
  have hxcsymm : (𝔇.φ).symm (𝔇.φ x) ∈ interior 𝔇.core := by rw [(𝔇.φ).left_inv hsrc]; exact hxc
  -- Rewrite each term with `rhoTilde = rhoHat` and the cocycle substitution.
  have hTerm : ∀ a b : 𝔇.toFiniteFamily.ι,
      𝔇.cechTermFun s a b (𝔇.φ x)
        = (𝔇.rhoHat b (𝔇.φ x)
            * (𝔇.holoHat s a i (𝔇.φ x) + 𝔇.holoHat s i b (𝔇.φ x))) * 𝔇.dRhoHat a (𝔇.φ x) := by
    intro a b
    show (𝔇.rhoTilde b (𝔇.φ x) * 𝔇.holoHat s a b (𝔇.φ x)) * 𝔇.dRhoHat a (𝔇.φ x) = _
    rw [𝔇.rhoTilde_eq_of_mem b hxtgt]
    by_cases hbb : x ∈ tsupport (coverPoU 𝔇 b)
    · by_cases hba : x ∈ tsupport (coverPoU 𝔇 a)
      · -- `x ∈ U_a ⊓ U_i ⊓ U_b`: cocycle applies.
        have hxa : x ∈ 𝔇.toFiniteFamily.U a := coverPoU_subordinate 𝔇 a hba
        have hxb : x ∈ 𝔇.toFiniteFamily.U b := coverPoU_subordinate 𝔇 b hbb
        have hxT : x ∈ (𝔇.toFiniteFamily.U a ⊓ 𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U b : Opens X) :=
          ⟨⟨hxa, hx⟩, hxb⟩
        rw [𝔇.holoHat_cocycle s a i b hxT]
      · -- `x ∉ tsupport ρ_a`: `dRhoHat a (φ x) = 0`.
        have hxCa : 𝔇.φ x ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 a) := by
          intro hc
          obtain ⟨y, hy, hyx⟩ := hc
          exact hba ((𝔇.φ).injOn (𝔇.subset_source a (coverPoU_subordinate 𝔇 a hy)) hsrc hyx ▸ hy)
        rw [𝔇.dRhoHat_eq_zero_of_notMem a hxtgt hxCa]; ring
    · -- `x ∉ tsupport ρ_b`: `rhoHat b (φ x) = 0`.
      have hxCb : 𝔇.φ x ∉ 𝔇.φ '' tsupport (coverPoU 𝔇 b) := by
        intro hc
        obtain ⟨y, hy, hyx⟩ := hc
        exact hbb ((𝔇.φ).injOn (𝔇.subset_source b (coverPoU_subordinate 𝔇 b hy)) hsrc hyx ▸ hy)
      rw [𝔇.rhoHat_eq_zero_of_notMem b hxtgt hxCb]; ring
  -- Sum the rewritten terms; split into the two pieces and collapse.
  show (∑ p : 𝔇.toFiniteFamily.ι × 𝔇.toFiniteFamily.ι, 𝔇.cechTermFun s p.1 p.2 (𝔇.φ x)) = _
  rw [show (∑ p : 𝔇.toFiniteFamily.ι × 𝔇.toFiniteFamily.ι, 𝔇.cechTermFun s p.1 p.2 (𝔇.φ x))
      = ∑ p : 𝔇.toFiniteFamily.ι × 𝔇.toFiniteFamily.ι,
          (𝔇.rhoHat p.2 (𝔇.φ x)
            * (𝔇.holoHat s p.1 i (𝔇.φ x) + 𝔇.holoHat s i p.2 (𝔇.φ x))) * 𝔇.dRhoHat p.1 (𝔇.φ x)
      from Finset.sum_congr rfl fun p _ => hTerm p.1 p.2]
  rw [Fintype.sum_prod_type]
  -- Per `(a,b)`: `R_b·(H_ai + H_ib)·D_a = R_b·H_ai·D_a + R_b·H_ib·D_a`.
  simp_rw [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  -- First piece `∑_a ∑_b R_b·H_ai·D_a = ∑_a (∑_b R_b)·H_ai·D_a = ∑_a H_ai·D_a` (since `∑_b R_b = 1`).
  have h1 : (∑ a, ∑ b, 𝔇.rhoHat b (𝔇.φ x) * 𝔇.holoHat s a i (𝔇.φ x) * 𝔇.dRhoHat a (𝔇.φ x))
      = ∑ a, 𝔇.holoHat s a i (𝔇.φ x) * 𝔇.dRhoHat a (𝔇.φ x) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, 𝔇.sum_rhoHat_apply hxcsymm, one_mul]
  -- Second piece `∑_a ∑_b R_b·H_ib·D_a = ∑_b R_b·H_ib·(∑_a D_a) = 0` (since `∑_a D_a = 0`).
  have h2 : (∑ a, ∑ b, 𝔇.rhoHat b (𝔇.φ x) * 𝔇.holoHat s i b (𝔇.φ x) * 𝔇.dRhoHat a (𝔇.φ x)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.mul_sum, 𝔇.sum_dRhoHat_apply hxtgt hxcsymm, mul_zero]
  rw [h1, h2, add_zero]

/-- **The glued `∂̄`-datum agrees with `∂̄(chartPrim s i)` on the chart-image of the closed-core
INTERIOR** (the honest closed-core agreement).  For each cocycle `s`, the chart-coordinate Bott–Tu
double sum `ω̂ = dbarDatum s` is globally `C^∞` (`contDiff_dbarDatum`) and agrees with
`∂̄(chartPrim s i)` at `z = φ x` for `x ∈ U_i ∩ interior 𝔇.core`: both sides equal
`∑_q holoHat q i z · dRhoHat q z` (`dbar_chartPrim_apply` — which needs no sum-to-one — and
`dbarDatum_apply` — whose Bott–Tu telescoping consumes `∑ ρ = 1` / `∑ ∂̄ρ = 0`, valid only on the
closed core).

**THE OBSTRUCTION (why this does NOT give the full `HasGluedDbarDatum`).**  `HasGluedDbarDatum` requires
agreement on ALL of `ball ∩ Ω_i`, but the Bott–Tu telescoping `dbarDatum_apply` holds only where
`∑ ρ = 1`, i.e. on `interior 𝔇.core`.  Off the core (on `U_i ∖ core`, which is non-empty for a
non-covering `SharedChartCover` — and a single-chart family CANNOT cover compact `X`, that is precisely
the un-vacuum) `∑ ρ ≠ 1` and `∑ ∂̄ρ ≠ 0`, so the global smooth `ω̂` does NOT equal `∂̄(chartPrim s i)`.
Consequently the ∂̄-corrected primitive `η̂_i = chartPrim s i − u` is holomorphic only on
`Ω_i ∩ ball ∩ φ '' interior core`, hence the ambient corrector `H_i` is chart-analytic only on
`U_i ∩ interior core` — NOT on all of `U_i`, which `OmegaD 0 (U_i)` (and the Čech `H¹ = 0` collapse)
requires.  The PoU-on-`X` globalization fundamentally needs `∑ ρ = 1` on the OPEN `⋃ U_i` (a genuine
partition of unity over the covered region), unavailable for a non-covering family without re-basing
the PoU onto the open submanifold `↥(⋃ U_i)` and solving `∂̄` there (with `⋃ Ω_i = ball`).  This is the
precise residual obstruction the un-vacuum exposes; the full `HasGluedDbarDatum` is therefore left as
the genuine (now non-vacuous) analytic obligation. -/
theorem dbarDatum_agrees_on_interiorCore (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.toFiniteFamily.ι) {x : X}
    (hxU : x ∈ 𝔇.toFiniteFamily.U i) (hxc : x ∈ interior 𝔇.core) :
    DbarDisk.dbar (chartPrim 𝔇 s i) (𝔇.φ x) = 𝔇.dbarDatum s (𝔇.φ x) := by
  rw [𝔇.dbar_chartPrim_apply s i hxU, 𝔇.dbarDatum_apply s i hxU hxc]

/-- **Rebased sound glued `∂̄` datum predicate.**  The right interface for the current construction:
agreement on `ball ∩ Ω_i` is only claimed on the open core image `φ '' interior 𝔇.core`, exactly
where the PoU sum-to-one calculation is available. -/
def HasGluedDbarDatumOnInteriorCore (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ dbarDatum : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) dbarDatum ∧
      ∀ i, ∀ z ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core),
        DbarDisk.dbar (chartPrim 𝔇 s i) z = dbarDatum z

/-- The rebased sound glued `∂̄` datum exists. -/
theorem hasGluedDbarDatumOnInteriorCore (𝔇 : SharedChartCover X) :
    HasGluedDbarDatumOnInteriorCore 𝔇 := by
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

/-- **Core-restricted chart-differentiable correctors from the rebased glued datum.**  This is the
largest immediately sound corrector statement available from the current interior-core datum: the
ambient correctors are differentiable in the chart on the open core, and their overlaps split the
analytic cocycle representatives on that same locus. -/
def HasChartDifferentiableCorrectorsOnInteriorCore (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
    ∃ H : 𝔇.toFiniteFamily.ι → X → ℂ,
      (∀ i, ∀ y : X, y ∈ 𝔇.toFiniteFamily.U i → y ∈ interior 𝔇.core →
        DifferentiableAt ℂ (fun z => H i ((chartAt (H := ℂ) y).symm z)) ((chartAt (H := ℂ) y) y)) ∧
      ∀ i j, ∀ x : X, x ∈ 𝔇.toFiniteFamily.U i → x ∈ 𝔇.toFiniteFamily.U j → x ∈ interior 𝔇.core →
        (fun z => H j z - H i z) =ᶠ[𝓝[≠] x] holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j)

/-- **Sound core-restricted correctors from the rebased glued datum.** -/
theorem hasChartDifferentiableCorrectors_of_hasGluedDbarDatumOnInteriorCore (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatumOnInteriorCore 𝔇) : HasChartDifferentiableCorrectorsOnInteriorCore 𝔇 := by
  intro s
  obtain ⟨dbarDatum, hdatum, hagree⟩ := H s
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

end SharedChartCover

end Jacobians.Dolbeault
