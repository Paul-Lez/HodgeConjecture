import KirovDolbeault.Montel.SupNorm
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Montel path — compactness of the closed unit ball

This file is the step-B decomposition of
`HolomorphicOneForms.closedBall_isCompact` in `Jacobians/Montel.lean`.
The classical outline (Ahlfors–Sario Ch II §5, Rudin Ch 14) proceeds:

1. `HOF X` embeds into `Π K ∈ chartCover, C(shrunkChart K, ℂ)` via
   `localRep`, continuous-linear with operator norm `≤ 1` under
   `supNormK` thanks to `norm_localRep_le_supNormK`.
2. Image of the unit ball is bounded by definition.
3. **Cauchy estimates**: `localRep α x₀` is analytic in chart
   coordinates ⇒ derivatives are bounded on slightly smaller sets.
4. **Arzelà–Ascoli**: bounded + equicontinuous + compact base
   ⇒ closed ball image relatively compact in `C(shrunkChart K, ℂ)`.
5. **Completeness / closedness**: uniform limits of holomorphic
   sections are holomorphic (via `TendstoLocallyUniformlyOn.analyticOn`).
6. Assembly: the closed unit ball is closed (under the sup-norm) and
   its image is relatively compact, hence compact.

This file lands step 1 — the continuous-map bundling of `localRep` on
the compact shrunk chart — as clean, complete API. Steps (3)–(6) are
completed across this file and `Complete.lean`.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff Topology
open Bundle Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step B.1 — `localRep` as a `ContinuousMap` on the shrunk chart

For `x₀ ∈ chartCover`, `shrunkChart x₀` is a compact subset of
`(chartAt ℂ x₀).source = (trivializationAt …).baseSet`, so
`localRep α x₀` is continuous there (via `localRep_continuousOn`).
We bundle this as `C(shrunkChart x₀, ℂ)` for downstream Arzelà–Ascoli.
-/

omit [ConnectedSpace X] [Nonempty X] in
/-- `shrunkChart x₀` is contained in the trivialization base set at `x₀`,
provided `x₀ ∈ chartCover`. -/
theorem shrunkChart_subset_baseSet (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    shrunkChart (X := X) x₀ ⊆
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet]
  exact shrunkChart_subset_source x₀ hx₀

omit [ConnectedSpace X] [Nonempty X] in
/-- `localRep α x₀` is continuous on the compact `shrunkChart x₀` for
`x₀ ∈ chartCover`. -/
theorem localRep_continuousOn_shrunkChart
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    ContinuousOn (localRep α x₀) (shrunkChart (X := X) x₀) :=
  (localRep_continuousOn α x₀).mono (shrunkChart_subset_baseSet x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The compact subtype `shrunkChart x₀` is a compact topological space
(automatic from `shrunkChart_isCompact`). -/
theorem shrunkChart_compactSpace (x₀ : X) :
    CompactSpace (shrunkChart (X := X) x₀) :=
  isCompact_iff_compactSpace.mp (shrunkChart_isCompact x₀)

/-- `localRep α x₀` bundled as a continuous map on the compact
`shrunkChart x₀`. Requires `x₀ ∈ chartCover` so that the shrunk chart
sits inside the trivialization base set where `localRep` is continuous.

For `x₀ ∉ chartCover`, `shrunkChart x₀ = ∅` (see `shrunkChart_eq_empty`),
so any continuous map out of it is vacuous; we still return a genuine
`C(shrunkChart x₀, ℂ)` by taking the restriction of the constant-zero
map in that case. -/
noncomputable def localRepOnShrunk
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : C(shrunkChart (X := X) x₀, ℂ) := by
  classical
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · -- `localRep α x₀` is continuous on `shrunkChart x₀` — restrict to subtype.
    exact
      { toFun := fun y => localRep α x₀ (y : X)
        continuous_toFun := by
          have h := localRep_continuousOn_shrunkChart α x₀ hx₀
          exact h.restrict }
  · exact
      { toFun := fun _ => 0
        continuous_toFun := continuous_const }

omit [ConnectedSpace X] [Nonempty X] in
/-- On the shrunk chart (for `x₀ ∈ chartCover`), `localRepOnShrunk` agrees
pointwise with `localRep`. -/
theorem localRepOnShrunk_apply
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y : shrunkChart (X := X) x₀) :
    localRepOnShrunk α x₀ y = localRep α x₀ (y : X) := by
  unfold localRepOnShrunk
  simp [hx₀]

/-! ### Step B.2 — pointwise norm bound on `localRepOnShrunk`

Under the `ContinuousMap.norm = sSup` identity on a compact `CompactSpace`,
the bundled form `localRepOnShrunk α x₀` has norm exactly `chartNormK α x₀`
— it bounds above by `supNormK α = ‖α‖`, establishing the component-wise
uniform bound on the image of the closed unit ball.

We avoid packaging the full product embedding `HOF X →L[ℂ] Π …` here
because the component-wise bound is what downstream Arzelà–Ascoli
actually consumes; product-norm bookkeeping adds complexity without
unlocking new content. -/

omit [ConnectedSpace X] in
/-- Component-wise bound: for `x₀ ∈ chartCover`, the bundled continuous
map `localRepOnShrunk α x₀` on the compact shrunk chart has norm ≤ the
global Montel sup-norm `supNormK α`. -/
theorem norm_localRepOnShrunk_le_supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := shrunkChart_compactSpace (X := X) x₀
    ‖localRepOnShrunk α x₀‖ ≤ HolomorphicOneForms.supNormK α := by
  letI := shrunkChart_compactSpace (X := X) x₀
  -- Non-empty vs empty shrunkChart split.
  by_cases hne : Nonempty (shrunkChart (X := X) x₀)
  · haveI := hne
    refine (ContinuousMap.norm_le_of_nonempty _).mpr ?_
    intro y
    have hy : (y : X) ∈ shrunkChart (X := X) x₀ := y.2
    calc ‖localRepOnShrunk α x₀ y‖
        = ‖localRep α x₀ (y : X)‖ := by
          rw [localRepOnShrunk_apply α hx₀ y]
      _ ≤ HolomorphicOneForms.supNormK α :=
          HolomorphicOneForms.norm_localRep_le_supNormK α hx₀ hy
  · -- Empty shrunk chart ⇒ ‖·‖ = 0 ≤ supNormK α.
    rw [not_nonempty_iff] at hne
    have h0 : localRepOnShrunk α x₀ = 0 := by
      ext y
      exact (hne.false y).elim
    rw [h0, norm_zero]
    exact HolomorphicOneForms.supNormK_nonneg α

/-! ### Inner analog: `localRepOnInnerShrunk` on `innerShrunkChart`

Inner closed shrinkage `innerShrunkChart x₀ ⊆ chartOpen x₀ ⊆ shrunkChart x₀`
gives the Arzelà–Ascoli domain: compact, covers X (in union over
`chartCover`), and has an OPEN `chartOpen x₀` neighborhood on which
`supNormK α` bounds `|localRep α x₀|`. This unlocks Cauchy-estimate
equicontinuity. -/

omit [ConnectedSpace X] [Nonempty X] in
theorem innerShrunkChart_subset_baseSet (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    innerShrunkChart (X := X) x₀ ⊆
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
  (innerShrunkChart_subset_shrunkChart x₀).trans (shrunkChart_subset_baseSet x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] in
theorem localRep_continuousOn_innerShrunkChart
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    ContinuousOn (localRep α x₀) (innerShrunkChart (X := X) x₀) :=
  (localRep_continuousOn α x₀).mono (innerShrunkChart_subset_baseSet x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem innerShrunkChart_compactSpace (x₀ : X) :
    CompactSpace (innerShrunkChart (X := X) x₀) :=
  isCompact_iff_compactSpace.mp (innerShrunkChart_isCompact x₀)

/-- `localRep α x₀` bundled as a continuous map on the compact inner
`innerShrunkChart x₀`. Fallback to constant zero for `x₀ ∉ chartCover`
(where `innerShrunkChart x₀ = ∅`). -/
noncomputable def localRepOnInnerShrunk
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : C(innerShrunkChart (X := X) x₀, ℂ) := by
  classical
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · exact
      { toFun := fun y => localRep α x₀ (y : X)
        continuous_toFun := by
          have h := localRep_continuousOn_innerShrunkChart α x₀ hx₀
          exact h.restrict }
  · exact
      { toFun := fun _ => 0
        continuous_toFun := continuous_const }

omit [ConnectedSpace X] [Nonempty X] in
theorem localRepOnInnerShrunk_apply
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y : innerShrunkChart (X := X) x₀) :
    localRepOnInnerShrunk α x₀ y = localRep α x₀ (y : X) := by
  unfold localRepOnInnerShrunk
  simp [hx₀]

omit [ConnectedSpace X] in
/-- Component-wise bound for the inner version: same `supNormK` bound
as outer, since `innerShrunkChart ⊆ shrunkChart` and the norm bound on
outer lifts to inner. -/
theorem norm_localRepOnInnerShrunk_le_supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    ‖localRepOnInnerShrunk α x₀‖ ≤ HolomorphicOneForms.supNormK α := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  by_cases hne : Nonempty (innerShrunkChart (X := X) x₀)
  · haveI := hne
    refine (ContinuousMap.norm_le_of_nonempty _).mpr ?_
    intro y
    have hy_inner : (y : X) ∈ innerShrunkChart (X := X) x₀ := y.2
    have hy_outer : (y : X) ∈ shrunkChart (X := X) x₀ :=
      innerShrunkChart_subset_shrunkChart x₀ hy_inner
    calc ‖localRepOnInnerShrunk α x₀ y‖
        = ‖localRep α x₀ (y : X)‖ := by rw [localRepOnInnerShrunk_apply α hx₀ y]
      _ ≤ HolomorphicOneForms.supNormK α :=
          HolomorphicOneForms.norm_localRep_le_supNormK α hx₀ hy_outer
  · rw [not_nonempty_iff] at hne
    have h0 : localRepOnInnerShrunk α x₀ = 0 := by
      ext y
      exact (hne.false y).elim
    rw [h0, norm_zero]
    exact HolomorphicOneForms.supNormK_nonneg α

/-! ### Bridge: open-neighborhood bound on `localRep`

The `Cover.lean` refactor exposes an open layer `chartOpen x₀` sitting
inside the outer closed `shrunkChart x₀`. Since `supNormK α` bounds
`|localRep α x₀|` on `shrunkChart x₀`, it also bounds it on the OPEN
`chartOpen x₀` — giving Arzelà–Ascoli the wiggle room it needs to apply
Cauchy estimates on a neighborhood of the inner compact. -/

omit [ConnectedSpace X] in
/-- `|localRep α x₀| ≤ supNormK α` on the OPEN layer `chartOpen x₀`
(for `x₀ ∈ chartCover`). Since `chartOpen x₀ ⊆ shrunkChart x₀`, this is
immediate from `norm_localRep_le_supNormK`. -/
theorem norm_localRep_le_supNormK_on_chartOpen
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ chartOpen (X := X) x₀) :
    ‖localRep α x₀ y‖ ≤ HolomorphicOneForms.supNormK α :=
  HolomorphicOneForms.norm_localRep_le_supNormK α hx₀
    (chartOpen_subset_shrunkChart x₀ hy)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- `chartOpen x₀` is contained in the chart source for `x₀ ∈ chartCover`. -/
theorem chartOpen_subset_source (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    chartOpen (X := X) x₀ ⊆ (chartAt ℂ x₀).source :=
  (chartOpen_subset_shrunkChart x₀).trans (shrunkChart_subset_source x₀ hx₀)

/-! ### Step B.3 — `localRep` is analytic in chart coordinates

The `ContMDiff ω ⇔ AnalyticOn ℂ` bridge at bundle-section level:
`z ↦ localRep α x₀ ((chartAt ℂ x₀).symm z)` is analytic on the chart
target (an open subset of `ℂ`).

**Proof outline.**
1. `α.contMDiff_toFun` gives smoothness of α as a bundle section in the
   Hom bundle globally.
2. The constant-1 frame tangent vector
   `y ↦ TotalSpace.mk' ℂ y (e.symmL ℂ y 1)` is `ContMDiffOn ω` on
   `e.baseSet` (from `e.contMDiffOn_section_baseSet_iff`: its
   trivialization representative is the constant function `1`, which
   is smooth).
3. `ContMDiffOn.clm_bundle_apply` combines (1) and (2) to give
   smoothness of `y ↦ TotalSpace.mk' ℂ y (localRep α x₀ y)` as a
   section of the Trivial ℂ bundle.
4. `contMDiffWithinAt_section` on the Trivial bundle (whose
   trivialization projection is the identity) extracts scalar
   smoothness `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localRep α x₀) e.baseSet`.
5. `contMDiffOn_iff` unfolds manifold-smoothness into
   `ContDiffOn ℂ ω (f ∘ (chartAt ℂ x₀).symm)` on the chart target
   (using `extChartAt 𝓘(ℂ) = chartAt ℂ` for ℂ as its own model).
6. `contDiffOn_omega_iff_analyticOn` on the open chart target
   concludes `AnalyticOn`. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The trivialization base set at `x₀` equals `(chartAt ℂ x₀).source`
(specialization of `TangentBundle.trivializationAt_baseSet`). -/
theorem baseSet_eq_chartAt_source (x₀ : X) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet =
      (chartAt ℂ x₀).source :=
  TangentBundle.trivializationAt_baseSet x₀

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The constant-1 tangent-frame section
`y ↦ (trivializationAt …).symmL ℂ y 1` is smooth as a bundle section
on the trivialization's base set. Proof: via
`Trivialization.contMDiffOn_section_baseSet_iff`, equivalent to
smoothness of the trivialization representative, which equals the
constant `1 : ℂ` on the base set. -/
theorem contMDiffOn_frame
    (x₀ : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun y : X => TotalSpace.mk' ℂ
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x) y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  rw [(trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).contMDiffOn_section_baseSet_iff]
  have hconst : Set.EqOn
      (fun y : X =>
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀)
          ⟨y, (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1⟩).2)
      (fun _ : X => (1 : ℂ))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy
    simp only
    have hsymmL :
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1 =
          (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symm y 1 := rfl
    rw [hsymmL]
    have hmk :
        (⟨y, (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symm y 1⟩ :
          TotalSpace ℂ (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x)) =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).toOpenPartialHomeomorph.symm (y, 1) :=
      Trivialization.mk_symm _ hy 1
    rw [hmk]
    simp [(trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).apply_symm_apply' hy]
  exact contMDiffOn_const.congr hconst

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Scalar smoothness of `localRep α x₀` as a function `X → ℂ` on the
chart source (= trivialization base set). Combines `α.contMDiff_toFun`,
`contMDiffOn_frame`, and `ContMDiffOn.clm_bundle_apply` via scalar
extraction on the Trivial bundle. -/
theorem localRep_contMDiffOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localRep α x₀)
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  have hα : ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        x (α.toFun x))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    α.contMDiff_toFun.contMDiffOn
  have happ : ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun y : X => TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) y (localRep α x₀ y))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    hα.clm_bundle_apply (contMDiffOn_frame x₀)
  intro y hy
  have h := happ y hy
  rw [contMDiffWithinAt_section] at h
  have heqPt : ∀ x : X,
      ((trivializationAt ℂ (Bundle.Trivial X ℂ) y) ⟨x, localRep α x₀ x⟩).2 = localRep α x₀ x := by
    intro x
    simp [Bundle.Trivial.trivialization]
  exact h.congr (fun x _ => heqPt x) (heqPt y)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- **Step B.3 — the holomorphicity bridge.**
In chart coordinates at `x₀`, the local representative of a holomorphic
1-form α is analytic on the chart target.

Proof chain:
1. `localRep_contMDiffOn` gives `ContMDiffOn ω` on the chart source.
2. `contMDiffOn_iff` reduces this to `ContDiffOn ℂ ω` in chart
   coordinates (using that ℂ's `extChartAt` is essentially the
   identity).
3. `contDiffOn_omega_iff_analyticOn` on the open chart target
   promotes `ContDiffOn ω` ⇒ `AnalyticOn`. -/
theorem localRep_analyticOn_chartTarget
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    AnalyticOn ℂ (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z))
      (chartAt ℂ x₀).target := by
  -- Step 1: manifold smoothness on the chart source.
  have hfm : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localRep α x₀) (chartAt ℂ x₀).source := by
    rw [← baseSet_eq_chartAt_source x₀]
    exact localRep_contMDiffOn α x₀
  -- Step 2: unfold contMDiffOn_iff to ContDiffOn ℂ ω via ℂ's identity model.
  rw [contMDiffOn_iff] at hfm
  obtain ⟨_, hf_chart⟩ := hfm
  have hCD := hf_chart x₀ (0 : ℂ)
  have h1 : (extChartAt 𝓘(ℂ, ℂ) x₀).target = (chartAt ℂ x₀).target := by simp [extChartAt]
  have h2 : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
  have h3 : ∀ z, (extChartAt 𝓘(ℂ, ℂ) x₀).symm z = (chartAt ℂ x₀).symm z := by
    intro z; simp [extChartAt]
  have h4 : ∀ z, (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)) z = z := by intro z; simp [extChartAt]
  rw [h2, Set.preimage_univ, Set.inter_univ] at hCD
  have hset : (extChartAt 𝓘(ℂ, ℂ) x₀).target ∩
      (extChartAt 𝓘(ℂ, ℂ) x₀).symm ⁻¹' (chartAt ℂ x₀).source = (chartAt ℂ x₀).target := by
    ext z
    refine ⟨fun ⟨htgt, _⟩ => by rw [h1] at htgt; exact htgt, fun hz => ?_⟩
    refine ⟨h1 ▸ hz, ?_⟩
    simp only [Set.mem_preimage]
    rw [h3]
    exact (chartAt ℂ x₀).map_target hz
  rw [hset] at hCD
  have hfun : ((extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)) ∘ localRep α x₀ ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z)) := by
    funext z
    simp [Function.comp_def]
  rw [hfun] at hCD
  -- Step 3: ContDiffOn ω ↔ AnalyticOn via UniqueDiffOn on open set.
  exact (contDiffOn_omega_iff_analyticOn (chartAt ℂ x₀).open_target.uniqueDiffOn).mp hCD

/-! ### Chart-image bridge to complex analysis

The chart image `(chartAt ℂ x₀) '' chartOpen x₀` is open in `ℂ`, and on
it the pullback `localRep α x₀ ∘ chart.symm` is both analytic (from B.3
+ monotonicity) and bounded by `supNormK α` (from the open-neighborhood
bound). This is the direct input to Arzelà–Ascoli on the chart side. -/

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart image of `chartOpen x₀` is open in `ℂ`. -/
theorem isOpen_chart_image_chartOpen (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    IsOpen ((chartAt ℂ x₀) '' chartOpen (X := X) x₀) := by
  apply (chartAt ℂ x₀).isOpen_image_iff_of_subset_source (chartOpen_subset_source x₀ hx₀) |>.mpr
  exact chartOpen_isOpen x₀

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart image of `chartOpen x₀` sits inside the chart target. -/
theorem chart_image_chartOpen_subset_target (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    (chartAt ℂ x₀) '' chartOpen (X := X) x₀ ⊆ (chartAt ℂ x₀).target := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact (chartAt ℂ x₀).map_source (chartOpen_subset_source x₀ hx₀ hy)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- `innerChartOpen x₀ ⊆ (chartAt ℂ x₀).source` for `x₀ ∈ chartCover`.
`innerChartOpen ⊆ closure(innerChartOpen) ⊆ chartOpen ⊆ chartAt source`. -/
theorem innerChartOpen_subset_source
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    innerChartOpen (X := X) x₀ ⊆ (chartAt ℂ x₀).source :=
  (subset_closure.trans (closure_innerChartOpen_subset_chartOpen x₀)).trans
    (chartOpen_subset_source x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart image of `innerChartOpen x₀` is open in `ℂ`. -/
theorem isOpen_chart_image_innerChartOpen
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    IsOpen ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀) := by
  apply (chartAt ℂ x₀).isOpen_image_iff_of_subset_source
    (innerChartOpen_subset_source x₀ hx₀) |>.mpr
  exact innerChartOpen_isOpen x₀

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart image of `innerChartOpen x₀` sits inside the chart target. -/
theorem chart_image_innerChartOpen_subset_target
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    (chartAt ℂ x₀) '' innerChartOpen (X := X) x₀ ⊆ (chartAt ℂ x₀).target := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact (chartAt ℂ x₀).map_source (innerChartOpen_subset_source x₀ hx₀ hy)

omit [ConnectedSpace X] [Nonempty X] in
/-- Pullback analyticity on the chart image of `innerChartOpen x₀`. -/
theorem localRep_analyticOn_chart_image_innerChartOpen
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    AnalyticOn ℂ (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z))
      ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀) :=
  (localRep_analyticOn_chartTarget α x₀).mono
    (chart_image_innerChartOpen_subset_target x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] in
/-- Pullback analyticity on the chart image of `chartOpen x₀`. Direct
specialization of `localRep_analyticOn_chartTarget` via
`AnalyticOn.mono`. -/
theorem localRep_analyticOn_chart_image_chartOpen
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    AnalyticOn ℂ (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z))
      ((chartAt ℂ x₀) '' chartOpen (X := X) x₀) :=
  (localRep_analyticOn_chartTarget α x₀).mono (chart_image_chartOpen_subset_target x₀ hx₀)

omit [ConnectedSpace X] in
/-- The pullback `localRep α x₀ ∘ chart.symm` is bounded by `supNormK α`
on the chart image of `chartOpen x₀`. -/
theorem norm_localRep_pullback_le_supNormK_on_chart_image_chartOpen
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {z : ℂ} (hz : z ∈ (chartAt ℂ x₀) '' chartOpen (X := X) x₀) :
    ‖localRep α x₀ ((chartAt ℂ x₀).symm z)‖ ≤ HolomorphicOneForms.supNormK α := by
  obtain ⟨y, hy, hzy⟩ := hz
  have hy_src : y ∈ (chartAt ℂ x₀).source := chartOpen_subset_source x₀ hx₀ hy
  have hsymm : (chartAt ℂ x₀).symm z = y := by
    rw [← hzy]; exact (chartAt ℂ x₀).left_inv hy_src
  rw [hsymm]
  exact norm_localRep_le_supNormK_on_chartOpen α hx₀ hy

/-! ### Step B.4 — Cauchy estimate: uniform derivative bound on compacta

Pure complex analysis (no bundles). For an analytic function `f : ℂ → ℂ`
on an open set `U`, bounded by `C` on `U`, the derivative is bounded by
`L · C` on any compact `K ⊂ U`, where `L = 1/δ` and `δ > 0` is a
thickening radius with `cthickening δ K ⊆ U` (which exists by
`IsCompact.exists_cthickening_subset_open`).

The derivative bound `L` depends only on `U` and `K`, not on `f`, so
this lemma directly yields **uniform** derivative bounds for families
of analytic functions — precisely what Arzelà–Ascoli needs. -/

/-- Cauchy estimate on a compact subset of an open set: for `f`
analytic on `U` with `‖f‖ ≤ C`, `‖deriv f z‖ ≤ L · C` for all `z ∈ K`,
with `L = 1/δ` depending only on `K ⊂ U`. -/
theorem exists_cauchy_deriv_bound
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : ℂ → ℂ), AnalyticOn ℂ f U → ∀ C : ℝ,
      (∀ z ∈ U, ‖f z‖ ≤ C) → ∀ z ∈ K, ‖deriv f z‖ ≤ L * C := by
  obtain ⟨δ, hδpos, hδsub⟩ := hKcpt.exists_cthickening_subset_open hU hKU
  refine ⟨1 / δ, by positivity, fun f hf C hfb z hz => ?_⟩
  have hclosedBall : Metric.closedBall z δ ⊆ U := by
    have h1 : Metric.closedBall z δ ⊆ Metric.cthickening δ K := by
      intro w hw
      rw [hKcpt.cthickening_eq_biUnion_closedBall hδpos.le]
      exact Set.mem_biUnion hz hw
    exact h1.trans hδsub
  have hAnalBall : AnalyticOn ℂ f (Metric.closedBall z δ) := hf.mono hclosedBall
  have hdcoc : DiffContOnCl ℂ f (Metric.ball z δ) :=
    ⟨(hAnalBall.mono Metric.ball_subset_closedBall).differentiableOn,
     by rw [closure_ball z hδpos.ne']; exact hAnalBall.continuousOn⟩
  have hsphere : ∀ w ∈ Metric.sphere z δ, ‖f w‖ ≤ C := fun w hw =>
    hfb w (hclosedBall (Metric.sphere_subset_closedBall hw))
  have hcd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδpos hdcoc hsphere
  calc ‖deriv f z‖ ≤ C / δ := hcd
    _ = 1 / δ * C := by ring

/-! ### Limits of analytic families (building block for B.10)

The classical "uniform limit of holomorphic is holomorphic" result,
packaged for our use: `TendstoLocallyUniformlyOn.differentiableOn`
combined with `DifferentiableOn.analyticOn` on open ℂ-sets. -/

/-- **Uniform-local limits of analytic functions are analytic.**
A locally-uniform limit of `AnalyticOn` functions on an open `U ⊆ ℂ`
is itself `AnalyticOn U`. -/
theorem analyticOn_of_tendstoLocallyUniformlyOn
    {ι : Type*} {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {φ : Filter ι} [φ.NeBot]
    (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, AnalyticOn ℂ (F n) U) :
    AnalyticOn ℂ f U := by
  have h_diff : DifferentiableOn ℂ f U :=
    TendstoLocallyUniformlyOn.differentiableOn hlim
      (by filter_upwards [hF] with n hn using hn.differentiableOn) hU
  exact h_diff.analyticOn hU

omit [ConnectedSpace X] [Nonempty X] in
/-- **Chart-pullback analytic limit.** Given a sequence of holomorphic
1-forms whose chart-pullbacks converge locally uniformly on
`chart '' chartOpen x₀`, the limit function is analytic there.

Specialization of `analyticOn_of_tendstoLocallyUniformlyOn` to our
pulled-back family. Used downstream in B.10 to reconstruct the limit
section's chart representatives as analytic functions. -/
theorem analyticOn_of_pullback_tendsto_locally_uniformly
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    (αf : ι → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun n : ι => fun z : ℂ => localRep (αf n) x₀ ((chartAt ℂ x₀).symm z))
      g φ ((chartAt ℂ x₀) '' chartOpen (X := X) x₀)) :
    AnalyticOn ℂ g ((chartAt ℂ x₀) '' chartOpen (X := X) x₀) := by
  apply analyticOn_of_tendstoLocallyUniformlyOn (isOpen_chart_image_chartOpen x₀ hx₀)
    hconv
  filter_upwards with n
  exact localRep_analyticOn_chart_image_chartOpen (αf n) x₀ hx₀

omit [ConnectedSpace X] [Nonempty X] in
/-- **Chart-pullback analytic limit on `innerChartOpen`.** Inner-open
variant of `analyticOn_of_pullback_tendsto_locally_uniformly`. Needed
when we can only establish locally uniform convergence on the smaller
`chart '' innerChartOpen x₀` (as arises from bcf-convergence on the
compact `innerShrunkChart x₀`, restricted to its open interior). -/
theorem analyticOn_of_pullback_tendsto_locally_uniformly_inner
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    (αf : ι → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (g : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun n : ι => fun z : ℂ => localRep (αf n) x₀ ((chartAt ℂ x₀).symm z))
      g φ ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀)) :
    AnalyticOn ℂ g ((chartAt ℂ x₀) '' innerChartOpen (X := X) x₀) := by
  apply analyticOn_of_tendstoLocallyUniformlyOn
    (isOpen_chart_image_innerChartOpen x₀ hx₀) hconv
  filter_upwards with n
  exact localRep_analyticOn_chart_image_innerChartOpen (αf n) x₀ hx₀

/-! ### Step B.5 — Uniform Lipschitz bound on convex compacta

Combining B.4's uniform derivative bound with the mean-value inequality
on a convex set gives a uniform Lipschitz bound for the family of
analytic functions on `U` uniformly bounded by `C`, restricted to any
**convex** compact `K ⊂ U`:

  `‖f z - f w‖ ≤ L · C · ‖z - w‖`   for z, w ∈ K,

with `L = 1/δ` depending only on `U`, `K`.

Convexity of `K` is required for the mean-value inequality
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`). A general
compact `K ⊂ U` can be covered by finitely many closed balls inside
`U`; equicontinuity then transfers from each ball to `K`. For our
downstream Arzelà–Ascoli use, applying this to a closed ball `closedBall
z₀ r` (convex) strictly inside the chart target is sufficient — the
closedBall form is what will bridge to the manifold side. -/

/-- Uniform Lipschitz bound for a family of analytic functions bounded
on an open set, restricted to a convex compact subset. -/
theorem exists_cauchy_lipschitz_bound
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U)
    (hKconv : Convex ℝ K) :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : ℂ → ℂ), AnalyticOn ℂ f U → ∀ C : ℝ,
      (∀ z ∈ U, ‖f z‖ ≤ C) → ∀ z ∈ K, ∀ w ∈ K, ‖f z - f w‖ ≤ L * C * ‖z - w‖ := by
  obtain ⟨L, hLpos, hLbd⟩ := exists_cauchy_deriv_bound hU hKcpt hKU
  refine ⟨L, hLpos, fun f hf C hfb z hz w hw => ?_⟩
  have hderBnd : ∀ x ∈ K, ‖deriv f x‖ ≤ L * C := hLbd f hf C hfb
  have hhasDer : ∀ x ∈ K, HasDerivWithinAt f (deriv f x) K x := by
    intro x hx
    have hx_in_U : x ∈ U := hKU hx
    have hdiff : DifferentiableAt ℂ f x :=
      (hf.differentiableOn x hx_in_U).differentiableAt (hU.mem_nhds hx_in_U)
    exact hdiff.hasDerivAt.hasDerivWithinAt
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hhasDer hderBnd hKconv hw hz

/-! ### Step B.6 — Uniform equicontinuity from a bounded analytic family

The direct corollary of B.5: a family of analytic functions on open
`U ⊂ ℂ` uniformly bounded on `U` is **uniformly equicontinuous** on any
convex compact `K ⊂ U`. This is the exact hypothesis Arzelà–Ascoli
needs (up to the BoundedContinuousFunction wrapping).

For a single fixed bound `C`, we express this as a uniform Lipschitz
constant that works for the whole family, then invoke Mathlib's
`LipschitzOnWith.uniformEquicontinuousOn`. -/

/-- A bounded family of analytic functions on open `U` is uniformly
equicontinuous on any convex compact `K ⊂ U`.

Note: requires `0 ≤ C` (trivially true if `U` is nonempty — take any
`z ∈ U` and use `‖f z‖ ≤ C`; stated explicitly here to avoid
case-splitting). -/
theorem uniformEquicontinuousOn_of_bounded_analyticOn
    {ι : Type*} {U K : Set ℂ} {f : ι → ℂ → ℂ} {C : ℝ}
    (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) (hKconv : Convex ℝ K)
    (hCnn : 0 ≤ C)
    (hf : ∀ i, AnalyticOn ℂ (f i) U)
    (hfb : ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    UniformEquicontinuousOn f K := by
  obtain ⟨L, hLpos, hLip⟩ := exists_cauchy_lipschitz_bound hU hKcpt hKU hKconv
  have hLC_nn : 0 ≤ L * C := mul_nonneg hLpos.le hCnn
  refine LipschitzOnWith.uniformEquicontinuousOn f (L * C).toNNReal ?_
  intro i
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro z hz w hw
  rw [Real.coe_toNNReal _ hLC_nn, dist_eq_norm, dist_eq_norm]
  exact hLip (f i) (hf i) C (hfb i) z hz w hw

/-! ### Step B.7a — Equicontinuity of the inner family at each point

For a uniformly bounded family of holomorphic 1-forms (`supNormK α ≤ M`),
the associated family `{localRepOnInnerShrunk α x₀}` is equicontinuous
at each point `y₀ ∈ innerShrunkChart x₀`.

The proof goes through the chart `φ = chartAt ℂ x₀`:
1. `φ y₀` lies in the open set `φ '' chartOpen x₀` (via the sequence of
   subset inclusions `innerShrunkChart ⊆ chartOpen`).
2. Pick a closed ball `B̄(φ y₀, r) ⊆ φ '' chartOpen` (convex, compact).
3. Apply B.6 on `B̄(φ y₀, r)`: pullback family is uniformly
   equicontinuous there — specifically, there's a `δ` s.t. for any two
   points in the closed ball within `δ`, pullback values are within `ε`.
4. Transfer: for `y ∈ innerShrunkChart x₀` near `y₀` (in the sense
   that `φ y` is within `min(r, δ)` of `φ y₀`), use step (3) to bound
   `|localRep α x₀ y - localRep α x₀ y₀|`. Chart continuity at `y₀`
   ensures such `y` form a neighborhood of `y₀` in the subtype. -/

omit [ConnectedSpace X] in
/-- For a holomorphic 1-form bounded by `M` under `supNormK`, the
pullback through the chart at `x₀` is bounded by `M` on
`chart '' chartOpen x₀`. Packaging of earlier bridge lemmas. -/
theorem norm_localRep_pullback_le_of_supNormK_le
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {M : ℝ} (hαM : HolomorphicOneForms.supNormK α ≤ M)
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {z : ℂ} (hz : z ∈ (chartAt ℂ x₀) '' chartOpen (X := X) x₀) :
    ‖localRep α x₀ ((chartAt ℂ x₀).symm z)‖ ≤ M := by
  calc ‖localRep α x₀ ((chartAt ℂ x₀).symm z)‖
      ≤ HolomorphicOneForms.supNormK α :=
        norm_localRep_pullback_le_supNormK_on_chart_image_chartOpen α hx₀ hz
    _ ≤ M := hαM

/-! ### Step B.7b — Equicontinuity of the inner family

Assembles local equicontinuity via B.6 on a closed ball inside
`chart '' chartOpen`, then transfers back to `innerShrunkChart x₀` via
chart continuity. -/

omit [ConnectedSpace X] in
/-- **Equicontinuity of the inner family.**
For each `y₀ : innerShrunkChart x₀` and ε > 0, there's an X-nbhd V of
`y₀.val` with: `‖localRep α x₀ y - localRep α x₀ y₀.val‖ < ε` for all
`α` with `supNormK α ≤ M` and all `y ∈ V ∩ innerShrunkChart x₀`.

Proof: via B.6 on a closed ball `closedBall (chart y₀) r` strictly
inside the open `chart '' chartOpen x₀`, then transfer through chart
continuity at `y₀`. -/
theorem equicontinuousAt_localRep_on_innerShrunkChart
    (M : ℝ) (hMnn : 0 ≤ M) {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y₀ : X) (hy₀ : y₀ ∈ innerShrunkChart (X := X) x₀) :
    ∀ ε > 0, ∃ V ∈ 𝓝 y₀, ∀ y ∈ V, ∀ α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x),
        HolomorphicOneForms.supNormK α ≤ M →
        y ∈ innerShrunkChart (X := X) x₀ →
        ‖localRep α x₀ y - localRep α x₀ y₀‖ ≤ ε := by
  intro ε hε
  -- z₀ = chart(y₀); lives in chart '' chartOpen (open).
  set z₀ := (chartAt ℂ x₀) y₀ with hz₀_def
  have hy₀_chartOpen : y₀ ∈ chartOpen (X := X) x₀ :=
    innerShrunkChart_subset_chartOpen x₀ hy₀
  have hy₀_src : y₀ ∈ (chartAt ℂ x₀).source :=
    chartOpen_subset_source x₀ hx₀ hy₀_chartOpen
  have hz₀_in : z₀ ∈ (chartAt ℂ x₀) '' chartOpen (X := X) x₀ :=
    ⟨y₀, hy₀_chartOpen, rfl⟩
  -- chart '' chartOpen is open in ℂ; pick r > 0 with closedBall z₀ r ⊂ chart '' chartOpen.
  have hopenU : IsOpen ((chartAt ℂ x₀) '' chartOpen (X := X) x₀) :=
    isOpen_chart_image_chartOpen x₀ hx₀
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hopenU z₀ hz₀_in
  -- Use closedBall z₀ (r/2) ⊂ ball z₀ r (strict) ⊂ chart '' chartOpen.
  have hr2pos : 0 < r / 2 := by linarith
  have hclosed_sub : Metric.closedBall z₀ (r/2) ⊆ (chartAt ℂ x₀) '' chartOpen (X := X) x₀ := by
    intro z hz
    have : z ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball]
      have : dist z z₀ ≤ r/2 := Metric.mem_closedBall.mp hz
      linarith
    exact hr_sub this
  -- B.6 on closedBall z₀ (r/2): UniformEquicontinuousOn of the pullback family.
  set U := (chartAt ℂ x₀) '' chartOpen (X := X) x₀
  set K := Metric.closedBall z₀ (r/2)
  -- Index family by α with supNormK ≤ M.
  let ι := {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
      HolomorphicOneForms.supNormK α ≤ M}
  let F : ι → ℂ → ℂ := fun α z => localRep α.1 x₀ ((chartAt ℂ x₀).symm z)
  have hF_analytic : ∀ i : ι, AnalyticOn ℂ (F i) U :=
    fun i => localRep_analyticOn_chart_image_chartOpen i.1 x₀ hx₀
  have hF_bound : ∀ i : ι, ∀ z ∈ U, ‖F i z‖ ≤ M := fun i z hz =>
    norm_localRep_pullback_le_of_supNormK_le i.1 i.2 hx₀ hz
  have hK_cpt : IsCompact K := isCompact_closedBall _ _
  have hK_conv : Convex ℝ K := convex_closedBall _ _
  have hK_sub : K ⊆ U := hclosed_sub
  have hEqui : UniformEquicontinuousOn F K :=
    uniformEquicontinuousOn_of_bounded_analyticOn hopenU hK_cpt hK_sub hK_conv hMnn
      hF_analytic hF_bound
  -- Convert to UniformEquicontinuous on subtype K and use Metric characterization.
  rw [← uniformEquicontinuous_restrict_iff] at hEqui
  rw [Metric.uniformEquicontinuous_iff] at hEqui
  obtain ⟨δ, hδpos, hδbd⟩ := hEqui ε hε
  -- Now find X-nbhd V of y₀ such that y ∈ V ⇒ chart y is close to chart y₀.
  -- chart is continuous at y₀ (since y₀ ∈ chart source).
  have h_chart_cont : ContinuousAt ((chartAt ℂ x₀) : X → ℂ) y₀ :=
    (chartAt ℂ x₀).continuousAt hy₀_src
  have hρ_pos : 0 < min (r/2) δ := lt_min hr2pos hδpos
  -- Neighborhood V: y ∈ (chartAt ℂ x₀).source ∩ chart⁻¹' (ball z₀ (min (r/2) δ))
  have hball_mem : Metric.ball z₀ (min (r/2) δ) ∈ 𝓝 z₀ :=
    Metric.ball_mem_nhds _ hρ_pos
  have hpreimage : (chartAt ℂ x₀) ⁻¹' Metric.ball z₀ (min (r/2) δ) ∈ 𝓝 y₀ := by
    apply h_chart_cont.preimage_mem_nhds
    exact hball_mem
  have hsource_nhds : (chartAt ℂ x₀).source ∈ 𝓝 y₀ :=
    (chartAt ℂ x₀).open_source.mem_nhds hy₀_src
  refine ⟨(chartAt ℂ x₀) ⁻¹' Metric.ball z₀ (min (r/2) δ) ∩ (chartAt ℂ x₀).source,
    Filter.inter_mem hpreimage hsource_nhds, ?_⟩
  intro y hyV α hαM hy_inner
  obtain ⟨hy_preimg, hy_src⟩ := hyV
  -- chart y is in ball(z₀, min (r/2) δ) ⊂ closedBall(z₀, r/2) = K.
  have hchart_y_ball : (chartAt ℂ x₀) y ∈ Metric.ball z₀ (min (r/2) δ) := hy_preimg
  have hchart_y_K : (chartAt ℂ x₀) y ∈ K := by
    have : dist ((chartAt ℂ x₀) y) z₀ < min (r/2) δ := Metric.mem_ball.mp hchart_y_ball
    have : dist ((chartAt ℂ x₀) y) z₀ ≤ r/2 := by
      have := lt_of_lt_of_le this (min_le_left _ _)
      exact this.le
    exact Metric.mem_closedBall.mp (Metric.mem_closedBall.mpr this)
  have hchart_y₀_K : z₀ ∈ K := Metric.mem_closedBall_self hr2pos.le
  -- Apply hδbd with subtype elements.
  have hdist_chart : dist ((chartAt ℂ x₀) y) z₀ < δ := by
    have : dist ((chartAt ℂ x₀) y) z₀ < min (r/2) δ := Metric.mem_ball.mp hchart_y_ball
    exact lt_of_lt_of_le this (min_le_right _ _)
  have hdist_sub : dist (⟨(chartAt ℂ x₀) y, hchart_y_K⟩ : K) ⟨z₀, hchart_y₀_K⟩ < δ := by
    simp [Subtype.dist_eq]; exact hdist_chart
  have hFbound := hδbd ⟨(chartAt ℂ x₀) y, hchart_y_K⟩ ⟨z₀, hchart_y₀_K⟩ hdist_sub ⟨α, hαM⟩
  -- Unfold K.restrict ∘ F.
  change dist (localRep α x₀ ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) y)))
           (localRep α x₀ ((chartAt ℂ x₀).symm z₀)) < ε at hFbound
  -- chart.symm (chart y) = y (on source), and chart.symm z₀ = y₀.
  have hsymm_y : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) y) = y :=
    (chartAt ℂ x₀).left_inv hy_src
  have hsymm_y₀ : (chartAt ℂ x₀).symm z₀ = y₀ :=
    (chartAt ℂ x₀).left_inv hy₀_src
  rw [hsymm_y, hsymm_y₀, dist_eq_norm] at hFbound
  exact hFbound.le

omit [ConnectedSpace X] in
/-- **Equicontinuous family on `innerShrunkChart x₀`.**
The family indexed by `α` with `supNormK α ≤ M` of functions
`(y : innerShrunkChart x₀) ↦ localRep α x₀ y.val` is `Equicontinuous`,
i.e., pointwise equicontinuous at every point. Derived from
`equicontinuousAt_localRep_on_innerShrunkChart` by packaging the
neighborhood-in-X witness into the subtype neighborhood via
`nhds_subtype`. -/
theorem equicontinuous_localRep_inner_family
    (M : ℝ) (hMnn : 0 ≤ M) {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    Equicontinuous
      (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
          (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
          HolomorphicOneForms.supNormK α ≤ M} =>
        fun y : innerShrunkChart (X := X) x₀ => localRep α.1 x₀ (y : X)) := by
  intro y₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨V, hV_nhds, hV_bd⟩ :=
    equicontinuousAt_localRep_on_innerShrunkChart M hMnn hx₀ y₀.1 y₀.2 (ε/2) (by linarith)
  -- Show Subtype.val ⁻¹' V ∈ 𝓝 y₀.
  rw [nhds_subtype]
  rw [Filter.eventually_comap]
  filter_upwards [hV_nhds] with y' hy' y hy_eq
  -- y : innerShrunkChart x₀, y.val = y' ∈ V.
  have hy_inner : y.val ∈ innerShrunkChart (X := X) x₀ := y.2
  have hy_in_V : y.val ∈ V := hy_eq ▸ hy'
  intro α
  have := hV_bd y.val hy_in_V α.1 α.2 hy_inner
  -- Need: dist (F α y₀) (F α y) < ε. We have ‖localRep α.1 x₀ y.val - localRep α.1 x₀ y₀.val‖ ≤ ε/2.
  rw [dist_eq_norm]
  calc ‖localRep α.1 x₀ (y₀ : X) - localRep α.1 x₀ (y : X)‖
      = ‖localRep α.1 x₀ (y : X) - localRep α.1 x₀ (y₀ : X)‖ := norm_sub_rev _ _
    _ ≤ ε/2 := this
    _ < ε := by linarith

/-! ### Step B.8 — Arzelà–Ascoli on each chart

Applies `BoundedContinuousFunction.arzela_ascoli` per chart: bounded +
equicontinuous (both now in place) gives relative compactness of the
inner-shrunk-chart image in `α →ᵇ ℂ`. -/

omit [ConnectedSpace X] in
/-- **Per-chart relative compactness.**
The image of the supNormK-`M`-ball under `α ↦ mkOfCompact ∘
localRepOnInnerShrunk α x₀` has compact closure in
`innerShrunkChart x₀ →ᵇ ℂ`. -/
theorem isCompact_closure_image_inner_bcf
    (M : ℝ) (hMnn : 0 ≤ M) {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    IsCompact (closure (Set.range
      (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
          (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
          HolomorphicOneForms.supNormK α ≤ M} =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀)))) := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) M)
    (isCompact_closedBall _ _)
  · -- in_s: all values in closedBall 0 M.
    rintro f y ⟨α, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right,
        BoundedContinuousFunction.mkOfCompact_apply]
    calc ‖localRepOnInnerShrunk α.1 x₀ y‖
        ≤ ‖localRepOnInnerShrunk α.1 x₀‖ :=
          ContinuousMap.norm_coe_le_norm _ y
      _ ≤ HolomorphicOneForms.supNormK α.1 :=
          norm_localRepOnInnerShrunk_le_supNormK α.1 hx₀
      _ ≤ M := α.2
  · -- Equicontinuous: transfer from the indexed family via Classical.choose.
    classical
    set ι := {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
          (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
          HolomorphicOneForms.supNormK α ≤ M}
    set F_bcf : ι → BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ :=
      fun α => BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀)
    -- `Equicontinuous (fun α : ι => ⇑(F_bcf α))` equals the known equicontinuous family.
    have hFbcf_fn : Equicontinuous (fun α : ι => (⇑(F_bcf α) : innerShrunkChart x₀ → ℂ)) := by
      have hF := equicontinuous_localRep_inner_family M hMnn hx₀
      have heq : (fun α : ι => (⇑(F_bcf α) : innerShrunkChart x₀ → ℂ)) =
          (fun α : ι => fun y : innerShrunkChart (X := X) x₀ => localRep α.1 x₀ (y : X)) := by
        funext α y
        simp only [F_bcf, BoundedContinuousFunction.mkOfCompact_apply]
        exact localRepOnInnerShrunk_apply _ hx₀ y
      rw [heq]; exact hF
    -- Now use Classical.choose to build u : Set.range F_bcf → ι and compose.
    let u : ↥(Set.range F_bcf) → ι := fun x => Classical.choose x.2
    have hu_spec : ∀ x : ↥(Set.range F_bcf), F_bcf (u x) = x.val :=
      fun x => Classical.choose_spec x.2
    have hcomp : (fun x : ↥(Set.range F_bcf) => (⇑x.val : innerShrunkChart x₀ → ℂ)) =
        (fun α : ι => (⇑(F_bcf α) : innerShrunkChart x₀ → ℂ)) ∘ u := by
      funext x y
      simp only [Function.comp]
      rw [hu_spec x]
    rw [hcomp]
    exact hFbcf_fn.comp u

/-! ### Step B.9 step 1 — Product compactness over `X` (all-index form)

The univ-indexed product of closures is compact: for `x₀ ∉ chartCover`,
`innerShrunkChart x₀ = ∅` so the image range is `{0}` (or degenerate);
for `x₀ ∈ chartCover`, B.8 gives compact closure. Either way each
factor is compact; by `isCompact_univ_pi`, the infinite product is
compact. -/

omit [ConnectedSpace X] in
/-- **Product compactness.**
Product over all `x₀ : X` of per-chart closures. Each factor is either
compact by B.8 (for `x₀ ∈ chartCover`) or a single-point singleton (for
`x₀ ∉ chartCover`, where `innerShrunkChart x₀ = ∅` makes the BCF zero). -/
theorem isCompact_univ_pi_closure_image_inner_bcf
    (M : ℝ) (hMnn : 0 ≤ M) :
    letI := fun x₀ : X => innerShrunkChart_compactSpace (X := X) x₀
    IsCompact (Set.univ.pi
      (fun x₀ : X =>
        closure (Set.range
          (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
              (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
              HolomorphicOneForms.supNormK α ≤ M} =>
            BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀))))) := by
  classical
  letI := fun x₀ : X => innerShrunkChart_compactSpace (X := X) x₀
  apply isCompact_univ_pi
  intro x₀
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · exact isCompact_closure_image_inner_bcf M hMnn hx₀
  · -- x₀ ∉ chartCover ⇒ innerShrunkChart x₀ = ∅ ⇒ all BCF values are 0 ⇒ range is {0}.
    have hempty : innerShrunkChart (X := X) x₀ = ∅ := innerShrunkChart_eq_empty x₀ hx₀
    have h_iso : IsEmpty (innerShrunkChart (X := X) x₀) := Set.isEmpty_coe_sort.mpr hempty
    have hrange_sub : Set.range
        (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
            (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
            HolomorphicOneForms.supNormK α ≤ M} =>
          BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀)) ⊆ {0} := by
      rintro f ⟨α, rfl⟩
      rw [Set.mem_singleton_iff]
      ext y
      exact h_iso.false y |>.elim
    -- closure of a subset of {0} is a subset of {0}, hence compact (finite).
    refine (Set.Finite.isCompact (Set.finite_singleton (0 :
        BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ))).of_isClosed_subset
      isClosed_closure ?_
    exact (isClosed_singleton.closure_subset_iff).mpr hrange_sub

omit [ConnectedSpace X] in
/-- **Step B.9 step 2 — Embedding lands in the compact product.**
For each α with `supNormK α ≤ M`, the associated function
`x₀ ↦ mkOfCompact (localRepOnInnerShrunk α x₀)` lies in the compact
`univ.pi`-set from step 1. -/
theorem embedding_in_univ_pi_closure
    (M : ℝ)
    (α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
        HolomorphicOneForms.supNormK α ≤ M}) :
    letI := fun x₀ : X => innerShrunkChart_compactSpace (X := X) x₀
    (fun x₀ : X =>
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀)) ∈
      Set.univ.pi
        (fun x₀ : X =>
          closure (Set.range
            (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
                (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
                HolomorphicOneForms.supNormK α ≤ M} =>
              BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 x₀)))) := by
  intro x₀ _
  exact subset_closure ⟨α, rfl⟩

/-! ### Linearity of the bcf-embedding components

Pure algebraic facts about the embedding maps used in B.9/B.10:
`localRepOnInnerShrunk` and its `mkOfCompact` packaging are ℂ-linear
in α. No topology involved — just the vector-space structure of
`ContMDiffSection` + pointwise linearity of `localRep`. -/

omit [ConnectedSpace X] [Nonempty X] in
/-- `localRepOnInnerShrunk` is additive in α. -/
theorem localRepOnInnerShrunk_add
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    localRepOnInnerShrunk (α + β) x₀ =
      localRepOnInnerShrunk α x₀ + localRepOnInnerShrunk β x₀ := by
  classical
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · ext y
    simp only [ContinuousMap.add_apply, localRepOnInnerShrunk_apply _ hx₀,
      localRep_add]
  · -- x₀ ∉ chartCover: innerShrunkChart empty, both sides zero.
    have h_iso : IsEmpty (innerShrunkChart (X := X) x₀) :=
      Set.isEmpty_coe_sort.mpr (innerShrunkChart_eq_empty x₀ hx₀)
    ext y
    exact h_iso.false y |>.elim

omit [ConnectedSpace X] [Nonempty X] in
/-- `localRepOnInnerShrunk` is ℂ-homogeneous in α. -/
theorem localRepOnInnerShrunk_smul
    (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    localRepOnInnerShrunk (c • α) x₀ = c • localRepOnInnerShrunk α x₀ := by
  classical
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · ext y
    simp only [ContinuousMap.smul_apply, localRepOnInnerShrunk_apply _ hx₀,
      localRep_smul]
  · have h_iso : IsEmpty (innerShrunkChart (X := X) x₀) :=
      Set.isEmpty_coe_sort.mpr (innerShrunkChart_eq_empty x₀ hx₀)
    ext y
    exact h_iso.false y |>.elim

/-! ### Step B.9 step 3a — Injectivity of the embedding

If `localRep α x₀ y = localRep β x₀ y` for every `y ∈ innerShrunkChart x₀`
and every `x₀ ∈ chartCover`, then `α = β`. Proof via pointwise
vanishing of `α - β`: for any `y ∈ X`, by inner-cover there's `x₀`
with `y ∈ innerShrunkChart x₀` (which ⊆ baseSet), so
`localRep (α - β) x₀ y = 0` forces `(α - β).toFun y = 0` by the
1-dim tangent argument (`alpha_toFun_eq_zero_of_localRep_eq_zero`). -/

omit [ConnectedSpace X] [Nonempty X] in
/-- **Injectivity of the bcf-embedding.** Equality of
`mkOfCompact (localRepOnInnerShrunk · x₀)` at every `x₀` (including
outside chartCover) pins down the holomorphic 1-form. -/
theorem eq_of_mkOfCompact_localRepOnInnerShrunk_eq
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ x₀ : X,
      letI := innerShrunkChart_compactSpace (X := X) x₀
      BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀) =
        BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk β x₀)) :
    α = β := by
  -- Extract pointwise equality localRep α x₀ y = localRep β x₀ y on innerShrunkChart x₀.
  have h' : ∀ x₀ ∈ (chartCover : Finset X), ∀ y ∈ innerShrunkChart (X := X) x₀,
      localRep α x₀ y = localRep β x₀ y := by
    intro x₀ hx₀ y hy
    haveI := innerShrunkChart_compactSpace (X := X) x₀
    have := congrArg (fun f => f ⟨y, hy⟩) (h x₀)
    simp only [BoundedContinuousFunction.mkOfCompact_apply] at this
    rw [localRepOnInnerShrunk_apply _ hx₀, localRepOnInnerShrunk_apply _ hx₀] at this
    exact this
  -- Now show α = β via pointwise vanishing of γ := α - β.
  apply ContMDiffSection.ext
  intro y
  -- y ∈ ⋃ innerShrunkChart x₀ = univ ⇒ ∃ x₀' ∈ chartCover, y ∈ innerShrunkChart x₀'.
  have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← iUnion_innerShrunkChart_chartCover_eq (X := X)] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨x₀', hx₀'mem, hy_in⟩ := hmem
  -- localRep (α - β) x₀' y = 0.
  have hlocal : localRep α x₀' y - localRep β x₀' y = 0 := by
    rw [h' x₀' hx₀'mem y hy_in]; ring
  -- Convert to: localRep (γ := α - β) x₀' y = 0.
  -- Use linearity of localRep (localRep_add and localRep_neg).
  have hγ_localRep : localRep (α - β) x₀' y = 0 := by
    have hsub : α - β = α + (-β) := by rw [sub_eq_add_neg]
    rw [hsub, localRep_add, localRep_neg]
    calc localRep α x₀' y + -localRep β x₀' y
        = localRep α x₀' y - localRep β x₀' y := by ring
      _ = 0 := hlocal
  -- y is in baseSet (since innerShrunkChart ⊆ baseSet for x₀' ∈ chartCover).
  have hy_base : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet :=
    innerShrunkChart_subset_baseSet x₀' hx₀'mem hy_in
  have h_toFun : (α - β).toFun y = 0 :=
    alpha_toFun_eq_zero_of_localRep_eq_zero (α - β) x₀' y hy_base hγ_localRep
  -- Convert "(α - β).toFun y = 0" to "α.toFun y = β.toFun y".
  have hsub_zero : α.toFun y - β.toFun y = 0 := by
    have heq : (α - β).toFun y = α.toFun y - β.toFun y := by
      change (⇑(α - β)) y = _
      rw [ContMDiffSection.coe_sub]
      rfl
    rw [← heq]; exact h_toFun
  exact sub_eq_zero.mp hsub_zero

/-! ### Next steps (scheduled, not implemented here)

**B.9** Inject HOF X into the finite product
`Π x₀ ∈ chartCover, C(innerShrunkChart x₀, ℂ)` (injective via
`iUnion_innerShrunkChart_chartCover_eq = univ`). Transfer compactness
of product to closedBall in HOF X.

**B.10** `closedBall_isClosed` — via uniform limits of holomorphic
functions being holomorphic (`TendstoLocallyUniformlyOn.analyticOn`).

**Assembly** — discharge `HolomorphicOneForms.closedBall_isCompact` in
`Jacobians/Montel.lean`. -/

end Jacobians.Montel
