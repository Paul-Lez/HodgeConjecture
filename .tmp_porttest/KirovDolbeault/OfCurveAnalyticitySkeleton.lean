/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KirovDolbeault.PeriodLattice
import KirovDolbeault.Discharge.Manifold.ContMDiffOmegaAnalytic
import KirovDolbeault.Montel.Compactness
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Analyticity skeleton for `ofCurve_contMDiff`

This file lays out the proof skeleton for `Jacobians.ofCurve_contMDiff`
(Forster §21: the Abel–Jacobi map is holomorphic, in the quotient
sense — see `Jacobians.exists_smoothPath_family` for why the
unquotiented version is mathematically false).

**Mathlib API used**
* `Mathlib.Analysis.Complex.HasPrimitives.DifferentiableOn.isExactOn_ball` —
  a holomorphic function on a ball has a primitive (Morera).
* `Mathlib.Analysis.Complex.CauchyIntegral.DifferentiableOn.analyticOn` —
  on an open set, `DifferentiableOn ℂ ⇒ AnalyticOn ℂ`.
* `Mathlib.Analysis.Calculus.ContDiff.Defs.AnalyticAt.contDiffAt` —
  in a complete codomain, `AnalyticAt ℂ ⇒ ContDiffAt ℂ n` for any `n`.

**Construction strategy**

For each `Q₀ : X`, in the chart `e := chartAt ℂ Q₀`, on the chart-ball
`B := e.target ∩ ball (e Q₀) r` for some `r > 0`, define the **local
lift**

```
Φ_{Q₀} : X → ℂ^g
Φ_{Q₀}(Q) := constant(Q₀) + ∫_{e Q₀}^{e Q} ω̃_i(w) dw    -- in chart coords
```

where `ω̃_i = (periodBasisForm i)` pulled back via `e.symm`, and the
integral is along the straight line in chart coordinates.

By Morera + Cauchy, this is locally analytic in `(e Q)`, hence
analytic-on-the-chart-pullback, hence `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ^g) ω`
at `Q₀`.

The local lifts agree with `ofCurve P` modulo the period lattice
(path-difference-is-closed-loop ⇒ lattice element). Local-to-global
smoothness in the **quotient** follows from `contMDiff_iff_forall_*`.

**Status of this file (updated 2026-06-09)**

The file is complete in all proof bodies: the local chart-ball
machinery (`localLift_contMDiffAt`, `chartFrame_cancel`,
`isSmoothPath_ChartBallPathSmooth`, the 2-piece junction loop, and
`localLift_quotient_eq_ofCurve_eventually`) is all proven and
`#print axioms`-clean. The former residual dependence through
`smoothPath` is closed: `exists_smoothPath_family` is proven
axiom-clean, so this entire file is unconditionally gap-free.
-/

open scoped Manifold ContDiff
open Complex Set
open MeasureTheory

namespace Jacobians.OfCurveSkeleton

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- `chartFormCoeff` and `chartFormCoeff_differentiableOn` have moved
-- UPSTREAM to `Jacobians/SmoothPathCore.lean` (same namespace
-- `Jacobians.OfCurveSkeleton`); they remain available here transitively
-- via `import Jacobians.PeriodLattice` → `Jacobians.SmoothPathCore`.

/-- **A holomorphic function on an open ball has an analytic primitive.**

Direct application of Mathlib's `DifferentiableOn.isExactOn_ball` +
`DifferentiableOn.analyticOn`. Mathlib defines `IsExactOn` as
existence of `g` with `HasDerivAt g (f z) z` for all `z` in the ball;
extracting `g` and showing its analyticity is the content here. -/
theorem exists_analytic_primitive_on_ball
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∃ g : ℂ → ℂ,
      (∀ z ∈ Metric.ball c r, HasDerivAt g (f z) z) ∧
      AnalyticOn ℂ g (Metric.ball c r) := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  refine ⟨g, hg, ?_⟩
  -- `g` is differentiable on the ball (each point has `HasDerivAt`).
  have hgdiff : DifferentiableOn ℂ g (Metric.ball c r) := by
    intro z hz
    exact (hg z hz).differentiableAt.differentiableWithinAt
  -- On an open set, `DifferentiableOn ℂ ⇒ AnalyticOn ℂ`.
  exact hgdiff.analyticOn Metric.isOpen_ball

/-- **FTC for a primitive along a straight-line segment in ℂ.**

If `g` is a primitive of `f` on a ball containing both `a` and `b`
(and the segment between them), then `∫_0^1 f(a + t(b-a)) (b-a) dt =
g(b) - g(a)`.

This is just the fundamental theorem of calculus applied to `s ↦
g(a + s(b - a))` whose derivative is `f(a + s(b - a)) (b - a)`. -/
theorem segmentIntegral_eq_primitive_diff
    {f g : ℂ → ℂ} {c : ℂ} {r : ℝ} {a b : ℂ}
    (_ha : a ∈ Metric.ball c r) (_hb : b ∈ Metric.ball c r)
    (hseg : Set.Icc (0 : ℝ) 1 ⊆ {t | a + (t : ℂ) * (b - a) ∈ Metric.ball c r})
    (hf_cont : ContinuousOn f (Metric.ball c r))
    (hg : ∀ z ∈ Metric.ball c r, HasDerivAt g (f z) z) :
    ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (b - a)) * (b - a) =
      g b - g a := by
  -- The composed path `φ : ℝ → ℂ`, `φ t := a + t • (b - a)`,
  -- has `HasDerivAt φ (b - a) t` (real-linear, derivative = `b - a`).
  -- Then by complex chain rule (a `HasDerivAt` composition where the
  -- inner derivative is real and the outer is complex),
  -- `t ↦ g(φ t)` has derivative `f(φ t) * (b - a)` at each `t ∈ [0,1]`.
  set φ : ℝ → ℂ := fun t => a + (t : ℂ) * (b - a) with hφ_def
  have hφ : ∀ t : ℝ, HasDerivAt φ (b - a) t := by
    intro t
    -- Express φ in terms of `smul`, take derivative via `HasDerivAt.smul_const`,
    -- then rewrite back to the `(·) * (b - a)` form.
    have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h_smul : HasDerivAt (fun s : ℝ => s • (b - a)) ((1 : ℝ) • (b - a)) t :=
      h_id.smul_const (b - a)
    have h_eq : (fun s : ℝ => s • (b - a)) = (fun s : ℝ => (s : ℂ) * (b - a)) := by
      funext s; exact Complex.real_smul
    rw [h_eq] at h_smul
    -- Simplify `1 • (b - a)` to `b - a`.
    have h_one : ((1 : ℝ) • (b - a) : ℂ) = b - a := by
      rw [Complex.real_smul]; simp
    rw [h_one] at h_smul
    -- h_smul : HasDerivAt (fun s : ℝ => (s : ℂ) * (b - a)) (b - a) t
    have h_const : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
    have h_add : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (b - a)) (0 + (b - a)) t :=
      h_const.add h_smul
    rw [zero_add] at h_add
    exact h_add
  -- Composed derivative: `(g ∘ φ)' t = (b - a) * f (φ t)`.
  have h_comp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => g (φ s)) (f (φ t) * (b - a)) t := by
    intro t ht
    have hzt : φ t ∈ Metric.ball c r := hseg ht
    have hg_at : HasDerivAt g (f (φ t)) (φ t) := hg (φ t) hzt
    have := hg_at.comp t (hφ t)
    simpa [mul_comm] using this
  -- FTC: `∫ t in 0..1, (g ∘ φ)' t = g (φ 1) - g (φ 0)`.
  have h_endpoints : φ 0 = a ∧ φ 1 = b := by
    refine ⟨?_, ?_⟩ <;> simp [φ]
  -- The integrand `f (φ t) * (b - a)` is continuous on `[0, 1]`,
  -- hence integrable on it.
  have hφ_cont : Continuous φ := by
    have : Continuous (fun t : ℝ => (t : ℂ) * (b - a)) :=
      (Complex.continuous_ofReal).mul continuous_const
    exact continuous_const.add this
  have h_int_cont : ContinuousOn (fun t : ℝ => f (φ t) * (b - a))
      (Set.Icc (0 : ℝ) 1) := by
    refine (ContinuousOn.mul ?_ continuousOn_const)
    exact (hf_cont.comp hφ_cont.continuousOn (fun t ht => hseg ht))
  have h_int : IntervalIntegrable (fun t : ℝ => f (φ t) * (b - a))
      MeasureTheory.volume 0 1 :=
    (h_int_cont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1))
  -- Convert `Set.Icc` HasDerivAt statement to `uIcc` form.
  have h_comp' : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => g (φ s)) (f (φ t) * (b - a)) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact h_comp t ht
  -- Apply FTC.
  have h_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt h_comp' h_int
  rw [h_endpoints.1, h_endpoints.2] at h_FTC
  exact h_FTC

-- `localLiftChart` has moved UPSTREAM to
-- `Jacobians/SmoothPathCore.lean` (same namespace); available here
-- transitively.

/-- **Local lift is analytic on a chart ball.**

Combines `exists_analytic_primitive_on_ball` (from `chartFormCoeff`'s
holomorphy) with `segmentIntegral_eq_primitive_diff` (rewriting the
straight-line integral as `g(z) - g(z₀)`).

The result `localLiftChart Q₀ constants i z = constants i + g(z) -
g(z₀)` is analytic in `z` because `g` is analytic.

Locally on the chart-ball `Metric.ball ((chartAt ℂ Q₀) Q₀) r`
contained in `e.target`. -/
theorem localLiftChart_analyticAt (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ)
    (i : Fin (kirovGenus X)) :
    AnalyticAt ℂ (localLiftChart (X := X) Q₀ constants i)
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  -- Step 1: pick a chart ball `Metric.ball z₀ r ⊆ chart.target`.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have h_open := (chartAt (H := ℂ) Q₀).open_target
  have h_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source h_src
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  -- Step 2: `chartFormCoeff` is `DifferentiableOn` on this ball.
  have hdiff : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i)
      (Metric.ball z₀ r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hr_subset
  -- Step 3: analytic primitive on the ball.
  obtain ⟨g, hg_deriv, hg_ana⟩ := exists_analytic_primitive_on_ball hdiff
  -- Step 4: continuity of `chartFormCoeff` on the ball (from
  -- `DifferentiableOn`).
  have hf_cont : ContinuousOn (chartFormCoeff (X := X) Q₀ i)
      (Metric.ball z₀ r) := hdiff.continuousOn
  -- Step 5: On `Metric.ball z₀ r`, the local lift equals
  -- `constants i + g z - g z₀`.
  have h_eq : Set.EqOn (localLiftChart (X := X) Q₀ constants i)
      (fun z => constants i + g z - g z₀) (Metric.ball z₀ r) := by
    intro z hz
    -- Apply `segmentIntegral_eq_primitive_diff` with `a = z₀`, `b = z`.
    -- Segment is contained in the ball (convexity).
    have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
    have hseg : Set.Icc (0 : ℝ) 1 ⊆
        {t | z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r} := by
      intro t ht
      show z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r
      have h_rewrite : z₀ + (t : ℂ) * (z - z₀) = z₀ + t • (z - z₀) := by
        rw [Complex.real_smul]
      rw [h_rewrite]
      exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz ht
    have := segmentIntegral_eq_primitive_diff (c := z₀) (r := r)
      (a := z₀) (b := z) (f := chartFormCoeff (X := X) Q₀ i) (g := g)
      hz₀_mem hz hseg hf_cont hg_deriv
    simp only [localLiftChart]
    rw [this]
    ring
  -- Step 6: `(fun z => constants i + g z - g z₀)` is `AnalyticAt` at z₀.
  -- It's `constants i - g z₀` (constant) plus `g` (analytic at z₀
  -- since z₀ is in the open ball).
  have hg_at : AnalyticAt ℂ g z₀ :=
    hg_ana.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
  have h_target : AnalyticAt ℂ (fun z => constants i + g z - g z₀) z₀ := by
    have h1 : AnalyticAt ℂ (fun _ : ℂ => constants i) z₀ := analyticAt_const
    have h2 : AnalyticAt ℂ (fun _ : ℂ => g z₀) z₀ := analyticAt_const
    exact (h1.add hg_at).sub h2
  -- Step 7: AnalyticAt is local; conclude via `EventuallyEq`.
  have h_nhds : (fun z => constants i + g z - g z₀) =ᶠ[nhds z₀]
      localLiftChart (X := X) Q₀ constants i := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)]
      with z hz using (h_eq hz).symm
  exact h_target.congr h_nhds

/-! ### Bridge: analyticAt of chart-coord lift ⇒ `ContMDiffAt` on the manifold

The vector-valued local lift, expressed as a function `X → (Fin (kirovGenus
X) → ℂ)`, is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (kirovGenus X) → ℂ) ω` at `Q₀`.

This is the analytic→ContMDiffAt bridge: from `AnalyticAt` of each
chart-coord component, we get `ContDiffAt ℂ ω` (Mathlib's
`AnalyticAt.contDiffAt`), bundle via `contDiffAt_pi`, then convert to
`ContMDiffAt` via the chart-pullback characterization. -/

-- `localLift` has moved UPSTREAM to `Jacobians/SmoothPathCore.lean`
-- (same namespace); available here transitively.

/-- **The chart-coord function** of the local lift, as a vector-valued
map `ℂ → (Fin (kirovGenus X) → ℂ)`. -/
noncomputable def localLiftChartVec (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ)
    (z : ℂ) : Fin (kirovGenus X) → ℂ :=
  fun i => localLiftChart (X := X) Q₀ constants i z

/-- **The chart-coord vector lift is `AnalyticAt`** at the chart point. -/
theorem localLiftChartVec_analyticAt (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ) :
    AnalyticAt ℂ (localLiftChartVec (X := X) Q₀ constants)
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  -- Bundle the per-component analyticAt into a `Pi`-valued analyticAt.
  -- Mathlib: `analyticAt_pi` or similar — each component analytic implies
  -- the pi-bundled function is analytic.
  rw [show localLiftChartVec (X := X) Q₀ constants
      = (fun z i => localLiftChart (X := X) Q₀ constants i z) from rfl]
  exact AnalyticAt.pi fun i => localLiftChart_analyticAt Q₀ constants i

/-- **The chart-coord vector lift is `ContDiffAt`** at the chart point. -/
theorem localLiftChartVec_contDiffAt (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ) :
    ContDiffAt ℂ ω (localLiftChartVec (X := X) Q₀ constants)
      ((chartAt (H := ℂ) Q₀) Q₀) :=
  (localLiftChartVec_analyticAt Q₀ constants).contDiffAt

/-- **The vector-valued local lift is `ContMDiffAt`** at `Q₀`.

`localLift Q₀ constants = localLiftChartVec Q₀ constants ∘ chartAt ℂ Q₀`.
The chart map `chartAt ℂ Q₀` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `Q₀`
(Mathlib's `contMDiffAt_extChartAt`), and the chart-coord function is
`ContDiffAt ℂ ω` at `(chartAt ℂ Q₀) Q₀` (above). Mathlib's
`ContDiffAt.comp_contMDiffAt` glues these into `ContMDiffAt 𝓘(ℂ)
𝓘(ℂ, Fin (kirovGenus X) → ℂ) ω` of the composition. -/
theorem localLift_contMDiffAt (Q₀ : X) (constants : Fin (kirovGenus X) → ℂ) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (kirovGenus X) → ℂ) ω
      (localLift (X := X) Q₀ constants) Q₀ := by
  -- Step 1: `chartAt ℂ Q₀` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `Q₀`.
  -- Use `contMDiffAt_extChartAt` and the fact that `extChartAt 𝓘(ℂ)` agrees
  -- with `chartAt ℂ` as a function (boundaryless model).
  have h_chart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω
      (chartAt (H := ℂ) Q₀ : X → ℂ) Q₀ := by
    have h_ext : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω
        (extChartAt 𝓘(ℂ) Q₀ : X → ℂ) Q₀ := contMDiffAt_extChartAt
    -- `extChartAt 𝓘(ℂ) Q₀` = `chartAt ℂ Q₀` as functions on the chart source.
    -- Their values agree pointwise (model is identity).
    have h_eq : (extChartAt 𝓘(ℂ) Q₀ : X → ℂ) = (chartAt (H := ℂ) Q₀ : X → ℂ) := by
      funext y
      simp
    rw [h_eq] at h_ext
    exact h_ext
  -- Step 2: chart-coord vector function is `ContDiffAt ℂ ω` at chart-image.
  have h_chartVec : ContDiffAt ℂ ω
      (localLiftChartVec (X := X) Q₀ constants) ((chartAt (H := ℂ) Q₀) Q₀) :=
    localLiftChartVec_contDiffAt Q₀ constants
  -- Step 3: compose via `ContDiffAt.comp_contMDiffAt`. The result is
  -- `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, V) ω (localLiftChartVec ∘ chartAt) Q₀`, which
  -- equals `ContMDiffAt ... (localLift ...) Q₀` by definition unfolding.
  have h_comp := h_chartVec.comp_contMDiffAt (x := Q₀) h_chart
  -- `localLift Q₀ constants = localLiftChartVec Q₀ constants ∘ chartAt ℂ Q₀`.
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (kirovGenus X) → ℂ) ω
    (localLiftChartVec (X := X) Q₀ constants ∘ (chartAt (H := ℂ) Q₀)) Q₀
  exact h_comp

/-! ### Identification with `ofCurve P` in the quotient

The local lift centered at `Q₀` with `constants := periodVec(smoothPath
P Q₀)` agrees, on a chart neighborhood of `Q₀`, with `ofCurve P` in
the lattice quotient.

**Mathematical proof.** For `Q` in a chart-ball around `Q₀`, the
chart-segment `ChartBallPath Q₀ Q₀ Q : ℝ → X` is a smooth path from
`Q₀` to `Q` (`Jacobians.ChartBallPath.start` + `.finish` +
chart-transition smoothness — built up in `Jacobians/SmoothPath.lean`).

Then:

```
localLift Q₀ constants Q
  = constants + ∫_0^1 chartFormCoeff(z₀ + t(z-z₀)) (z-z₀) dt    -- def
  = constants + periodVec(ChartBallPath Q₀ Q₀ Q)                -- chart-frame line integral
  = periodVec(smoothPath P Q₀) + periodVec(ChartBallPath Q₀ Q₀ Q) -- choice of constants
  = periodVec(smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q)           -- periodVec_concat
```

The concatenation `smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q` is a
smooth path from `P` to `Q`. The difference `(smoothPath P Q₀ ∗
ChartBallPath Q₀ Q₀ Q) ∗ reverse(smoothPath P Q)` is a smooth closed
loop at `P`. By `periodVec_concat` + `periodVec_reverse`:

```
periodVec((smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q) ∗ reverse(smoothPath P Q))
  = periodVec(smoothPath P Q₀ ∗ ChartBallPath ...) - periodVec(smoothPath P Q)
```

This closed loop's periodVec is in `truePeriodLattice X` by
`periodVec_mem_truePeriodLattice_of_closed`. Hence in the quotient:

```
[localLift Q₀ constants Q] = [periodVec(smoothPath P Q)]
```

**Status.** The Lean proof needs three sub-pieces, each ~50-150 LOC:

(a) `localLift_eq_constants_add_periodVec_ChartBallPath`: chart-coord
    integral equals path-integral.

    **Mathematical resolution (chart-frame cancellation by 1-form
    covariance).** For `γ := ChartBallPath Q₀ Q₀ Q` and `α :=
    periodBasisForm X i`, the path-integral integrand is
    `α.toFun (γ t) (pathSpeed γ t)`. This uses `chartAt (γ t)`-frame
    in `pathSpeed`, but the value is intrinsic (1-form against
    tangent vector).

    Compute in chart-Q₀ frame: let `h := chartAt (γ t) ∘ chartAt Q₀.
    symm` (the transition map). Then:
    * `pathSpeed γ t = h'(z(γt)) * (z - z₀)` (chain rule on
      `chartAt(γt) ∘ γ = h ∘ (chartAt(Q₀) ∘ γ)` evaluated at the
      chart-Q₀-frame derivative `(z - z₀)`).
    * The 1-form transforms covariantly: `α_γt(w) = α_Q₀(h⁻¹(w)) /
      h'(h⁻¹(w))`.
    * Hence `α.toFun (γt) v = α_γt(chartAt(γt)(γt)) · v` (in
      chart-γt frame) `= α_Q₀(z(γt))/h'(z(γt)) · v`.

    Plugging in `v = pathSpeed γ t = h'(z(γt)) · (z - z₀)`:
    `α.toFun (γt) (pathSpeed γt) = α_Q₀(z(γt)) · (z - z₀)`. The
    transition `h'` cancels exactly.

    And `α_Q₀(z(γt)) = localRep α Q₀ (γt) = chartFormCoeff Q₀ i
    (z₀ + t(z - z₀))`. So pointwise, the path-integral integrand
    equals the chart-coord integrand. `intervalIntegral.integral_congr`
    then gives equality of integrals.

    **Lean formalization cost.** ~150-300 LOC: requires manipulating
    `Trivialization.symmL`, `ContinuousLinearMap.smul_apply`, chain
    rule via `pathSpeed_comp_eq_mfderiv`-style decomposition. The
    chart `(chartAt Q₀).symm` isn't a global manifold map, so direct
    use of `pathSpeed_comp_eq_mfderiv` doesn't apply — we'd need a
    chart-restricted variant.

(b) `periodVec_concat` (PROVEN) + integrability bookkeeping on the
    concatenation of `smoothPath P Q₀` and `ChartBallPath Q₀ Q₀ Q`.
    The integrability of basis-form integrands on each piece needs
    `IsSmoothPath.integrable` for `smoothPath`, plus a separate
    integrability lemma for `ChartBallPath` (continuous integrand on
    `[0,1]` × compact chart-ball).

(c) `periodVec_smoothPath_eq_periodVec_concat_mod_lattice`: the
    closed-loop argument via `periodVec_mem_truePeriodLattice_of_closed`.
    The non-trivial step is showing `(smoothPath P Q₀ ∗ ChartBallPath
    Q₀ Q₀ Q) ∗ reverse(smoothPath P Q)` is a `IsClosedSmoothLoop`,
    which requires concat-smoothness + reverse-smoothness (both with
    proven infrastructure in `Jacobians/LineIntegral.lean` and
    `PeriodLattice.lean`). -/
/-! ### Chart-frame cancellation: pathSpeed of `ChartBallPath` and `localRep`

To prove the main identification (`localLift_quotient_eq_ofCurve_eventually`),
the structural content is the chart-frame cancellation lemma: for `γ :=
ChartBallPath Q₀ Q₀ Q t` and `α := periodBasisForm X i`,

```
α.toFun (γ t) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) · (z - z₀)
```

The proof uses Mathlib's `TangentBundle.symmL_trivializationAt_eq_core`,
which identifies `(trivAt b₀).symmL ℂ b 1` with the chart-transition
derivative. The chain-rule on `(chartAt γt) ∘ (chartAt Q₀).symm ∘ affine`
gives the matching `pathSpeed γ t = fderiv (chart transition)((z-z₀))`.

We do NOT attempt to formalize this here in full generality. Instead, we
take a different route: we identify both sides at the single point
`Q = Q₀` and use that on the chart source, the **difference** is a
locally analytic ℂ^g-valued function that vanishes at Q₀ AND lands in
the period lattice (mod which the quotient is defined), so it's a
constant equal to zero in the quotient.

Specifically, the strategy uses:

* `localLift_contMDiffAt` (PROVEN) — the LHS is `ContMDiffAt` at Q₀.
* `ofCurve_contMDiff` would tell us the RHS is `ContMDiffAt` at Q₀,
  except we're proving that exact thing! So we use:
* `smoothPath_basepoint_change` (PROVEN) — algebraic reduction of RHS.
* Concrete closed-loop argument via `periodVec_concat`,
  `periodVec_reverse`, `periodVec_mem_truePeriodLattice_of_closed`.
-/

-- `trivAt_symmL_one_eq_fderiv`, `trivAt_symmL_one_eq_fderiv_C`, and
-- `chartBallPath_mem_source_of_affine` have moved UPSTREAM to
-- `Jacobians/SmoothPathCore.lean` (same namespace); available here
-- transitively.

-- `chartFrame_cancel`, `Q_in_chart_source_eventually`, and
-- `affine_in_target_eventually` have moved UPSTREAM to
-- `Jacobians/SmoothPathCore.lean` (same namespace); available here
-- transitively.

-- `localLift_eq_const_add_periodVec_ChartBallPath`,
-- `pathSpeed_smoothStep01_comp_eq`, and `isSmoothPath_ChartBallPathSmooth`
-- have moved UPSTREAM to `Jacobians/SmoothPathCore.lean` (same namespace);
-- available here transitively via `import Jacobians.PeriodLattice`.

/-! ### Reparameterization invariance of periodVec under smoothStep01

By substitution-of-variables (`intervalIntegral.integral_comp_mul_deriv`),
`periodVec (γ ∘ smoothStep01) = periodVec γ` for any smooth path γ
(with appropriate regularity hypotheses). Applied to ChartBallPath
gives `periodVec (ChartBallPathSmooth Q₀ Q) = periodVec (ChartBallPath
Q₀ Q₀ Q)`. -/

/-- **Generic periodVec invariance under smoothStep01 reparameterization.**

For any path `γ : ℝ → X` whose chart-pullback is `DifferentiableAt ℝ`
at each `s ∈ [0, 1]`, and whose basis-form integrand is `ContinuousOn`
`[0, 1]`, `periodVec (γ ∘ smoothStep01) = periodVec γ`.

The proof:
1. By `pathSpeed_smoothStep01_comp_eq`, the integrand of
   `periodVec (γ ∘ σ) i` equals
   `σ'(t) • (α.toFun(γ(σ t)))(pathSpeed γ (σ t))` pointwise on `[0, 1]`.
2. By `intervalIntegral.integral_deriv_smul_comp'` (substitution-of-
   variables with `f = σ`, `f' = σ'`, `g(u) = α.toFun(γ u)(pathSpeed γ u)`),
   the integral equals `∫_{σ 0}^{σ 1} g(u) du = ∫_0^1 g(u) du =
   periodVec γ i`.

The substitution lemma's hypotheses:
* `HasDerivAt smoothStep01 (smoothStep01_deriv x) x` for each `x ∈ uIcc 0 1` (PROVEN).
* `ContinuousOn smoothStep01_deriv (uIcc 0 1)` (PROVEN).
* `ContinuousOn g (smoothStep01 '' [[0, 1]] = [0, 1])` (parameter — caller supplies). -/
lemma periodVec_smoothStep01_comp_eq_generic (γ : ℝ → X)
    (hγ_diff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hg_cont : ∀ i : Fin (kirovGenus X),
      ContinuousOn (fun u => (periodBasisForm X i).toFun (γ u)
        (Jacobians.pathSpeed γ u)) (Set.Icc (0 : ℝ) 1)) :
    Jacobians.periodVec (γ ∘ Jacobians.smoothStep01) = Jacobians.periodVec γ := by
  funext i
  -- Definitions: periodVec γ i = ∫_0^1 (periodBasisForm i).toFun (γ t) (pathSpeed γ t).
  show ∫ t in (0 : ℝ)..1, (periodBasisForm X i).toFun ((γ ∘ Jacobians.smoothStep01) t)
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      ∫ t in (0 : ℝ)..1, (periodBasisForm X i).toFun (γ t) (Jacobians.pathSpeed γ t)
  -- Set g(u) := (periodBasisForm i).toFun(γ u)(pathSpeed γ u).
  set g : ℝ → ℂ :=
    fun u => (periodBasisForm X i).toFun (γ u) (Jacobians.pathSpeed γ u) with hg_def
  -- Step 1: integrand of LHS at t ∈ [0,1] equals σ'(t) • g(σ t).
  have h_integrand_eq : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      (periodBasisForm X i).toFun ((γ ∘ Jacobians.smoothStep01) t)
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t) := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    have hs_Icc : Jacobians.smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 :=
      Jacobians.smoothStep01_mem_unit t
    have hγ_diff_at_s := hγ_diff (Jacobians.smoothStep01 t) hs_Icc
    have h_speed := pathSpeed_smoothStep01_comp_eq γ t hγ_diff_at_s
    -- LHS = α.toFun(γ(σ t)) (pathSpeed (γ ∘ σ) t)
    -- = α.toFun(γ(σ t)) ((σ'(t) : ℂ) * pathSpeed γ (σ t))
    -- = (σ'(t) : ℂ) * α.toFun(γ(σ t)) (pathSpeed γ (σ t))  [ℂ-linearity]
    -- = σ'(t) • g(σ t)
    show (periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t))
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t)
    rw [h_speed]
    -- α.toFun(γt) is ℂ-linear, so α.toFun(γt) ((σ' : ℂ) * x) = (σ' : ℂ) * α.toFun(γt)(x).
    -- Then (σ' : ℂ) * (...) = σ' • (...) via Complex.real_smul.symm.
    have h_lin : ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
        ((Jacobians.smoothStep01_deriv t : ℂ) *
          Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) =
      (Jacobians.smoothStep01_deriv t : ℂ) *
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
          (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) := by
      -- Use ContinuousLinearMap.map_smul to extract the ℂ-scalar.
      have h_lin :=
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t))).map_smul
        (Jacobians.smoothStep01_deriv t : ℂ)
        (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      -- h_lin : α.toFun (γ ...) ((↑σ' : ℂ) • path) = (↑σ' : ℂ) • α.toFun (γ ...) (path)
      -- Convert smul to mul on both sides.
      simp only [smul_eq_mul] at h_lin
      exact h_lin
    rw [h_lin]
    -- Now: (σ' : ℂ) * g(σ t) = σ' • g(σ t) via Complex.real_smul.symm.
    show (Jacobians.smoothStep01_deriv t : ℂ) *
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
          (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t)
    exact Complex.real_smul.symm
  -- Step 2: rewrite the integral via this pointwise identity.
  rw [intervalIntegral.integral_congr h_integrand_eq]
  -- Now: ∫ t in 0..1, σ'(t) • g(σ t) = ∫ t in 0..1, g t
  -- Step 3: apply substitution-of-variables.
  have h_subst : ∫ x in (0 : ℝ)..1, Jacobians.smoothStep01_deriv x •
        (g ∘ Jacobians.smoothStep01) x =
      ∫ x in Jacobians.smoothStep01 0..Jacobians.smoothStep01 1, g x :=
    intervalIntegral.integral_deriv_smul_comp'
      (h := fun x _ => Jacobians.smoothStep01_hasDerivAt_explicit x)
      (h' := Jacobians.smoothStep01_deriv_continuousOn_uIcc)
      (hg := by
        have h_subset : Jacobians.smoothStep01 '' (Set.uIcc (0 : ℝ) 1) ⊆ Set.Icc (0 : ℝ) 1 := by
          intro u hu
          obtain ⟨s, _, hs_eq⟩ := hu
          rw [← hs_eq]
          exact Jacobians.smoothStep01_mem_unit s
        exact (hg_cont i).mono h_subset)
  rw [Jacobians.smoothStep01_zero, Jacobians.smoothStep01_one] at h_subst
  -- The LHS of h_subst matches our goal's LHS (modulo composition unfolding).
  -- Note: σ'(t) • (g ∘ σ)(t) = σ'(t) • g(σ t).
  show ∫ t in (0 : ℝ)..1, Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t) =
      ∫ t in (0 : ℝ)..1, g t
  exact h_subst

/-- **PeriodVec is invariant under `smoothStep01` reparameterization for ChartBallPath.**
Direct corollary of `periodVec_smoothStep01_comp_eq_generic` applied to
`ChartBallPath Q₀ Q₀ Q`. -/
lemma periodVec_ChartBallPathSmooth_eq (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.periodVec (Jacobians.ChartBallPathSmooth Q₀ Q) =
    Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) := by
  -- ChartBallPathSmooth Q₀ Q = ChartBallPath Q₀ Q₀ Q ∘ smoothStep01 (def unfolding).
  show Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) =
      Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q)
  apply periodVec_smoothStep01_comp_eq_generic
  · -- Chart-pullback diff at each s ∈ [0, 1].
    intro s hs
    exact Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q s
      (h_chart_ball s hs)
  · -- ContinuousOn of integrand on [0, 1]. Use chartFrame_cancel:
    -- α.toFun (γt) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) * (z - z₀).
    -- RHS is continuous on [0, 1] (chartFormCoeff continuous + polynomial in t).
    intro i
    -- Step 1: rewrite pointwise via chartFrame_cancel.
    set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀
    set z : ℂ := (chartAt (H := ℂ) Q₀) Q
    have h_eq : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q u)
          (Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) u) =
        chartFormCoeff (X := X) Q₀ i (z₀ + (u : ℂ) * (z - z₀)) * (z - z₀) := by
      intro u hu
      -- Need: nbhd hypothesis for chartFrame_cancel.
      have h_target_nbhd : ∀ᶠ s : ℝ in nhds u,
          ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z) ∈ (chartAt (H := ℂ) Q₀).target := by
        have h_cont : Continuous (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) := by
          refine Continuous.add ?_ ?_
          · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
          · exact Complex.continuous_ofReal.mul continuous_const
        have h_open : IsOpen
            {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ (chartAt (H := ℂ) Q₀).target} :=
          (chartAt (H := ℂ) Q₀).open_target.preimage h_cont
        exact h_open.mem_nhds (h_chart_ball u hu)
      have h_cf := chartFrame_cancel (X := X) Q₀ Q i u h_target_nbhd
      -- h_cf : chartFormCoeff Q₀ i ((1-u)·(chartAt Q₀)Q₀ + u·(chartAt Q₀)Q) *
      --        ((chartAt Q₀)Q - (chartAt Q₀)Q₀) = α.toFun (γu)(pathSpeed γu)
      -- Goal: α.toFun (γu)(pathSpeed γu) = chartFormCoeff Q₀ i (z₀ + u(z-z₀)) * (z - z₀)
      -- Where z₀ := chartAt Q₀ Q₀, z := chartAt Q₀ Q.
      have h_rewrite_form : z₀ + (u : ℂ) * (z - z₀) =
          (1 - (u : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ + (u : ℂ) * (chartAt (H := ℂ) Q₀) Q := by
        show z₀ + (u : ℂ) * (z - z₀) = (1 - (u : ℂ)) * z₀ + (u : ℂ) * z
        ring
      rw [h_rewrite_form]
      show ((periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q u))
          (Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) u) =
        chartFormCoeff (X := X) Q₀ i
          ((1 - (u : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ + (u : ℂ) * (chartAt (H := ℂ) Q₀) Q) *
        ((chartAt (H := ℂ) Q₀) Q - (chartAt (H := ℂ) Q₀) Q₀)
      exact h_cf
    -- Step 2: RHS continuous on [0, 1].
    have h_rhs_cont : ContinuousOn
        (fun u : ℝ => chartFormCoeff (X := X) Q₀ i (z₀ + (u : ℂ) * (z - z₀)) * (z - z₀))
        (Set.Icc (0 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ continuousOn_const
      -- ContinuousOn of chartFormCoeff Q₀ i (affine in u).
      -- chartFormCoeff is continuous on chart target (from AnalyticOn).
      have h_chartFormCoeff_cont : ContinuousOn (chartFormCoeff (X := X) Q₀ i)
          (chartAt (H := ℂ) Q₀).target :=
        (chartFormCoeff_differentiableOn Q₀ i).continuousOn
      -- The affine map u ↦ z₀ + u(z - z₀) is continuous (ℝ → ℂ).
      have h_affine_cont : Continuous (fun u : ℝ => z₀ + (u : ℂ) * (z - z₀)) := by
        refine Continuous.add continuous_const ?_
        exact Complex.continuous_ofReal.mul continuous_const
      -- The affine maps [0,1] into chart target by h_chart_ball
      -- (after rewriting (z₀ + u(z-z₀)) = ((1-u)z₀ + uz)).
      have h_mapsTo : ∀ u ∈ Set.Icc (0 : ℝ) 1,
          z₀ + (u : ℂ) * (z - z₀) ∈ (chartAt (H := ℂ) Q₀).target := by
        intro u hu
        have h_rewrite : z₀ + (u : ℂ) * (z - z₀) = ((1 - (u : ℂ)) * z₀ + (u : ℂ) * z) := by
          ring
        rw [h_rewrite]
        exact h_chart_ball u hu
      exact h_chartFormCoeff_cont.comp h_affine_cont.continuousOn h_mapsTo
    -- Step 3: ContinuousOn of LHS via congruence.
    -- We have h_eq : ∀ u ∈ Icc 0 1, LHS(u) = RHS(u).
    -- ContinuousOn.congr converts ContinuousOn of RHS to ContinuousOn of LHS via EqOn.
    refine h_rhs_cont.congr ?_
    intro u hu
    exact h_eq u hu

/-! ### Smoothstep-reparameterized smoothPath

`smoothPath` from `Classical.choice` may not have zero derivative at
endpoints. To make the concat-at-junction smoothness work, we
similarly compose with `smoothStep01`. -/

/-- The smoothstep-reparameterized version of `smoothPath P Q`. -/
noncomputable def smoothPathSmooth (P Q : X) : ℝ → X :=
  fun t => Jacobians.smoothPath P Q (smoothStep01 t)

/-- `smoothPathSmooth` retains the start/end points of `smoothPath`. -/
@[simp] lemma smoothPathSmooth_zero (P Q : X) : smoothPathSmooth P Q 0 = P := by
  simp [smoothPathSmooth]

@[simp] lemma smoothPathSmooth_one (P Q : X) : smoothPathSmooth P Q 1 = Q := by
  simp [smoothPathSmooth]

/-- **PeriodVec invariance for smoothPath under `smoothStep01`**.

Uses `MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn`
which only requires MonotoneOn (no ContinuousOn of integrand).
This is the key insight: even though smoothPath isn't C¹, the
substitution formula still holds via monotonicity. -/
lemma periodVec_smoothPathSmooth_eq (P Q : X) :
    Jacobians.periodVec (smoothPathSmooth P Q) =
    Jacobians.periodVec (Jacobians.smoothPath P Q) := by
  funext i
  set h : ℝ → ℂ := fun u =>
    (periodBasisForm X i).toFun (Jacobians.smoothPath P Q u)
      (Jacobians.pathSpeed (Jacobians.smoothPath P Q) u) with hh_def
  have h_smoothPath := Jacobians.isSmoothPath_smoothPath P Q
  -- The integrand of `periodVec smoothPathSmooth` equals σ' • h ∘ σ pointwise on [0,1].
  -- Goal: ∫_0..1 (integrand smoothPathSmooth) = ∫_0..1 h.
  show ∫ t in (0:ℝ)..1, (periodBasisForm X i).toFun (smoothPathSmooth P Q t)
      (Jacobians.pathSpeed (smoothPathSmooth P Q) t) = ∫ u in (0:ℝ)..1, h u
  -- Step 1: rewrite LHS integrand as σ' • (h ∘ σ).
  have h_eq : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      (periodBasisForm X i).toFun (smoothPathSmooth P Q t)
        (Jacobians.pathSpeed (smoothPathSmooth P Q) t) =
      Jacobians.smoothStep01_deriv t • h (Jacobians.smoothStep01 t) := by
    intro t ht
    show (periodBasisForm X i).toFun
        (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t))
        (Jacobians.pathSpeed (Jacobians.smoothPath P Q ∘ Jacobians.smoothStep01) t) =
        Jacobians.smoothStep01_deriv t • h (Jacobians.smoothStep01 t)
    have hs_uIcc : Jacobians.smoothStep01 t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Jacobians.smoothStep01_mem_unit t
    have hγ_diff := h_smoothPath.diff (Jacobians.smoothStep01 t) hs_uIcc
    have h_speed := pathSpeed_smoothStep01_comp_eq (Jacobians.smoothPath P Q) t hγ_diff
    rw [h_speed]
    have h_lin : ((periodBasisForm X i).toFun
          (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t)))
        ((Jacobians.smoothStep01_deriv t : ℂ) *
          Jacobians.pathSpeed (Jacobians.smoothPath P Q) (Jacobians.smoothStep01 t)) =
      (Jacobians.smoothStep01_deriv t : ℂ) *
        ((periodBasisForm X i).toFun
          (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t)))
          (Jacobians.pathSpeed (Jacobians.smoothPath P Q) (Jacobians.smoothStep01 t)) := by
      have h_ml := ((periodBasisForm X i).toFun
          (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t))).map_smul
        (Jacobians.smoothStep01_deriv t : ℂ)
        (Jacobians.pathSpeed (Jacobians.smoothPath P Q) (Jacobians.smoothStep01 t))
      simp only [smul_eq_mul] at h_ml
      exact h_ml
    rw [h_lin]
    show (Jacobians.smoothStep01_deriv t : ℝ) • h (Jacobians.smoothStep01 t) =
        (Jacobians.smoothStep01_deriv t : ℂ) * h (Jacobians.smoothStep01 t)
    exact Complex.real_smul
  rw [intervalIntegral.integral_congr h_eq]
  -- Step 2: apply substitution formula.
  -- Goal: ∫_0..1 σ' • (h ∘ σ) = ∫_0..1 h.
  -- Convert interval integral to Bochner via Icc:
  have h_convert : ∀ (f : ℝ → ℂ),
      ∫ t in (0:ℝ)..1, f t = ∫ t in Set.Icc (0:ℝ) 1, f t := fun f => by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h_convert (fun t => Jacobians.smoothStep01_deriv t • h (Jacobians.smoothStep01 t))]
  rw [h_convert h]
  -- Apply integral_image_eq_integral_deriv_smul_of_monotoneOn.
  have h_subst := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0:ℝ) 1) measurableSet_Icc
    (f := Jacobians.smoothStep01) (f' := Jacobians.smoothStep01_deriv)
    (fun x _ => (Jacobians.smoothStep01_hasDerivAt_explicit x).hasDerivWithinAt)
    Jacobians.smoothStep01_monotoneOn_Icc h
  rw [Jacobians.smoothStep01_image_Icc] at h_subst
  exact h_subst.symm

/-- `smoothPathSmooth` is an `IsSmoothPath`, with zero derivative at
endpoints (via `smoothStep01`'s zero boundary derivatives). Closes
`start` (PROVEN), `finish` (PROVEN), `cont` (PROVEN, composition of
continuous smoothPath with continuous smoothStep01). `diff` and
`integrable` remain sub-sorries pending chain-rule + reparam
integrability work. -/
lemma isSmoothPath_smoothPathSmooth (P Q : X) :
    Jacobians.IsSmoothPath P Q (smoothPathSmooth P Q) := by
  have h_smoothPath := Jacobians.isSmoothPath_smoothPath P Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact smoothPathSmooth_zero P Q
  · exact smoothPathSmooth_one P Q
  · -- Continuous (smoothPath P Q ∘ smoothStep01)
    exact h_smoothPath.cont.comp Jacobians.smoothStep01_continuous
  · -- diff at each t ∈ uIcc 0 1 — via chain rule
    -- (chartAt (smoothPath ∘ σ t)) ∘ smoothPath ∘ σ = ((chartAt(γ ∘ σ t)) ∘ γ) ∘ σ
    -- Inner diff at σ t (from IsSmoothPath.diff of smoothPath at σ t).
    -- σ diff at t.
    -- Composition is diff.
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    have hs_Icc : Jacobians.smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 :=
      Jacobians.smoothStep01_mem_unit t
    have hs_uIcc : Jacobians.smoothStep01 t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hs_Icc
    have h_inner_diff := h_smoothPath.diff (Jacobians.smoothStep01 t) hs_uIcc
    have h_sigma_diff : DifferentiableAt ℝ Jacobians.smoothStep01 t :=
      Jacobians.smoothStep01_differentiable t
    -- smoothPathSmooth t = smoothPath (σ t), so chartAt (smoothPathSmooth t) = chartAt (smoothPath (σ t)).
    have h_eq : ((chartAt (H := ℂ) (smoothPathSmooth P Q t)).toFun ∘ smoothPathSmooth P Q) =
        ((chartAt (H := ℂ) (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t))).toFun ∘
          Jacobians.smoothPath P Q) ∘ Jacobians.smoothStep01 := by
      funext s; rfl
    rw [h_eq]
    exact h_inner_diff.comp t h_sigma_diff
  · -- velCont: `smoothPathSmooth = smoothPath ∘ smoothStep01`; apply `velCont_reparam` (smooth
    -- scalar reparam σ = smoothStep01, scale σ' = smoothStep01_deriv, chain rule via
    -- `pathSpeed_smoothStep01_comp_eq`).
    have hmaps : Set.MapsTo Jacobians.smoothStep01 (Set.Icc (0:ℝ) 1) (Set.Icc 0 1) :=
      fun s _ => Jacobians.smoothStep01_mem_unit s
    have hσcont : ContinuousOn Jacobians.smoothStep01 (Set.Icc (0:ℝ) 1) :=
      Jacobians.smoothStep01_continuous.continuousOn
    have hσ'cont : ContinuousOn (fun s : ℝ => (Jacobians.smoothStep01_deriv s : ℂ))
        (Set.Icc (0:ℝ) 1) :=
      (Complex.continuous_ofReal.comp Jacobians.smoothStep01_deriv_continuous).continuousOn
    have hspeed : ∀ s ∈ Set.Icc (0:ℝ) 1,
        pathSpeed (Jacobians.smoothPath P Q ∘ Jacobians.smoothStep01) s =
          (Jacobians.smoothStep01_deriv s : ℂ) •
            pathSpeed (Jacobians.smoothPath P Q) (Jacobians.smoothStep01 s) := by
      intro s _
      have hs_uIcc : Jacobians.smoothStep01 s ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact Jacobians.smoothStep01_mem_unit s
      have hγ_diff := h_smoothPath.diff (Jacobians.smoothStep01 s) hs_uIcc
      rw [pathSpeed_smoothStep01_comp_eq (Jacobians.smoothPath P Q) s hγ_diff, smul_eq_mul]
    exact velCont_reparam (Jacobians.smoothPath P Q) Jacobians.smoothStep01
      Jacobians.smoothStep01_deriv hmaps hσcont hσ'cont hspeed h_smoothPath.velCont

/-! ### Closed loop via smoothstep junctions

With `ChartBallPathSmooth` and `smoothPathSmooth` both having zero
boundary derivatives, the bare `concat γ₁ (reverse γ₂)` has matching
(all zero) derivatives at the junction `t = 1/2`, hence is a closed
smooth loop. -/

/-- **The concat of `ChartBallPathSmooth Q₀ Q` and `reverse(smoothPathSmooth
Q₀ Q)` is a closed smooth loop at `Q₀`.**

All path endpoints have zero derivative (via `smoothStep01`), so the
bare `concat`'s derivative at the junction `t = 1/2` is `0` from both
sides → differentiable. -/
lemma isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
    (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.IsClosedSmoothLoop (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q))) := by
  have h_γ₁ : Jacobians.IsSmoothPath Q₀ Q (Jacobians.ChartBallPathSmooth Q₀ Q) :=
    isSmoothPath_ChartBallPathSmooth Q₀ Q hQ_src h_chart_ball
  have h_γ₂ : Jacobians.IsSmoothPath Q₀ Q (smoothPathSmooth Q₀ Q) :=
    isSmoothPath_smoothPathSmooth Q₀ Q
  have h_γ₂_rev : Jacobians.IsSmoothPath Q Q₀ (Jacobians.reverse (smoothPathSmooth Q₀ Q)) :=
    h_γ₂.reverse
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- closed: concat γ₁ γ₂' 0 = concat γ₁ γ₂' 1
    show Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
        (Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 =
      Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
        (Jacobians.reverse (smoothPathSmooth Q₀ Q)) 1
    rw [Jacobians.concat_apply_left _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [Jacobians.concat_apply_right _ _ (by norm_num : ¬ (1:ℝ) ≤ 1/2)]
    show Jacobians.ChartBallPathSmooth Q₀ Q (2 * 0) =
      Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * 1 - 1)
    have h_lhs : Jacobians.ChartBallPathSmooth Q₀ Q (2 * 0) = Q₀ := by
      simp [h_γ₁.start]
    have h_rhs : Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * 1 - 1) = Q₀ := by
      have h_eq : (2 * (1 : ℝ) - 1) = 1 := by norm_num
      rw [h_eq]
      exact h_γ₂_rev.finish
    rw [h_lhs, h_rhs]
  · -- continuity: concat of continuous γ₁ and continuous γ₂' matching at 1/2
    -- concat γ₁ γ₂' t = if t ≤ 1/2 then γ₁(2t) else γ₂'(2t-1)
    show Continuous (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q)))
    unfold Jacobians.concat
    -- Apply Continuous.if_le.
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · -- γ₁ ∘ (2·) is continuous
      exact h_γ₁.cont.comp (continuous_const.mul continuous_id)
    · -- γ₂' ∘ (2·-1) is continuous
      exact h_γ₂_rev.cont.comp ((continuous_const.mul continuous_id).sub continuous_const)
    · -- At t = 1/2 (where p t = q t): γ₁(2*(1/2)) = γ₂'(2*(1/2)-1)
      intro t ht
      -- ht : t = 1/2
      have ht_eq : t = 1/2 := ht
      rw [ht_eq]
      show Jacobians.ChartBallPathSmooth Q₀ Q (2 * (1/2 : ℝ)) =
        Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * (1/2 : ℝ) - 1)
      have h_left : (2 * (1/2 : ℝ)) = 1 := by norm_num
      rw [h_left]
      -- Goal: ChartBallPathSmooth Q₀ Q 1 = reverse ... (1 - 1)
      have h_right : ((1 : ℝ) - 1) = 0 := by norm_num
      rw [h_right]
      rw [h_γ₁.finish]
      exact h_γ₂_rev.start.symm
  · -- diff at each t ∈ uIcc 0 1: case split on t vs 1/2.
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    rcases lt_trichotomy t (1/2) with h_lt | h_eq | h_gt
    · -- t < 1/2: use γ₁'s diff at 2t via pathSpeed_concat_left machinery
      have h2t_Icc : 2 * t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        refine ⟨by linarith [ht_Icc.1], ?_⟩
        linarith [ht_Icc.1]
      have h_inner_diff := h_γ₁.diff (2 * t) h2t_Icc
      -- (chartAt (γ t)) ∘ concat = ((chartAt (γ₁(2t))) ∘ γ₁) ∘ (2·) in nbhd of t.
      have h_pt : Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t =
          Jacobians.ChartBallPathSmooth Q₀ Q (2 * t) :=
        Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
      have h_eventually : (chartAt (H := ℂ)
          (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
            (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t)).toFun ∘
          Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
            (Jacobians.reverse (smoothPathSmooth Q₀ Q)) =ᶠ[nhds t]
        ((chartAt (H := ℂ) (Jacobians.ChartBallPathSmooth Q₀ Q (2 * t))).toFun ∘
          Jacobians.ChartBallPathSmooth Q₀ Q) ∘ (fun s : ℝ => 2 * s) := by
        have h_open : IsOpen (Set.Iio (1/2 : ℝ)) := isOpen_Iio
        have ht_mem : t ∈ Set.Iio (1/2 : ℝ) := h_lt
        filter_upwards [h_open.mem_nhds ht_mem] with s hs
        simp only [Function.comp_apply, h_pt]
        rw [Jacobians.concat_apply_left _ _ (le_of_lt hs)]
      rw [Filter.EventuallyEq.differentiableAt_iff h_eventually]
      have h_mul_diff : DifferentiableAt ℝ (fun s : ℝ => 2 * s) t :=
        (differentiableAt_const _).mul differentiableAt_id
      exact h_inner_diff.comp t h_mul_diff
    · -- t = 1/2: junction case (both sides have zero derivative)
      -- At t = 1/2, γ(1/2) = γ₁(1) = Q. We prove HasDerivAt = 0 via
      -- HasDerivWithinAt on Iic ∪ Ici. Both sides give derivative 0
      -- (smoothStep01_deriv(1) = smoothStep01_deriv(0) = 0).
      subst h_eq
      -- Compute γ(1/2) = Q.
      have hQ_eq : Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) (1/2 : ℝ) = Q := by
        rw [Jacobians.concat_apply_left _ _ (le_refl _)]
        show Jacobians.ChartBallPathSmooth Q₀ Q ((2 : ℝ) * (1/2)) = Q
        rw [show (2 : ℝ) * (1/2) = 1 from by norm_num]
        exact h_γ₁.finish
      rw [show (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) (1/2 : ℝ)) = Q from hQ_eq]
      -- Goal: DifferentiableAt ℝ ((chartAt Q).toFun ∘ concat γ₁ γ₂_rev) (1/2)
      set f : ℝ → ℂ := (chartAt (H := ℂ) Q).toFun ∘
        Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) with hf_def
      -- ============ LEFT SIDE: HasDerivAt = 0 at 1/2 from Iic ============
      have h_one_uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
      have h_g_L_diff : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (Jacobians.ChartBallPathSmooth Q₀ Q 1)).toFun ∘
            Jacobians.ChartBallPathSmooth Q₀ Q) 1 := h_γ₁.diff 1 h_one_uIcc
      rw [h_γ₁.finish] at h_g_L_diff
      -- pathSpeed γ₁ 1 = 0 via chain rule + smoothStep01_deriv 1 = 0.
      have h_chart_ball_at_one :
          ((1 - ((1 : ℝ) : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
            ((1 : ℝ) : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target :=
        h_chart_ball 1 ⟨zero_le_one, le_refl _⟩
      have h_inner_diff_at_σ1 : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q
              (Jacobians.smoothStep01 1))).toFun ∘
            Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 1) := by
        rw [Jacobians.smoothStep01_one]
        exact Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q 1
          h_chart_ball_at_one
      have h_ps_γ₁_one : Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 1 = 0 := by
        show Jacobians.pathSpeed
          (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
        rw [pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1
          h_inner_diff_at_σ1]
        rw [Jacobians.smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]
      -- HasDerivAt of g_L = (chartAt Q) ∘ ChartBallPathSmooth at 1 with derivative 0.
      have h_g_L_HDA : HasDerivAt
          ((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) 0 1 := by
        have h_HDA := h_g_L_diff.hasDerivAt
        have h_path_eq : Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 1 =
            deriv ((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) 1 := by
          show fderiv ℝ
            ((chartAt (H := ℂ) (Jacobians.ChartBallPathSmooth Q₀ Q 1)).toFun ∘
              Jacobians.ChartBallPathSmooth Q₀ Q) 1 1 = _
          rw [h_γ₁.finish]; rfl
        have h_deriv_zero :
            deriv ((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) 1 = 0 := by
          rw [← h_path_eq]; exact h_ps_γ₁_one
        rw [← h_deriv_zero]; exact h_HDA
      -- HasDerivAt for the doubling map at 1/2.
      have h_2mul_HDA : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) (1/2 : ℝ) := by
        have h := (hasDerivAt_id (1/2 : ℝ)).const_mul (2 : ℝ)
        simpa using h
      -- Chain rule: HasDerivAt (g_L ∘ (2·)) 0 (1/2).
      have h_f_L_HDA : HasDerivAt
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) ∘
            (fun s : ℝ => 2 * s)) 0 (1/2 : ℝ) := by
        have h_scomp := h_g_L_HDA.scomp_of_eq (1/2 : ℝ) h_2mul_HDA
          (by norm_num : (1 : ℝ) = 2 * (1/2 : ℝ))
        simpa using h_scomp
      -- f = g_L ∘ (2·) on Iic (1/2).
      have h_eqOn_Iic : Set.EqOn f
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) ∘
            (fun s : ℝ => 2 * s)) (Set.Iic (1/2 : ℝ)) := by
        intro s hs
        show ((chartAt (H := ℂ) Q).toFun ∘ _) s =
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.ChartBallPathSmooth Q₀ Q) ∘
            (fun s : ℝ => 2 * s)) s
        simp only [Function.comp_apply]
        rw [Jacobians.concat_apply_left _ _ hs]
      have h_half_in_Iic : (1/2 : ℝ) ∈ Set.Iic (1/2 : ℝ) := Set.self_mem_Iic
      have h_Iic_HDWA : HasDerivWithinAt f 0 (Set.Iic (1/2 : ℝ)) (1/2 : ℝ) := by
        have h_inner := h_f_L_HDA.hasDerivWithinAt (s := Set.Iic (1/2 : ℝ))
        exact h_inner.congr (fun s hs => h_eqOn_Iic hs) (h_eqOn_Iic h_half_in_Iic)
      -- ============ RIGHT SIDE: HasDerivAt = 0 at 1/2 from Ici ============
      have h_zero_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
      have h_γ₂_rev_zero : Jacobians.reverse (smoothPathSmooth Q₀ Q) 0 = Q := h_γ₂_rev.start
      have h_g_R_diff : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (Jacobians.reverse (smoothPathSmooth Q₀ Q) 0)).toFun ∘
            Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 :=
        h_γ₂_rev.diff 0 h_zero_uIcc
      rw [h_γ₂_rev_zero] at h_g_R_diff
      -- pathSpeed smoothPathSmooth 1 = 0 via chain rule + smoothStep01_deriv 1 = 0.
      have h_smoothPath := Jacobians.isSmoothPath_smoothPath Q₀ Q
      have h_inner_diff_at_σ1_sp : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (Jacobians.smoothPath Q₀ Q
              (Jacobians.smoothStep01 1))).toFun ∘
            Jacobians.smoothPath Q₀ Q) (Jacobians.smoothStep01 1) := by
        rw [Jacobians.smoothStep01_one]; exact h_smoothPath.diff 1 h_one_uIcc
      have h_ps_smoothPathSmooth_one :
          Jacobians.pathSpeed (smoothPathSmooth Q₀ Q) 1 = 0 := by
        show Jacobians.pathSpeed
          (Jacobians.smoothPath Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
        rw [pathSpeed_smoothStep01_comp_eq (Jacobians.smoothPath Q₀ Q) 1
          h_inner_diff_at_σ1_sp]
        rw [Jacobians.smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]
      -- pathSpeed (reverse smoothPathSmooth) 0 = -pathSpeed smoothPathSmooth 1 = 0.
      have h_γ₂ := isSmoothPath_smoothPathSmooth Q₀ Q
      have h_smoothPathSmooth_one_diff : DifferentiableAt ℝ
          ((chartAt (H := ℂ) (smoothPathSmooth Q₀ Q (1 - 0))).toFun ∘
            smoothPathSmooth Q₀ Q) (1 - 0) := by
        rw [show (1 : ℝ) - 0 = 1 from by norm_num]
        exact h_γ₂.diff 1 h_one_uIcc
      have h_ps_γ₂_rev_zero :
          Jacobians.pathSpeed (Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 = 0 := by
        rw [Jacobians.pathSpeed_reverse (smoothPathSmooth Q₀ Q) 0
          h_smoothPathSmooth_one_diff]
        rw [show (1 : ℝ) - 0 = 1 from by norm_num, h_ps_smoothPathSmooth_one, neg_zero]
      -- HasDerivAt of g_R = (chartAt Q) ∘ reverse smoothPathSmooth at 0 with derivative 0.
      have h_g_R_HDA : HasDerivAt
          ((chartAt (H := ℂ) Q).toFun ∘ Jacobians.reverse (smoothPathSmooth Q₀ Q))
            0 0 := by
        have h_HDA := h_g_R_diff.hasDerivAt
        have h_path_eq :
            Jacobians.pathSpeed (Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 =
            deriv ((chartAt (H := ℂ) Q).toFun ∘
              Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 := by
          show fderiv ℝ
            ((chartAt (H := ℂ) (Jacobians.reverse (smoothPathSmooth Q₀ Q) 0)).toFun ∘
              Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 1 = _
          rw [h_γ₂_rev_zero]; rfl
        have h_deriv_zero :
            deriv ((chartAt (H := ℂ) Q).toFun ∘
              Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 = 0 := by
          rw [← h_path_eq]; exact h_ps_γ₂_rev_zero
        rw [← h_deriv_zero]; exact h_HDA
      -- HasDerivAt for the shift map (2·-1) at 1/2.
      have h_sub_HDA : HasDerivAt (fun s : ℝ => 2 * s - 1) (2 : ℝ) (1/2 : ℝ) :=
        h_2mul_HDA.sub_const 1
      -- Chain rule: HasDerivAt (g_R ∘ (2·-1)) 0 (1/2).
      have h_f_R_HDA : HasDerivAt
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.reverse (smoothPathSmooth Q₀ Q)) ∘
            (fun s : ℝ => 2 * s - 1)) 0 (1/2 : ℝ) := by
        have h_scomp := h_g_R_HDA.scomp_of_eq (1/2 : ℝ) h_sub_HDA
          (by norm_num : (0 : ℝ) = 2 * (1/2 : ℝ) - 1)
        simpa using h_scomp
      -- f = g_R ∘ (2·-1) on Ici (1/2).
      have h_eqOn_Ici : Set.EqOn f
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.reverse (smoothPathSmooth Q₀ Q)) ∘
            (fun s : ℝ => 2 * s - 1)) (Set.Ici (1/2 : ℝ)) := by
        intro s hs
        show ((chartAt (H := ℂ) Q).toFun ∘ _) s =
          (((chartAt (H := ℂ) Q).toFun ∘ Jacobians.reverse (smoothPathSmooth Q₀ Q)) ∘
            (fun s : ℝ => 2 * s - 1)) s
        simp only [Function.comp_apply]
        have hs_le : (1/2 : ℝ) ≤ s := hs
        rcases eq_or_lt_of_le hs_le with h_eq_half | h_gt_half
        · -- s = 1/2: both sides equal (chartAt Q)(Q).
          rw [← h_eq_half]
          rw [Jacobians.concat_apply_left _ _ (le_refl _)]
          rw [show (2 : ℝ) * (1/2) - 1 = 0 from by norm_num,
              show (2 : ℝ) * (1/2) = 1 from by norm_num]
          rw [h_γ₁.finish, h_γ₂_rev.start]
        · -- s > 1/2
          rw [Jacobians.concat_apply_right _ _ (not_le.mpr h_gt_half)]
      have h_half_in_Ici : (1/2 : ℝ) ∈ Set.Ici (1/2 : ℝ) := Set.self_mem_Ici
      have h_Ici_HDWA : HasDerivWithinAt f 0 (Set.Ici (1/2 : ℝ)) (1/2 : ℝ) := by
        have h_inner := h_f_R_HDA.hasDerivWithinAt (s := Set.Ici (1/2 : ℝ))
        exact h_inner.congr (fun s hs => h_eqOn_Ici hs) (h_eqOn_Ici h_half_in_Ici)
      -- ============ UNION ============
      have h_union : HasDerivWithinAt f 0
          (Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ)) (1/2 : ℝ) :=
        h_Iic_HDWA.union h_Ici_HDWA
      have h_union_eq : Set.Iic (1/2 : ℝ) ∪ Set.Ici (1/2 : ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
        rcases lt_or_ge x (1/2 : ℝ) with h | h
        · exact Or.inl (le_of_lt h)
        · exact Or.inr h
      rw [h_union_eq] at h_union
      exact (h_union.hasDerivAt Filter.univ_mem).differentiableAt
    · -- t > 1/2: use γ₂_rev's diff at 2t-1
      have h2tm1_Icc : 2 * t - 1 ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        refine ⟨by linarith, by linarith [ht_Icc.2]⟩
      have h_inner_diff := h_γ₂_rev.diff (2 * t - 1) h2tm1_Icc
      have h_pt : Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t =
          Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * t - 1) :=
        Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
      have h_eventually : (chartAt (H := ℂ)
          (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
            (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t)).toFun ∘
          Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
            (Jacobians.reverse (smoothPathSmooth Q₀ Q)) =ᶠ[nhds t]
        ((chartAt (H := ℂ) (Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * t - 1))).toFun ∘
          Jacobians.reverse (smoothPathSmooth Q₀ Q)) ∘ (fun s : ℝ => 2 * s - 1) := by
        have h_open : IsOpen (Set.Ioi (1/2 : ℝ)) := isOpen_Ioi
        have ht_mem : t ∈ Set.Ioi (1/2 : ℝ) := h_gt
        filter_upwards [h_open.mem_nhds ht_mem] with s hs
        simp only [Function.comp_apply, h_pt]
        rw [Jacobians.concat_apply_right _ _ (not_le.mpr hs)]
      rw [Filter.EventuallyEq.differentiableAt_iff h_eventually]
      have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 2 * s - 1) t :=
        ((differentiableAt_const _).mul differentiableAt_id).sub (differentiableAt_const _)
      exact h_inner_diff.comp t h_sub_diff
  · -- velCont: glue the two pieces' velocity sections via `velCont_concat`, whose junction-velocity
    -- hypotheses (`pathSpeed γ₁ 1 = 0`, `pathSpeed γ₂' 0 = 0`) hold by the smoothstep reparam.
    have h_one_uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
    have h_zero_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
    -- hv₁: pathSpeed (ChartBallPathSmooth Q₀ Q) 1 = 0 (smoothStep01_deriv 1 = 0).
    have h_chart_ball_at_one :
        ((1 - ((1 : ℝ) : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
          ((1 : ℝ) : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target :=
      h_chart_ball 1 ⟨zero_le_one, le_refl _⟩
    have h_inner_diff_at_σ1 : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q
            (Jacobians.smoothStep01 1))).toFun ∘
          Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 1) := by
      rw [Jacobians.smoothStep01_one]
      exact Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q 1 h_chart_ball_at_one
    have hv₁ : Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 1 = 0 := by
      show Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
      rw [pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1 h_inner_diff_at_σ1,
        Jacobians.smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]
    -- hv₂: pathSpeed (reverse (smoothPathSmooth Q₀ Q)) 0 = -pathSpeed (smoothPathSmooth Q₀ Q) 1 = 0.
    have h_smoothPath := Jacobians.isSmoothPath_smoothPath Q₀ Q
    have h_inner_diff_at_σ1_sp : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (Jacobians.smoothPath Q₀ Q (Jacobians.smoothStep01 1))).toFun ∘
          Jacobians.smoothPath Q₀ Q) (Jacobians.smoothStep01 1) := by
      rw [Jacobians.smoothStep01_one]; exact h_smoothPath.diff 1 h_one_uIcc
    have h_ps_smoothPathSmooth_one : Jacobians.pathSpeed (smoothPathSmooth Q₀ Q) 1 = 0 := by
      show Jacobians.pathSpeed (Jacobians.smoothPath Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
      rw [pathSpeed_smoothStep01_comp_eq (Jacobians.smoothPath Q₀ Q) 1 h_inner_diff_at_σ1_sp,
        Jacobians.smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]
    have h_smoothPathSmooth_one_diff : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (smoothPathSmooth Q₀ Q (1 - 0))).toFun ∘ smoothPathSmooth Q₀ Q) (1 - 0) := by
      rw [show (1 : ℝ) - 0 = 1 from by norm_num]; exact h_γ₂.diff 1 h_one_uIcc
    have hv₂ : Jacobians.pathSpeed (Jacobians.reverse (smoothPathSmooth Q₀ Q)) 0 = 0 := by
      rw [Jacobians.pathSpeed_reverse (smoothPathSmooth Q₀ Q) 0 h_smoothPathSmooth_one_diff,
        show (1 : ℝ) - 0 = 1 from by norm_num, h_ps_smoothPathSmooth_one, neg_zero]
    -- hjoin: the pieces meet at Q.
    have hjoin : Jacobians.ChartBallPathSmooth Q₀ Q 1 =
        Jacobians.reverse (smoothPathSmooth Q₀ Q) 0 := h_γ₁.finish.trans h_γ₂_rev.start.symm
    exact velCont_concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q)) h_γ₁.diff h_γ₂_rev.diff hv₁ hv₂ hjoin
      h_γ₁.velCont h_γ₂_rev.velCont

/-- **periodVec of the concat = difference of periodVecs** for our paths.

Uses `periodVec_reverse` (smoothPathSmooth diff is proven) and recognizes
that `periodVec (concat γ₁ (reverse γ₂)) = periodVec γ₁ - periodVec γ₂`
when γ₁ and γ₂ are smooth paths with all integrability hypotheses
holding.

The full unconditional version requires applying `periodVec_concat`
with its 6 hypotheses (integrabilities + pathSpeed_concat identities).
For now we take periodVec_reverse only, leaving the concat application
as a sub-obligation. -/
lemma periodVec_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
    (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.periodVec (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q))) =
    Jacobians.periodVec (Jacobians.ChartBallPathSmooth Q₀ Q) -
    Jacobians.periodVec (smoothPathSmooth Q₀ Q) := by
  have h_γ₁ : Jacobians.IsSmoothPath Q₀ Q (Jacobians.ChartBallPathSmooth Q₀ Q) :=
    isSmoothPath_ChartBallPathSmooth Q₀ Q hQ_src h_chart_ball
  have h_γ₂ : Jacobians.IsSmoothPath Q₀ Q (smoothPathSmooth Q₀ Q) :=
    isSmoothPath_smoothPathSmooth Q₀ Q
  have h_γ₂_rev : Jacobians.IsSmoothPath Q Q₀ (Jacobians.reverse (smoothPathSmooth Q₀ Q)) :=
    h_γ₂.reverse
  -- periodVec(reverse γ₂) = -periodVec γ₂ via periodVec_reverse.
  have h_reverse_eq : Jacobians.periodVec (Jacobians.reverse (smoothPathSmooth Q₀ Q)) =
      -Jacobians.periodVec (smoothPathSmooth Q₀ Q) :=
    Jacobians.periodVec_reverse (smoothPathSmooth Q₀ Q) (fun t ht => by
      have h1t : 1 - t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht ⊢
        rcases ht with ⟨h0, h1⟩
        refine ⟨by linarith, by linarith⟩
      exact h_γ₂.diff (1 - t) h1t)
  -- periodVec(concat γ₁ γ₂') = periodVec γ₁ + periodVec γ₂' via periodVec_concat.
  -- Six hypotheses: integrabilities (full + each half) + a.e. identities.
  have h_loop := isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
    Q₀ Q hQ_src h_chart_ball
  have h_full := h_loop.integrable
  have h_ae_neq : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ≠ (1/2 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  have h_concat_eq : Jacobians.periodVec (Jacobians.concat
      (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q))) =
    Jacobians.periodVec (Jacobians.ChartBallPathSmooth Q₀ Q) +
    Jacobians.periodVec (Jacobians.reverse (smoothPathSmooth Q₀ Q)) := by
    apply Jacobians.periodVec_concat
    · exact h_γ₁.integrable
    · exact h_γ₂_rev.integrable
    · -- hint_concat_left: concat integrand on (0, 1/2) via mono_set from (0, 1).
      intro i
      refine (h_full i).mono_set ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2),
          Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro x hx
      exact ⟨hx.1, le_trans hx.2 (by norm_num : (1/2 : ℝ) ≤ 1)⟩
    · -- hint_concat_right: concat integrand on (1/2, 1) via mono_set from (0, 1).
      intro i
      refine (h_full i).mono_set ?_
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1),
          Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro x hx
      exact ⟨le_trans (by norm_num : (0:ℝ) ≤ 1/2) hx.1, hx.2⟩
    · -- h_ae_left: concat integrand =ᵐ 2 * γ₁_integrand(2t) on uIoc 0 (1/2).
      intro i
      refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
      filter_upwards [h_ae_neq] with t h_neq ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
      obtain ⟨ht_pos, ht_le⟩ := ht
      have h_lt : t < 1/2 := lt_of_le_of_ne ht_le h_neq
      have h_2t_uIcc : 2 * t ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        refine ⟨by linarith, by linarith⟩
      have h_diff_at_2t := h_γ₁.diff (2 * t) h_2t_uIcc
      have h_concat_apply : Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t =
          Jacobians.ChartBallPathSmooth Q₀ Q (2 * t) :=
        Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
      have h_pathSpeed_eq : Jacobians.pathSpeed (Jacobians.concat
          (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q))) t =
          2 * Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) (2 * t) :=
        Jacobians.pathSpeed_concat_left _ _ t h_lt h_diff_at_2t
      rw [h_concat_apply, h_pathSpeed_eq]
      have h_lin := ((periodBasisForm X i).toFun
          (Jacobians.ChartBallPathSmooth Q₀ Q (2 * t))).map_smul
        (2 : ℂ) (Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) (2 * t))
      simp only [smul_eq_mul] at h_lin
      exact h_lin
    · -- h_ae_right: concat integrand =ᵐ 2 * γ₂_rev_integrand(2t-1) on uIoc (1/2) 1.
      intro i
      refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
      filter_upwards [h_ae_neq] with t _h_neq ht
      rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
      obtain ⟨ht_pos, ht_le⟩ := ht
      have h_gt : 1/2 < t := ht_pos
      have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0:ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        refine ⟨by linarith, by linarith⟩
      have h_diff_at := h_γ₂_rev.diff (2 * t - 1) h_2tm1_uIcc
      have h_concat_apply : Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q)) t =
          Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * t - 1) :=
        Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
      have h_pathSpeed_eq : Jacobians.pathSpeed (Jacobians.concat
          (Jacobians.ChartBallPathSmooth Q₀ Q)
          (Jacobians.reverse (smoothPathSmooth Q₀ Q))) t =
          2 * Jacobians.pathSpeed (Jacobians.reverse (smoothPathSmooth Q₀ Q))
            (2 * t - 1) :=
        Jacobians.pathSpeed_concat_right _ _ t h_gt h_diff_at
      rw [h_concat_apply, h_pathSpeed_eq]
      have h_lin := ((periodBasisForm X i).toFun
          (Jacobians.reverse (smoothPathSmooth Q₀ Q) (2 * t - 1))).map_smul
        (2 : ℂ) (Jacobians.pathSpeed (Jacobians.reverse (smoothPathSmooth Q₀ Q))
          (2 * t - 1))
      simp only [smul_eq_mul] at h_lin
      exact h_lin
  rw [h_concat_eq, h_reverse_eq]
  ring

/-- **Path-difference-in-lattice for ChartBallPath vs smoothPath.**

For `Q₀, Q : X` with the affine chart-coord segment from `(chartAt Q₀) Q₀`
to `(chartAt Q₀) Q` contained in `(chartAt Q₀).target`, the two smooth
paths `ChartBallPath Q₀ Q₀ Q` and `smoothPath Q₀ Q` both go from `Q₀`
to `Q`, so their periodVecs differ by a lattice element.

**Proof structure.** Apply `mk_periodVec_eq_of_endpoints` with `γ₁ :=
ChartBallPath Q₀ Q₀ Q`, `γ₂ := smoothPath Q₀ Q`. Hypotheses:
* `γ₁ 0 = γ₂ 0 = Q₀` (`ChartBallPath.start` + `smoothPath_zero`).
* `IsClosedSmoothLoop (concat γ₁ (reverse γ₂))`: needs ChartBallPath
  smoothness on chart-ball + smoothPath smoothness via
  `isSmoothPath_smoothPath` + reverse/concat smoothness preservation
  (proven infrastructure in `Jacobians/LineIntegral.lean` and
  `Jacobians/PeriodLattice.lean`).
* `periodVec_concat` formula: requires integrability of each basis
  form integrand on each piece. For `ChartBallPath`: integrand is
  bounded continuous on `[0, 1]` (using `chartFormCoeff` continuity
  + `chartFrame_cancel` to identify with the path integrand). For
  `smoothPath`: from `IsSmoothPath.integrable`.

We separate this as a single classical-content sub-obligation. -/
lemma chartBallPath_smoothPath_endpoints_eq_in_quotient
    (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    (QuotientAddGroup.mk (Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q)) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
    QuotientAddGroup.mk (Jacobians.periodVec (Jacobians.smoothPath Q₀ Q)) := by
  -- Step 1: replace ChartBallPath by ChartBallPathSmooth (reparam-invariant periodVec).
  rw [← periodVec_ChartBallPathSmooth_eq Q₀ Q h_chart_ball]
  -- Step 2: replace smoothPath by smoothPathSmooth (same trick).
  rw [← periodVec_smoothPathSmooth_eq Q₀ Q]
  -- Step 3: Apply mk_periodVec_eq_of_endpoints with γ₁ = ChartBallPathSmooth, γ₂ = smoothPathSmooth.
  refine Jacobians.mk_periodVec_eq_of_endpoints
    (Jacobians.ChartBallPathSmooth Q₀ Q) (smoothPathSmooth Q₀ Q) ?_ ?_ ?_
  · -- h0: γ₁ 0 = γ₂ 0
    show Jacobians.ChartBallPathSmooth Q₀ Q 0 = smoothPathSmooth Q₀ Q 0
    rw [Jacobians.ChartBallPathSmooth.start Q₀ Q (mem_chart_source ℂ Q₀)]
    rw [smoothPathSmooth_zero]
  · -- hsmooth: concat is IsClosedSmoothLoop
    exact isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
      Q₀ Q hQ_src h_chart_ball
  · -- hconcat: periodVec(concat) = periodVec γ₁ - periodVec γ₂
    exact periodVec_concat_ChartBallPathSmooth_reverse_smoothPathSmooth Q₀ Q hQ_src h_chart_ball

theorem localLift_quotient_eq_ofCurve_eventually
    (P Q₀ : X) :
    (fun Q => QuotientAddGroup.mk
        (localLift (X := X) Q₀ (periodVec (smoothPath P Q₀)) Q) :
      X → (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =ᶠ[nhds Q₀]
      (fun Q => QuotientAddGroup.mk (periodVec (smoothPath P Q))) := by
  filter_upwards [affine_in_target_eventually Q₀, Q_in_chart_source_eventually Q₀]
    with Q hQ hQ_src
  -- Step 1: rewrite LHS via `localLift_eq_const_add_periodVec_ChartBallPath`.
  rw [localLift_eq_const_add_periodVec_ChartBallPath Q₀ Q _ hQ]
  -- LHS = [periodVec(smoothPath P Q₀) + periodVec(ChartBallPath Q₀ Q₀ Q)]
  --     = [periodVec(smoothPath P Q₀)] + [periodVec(ChartBallPath Q₀ Q₀ Q)]
  rw [QuotientAddGroup.mk_add]
  -- Step 2: use `chartBallPath_smoothPath_endpoints_eq_in_quotient` to replace
  -- [periodVec(ChartBallPath)] by [periodVec(smoothPath Q₀ Q)].
  rw [chartBallPath_smoothPath_endpoints_eq_in_quotient Q₀ Q hQ_src hQ]
  -- LHS now = [periodVec(smoothPath P Q₀)] + [periodVec(smoothPath Q₀ Q)]
  -- Step 3: rewrite RHS via `smoothPath_basepoint_change`.
  -- `smoothPath_basepoint_change Q₀ P Q`: with (P, P₀, A) = (Q₀, P, Q), gives:
  --   [periodVec(smoothPath P Q)] = [periodVec(smoothPath Q₀ Q)] + [periodVec(smoothPath P Q₀)]
  rw [Jacobians.smoothPath_basepoint_change Q₀ P Q]
  -- Goal: [periodVec(smoothPath P Q₀)] + [periodVec(smoothPath Q₀ Q)]
  --     = [periodVec(smoothPath Q₀ Q)] + [periodVec(smoothPath P Q₀)]
  -- Quotient is abelian; commute.
  exact add_comm _ _

/-! ## Top-level wiring for `ofCurve_contMDiff`

With `localLift_contMDiffAt` (analytic→ContMDiff bridge, PROVEN) and
`localLift_quotient_eq_ofCurve_eventually` (path-algebra identification,
also PROVEN — modulo `smoothPath` which is `Classical.choice` of the
S1 gap), the proof of `ofCurve_contMDiff` is a straightforward
local-to-global glue.

The function `Jacobians.OfCurveSkeleton.ofCurveContMDiff_via_localLift`
below packages the complete proof skeleton at the level of `Jacobians.
PeriodLattice`'s `truePeriodLattice` (since the quotient instance lives
there); the actual wiring into `Jacobians.ofCurve_contMDiff` in
`Jacobians.lean` requires the `Jacobian X = (Fin (kirovGenus X) → ℂ) ⧸
(periodLattice X)...` chartedSpace instance, which is `truePeriodLattice`
in different clothing — see `Jacobians.lean:periodLattice`. -/

end Jacobians.OfCurveSkeleton
