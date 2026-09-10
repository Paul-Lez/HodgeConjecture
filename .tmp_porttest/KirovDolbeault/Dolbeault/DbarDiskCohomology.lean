/-
  DbarDiskCohomology.lean

  ∂̄-solvability on a disk (full-ball solvability) and the disk-acyclicity it produces.

  The first Dolbeault rung `DbarLocal.dbar_solvable_locally` solves `∂̄u = g` only on a
  *neighborhood* of a point.  Here we upgrade to solvability on a whole **ball** `ball c r`:
  because the *closure* of a bounded ball is compact, a single smooth cutoff `χ` that equals `1`
  on `closedBall c r` already has compact support, so the compactly-supported atom
  `DbarDisk.dbar_solvable_of_compactSupport` solves `∂̄u = χ·g` globally, and `χ·g = g` on the ball.
  No Mittag-Leffler exhaustion is needed — boundedness of the ball does the work.

  `dbar_solvable_ball` is therefore proven **complete** and **axiom-clean**.

  `dbar_holo_splitting_ball` is the genuine Čech↔Dolbeault dictionary on a ball, ALSO proven
  **complete**: a *holomorphic* difference `f = h₂ - h₁` of smooth functions whose `∂̄`s agree can
  be re-split as a *holomorphic* difference of *holomorphic* functions, by solving `∂̄u = ∂̄h₁` on the
  ball (the proven `dbar_solvable_ball`) and subtracting `u`.  This is the local engine behind
  `H¹(disk, 𝒪) = 0`.  The `∂̄ = 0 ⇒ holomorphic` direction is supplied by the Wirtinger
  characterisation `differentiableAt_complex_iff_differentiableAt_real`.
-/
import KirovDolbeault.Dolbeault.DbarLocal

open Complex MeasureTheory Metric
open scoped Topology

namespace Jacobians.Dolbeault.DbarDiskCohomology

/-- **∂̄-solvability on a ball (full-disk solvability).** For `g : ℂ → ℂ` smooth on all of `ℂ` and
any ball `ball c r` (`r > 0`), there is a smooth `u : ℂ → ℂ` with `∂̄u = g` on `ball c r`.

Proof: take a smooth bump `χ` with `χ.rIn = r`, `χ.rOut = r + 1`, so `χ ≡ 1` on the *compact*
`closedBall c r ⊇ ball c r` and `χ` has compact support.  The product `χ·g` is smooth with compact
support, so `DbarDisk.dbar_solvable_of_compactSupport` gives a global smooth `u` with `∂̄u = χ·g`
everywhere; on `ball c r` the cutoff is `1`, so `∂̄u = g` there.

Strictly stronger than the local rung `DbarLocal.dbar_solvable_locally` (it solves on the *whole*
ball, not just a neighborhood of the center).  The crucial point making this elementary — no
exhaustion — is that a bounded ball has *compact* closure, so a single compactly-supported cutoff
suffices. -/
theorem dbar_solvable_ball {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ z ∈ Metric.ball c r, DbarDisk.dbar u z = g z := by
  -- A bump `= 1` on `closedBall c r` (so on `ball c r`) with compact support.
  set χ : ContDiffBump c :=
    { rIn := r, rOut := r + 1, rIn_pos := hr, rIn_lt_rOut := by linarith } with hχ
  set χℂ : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) with hχℂ
  obtain ⟨hχℂ_smooth, hχℂ_supp⟩ := DbarLocal.contDiff_hasCompactSupport_ofReal_contDiffBump χ
  -- The cutoff product `G = χℂ·g` is smooth with compact support.
  set G : ℂ → ℂ := fun z => χℂ z * g z with hG
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G := hχℂ_smooth.mul hg
  have hG_supp : HasCompactSupport G := (show G = χℂ * g from rfl) ▸ hχℂ_supp.mul_right
  -- Solve `∂̄u = G` everywhere via the compactly-supported atom.
  obtain ⟨u, hu_smooth, hu_dbar⟩ := DbarDisk.dbar_solvable_of_compactSupport hG_smooth hG_supp
  refine ⟨u, hu_smooth, fun z hz => ?_⟩
  rw [hu_dbar z]
  show ((χ z : ℝ) : ℂ) * g z = g z
  -- `z ∈ ball c r ⊆ closedBall c χ.rIn`, where the cutoff is `1`.
  rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
  simp

/-- **`∂̄ = 0 ⇒ holomorphic` (Wirtinger).** A function smooth on `ℂ` whose Wirtinger `∂̄` vanishes at
`x` is complex-differentiable at `x`.  `dbar g x = ½((fderiv 1) + I·(fderiv I)) = 0` rearranges to
`fderiv I = I·(fderiv 1)`, the Cauchy–Riemann condition of
`differentiableAt_complex_iff_differentiableAt_real`. -/
theorem differentiableAt_of_dbar_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x : ℂ}
    (hdb : DbarDisk.dbar g x = 0) : DifferentiableAt ℂ g x := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hg.differentiable (by norm_num) x, ?_⟩
  have h2 : (fderiv ℝ g x) 1 + Complex.I * (fderiv ℝ g x) Complex.I = 0 := by
    have := hdb
    rw [DbarDisk.dbar] at this
    field_simp at this
    linear_combination this
  have hD1 : (fderiv ℝ g x) 1 = -(Complex.I * (fderiv ℝ g x) Complex.I) := by linear_combination h2
  rw [hD1, smul_eq_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring

/-- **Holomorphic re-splitting on a ball (the Čech↔Dolbeault dictionary).**
Suppose `f = h₂ - h₁` on a ball `ball c r`, with `h₁, h₂` smooth and `f` *holomorphic* on the ball
(equivalently `∂̄h₁ = ∂̄h₂` there).  Then `f` is also a difference `g₂ - g₁` of functions that are
each *holomorphic* on the ball: solve `∂̄u = ∂̄h₁` on the ball (`dbar_solvable_ball`, since `∂̄h₁` is
smooth), and set `gᵢ = hᵢ - u`; then `gᵢ` is holomorphic (`∂̄gᵢ = ∂̄hᵢ - ∂̄u = 0`,
`differentiableAt_of_dbar_eq_zero`) and `g₂ - g₁ = h₂ - h₁ = f`.

This is the local engine of `H¹(disk, 𝒪) = 0`: a smooth Čech splitting of a holomorphic cocycle can
be corrected to a *holomorphic* splitting.  Proven complete. -/
theorem dbar_holo_splitting_ball (c : ℂ) {r : ℝ} (hr : 0 < r)
    {h₁ h₂ : ℂ → ℂ} (hh₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (hh₂ : ContDiff ℝ (⊤ : ℕ∞) h₂)
    (hdbar : ∀ z ∈ Metric.ball c r, DbarDisk.dbar h₁ z = DbarDisk.dbar h₂ z) :
    ∃ g₁ g₂ : ℂ → ℂ,
      DifferentiableOn ℂ g₁ (Metric.ball c r) ∧ DifferentiableOn ℂ g₂ (Metric.ball c r) ∧
        ∀ z ∈ Metric.ball c r, h₂ z - h₁ z = g₂ z - g₁ z := by
  -- `∂̄h₁` is smooth (built from `fderiv h₁`, itself `C^∞`), so `∂̄u = ∂̄h₁` is solvable on the ball.
  have hdb1_smooth : ContDiff ℝ (⊤ : ℕ∞) (DbarDisk.dbar h₁) := by
    unfold DbarDisk.dbar
    have : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h₁) := hh₁.fderiv_right (le_refl _)
    fun_prop
  obtain ⟨u, hu_smooth, hu_dbar⟩ := dbar_solvable_ball hdb1_smooth c hr
  -- Subtractivity of `∂̄` at a differentiable point (in the lambda form the goal presents `h - u`).
  have hsub : ∀ (h : ℂ → ℂ) (w : ℂ), DifferentiableAt ℝ h w →
      DbarDisk.dbar (fun x => h x - u x) w = DbarDisk.dbar h w - DbarDisk.dbar u w := by
    intro h w hh
    show DbarDisk.dbar (h - u) w = _
    unfold DbarDisk.dbar
    rw [fderiv_sub hh (hu_smooth.differentiable (by norm_num) w)]
    simp only [ContinuousLinearMap.sub_apply]; ring
  refine ⟨h₁ - u, h₂ - u, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · -- `∂̄(h₁ - u) = ∂̄h₁ - ∂̄u = 0` on the ball, so `h₁ - u` is holomorphic there.
    refine (differentiableAt_of_dbar_eq_zero (hh₁.sub hu_smooth) ?_).differentiableWithinAt
    rw [hsub h₁ z (hh₁.differentiable (by norm_num) z), hu_dbar z hz]; ring
  · -- `∂̄(h₂ - u) = ∂̄h₂ - ∂̄u = ∂̄h₂ - ∂̄h₁ = 0` (using `hdbar`).
    refine (differentiableAt_of_dbar_eq_zero (hh₂.sub hu_smooth) ?_).differentiableWithinAt
    rw [hsub h₂ z (hh₂.differentiable (by norm_num) z), hu_dbar z hz, ← hdbar z hz]; ring
  · -- The corrected difference is unchanged: `(h₂ - u) - (h₁ - u) = h₂ - h₁`.
    show h₂ z - h₁ z = (h₂ z - u z) - (h₁ z - u z)
    ring

end Jacobians.Dolbeault.DbarDiskCohomology
