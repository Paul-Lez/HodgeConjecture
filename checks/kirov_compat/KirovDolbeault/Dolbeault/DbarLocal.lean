/-
  DbarLocal.lean

  Local ∂̄-solvability — the first rung of the Dolbeault comparison (the kernel of
  the `D = 0` Serre-duality input).

  From the compactly-supported ∂̄-solvability atom `DbarDisk.dbar_solvable_of_compactSupport`
  (the Cauchy transform, proven axiom-clean in `DbarDisk.lean`), we deduce that *any* smooth
  `g : ℂ → ℂ` can be ∂̄-solved on a neighborhood of an arbitrary point: multiply `g` by a
  smooth cutoff `χ` (a `ContDiffBump`) that equals `1` near `z₀` and has compact support, solve
  the compactly-supported problem for `χ · g`, and restrict to the inner ball where `χ ≡ 1`.

  Main result: `DbarLocal.dbar_solvable_locally`.
-/
import Mathlib
import KirovDolbeault.DbarDisk

open Complex MeasureTheory
open scoped Topology

namespace DbarLocal

/-- The smooth cutoff `χ` is `1` on the open inner ball `Metric.ball z₀ χ.rIn` (not just on the
closed ball), since `ball ⊆ closedBall` and `ContDiffBump.one_of_mem_closedBall`. -/
theorem contDiffBump_eq_one_on_ball {z₀ z : ℂ} (χ : ContDiffBump z₀)
    (hz : z ∈ Metric.ball z₀ χ.rIn) : (χ : ℂ → ℝ) z = 1 :=
  χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)

/-- The ℝ→ℂ coercion of a smooth compactly-supported cutoff `χ : ContDiffBump z₀` is itself a
smooth, compactly-supported function `ℂ → ℂ`.  Returned as a conjunction so callers get both
facts from one cutoff. -/
theorem contDiff_hasCompactSupport_ofReal_contDiffBump {z₀ : ℂ} (χ : ContDiffBump z₀) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ((χ z : ℝ) : ℂ)) ∧
      HasCompactSupport (fun z => ((χ z : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp χ.contDiff, ?_⟩
  -- `fun z => ((χ z : ℝ) : ℂ) = ofReal ∘ χ`, and `ofReal 0 = 0`, so compact support transfers.
  exact (show (fun z => ((χ z : ℝ) : ℂ)) = (fun r : ℝ => (r : ℂ)) ∘ (χ : ℂ → ℝ) from rfl) ▸
    χ.hasCompactSupport.comp_left (by simp)

/-- **Local ∂̄-solvability (the first Dolbeault rung).**  Any smooth `g : ℂ → ℂ` can be
∂̄-solved on an open neighborhood `V` of an arbitrary point `z₀`: there is a smooth `u` with
`∂̄u = g` on `V`.

Proof: cut off `g` by a smooth bump `χ` that is `1` near `z₀` and compactly supported, solve the
compactly-supported equation `∂̄u = χ·g` everywhere via `DbarDisk.dbar_solvable_of_compactSupport`,
and observe `χ·g = g` on the inner ball `V` where `χ ≡ 1`. -/
theorem dbar_solvable_locally {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z₀ : ℂ) :
    ∃ (V : Set ℂ) (u : ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ z ∈ V, DbarDisk.dbar u z = g z := by
  -- A smooth cutoff bump centered at `z₀` (the default instance has `rIn = 1`, `rOut = 2`).
  set χ : ContDiffBump z₀ := default with hχ
  -- Its ℝ→ℂ coercion `χℂ`, smooth with compact support.
  set χℂ : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) with hχℂ
  obtain ⟨hχℂ_smooth, hχℂ_supp⟩ := contDiff_hasCompactSupport_ofReal_contDiffBump χ
  -- The cutoff product `G = χℂ · g` is smooth with compact support.
  set G : ℂ → ℂ := fun z => χℂ z * g z with hG
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G := hχℂ_smooth.mul hg
  have hG_supp : HasCompactSupport G :=
    (show G = χℂ * g from rfl) ▸ hχℂ_supp.mul_right
  -- Solve `∂̄u = G` everywhere via the compactly-supported atom.
  obtain ⟨u, hu_smooth, hu_dbar⟩ := DbarDisk.dbar_solvable_of_compactSupport hG_smooth hG_supp
  -- On `V = ball z₀ rIn`, the cutoff is `1`, so `G = g`; ship `⟨V, u, …⟩`.
  refine ⟨Metric.ball z₀ χ.rIn, u, Metric.isOpen_ball, Metric.mem_ball_self χ.rIn_pos,
    hu_smooth, fun z hz => ?_⟩
  rw [hu_dbar z]
  show ((χ z : ℝ) : ℂ) * g z = g z
  rw [contDiffBump_eq_one_on_ball χ hz]
  simp

end DbarLocal
