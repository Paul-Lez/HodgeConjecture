/-
  Dolbeault ladder — the underlying REAL-`C^∞` manifold structure of a complex manifold.

  Real Dolbeault (real-`C^∞` functions, (0,1)-forms, the ∂̄ operator) needs `X` viewed as a REAL
  manifold, not the ℂ-manifold the rest of the repo uses: over the ℂ-model `𝓘(ℂ)`, `ContMDiff … ⊤`
  means *holomorphic* (`ContDiff ℂ 1 ⟹` holo), which is the wrong (often-zero) class for ∂̄. This
  module supplies the real structure `IsManifold 𝓘(ℝ,ℂ) ⊤ X` from the complex one: the holomorphic
  chart transitions (`contDiffGroupoid ω 𝓘(ℂ)`) are real-smooth (`contDiffGroupoid ⊤ 𝓘(ℝ,ℂ)`), via
  `ContDiffOn ℂ ω ⟹ ContDiffOn ℝ ⊤` (`of_le` + `restrict_scalars`).

  The ℂ-as-ℝ-module instance diamond in `restrict_scalars` (cf. `reference_module_real_diamond`) is a
  defeq-transparency issue, handled exactly as Mathlib's own `Analysis/Complex/RealDeriv.lean` does:
  `set_option backward.isDefEq.respectTransparency false`.
-/
import KirovDolbeault.Genus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff

namespace Jacobians.Dolbeault

set_option backward.isDefEq.respectTransparency false in
/-- **A complex manifold is a real-`C^∞` manifold.** Holomorphic chart transitions are real-smooth,
so the ℂ-atlas is a `𝓘(ℝ,ℂ)`-smooth atlas. This is the foundational layer for real Dolbeault. -/
instance realManifold_of_complex {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : IsManifold (𝓘(ℝ, ℂ)) (⊤ : ℕ∞) X := by
  have hle : contDiffGroupoid ω 𝓘(ℂ) ≤ contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ)) := by
    intro e he
    have he' : e ∈ contDiffGroupoid ω 𝓘(ℂ) := he
    show e ∈ contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ))
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he' ⊢
    simp only [contDiffPregroupoid] at he' ⊢
    obtain ⟨h1, h2⟩ := he'
    refine ⟨?_, ?_⟩
    · have key : ContDiffOn ℝ (⊤ : ℕ∞) _ _ := (h1.of_le le_top).restrict_scalars ℝ
      simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id] using key
    · have key : ContDiffOn ℝ (⊤ : ℕ∞) _ _ := (h2.of_le le_top).restrict_scalars ℝ
      simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id] using key
  haveI : HasGroupoid X (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ))) :=
    hasGroupoid_of_le ‹IsManifold 𝓘(ℂ) ω X›.toHasGroupoid hle
  exact IsManifold.mk' _ _ _

end Jacobians.Dolbeault
