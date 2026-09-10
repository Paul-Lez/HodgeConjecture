/-
  Dolbeault ladder -- common refinements of finite covers.

  This is the complete part of the cover-independence scaffold: given two finite covers
  `𝔘` and `𝔙`, form their pairwise-intersection refinement and record the two projection
  refinement maps.  The analytic Leray assertions for strict refinements stay in
  `CechRefinementLeray`.
-/
import KirovDolbeault.Dolbeault.CechRefinementLeray

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

/-- The pairwise-intersection common refinement of two finite covers. -/
noncomputable def commonRefinement (𝔘 𝔙 : FiniteCover X) : FiniteCover X where
  ι := 𝔘.ι × 𝔙.ι
  fintype := inferInstance
  U p := 𝔘.U p.1 ⊓ 𝔙.U p.2
  covers := by
    rw [← iSup_inf_iSup, 𝔘.covers, 𝔙.covers, inf_idem]

/-- The projection refinement from `commonRefinement 𝔘 𝔙` to `𝔘`. -/
theorem commonRefinement_proj1 (𝔘 𝔙 : FiniteCover X) :
    IsRefinement (commonRefinement 𝔘 𝔙) 𝔘 Prod.fst := by
  intro p
  exact inf_le_left

/-- The projection refinement from `commonRefinement 𝔘 𝔙` to `𝔙`. -/
theorem commonRefinement_proj2 (𝔘 𝔙 : FiniteCover X) :
    IsRefinement (commonRefinement 𝔘 𝔙) 𝔙 Prod.snd := by
  intro p
  exact inf_le_right

end FiniteCover

end Jacobians.Dolbeault
