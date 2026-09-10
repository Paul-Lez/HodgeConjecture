import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

namespace Jacobians

/-- **Holomorphic functions on a convex open set have a primitive.** If `h` is complex-
differentiable on a convex open `U ⊆ ℂ`, there is `F` with `HasDerivAt F (h z) z` for every
`z ∈ U`. -/
theorem exists_primitive_of_convex {U : Set ℂ} (hU : Convex ℝ U) (hUo : IsOpen U)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (h z) z := by
  obtain ⟨F, hF⟩ := hU.exists_forall_hasDerivWithinAt hh
  exact ⟨F, fun z hz => (hF z hz).hasDerivAt (hUo.mem_nhds hz)⟩

end Jacobians
