module

public import Mathlib.LinearAlgebra.Quotient.Basic

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Lifting a sum of maps to the quotient is the sum of the lifts. -/
theorem liftQ_add (p : Submodule R M) {f g : M →ₛₗ[τ₁₂] M₂}
    (hf : p ≤ LinearMap.ker f) (hg : p ≤ LinearMap.ker g)
    {h : p ≤ LinearMap.ker (f + g)} :
    p.liftQ (f + g) h = p.liftQ f hf + p.liftQ g hg :=
  p.linearMap_qext (by ext; simp)

/-- Lifting a scalar multiple of a map to the quotient is the scalar multiple of the lift. -/
theorem liftQ_smul {S : Type*} [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
    (p : Submodule R M) {f : M →ₛₗ[τ₁₂] M₂} (hf : p ≤ LinearMap.ker f) (c : S)
    {h : p ≤ LinearMap.ker (c • f)} :
    p.liftQ (c • f) h = c • p.liftQ f hf :=
  p.linearMap_qext (by ext; simp)

end Submodule
