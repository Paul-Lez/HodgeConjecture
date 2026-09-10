/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Scalar naturality of the complex constant-to-de Rham comparison

The analytic Poincare comparison was initially exposed as an unbundled equivalence.  This
file records the chain-level scalar naturality needed when transporting eigenclasses through
that equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The complex constant-to-de Rham equivalence intertwines its two chain-level scalar
endomorphisms. -/
theorem complexConstantCohomologyDeRhamEquiv_scalar
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X))
    (n : ℤ) (c : ℂ) (α : ComplexConstantCohomology X n) :
    complexConstantCohomologyDeRhamEquiv X h n
        (hypercohomologyMap X (complexScalarComplexInt X c) n α) =
      c • complexConstantCohomologyDeRhamEquiv X h n α := by
  rw [complexConstantCohomologyDeRhamEquiv_apply,
    complexConstantCohomologyDeRhamEquiv_apply]
  rw [deRham_complex_smul_eq]
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  exact congrArg (fun f ↦ hypercohomologyMap X f n α)
    (constantsToHolomorphicDeRhamComplexInt_scalar X c).symm

/-- Scalar naturality in the inverse direction. -/
theorem complexConstantCohomologyDeRhamEquiv_symm_smul
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X))
    (n : ℤ) (c : ℂ) (α : DeRhamHypercohomology X n) :
    (complexConstantCohomologyDeRhamEquiv X h n).symm (c • α) =
      hypercohomologyMap X (complexScalarComplexInt X c) n
        ((complexConstantCohomologyDeRhamEquiv X h n).symm α) := by
  apply (complexConstantCohomologyDeRhamEquiv X h n).injective
  rw [Equiv.apply_symm_apply]
  rw [complexConstantCohomologyDeRhamEquiv_scalar]
  rw [Equiv.apply_symm_apply]

end AlgebraicGeometry.ComplexPoint
