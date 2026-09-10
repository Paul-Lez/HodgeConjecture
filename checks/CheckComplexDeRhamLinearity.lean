import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsAdditivity

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

@[expose] noncomputable section

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

lemma check_complexConstantCohomologyDeRhamEquiv_scalar
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

end

end AlgebraicGeometry.ComplexPoint
