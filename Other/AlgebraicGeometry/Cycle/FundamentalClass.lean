/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicGeometry.Cohomology.SupportConeInjectiveModelLemmas
public import Other.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# FundamentalClass, the part the statement does not need

Separated out of
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- The normalized global extension is unique, by injectivity of the
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSupportedInjectiveClass X x hx := by
  apply (cycleComponentSupportedClassNormalizationIso X x hx).injective
  change (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom
      (cycleComponentSupportedInjectiveClass X x hx)
  rw [ha]
  exact (cycleComponentSupportedClassNormalizationIso X x hx).apply_symm_apply
    (cycleComponentSmoothSupportCoclassSection X x hx) |>.symm

/-- The ordinary class is the support-forgetting image of the supported class. Since
`cycleComponentSheafClass` is now defined as that composite, this holds by definition; it is
kept as a named rewrite for the proofs that use it. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x hx =
      forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
        (cycleComponentSupportedInjectiveClass X x hx) :=
  rfl

end AlgebraicGeometry.ComplexPoint
end
