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
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# FundamentalClass, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.FundamentalClass`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
attribute [local instance] cycleComponentSheafClassAnalyticTopology
variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- The prescribed smooth-locus section determines the extension uniquely. -/
theorem cycleComponentExtendSmoothCoclass_unique
    (s : CycleComponentSmoothCoclassSections X x p)
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).hom a = s) :
    a = cycleComponentExtendSmoothCoclass X x hx s :=
  (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv.injective
    (ha.trans (cycleComponentExtendSmoothCoclass_normalization X x hx s).symm)

/-- The normalized global extension is unique, by injectivity of the
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).hom a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSupportedInjectiveClass X x hx :=
  cycleComponentExtendSmoothCoclass_unique X x hx _ a ha

/-- The ordinary class is the support-forgetting image of the supported class. Since
`cycleComponentSheafClass` is now defined as that composite, this holds by definition; it is
kept as a named rewrite for the proofs that use it. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x hx =
      forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
        (cycleComponentSheafSupportedClass X x hx) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary class computed directly in the ambient injective model, bypassing the
mapping-cone presentation. This was the old definition of `cycleComponentSheafClass`. -/
theorem cycleComponentSheafClass_eq_injectiveModel :
    cycleComponentSheafClass X x hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (Point ℂ X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
            (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
          (cycleComponentSupportedInjectiveClass X x hx)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [cycleComponentSheafClass_eq_forgetSupport,
    rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [cycleComponentSheafSupportedClass, AddEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
end
