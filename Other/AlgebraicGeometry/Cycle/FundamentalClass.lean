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
# Constructed sheaf cycle classes in arbitrary codimension

The normalized extension across the singular boundary is unique, and the ordinary class is
the support-forgetting image of the supported class.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
attribute [local instance] cycleComponentSheafClassAnalyticTopology
variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Extension recovers exactly the prescribed smooth-locus section. -/
@[simp]
theorem cycleComponentExtendSmoothCoclass_normalization
    (s : CycleComponentSmoothCoclassSections X x p) :
    (cycleComponentSupportedClassNormalizationIso X x hx).hom
      (cycleComponentExtendSmoothCoclass X x hx s) = s :=
  AddEquiv.apply_symm_apply
    (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv s

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x hx).hom
      (cycleComponentSupportedInjectiveClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  cycleComponentExtendSmoothCoclass_normalization X x hx _

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

/-- The ordinary class is the support-forgetting image of the supported class, by definition. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x hx =
      forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
        (cycleComponentSheafSupportedClass X x hx) :=
  rfl

/-- The supported class in the mapping-cone model of cohomology with support. -/
def coneCycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) ((2 * p : ℕ) : ℤ) :=
  (coneSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed ((2 * p : ℕ) : ℤ)).symm
      (cycleComponentSupportedInjectiveClass X x hx)

/-- The class of the component computed through the mapping-cone model. Its agreement with
`cycleComponentSheafClass` is not yet proved. -/
def coneCycleComponentSheafClass : H^(2 * p)(X; ℚ) :=
  coneForgetSupport X (cycleComponentSupport X x) (2 * p)
    (coneCycleComponentSheafSupportedClass X x hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The mapping-cone class computed directly in the ambient injective model. -/
theorem coneCycleComponentSheafClass_eq_injectiveModel :
    coneCycleComponentSheafClass X x hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * p)).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
            (ambientRationalInjectiveComplex X)).f (2 * p)
          (cycleComponentSupportedInjectiveClass X x hx)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * p)).injective
  rw [AddEquiv.apply_symm_apply]
  change rationalHypercohomologyAddEquivAmbientInjectiveHomology X _
    ((hypercohomologyAddEquivConstantCohomology ℚ X (2 * p)).symm
      ((hypercohomologyAddEquivConstantCohomology ℚ X (2 * p))
        (forgetSupportHypercohomology X _ _ _))) = _
  rw [AddEquiv.symm_apply_apply,
    coneSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [coneCycleComponentSheafSupportedClass, AddEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
end
