/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SheafClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# Constructed sheaf cycle classes in arbitrary codimension

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SheafClass`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
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

/-- The prescribed smooth-locus section determines the extension uniquely. -/
theorem cycleComponentExtendSmoothCoclass_unique
    (s : CycleComponentSmoothCoclassSections X x p)
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).hom a = s) :
    a = cycleComponentExtendSmoothCoclass X x hx s :=
  (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv.injective
    (ha.trans (cycleComponentExtendSmoothCoclass_normalization X x hx s).symm)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x hx).hom
      (cycleComponentSupportedInjectiveClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  cycleComponentExtendSmoothCoclass_normalization X x hx _

/-- The normalized global extension is unique, by injectivity of the actual
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).hom a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSupportedInjectiveClass X x hx :=
  cycleComponentExtendSmoothCoclass_unique X x hx _ a ha

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary class agrees with the repository's support-forgetting map,
through the constructed, sign-correct support comparison. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x hx =
      forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
        (cycleComponentSheafSupportedClass X x hx) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [cycleComponentSheafClass, cycleComponentSheafSupportedClass,
    AddEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
