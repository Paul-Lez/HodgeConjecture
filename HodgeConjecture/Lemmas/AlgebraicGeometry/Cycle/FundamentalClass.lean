/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.InjectiveModel

/-!
# The class of an integral cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass`.

The supported class is characterized by its restriction to the smooth locus, and the
ordinary class is its support-forgetting image. Both statements stay in the mapping-cone
model; `cycleComponentSheafSupportedClass_eq_injectiveClass` is the one place that names
the injective model, for the proofs that still compute in it.
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
    cycleComponentSupportedClassEquiv X x hx
      (cycleComponentExtendSmoothCoclass X x hx s) = s :=
  AddEquiv.apply_symm_apply (cycleComponentSupportedClassEquiv X x hx) s

/-- The prescribed smooth-locus section determines the extension uniquely. -/
theorem cycleComponentExtendSmoothCoclass_unique
    (s : CycleComponentSmoothCoclassSections X x p)
    (a : RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)))
    (ha : cycleComponentSupportedClassEquiv X x hx a = s) :
    a = cycleComponentExtendSmoothCoclass X x hx s :=
  (cycleComponentSupportedClassEquiv X x hx).injective
    (ha.trans (cycleComponentExtendSmoothCoclass_normalization X x hx s).symm)

/-- The supported class restricts to exactly the normalized smooth-locus coclass. -/
@[simp]
theorem cycleComponentSheafSupportedClass_normalization :
    cycleComponentSupportedClassEquiv X x hx
      (cycleComponentSheafSupportedClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  cycleComponentExtendSmoothCoclass_normalization X x hx _

/-- The supported class is determined by that restriction. -/
theorem cycleComponentSheafSupportedClass_unique
    (a : RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)))
    (ha : cycleComponentSupportedClassEquiv X x hx a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSheafSupportedClass X x hx :=
  cycleComponentExtendSmoothCoclass_unique X x hx _ a ha

/-- The supported class, written in the injective model. This is the only statement here
that names a resolution; it exists for the proofs that compute in one. -/
theorem cycleComponentSheafSupportedClass_eq_injectiveClass :
    cycleComponentSheafSupportedClass X x hx =
      (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
        (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
          (cycleComponentSupportedInjectiveClass X x hx) :=
  rfl

/-- The ordinary class is the support-forgetting image of the supported class. Since
`cycleComponentSheafClass` is defined as that composite, this holds by definition; it is
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
mapping-cone presentation. -/
theorem cycleComponentSheafClass_eq_injectiveModel :
    cycleComponentSheafClass X x hx =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
            (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
          (cycleComponentSupportedInjectiveClass X x hx)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [cycleComponentSheafClass_eq_forgetSupport,
    rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [cycleComponentSheafSupportedClass_eq_injectiveClass, AddEquiv.apply_symm_apply]
  rfl

include X hx in
omit [IsProjective X.hom] in
/-- The dimension bound needed for the Borel–Moore degree, not an extra input. -/
theorem cycleComponentSheafClass_codimension_le : p ≤ dim X.left := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
  rw [hx] at h
  exact_mod_cast h

end AlgebraicGeometry.ComplexPoint
