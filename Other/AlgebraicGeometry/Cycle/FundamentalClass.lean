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
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import Other.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# Normalization and uniqueness of closed-subvariety classes

The smooth-locus normalization determines the supported class uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)}
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
attribute [local instance] closedEmbeddingSheafClassAnalyticTopology
variable {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : dim Y.left + p = dim X.left)

/-- Extension recovers exactly the prescribed smooth-locus section. -/
@[simp]
theorem closedEmbeddingExtendSmoothCoclass_normalization
    (s : ClosedEmbeddingSmoothCoclassSections i p) :
    (closedEmbeddingSupportedClassNormalizationIso i hi).hom
      (closedEmbeddingExtendSmoothCoclass i hi s) = s :=
  AddEquiv.apply_symm_apply
    (closedEmbeddingSupportedClassNormalizationIso i hi).addCommGroupIsoToAddEquiv s

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem closedEmbeddingSupportedInjectiveClass_normalization :
    (closedEmbeddingSupportedClassNormalizationIso i hi).hom
      (closedEmbeddingSupportedInjectiveClass i hi) =
    closedEmbeddingSmoothSupportCoclassSection i hi :=
  closedEmbeddingExtendSmoothCoclass_normalization i hi _

/-- The component class of `x` is the class of the closed embedding of the reduced closure
of `x`. -/
@[simp]
theorem cycleComponentSheafClass_eq_closedEmbeddingSheafClass (x : X.left)
    (hx : Order.coheight x = p)
    (h : dim (CycleComponent.over X x).left + p = dim X.left) :
    cycleComponentSheafClass X x hx =
      closedEmbeddingSheafClass (CycleComponent.ι X x) h :=
  rfl


/-- The prescribed smooth-locus section determines the extension uniquely. -/
theorem closedEmbeddingExtendSmoothCoclass_unique
    (s : ClosedEmbeddingSmoothCoclassSections i p)
    (a : ClosedEmbeddingSupportedCohomology i p)
    (ha : (closedEmbeddingSupportedClassNormalizationIso i hi).hom a = s) :
    a = closedEmbeddingExtendSmoothCoclass i hi s :=
  (closedEmbeddingSupportedClassNormalizationIso i hi).addCommGroupIsoToAddEquiv.injective
    (ha.trans (closedEmbeddingExtendSmoothCoclass_normalization i hi s).symm)

/-- The normalized global extension is unique, by injectivity of the
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem closedEmbeddingSupportedInjectiveClass_unique
    (a : ClosedEmbeddingSupportedCohomology i p)
    (ha : (closedEmbeddingSupportedClassNormalizationIso i hi).hom a =
      closedEmbeddingSmoothSupportCoclassSection i hi) :
    a = closedEmbeddingSupportedInjectiveClass i hi :=
  closedEmbeddingExtendSmoothCoclass_unique i hi _ a ha

/-- The ordinary class is the support-forgetting image of the supported class. Since
`closedEmbeddingSheafClass` is defined as that composite, this holds by definition; it is
kept as a named rewrite for the proofs that use it. -/
theorem closedEmbeddingSheafClass_eq_forgetSupport :
    closedEmbeddingSheafClass i hi =
      forgetSupport X (closedEmbeddingSupport i) (2 * (p : ℤ))
        (closedEmbeddingSheafSupportedClass i hi) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary class computed directly in the ambient injective model, bypassing the
mapping-cone presentation. This was the old definition of `closedEmbeddingSheafClass`. -/
theorem closedEmbeddingSheafClass_eq_injectiveModel :
    closedEmbeddingSheafClass i hi =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X)) (closedEmbeddingSupport i).compl ⊤
            (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
          (closedEmbeddingSupportedInjectiveClass i hi)) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [closedEmbeddingSheafClass_eq_forgetSupport,
    rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (closedEmbeddingSupport i) (closedEmbeddingSupport i).isClosed]
  simp only [closedEmbeddingSheafSupportedClass, AddEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
end
