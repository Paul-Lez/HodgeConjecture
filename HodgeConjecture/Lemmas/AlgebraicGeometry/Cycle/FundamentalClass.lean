/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# Constructed sheaf cycle classes in arbitrary codimension

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass`.
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

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x hx).hom
      (cycleComponentSupportedInjectiveClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  cycleComponentExtendSmoothCoclass_normalization X x hx _

end AlgebraicGeometry.ComplexPoint
