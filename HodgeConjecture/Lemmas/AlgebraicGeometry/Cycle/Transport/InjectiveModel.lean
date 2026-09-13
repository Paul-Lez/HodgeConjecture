/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.InjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeForget

/-!
# The injective model of supported cohomology, and its comparisons

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.InjectiveModel`.

These characterize the injective-model class by its restriction to the smooth locus. The
statement-facing versions, in the mapping-cone model, are in
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.FundamentalClass`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] cycleComponentSheafClassAnalyticTopology

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- The class in the injective model extending the exact complex-normal coclass.

This lives here rather than in `Definitions`: after the extension step is stated in the
mapping-cone model, nothing the conjecture's statement inspects passes through it. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x hx).hom
      (cycleComponentSupportedInjectiveClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  AddEquiv.apply_symm_apply
    (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv _

/-- The normalized global extension is unique, by injectivity of the
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).hom a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSupportedInjectiveClass X x hx :=
  (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv.injective
    (ha.trans (cycleComponentSupportedInjectiveClass_normalization X x hx).symm)

end AlgebraicGeometry.ComplexPoint
