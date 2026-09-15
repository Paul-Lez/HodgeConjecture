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

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] cycleComponentSheafClassAnalyticTopology

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso x hx).hom
      (cycleComponentSupportedInjectiveClass hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  (cycleComponentSupportedClassNormalizationIso x hx).inv_hom_id_apply _

end AlgebraicGeometry.ComplexPoint
