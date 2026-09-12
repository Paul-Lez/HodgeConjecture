/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension

/-!
# Unique extension across a cycle component's singular boundary

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

attribute [local instance] cycleComponentSupportExtensionAnalyticTopology

@[simp]
theorem cycleComponentSupportExtensionIso_hom :
    (cycleComponentSupportExtensionIso X x hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := rfl

end AlgebraicGeometry.ComplexPoint
