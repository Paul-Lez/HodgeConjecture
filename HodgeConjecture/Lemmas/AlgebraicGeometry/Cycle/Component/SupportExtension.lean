/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension

/-!
# Unique extension across the singular boundary of a closed subvariety

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

@[simp]
theorem closedEmbeddingSupportExtensionIso_hom :
    (closedEmbeddingSupportExtensionIso i hi).hom =
      HomologicalComplex.homologyMap (closedEmbeddingSupportSectionRestriction i) (2 * (p : ℤ)) := rfl

end AlgebraicGeometry.ComplexPoint
