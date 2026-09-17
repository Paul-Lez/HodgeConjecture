/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity

/-!
# Actual purity along the smooth locus of a closed subvariety

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

/-- Its forward map displays the actual open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem closedEmbeddingSmoothSupportLowestSectionCohomologyIso_hom :
    (closedEmbeddingSmoothSupportLowestSectionCohomologyIso i hi).hom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint X))
          (closedEmbeddingSmoothSupportAmbientOpen i)
          (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))).inv
        (2 * (p : ℤ)) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (closedEmbeddingSmoothSupportAmbientOpen i))
        (closedEmbeddingSmoothRestrictedInjectiveComplex i) (2 * (p : ℤ)) ⊤ ≫
      (TopCat.Sheaf.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint X))
        (closedEmbeddingSmoothSupportAmbientOpen i)
        (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))
        (2 * (p : ℤ))).hom := rfl

end AlgebraicGeometry.ComplexPoint
