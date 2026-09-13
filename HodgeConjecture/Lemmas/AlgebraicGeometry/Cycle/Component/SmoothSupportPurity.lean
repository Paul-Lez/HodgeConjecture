/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity

/-!
# Purity along the smooth locus of an integral cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Its forward map displays the open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem cycleComponentSmoothSupportLowestSectionCohomologyIso_hom :
    (cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx).hom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint X))
          (cycleComponentSmoothSupportAmbientOpen X x)
          (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).inv
        (2 * (p : ℤ)) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))
        (cycleComponentSmoothRestrictedInjectiveComplex X x) (2 * (p : ℤ)) ⊤ ≫
      (TopCat.Sheaf.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ))).hom := rfl

end AlgebraicGeometry.ComplexPoint
