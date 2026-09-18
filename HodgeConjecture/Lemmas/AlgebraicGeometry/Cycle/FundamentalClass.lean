/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel

/-!
# Constructed sheaf cycle classes in arbitrary codimension

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.FundamentalClass`.
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
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

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
    (h : Order.coheight (closedEmbeddingGenericPoint (cycleComponentOverι X x)) = p) :
    cycleComponentSheafClass X x hx =
      closedEmbeddingSheafClass (cycleComponentOverι X x) h :=
  rfl

end AlgebraicGeometry.ComplexPoint
