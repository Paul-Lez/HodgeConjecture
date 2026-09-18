/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.SourceOpen
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension

/-!
# The smooth-locus closed lift of a closed subvariety

The ambient open is the complement of the first canonical singular-boundary support, and
the smooth locus embeds closed in it. Its constant relative dimension is `d-p`, by smooth
equidimensionality together with the coheight formula for a closed point of the integral
component.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]

/-- The precise algebraic open complementary to the canonical singular boundary. -/
def closedEmbeddingSmoothLocusAmbientOpen : X.left.Opens :=
  (closedEmbeddingSingularAmbientClosedFiltration i 0).compl

/-- The ambient boundary complement with its induced structure map to `Spec ℂ`. -/
abbrev closedEmbeddingSmoothLocusAmbientOpenOver : Over (Spec ↧ℂ) :=
  ComplexPoint.openScheme X (closedEmbeddingSmoothLocusAmbientOpen i)

instance closedEmbeddingSmoothLocusAmbientOpenOver_locallyOfFiniteType :
    LocallyOfFiniteType (closedEmbeddingSmoothLocusAmbientOpenOver i).hom := by
  change LocallyOfFiniteType ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom)
  infer_instance

instance closedEmbeddingSmoothLocusAmbientOpenInclusion_isImmersion :
    IsImmersion
      (ComplexPoint.openInclusion X (closedEmbeddingSmoothLocusAmbientOpen i)).left := by
  change IsImmersion (closedEmbeddingSmoothLocusAmbientOpen i).ι
  infer_instance

/-- The actual smooth locus, closed in the complement of its singular boundary. -/
def closedEmbeddingSmoothLocusClosedLift :
    (i.left ≫ X.hom).smoothLocus.toScheme ⟶
      (closedEmbeddingSmoothLocusAmbientOpen i).toScheme :=
  closedImmersionSourceOpenLift (i.left) (i.left ≫ X.hom).smoothLocus

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance closedEmbeddingSmoothLocusClosedLift_isClosedImmersion :
    IsClosedImmersion (closedEmbeddingSmoothLocusClosedLift i) := by
  dsimp [closedEmbeddingSmoothLocusClosedLift]
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
@[reassoc (attr := simp)]
theorem closedEmbeddingSmoothLocusClosedLift_ι :
    closedEmbeddingSmoothLocusClosedLift i ≫ (closedEmbeddingSmoothLocusAmbientOpen i).ι =
      (i.left ≫ X.hom).smoothLocus.ι ≫ i.left :=
  closedImmersionSourceOpenLift_ι _ _

/-- The smooth-locus closed lift bundled over `Spec ℂ`. -/
def closedEmbeddingSmoothLocusClosedLiftOver :
    ComplexPoint.closedEmbeddingSmoothLocusOver i ⟶
      closedEmbeddingSmoothLocusAmbientOpenOver i :=
  Over.homMk (closedEmbeddingSmoothLocusClosedLift i) (by
    change closedEmbeddingSmoothLocusClosedLift i ≫
      ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom) =
        (i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom
    rw [← Category.assoc, closedEmbeddingSmoothLocusClosedLift_ι, Category.assoc]
    exact congrArg (fun f ↦ (i.left ≫ X.hom).smoothLocus.ι ≫ f) (Over.w i))

instance closedEmbeddingSmoothLocusClosedLiftOver_isClosedImmersion :
    IsClosedImmersion (closedEmbeddingSmoothLocusClosedLiftOver i).left := by
  change IsClosedImmersion (closedEmbeddingSmoothLocusClosedLift i)
  infer_instance

variable {d p : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- The ambient open retains the original smooth relative dimension. These stay generic in
`d`: they are instances, found by resolution, and narrowing them to `dim X.left` would make
them fire less often. -/
instance closedEmbeddingSmoothLocusAmbientOpen_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (closedEmbeddingSmoothLocusAmbientOpen i).ι X.hom

instance closedEmbeddingSmoothLocusAmbientOpenOver_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d (closedEmbeddingSmoothLocusAmbientOpenOver i).hom := by
  change SmoothOfRelativeDimension d
    ((closedEmbeddingSmoothLocusAmbientOpen i).ι ≫ X.hom)
  infer_instance

namespace ComplexPoint

/-- The full cycle support as an actual closed analytic subset. -/
def closedEmbeddingAnalyticClosedSupport : Closeds (ComplexPoint X) :=
  ⟨closedEmbeddingSupport i, isClosed_closedEmbeddingSupport i⟩

end ComplexPoint
end AlgebraicGeometry
