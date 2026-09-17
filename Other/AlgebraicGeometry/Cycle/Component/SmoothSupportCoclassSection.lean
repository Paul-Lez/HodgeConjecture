/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import Other.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

/-!
# The normalized component coclass on the original ambient smooth-support open

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

section Component

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

/-- Restriction to each image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem closedEmbeddingSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)))
    (hV : (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i).functor.obj V ≤
      closedEmbeddingSmoothSupportAmbientOpen i) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (closedEmbeddingSupport i) (2 * p)).obj.map (homOfLE hV).op
        (closedEmbeddingSmoothSupportCoclassSection i hi) =
    (supportRelativeCohomologySheafOpenIso (closedEmbeddingSmoothClosedLiftAmbientMap i)
      (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i)
      (closedEmbeddingSupport i)
      (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
      (closedEmbeddingSmoothClosedLiftAmbientMap_support i) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)))
        (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (closedEmbeddingSmoothClosedLiftCoclassSection i hi)) :=
  supportRelativeCohomologySectionOnOpen_restrict
    (closedEmbeddingSmoothClosedLiftAmbientMap i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i)
    (closedEmbeddingSupport i)
    (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
    (closedEmbeddingSmoothClosedLiftAmbientMap_support i)
    (2 * p) (closedEmbeddingSmoothSupportAmbientOpen i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i)
    (closedEmbeddingSmoothClosedLiftCoclassSection i hi) V hV

end Component

end AlgebraicGeometry.ComplexPoint
