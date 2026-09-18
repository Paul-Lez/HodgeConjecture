/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.RelativeCohomologyOpenTransport
/-!
# The normalized component coclass on the original ambient smooth-support open

The component's smooth locus is closed in the complement of its singular
boundary. We construct its exactly normalized smooth-support section there and
transport it through the analytic open embedding. The result is a section
of the ORIGINAL ambient relative-cohomology sheaf on the singular-boundary
complement. No section, purity comparison, or orientation coherence is an input.
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

include hi in
/-- The proved dimension of the smooth locus, bundled over `Spec ℂ`. -/
theorem closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (dim X.left - p) (closedEmbeddingSmoothLocusOver i).hom := by
  change SmoothOfRelativeDimension (dim X.left - p)
    ((i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom)
  rw [show Y.hom = i.left ≫ X.hom from (Over.w i).symm]
  exact closedEmbeddingSmoothLocus_smoothOfRelativeDimension i hi

include hi in
omit [IsProjective X.hom] [IsClosedImmersion i.left] in
/-- The codimension arithmetic is proved from the coheight bound. -/
theorem closedEmbeddingSmoothClosedLift_codimension :
    dim X.left - (dim X.left - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) (closedEmbeddingGenericPoint i)
  rw [hi] at h
  have hpd : p ≤ dim X.left := by exact_mod_cast h
  omega

/-- The normalized global section of `𝓗^{2p}_{Z_reg(ℂ)}` on the complex manifold `(X \ Z_sing)(ℂ)`,
where `𝓗^{2p}_{Z_reg(ℂ)}` is the sheaf associated with `V ↦ H^{2p}(V, V \ Z_reg(ℂ); ℚ)`. It is glued
from the normal-chart coclasses; `2p` is twice the codimension of `Z` in `X`. -/
def closedEmbeddingSmoothClosedLiftCoclassSection :
    -- The support is the image of `Z_reg`; if `Z ⊆ X` is the variety, the ambient space is the
    -- `X \ Z_sing` open, as a complex manifold.
    (𝓗_[Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i))]^(2 * p)
      (TopCat.of (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)); ℚ)).obj.obj
      (op ⊤) :=
  letI := closedEmbeddingSmoothLocusOver_hom_smoothOfRelativeDimension i hi
  have hdeg := closedEmbeddingSmoothClosedLift_codimension i hi
  hdeg ▸ smoothClosedSupportCoclassSection
    (closedEmbeddingSmoothLocusAmbientOpenOver i)
    (closedEmbeddingSmoothLocusOver i)
    (closedEmbeddingSmoothLocusClosedLiftOver i) (dim X.left - p) (dim X.left)

/-- The analytic open-embedding map back to the original ambient space. -/
def closedEmbeddingSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint (closedEmbeddingSmoothLocusAmbientOpenOver i)) ⟶
    TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap
    (openInclusion X (closedEmbeddingSmoothLocusAmbientOpen i)))

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
theorem closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (closedEmbeddingSmoothClosedLiftAmbientMap i) :=
  isOpenEmbedding_map_open X (closedEmbeddingSmoothLocusAmbientOpen i)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- Support membership is transported by the lift-image theorem. -/
theorem closedEmbeddingSmoothClosedLiftAmbientMap_support :
    closedEmbeddingSmoothClosedLiftAmbientMap i ⁻¹' closedEmbeddingSupport i =
      Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)) :=
  (closedEmbeddingSmoothLocusClosedLift_complexPoints_range i).symm

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen :
    (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i).functor.obj ⊤ =
      closedEmbeddingSmoothSupportAmbientOpen i := by
  apply Opens.ext
  change (closedEmbeddingSmoothClosedLiftAmbientMap i) '' Set.univ = _
  rw [Set.image_univ]
  exact closedEmbeddingSmoothLocusAmbientOpen_analytic_image i

/-- The normalized section of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, where `𝓗^{2p}_{Z(ℂ)}` is
the sheaf on `X(ℂ)` associated with `V ↦ H^{2p}(V, V \ Z(ℂ); ℚ)`. It is the previous section,
transported along the open embedding `(X \ Z_sing)(ℂ) ↪ X(ℂ)`. -/
def closedEmbeddingSmoothSupportCoclassSection :
    -- The support is `Z(ℂ)`, the complex points of the subvariety, inside `X(ℂ)`.
    (𝓗_[closedEmbeddingSupport i]^(2 * p)(TopCat.of (ComplexPoint X); ℚ)).obj.obj
      -- The open set of complex points of the complement of the singular boundary, i.e. `X(ℂ) \ Z_sing(ℂ)`.
      (op (closedEmbeddingSmoothSupportAmbientOpen i)) :=
  supportRelativeCohomologySectionOnOpen (closedEmbeddingSmoothClosedLiftAmbientMap i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_isOpenEmbedding i)
    (closedEmbeddingSupport i)
    (Set.range (Point.map (closedEmbeddingSmoothLocusClosedLiftOver i)))
    (closedEmbeddingSmoothClosedLiftAmbientMap_support i)
    (2 * p) (closedEmbeddingSmoothSupportAmbientOpen i)
    (closedEmbeddingSmoothClosedLiftAmbientMap_imageOpen i)
    (closedEmbeddingSmoothClosedLiftCoclassSection i hi)

end Component

end AlgebraicGeometry.ComplexPoint
