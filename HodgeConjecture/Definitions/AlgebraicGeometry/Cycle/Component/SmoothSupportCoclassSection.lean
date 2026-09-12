/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothSupport.CoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologyOpenTransport
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

section GeneralOpenTransport

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]
  {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
  (hf : IsOpenEmbedding f) (S : Set M)
  (hS : f ⁻¹' S = Set.range (Point.map i))

end GeneralOpenTransport

section Component

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- The proved dimension of the smooth locus, bundled over `Spec ℂ`. -/
theorem cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (dim X.left - p) (cycleComponentSmoothLocusOver X x).hom :=
  cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx

include X hx in
omit [IsProjective X.hom] in
/-- The codimension arithmetic is proved from the coheight bound. -/
theorem cycleComponentSmoothClosedLift_codimension :
    dim X.left - (dim X.left - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
  rw [hx] at h
  have hpd : p ≤ dim X.left := by exact_mod_cast h
  omega

/-- The normalized section in the auxiliary algebraic ambient open, in the proved
degree 2p. The class is the general normal-chart gluing, not supplied data. -/
def cycleComponentSmoothClosedLiftCoclassSection :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (2 * p)).obj.obj (op ⊤) := by
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x hx
  exact hdeg ▸ smoothClosedSupportCoclassSection
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - p) (dim X.left)

/-- The analytic open-embedding map back to the original ambient space. -/
def cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)) ⟶
    TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap
    (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)))

omit [IsIntegral X.left] [Smooth X.hom] in
theorem cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (cycleComponentSmoothClosedLiftAmbientMap X x) :=
  isOpenEmbedding_map_open X (cycleComponentSmoothLocusAmbientOpen X x)

/-- Support membership is transported by the lift-image theorem. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_support :
    cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' cycleComponentSupport X x =
      Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) :=
  (cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ =
      cycleComponentSmoothSupportAmbientOpen X x := by
  apply Opens.ext
  change (cycleComponentSmoothClosedLiftAmbientMap X x) '' Set.univ = _
  rw [Set.image_univ]
  exact cycleComponentSmoothLocusAmbientOpen_analytic_image X x

/-- The normalized component coclass section, living on the singular-boundary
complement in the ORIGINAL ambient relative-cohomology sheaf. -/
def cycleComponentSmoothSupportCoclassSection :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.obj
      (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x hx)

end Component

end AlgebraicGeometry.ComplexPoint
