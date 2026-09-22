/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
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

open CycleComponent

section Component

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include X hx in
omit [IsProjective X.hom] in
/-- The codimension arithmetic is proved from the coheight bound. -/
theorem cycleComponentSmoothClosedLift_codimension :
    dim X.left - (dim X.left - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
  rw [hx] at h
  have hpd : p ≤ dim X.left := by exact_mod_cast h
  omega

/-- The normalized global section of `𝓗^{2p}_{Z_reg(ℂ)}` on the complex manifold `(X \ Z_sing)(ℂ)`,
where `𝓗^{2p}_{Z_reg(ℂ)}` is the sheaf associated with `V ↦ H^{2p}(V, V \ Z_reg(ℂ); ℚ)`. It is glued
from the normal-chart coclasses; `2p` is twice the codimension of `Z` in `X`. -/
def cycleComponentSmoothClosedLiftCoclassSection :
    (supportRelativeCohomologySheaf
      -- If `Z ⊆ X` is the variety, this is the `X \ Z_sing` open, as a complex manifold.
      (TopCat.of (ComplexPoint (smoothAmbientOpenOver X x)))
      -- The image of `Z_reg`.
      (Set.range (Point.map (smoothClosedLift X x)))
      (2 * p)).obj.obj (op ⊤) :=
  letI := smoothLocusOver_smoothOfRelativeDimension X x hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x hx
  hdeg ▸ smoothClosedSupportCoclassSection
    (smoothAmbientOpenOver X x)
    (smoothLocusOver X x)
    (smoothClosedLift X x) (dim X.left - p) (dim X.left)

/-- The analytic open-embedding map back to the original ambient space. -/
def cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint (smoothAmbientOpenOver X x)) ⟶
    TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap
    (openInclusion X (smoothAmbientOpen X x)))

omit [IsIntegral X.left] [IsProjective X.hom] in
theorem cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (cycleComponentSmoothClosedLiftAmbientMap X x) :=
  isOpenEmbedding_map_open X (smoothAmbientOpen X x)

omit [IsIntegral X.left] [IsProjective X.hom] in
/-- Support membership is transported by the lift-image theorem. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_support :
    cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' x‾(ℂ) =
      Set.range (Point.map (smoothClosedLift X x)) :=
  (range_map_smoothClosedLift X x).symm

omit [IsIntegral X.left] [IsProjective X.hom] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ =
      x‾ˢⁱⁿᵍ(ℂ)ᶜ := by
  apply Opens.ext
  change (cycleComponentSmoothClosedLiftAmbientMap X x) '' Set.univ = _
  rw [Set.image_univ]
  exact range_map_openInclusion X _

/-- The normalized section of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, where `𝓗^{2p}_{Z(ℂ)}` is
the sheaf on `X(ℂ)` associated with `V ↦ H^{2p}(V, V \ Z(ℂ); ℚ)`. It is the previous section,
transported along the open embedding `(X \ Z_sing)(ℂ) ↪ X(ℂ)`. -/
def cycleComponentSmoothSupportCoclassSection :
    (supportRelativeCohomologySheaf
      -- `X(ℂ)` the topological space of complex points of the ambient variety.
      (TopCat.of (ComplexPoint X))
      -- `Z(ℂ)` the topological space of complex points of the subvariety we're considering.
      (x‾(ℂ)) (2 * p)).obj.obj
      -- The open set of complex points of the complement of the singular boundary, i.e. `X(ℂ) \ Z_sing(ℂ)`.
      (op (x‾ˢⁱⁿᵍ(ℂ)ᶜ)) :=
  supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (x‾(ℂ))
    (Set.range (Point.map (smoothClosedLift X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (x‾ˢⁱⁿᵍ(ℂ)ᶜ)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x hx)

end Component

end AlgebraicGeometry.ComplexPoint
