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

The component's smooth locus is closed in the complement of its singular boundary. Its exactly
normalized smooth-support section there is transported through the analytic open embedding,
giving a section of the original ambient relative-cohomology sheaf on the singular-boundary
complement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

section Component

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- The dimension of the smooth locus, bundled over `Spec ℂ`. -/
theorem cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (dim X.left - p) (cycleComponentSmoothLocusOver X x).hom :=
  cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx

include X hx in
omit [IsProjective X.hom] in
/-- The codimension arithmetic, from the coheight bound. -/
theorem cycleComponentSmoothClosedLift_codimension :
    dim X.left - (dim X.left - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
  rw [hx] at h
  have hpd : p ≤ dim X.left := by exact_mod_cast h
  omega

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. On the analytic space of the open scheme `X \
Z_sing`, this is the global section of the sheafification of `V ↦ H^{2p}(V, V \ Z_reg(ℂ); ℚ)`
obtained by gluing local normal orientation coclasses. The local class is normalized to pair to
`1` with the orientation class of the complex normal space. -/
def cycleComponentSmoothClosedLiftCoclassSection :
    -- The support is the image of `Z_reg`; if `Z ⊆ X` is the variety, the ambient space is the
    -- `X \ Z_sing` open, as a complex manifold.
    (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * p)
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
      (op ⊤) :=
  letI := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x hx
  hdeg ▸ smoothClosedSupportCoclassSection
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - p) (dim X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. This is the continuous map `(X \ Z_sing)(ℂ) → X(ℂ)` induced by
inclusion of the open subscheme. It identifies its source with the analytic open subset `X(ℂ) \
Z_sing(ℂ)`. -/
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

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This section of `𝓗^{2p}_S` on
`U` is obtained by gluing the local coclasses defined by complex normal coordinates along
`Z_reg(ℂ)`. The local class is normalized to pair to `1` with the orientation class of the
complex normal space. -/
def cycleComponentSmoothSupportCoclassSection :
    -- The support is `Z(ℂ)`, the complex points of the subvariety, inside `X(ℂ)`.
    (𝓗_[cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint X); ℚ)).presheaf.obj
      -- The open set of complex points of the complement of the singular boundary, i.e. `X(ℂ) \ Z_sing(ℂ)`.
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
