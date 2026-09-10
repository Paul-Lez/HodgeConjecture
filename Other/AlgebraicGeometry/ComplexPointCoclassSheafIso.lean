/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexPointCoclassSchemeIso
public import Other.AlgebraicGeometry.SmoothClosedPointCoclassSectionNormalization
public import Other.AlgebraicTopology.SupportRelativeCohomologyOpenTransport

/-! # Exact transport of old point coclass sections through scheme isomorphisms

The old coclass enters the relative-cohomology sheaf through the actual
neighborhood-to-point pair map and the sheafification unit. Literal pair squares
and complex orientation naturality prove its compatibility with open transport.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]

/-- The old exactly normalized point coclass, included in a larger support and
restricted to a literal ambient neighborhood before sheafification. -/
def analyticPointCoclassSupportSection (S : Set (ComplexPoint X))
    (z : ComplexPoint X) (hz : z ∈ S) (V : Opens (ComplexPoint X)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S (2 * d)).obj.obj (op V) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S (2 * d)).app (op V)
    (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
      (analyticPointLocalCoclass X d z))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Its actual restriction is the same old coclass on the smaller neighborhood. -/
theorem analyticPointCoclassSupportSection_restrict (S : Set (ComplexPoint X))
    (z : ComplexPoint X) (hz : z ∈ S) {U V : Opens (ComplexPoint X)} (hUV : U ≤ V) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S (2 * d)).obj.map (homOfLE hUV).op
      (analyticPointCoclassSupportSection X d S z hz V) =
      analyticPointCoclassSupportSection X d S z hz U := by
  have hn := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S (2 * d)).naturality
      (homOfLE hUV).op)
    (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
      (analyticPointLocalCoclass X d z))
  simp only [ConcreteCategory.comp_apply] at hn
  refine hn.symm.trans ?_
  change (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S (2 * d)).app (op U)
    (relativeCohomologyMap ℚ (2 * d)
      (neighborhoodSupportInclusionPairMap (W := (U : Set _)) (V := (V : Set _)) hUV S)
      (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
        (analyticPointLocalCoclass X d z))) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  rfl

section Iso

variable (Y : Over (Spec (.of ℂ)))
  (e : Y ≅ X)
  [SmoothOfRelativeDimension d Y.hom] [IsProjective Y.hom]

/-- The actual analytic scheme-isomorphism map as a topological-category morphism. -/
def complexSchemeIsoTopMap : TopCat.of (ComplexPoint Y) ⟶ TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap e.hom)

omit [IsProjective X.hom] [IsProjective Y.hom] in
theorem complexSchemeIsoTopMap_isOpenEmbedding :
    IsOpenEmbedding (complexSchemeIsoTopMap X Y e) :=
  (Point.isoMapHomeomorph e).isOpenEmbedding

omit [IsProjective X.hom] [IsProjective Y.hom] in
/-- The pair square behind point normalization on an image neighborhood. -/
theorem neighborhoodSupportPairImageIso_inv_to_point
    (S : Set (ComplexPoint X)) (B : Set (ComplexPoint Y))
    (hB : Point.map e.hom ⁻¹' S = B)
    (z : ComplexPoint Y) (hz : z ∈ B) (V : Opens (ComplexPoint Y)) :
    (neighborhoodSupportPairImageIso (complexSchemeIsoTopMap X Y e)
      (complexSchemeIsoTopMap_isOpenEmbedding X Y e).isEmbedding (V : Set _) B S
      (fun y _ => by rw [← hB]; rfl)).inv ≫
        neighborhoodSupportToPointPairMap (V : Set _) B z hz ≫
          complexSchemeIsoPointPairMap X Y e z =
    neighborhoodSupportToPointPairMap
      ((complexSchemeIsoTopMap_isOpenEmbedding X Y e).functor.obj V : Set _)
      S (Point.map e.hom z) (by rw [← hB] at hz; exact hz) := by
  apply (cancel_epi (neighborhoodSupportPairImageIso (complexSchemeIsoTopMap X Y e)
    (complexSchemeIsoTopMap_isOpenEmbedding X Y e).isEmbedding (V : Set _) B S
    (fun y _ => by rw [← hB]; rfl)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact compatibility of the old point coclass with the constructed sheaf
open-isomorphism transport, on every actual neighborhood. -/
theorem analyticPointCoclassSupportSection_schemeIso_transport
    (S : Set (ComplexPoint X)) (B : Set (ComplexPoint Y))
    (hB : Point.map e.hom ⁻¹' S = B)
    (z : ComplexPoint Y) (hz : z ∈ B) (V : Opens (ComplexPoint Y)) :
    (supportRelativeCohomologySheafOpenIso (complexSchemeIsoTopMap X Y e)
      (complexSchemeIsoTopMap_isOpenEmbedding X Y e) S B hB (2 * d)).hom.hom.app (op V)
      (analyticPointCoclassSupportSection Y d B z hz V) =
    analyticPointCoclassSupportSection X d S (Point.map e.hom z)
      (by rw [← hB] at hz; exact hz)
      ((complexSchemeIsoTopMap_isOpenEmbedding X Y e).functor.obj V) := by
  rw [analyticPointCoclassSupportSection, supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]
  apply congrArg ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S (2 * d)).app _)
  rw [← analyticPointLocalCoclass_schemeIso_pullback X Y e d z]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Category.assoc, neighborhoodSupportPairImageIso_inv_to_point X Y e S B hB z hz V]
  rfl

end Iso
end AlgebraicGeometry.ComplexPoint
