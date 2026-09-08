/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ComplexPointCoclassSchemeIso
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedPointCoclassSectionNormalization
public import HodgeConjecture.Other.AlgebraicTopology.SupportRelativeCohomologyOpenTransport

/-! # Exact transport of old point coclass sections through scheme isomorphisms

The old coclass enters the relative-cohomology sheaf through the actual
neighborhood-to-point pair map and the sheafification unit. Literal pair squares
and complex orientation naturality prove its compatibility with open transport.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d s] [IsProjective s]

/-- The old exactly normalized point coclass, included in a larger support and
restricted to a literal ambient neighborhood before sheafification. -/
def analyticPointCoclassSupportSection (S : Set (ComplexPoint X s))
    (z : ComplexPoint X s) (hz : z ∈ S) (V : Opens (ComplexPoint X s)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).obj.obj (op V) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).app (op V)
    (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
      (analyticPointLocalCoclass s d z))

/-- Its actual restriction is the same old coclass on the smaller neighborhood. -/
theorem analyticPointCoclassSupportSection_restrict (S : Set (ComplexPoint X s))
    (z : ComplexPoint X s) (hz : z ∈ S) {U V : Opens (ComplexPoint X s)} (hUV : U ≤ V) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).obj.map (homOfLE hUV).op
      (analyticPointCoclassSupportSection s d S z hz V) =
      analyticPointCoclassSupportSection s d S z hz U := by
  have hn := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).naturality
      (homOfLE hUV).op)
    (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
      (analyticPointLocalCoclass s d z))
  simp only [ConcreteCategory.comp_apply] at hn
  refine hn.symm.trans ?_
  change (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).app (op U)
    (relativeCohomologyMap ℚ (2 * d)
      (neighborhoodSupportInclusionPairMap (W := (U : Set _)) (V := (V : Set _)) hUV S)
      (relativeCohomologyMap ℚ (2 * d) (neighborhoodSupportToPointPairMap (V : Set _) S z hz)
        (analyticPointLocalCoclass s d z))) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_toPoint]
  rfl

section Iso

variable {Y : Scheme} (sY : Y ⟶ Spec (.of ℂ))
  (e : Y ≅ X) (he : e.hom ≫ s = sY)
  [SmoothOfRelativeDimension d sY] [IsProjective sY]

/-- The actual analytic scheme-isomorphism map as a topological-category morphism. -/
def complexSchemeIsoTopMap : TopCat.of (ComplexPoint Y sY) ⟶ TopCat.of (ComplexPoint X s) :=
  TopCat.ofHom (Point.continuousMap e.hom he)

omit [IsProjective s] [IsProjective sY] in
theorem complexSchemeIsoTopMap_isOpenEmbedding :
    IsOpenEmbedding (complexSchemeIsoTopMap s sY e he) :=
  (Point.isoMapHomeomorph e he).isOpenEmbedding

omit [IsProjective s] [IsProjective sY] in
/-- The pair square behind point normalization on an image neighborhood. -/
theorem neighborhoodSupportPairImageIso_inv_to_point
    (S : Set (ComplexPoint X s)) (B : Set (ComplexPoint Y sY))
    (hB : Point.map e.hom he ⁻¹' S = B)
    (z : ComplexPoint Y sY) (hz : z ∈ B) (V : Opens (ComplexPoint Y sY)) :
    (neighborhoodSupportPairImageIso (complexSchemeIsoTopMap s sY e he)
      (complexSchemeIsoTopMap_isOpenEmbedding s sY e he).isEmbedding (V : Set _) B S
      (fun y _ => by rw [← hB]; rfl)).inv ≫
        neighborhoodSupportToPointPairMap (V : Set _) B z hz ≫
          complexSchemeIsoPointPairMap s sY e he z =
    neighborhoodSupportToPointPairMap
      ((complexSchemeIsoTopMap_isOpenEmbedding s sY e he).functor.obj V : Set _)
      S (Point.map e.hom he z) (by rw [← hB] at hz; exact hz) := by
  apply (cancel_epi (neighborhoodSupportPairImageIso (complexSchemeIsoTopMap s sY e he)
    (complexSchemeIsoTopMap_isOpenEmbedding s sY e he).isEmbedding (V : Set _) B S
    (fun y _ => by rw [← hB]; rfl)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

/-- Exact compatibility of the old point coclass with the constructed sheaf
open-isomorphism transport, on every actual neighborhood. -/
theorem analyticPointCoclassSupportSection_schemeIso_transport
    (S : Set (ComplexPoint X s)) (B : Set (ComplexPoint Y sY))
    (hB : Point.map e.hom he ⁻¹' S = B)
    (z : ComplexPoint Y sY) (hz : z ∈ B) (V : Opens (ComplexPoint Y sY)) :
    (supportRelativeCohomologySheafOpenIso (complexSchemeIsoTopMap s sY e he)
      (complexSchemeIsoTopMap_isOpenEmbedding s sY e he) S B hB (2 * d)).hom.hom.app (op V)
      (analyticPointCoclassSupportSection sY d B z hz V) =
    analyticPointCoclassSupportSection s d S (Point.map e.hom he z)
      (by rw [← hB] at hz; exact hz)
      ((complexSchemeIsoTopMap_isOpenEmbedding s sY e he).functor.obj V) := by
  rw [analyticPointCoclassSupportSection, supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]
  apply congrArg ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S (2 * d)).app _)
  rw [← analyticPointLocalCoclass_schemeIso_pullback s sY e he d z]
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Category.assoc, neighborhoodSupportPairImageIso_inv_to_point s sY e he S B hB z hz V]
  rfl

end Iso
end AlgebraicGeometry.ComplexPoint
