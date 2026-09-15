/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexPoint.CoclassSchemeIso
public import Other.AlgebraicGeometry.Cycle.SmoothPair.PointCoclassSection
public import Other.AlgebraicTopology.Support.RelativeCohomologyOpenTransport
/-! # Exact transport of old point coclass sections through scheme isomorphisms

The old coclass enters the relative-cohomology sheaf through the actual
neighborhood-to-point pair map and the sheafification unit. Literal pair squares
and complex orientation naturality prove its compatibility with open transport.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]

/-- The old exactly normalized point coclass, included in a larger support and
restricted to a literal ambient neighborhood before sheafification. -/
def analyticPointCoclassSupportSection (S : Set (ComplexPoint X))
    (z : ComplexPoint X) (hz : z ∈ S) (V : Opens (ComplexPoint X)) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S (2 * d)).obj.obj (op V) :=
  supportRelativeCohomologyPointSection V hz
    (analyticPointLocalCoclass X d z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Its actual restriction is the same old coclass on the smaller neighborhood. -/
theorem analyticPointCoclassSupportSection_restrict (S : Set (ComplexPoint X))
    (z : ComplexPoint X) (hz : z ∈ S) {U V : Opens (ComplexPoint X)} (hUV : U ≤ V) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S (2 * d)).obj.map (homOfLE hUV).op
      (analyticPointCoclassSupportSection X d S z hz V) =
      analyticPointCoclassSupportSection X d S z hz U :=
  supportRelativeCohomologyPointSection_restrict
    (TopCat.of (ComplexPoint X)) S (2 * d) hz (analyticPointLocalCoclass X d z) hUV

section Iso

variable (Y : Over (Spec ↧ℂ))
  (e : Y ≅ X)
  [SmoothOfRelativeDimension d Y.hom] [IsProjective Y.hom]

/-- A scheme isomorphism induces an open embedding on complex points. -/
theorem complexSchemeIsoMap_isOpenEmbedding
    {X Y : Over (Spec ↧ℂ)} (e : Y ≅ X) :
    IsOpenEmbedding (TopCat.ofHom (Point.continuousMap e.hom)) :=
  (Point.isoMapHomeomorph e).isOpenEmbedding

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact compatibility of the old point coclass with the constructed sheaf
open-isomorphism transport, on every actual neighborhood. -/
theorem analyticPointCoclassSupportSection_schemeIso_transport
    (S : Set (ComplexPoint X)) (B : Set (ComplexPoint Y))
    (hB : Point.map e.hom ⁻¹' S = B)
    (z : ComplexPoint Y) (hz : z ∈ B) (V : Opens (ComplexPoint Y)) :
    (supportRelativeCohomologySheafOpenIso
      (complexSchemeIsoMap_isOpenEmbedding e) hB (2 * d)).hom.hom.app (op V)
      (analyticPointCoclassSupportSection Y d B z hz V) =
    analyticPointCoclassSupportSection X d S (Point.map e.hom z)
      (by rw [← hB] at hz; exact hz)
      ((complexSchemeIsoMap_isOpenEmbedding e).functor.obj V) := by
  rw [analyticPointCoclassSupportSection,
    ← analyticPointLocalCoclass_schemeIso_pullback X Y e d z,
    complexSchemeIsoPointPairMap]
  exact supportRelativeCohomologyPointSection_open
    (complexSchemeIsoMap_isOpenEmbedding e) hB (2 * d) V hz
      (analyticPointLocalCoclass X d (Point.map e.hom z))

end Iso
end AlgebraicGeometry.ComplexPoint
