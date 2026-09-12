/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection

/-!
# The normalized component coclass on the original ambient smooth-support open

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection`.
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
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

/-- Restriction to each actual image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem cycleComponentSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
    (hV : (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj V ≤
      cycleComponentSmoothSupportAmbientOpen X x) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.map (homOfLE hV).op
        (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap X x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
      (cycleComponentSupport X x)
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (cycleComponentSmoothClosedLiftAmbientMap_support X x) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx)) :=
  supportRelativeCohomologySectionOnOpen_restrict
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx) V hV

end Component

end AlgebraicGeometry.ComplexPoint
