/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
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

open CycleComponent

section Component

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Restriction to each image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem cycleComponentSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (smoothAmbientOpenOver X x)))
    (hV : (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj V ≤
      x‾ˢⁱⁿᵍ(ℂ)ᶜ) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (x‾(ℂ)) (2 * p)).obj.map (homOfLE hV).op
        (cycleComponentSmoothSupportCoclassSection X x hx) =
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap X x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
      (x‾(ℂ))
      (Set.range (Point.map (smoothClosedLift X x)))
      (cycleComponentSmoothClosedLiftAmbientMap_support X x) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (smoothAmbientOpenOver X x)))
        (Set.range (Point.map (smoothClosedLift X x)))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (cycleComponentSmoothClosedLiftCoclassSection X x hx)) :=
  supportRelativeCohomologySectionOnOpen_restrict
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (x‾(ℂ))
    (Set.range (Point.map (smoothClosedLift X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (x‾ˢⁱⁿᵍ(ℂ)ᶜ)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x hx) V hV

end Component

end AlgebraicGeometry.ComplexPoint
