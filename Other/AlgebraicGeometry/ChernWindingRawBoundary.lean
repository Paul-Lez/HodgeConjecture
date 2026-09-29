/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingSupportedBoundary

/-!
# Raw relative boundaries of winding classes

The prescribed raw-to-relative comparison sends the positive raw winding boundary
to the existing positive winding class, retaining the literal intersection-pair iso.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

namespace ChernWinding
variable (X : TopCat.{0}) [T2Space X] [∀ W : Opens X, ParacompactSpace W]
  (S : Set X) (hS : IsClosed S) (V : Opens X)
/-- The actual raw relative boundary is the existing winding relative class. -/
lemma openRawRelative_winding_boundary
    (g : C(puncturedSpace (V : Set X) S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (h : HasRationalWindingPeriod (V : Set X) S g hg) :
    let U : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩
    let q := openIntersectionPairIsoSupportComplement X S hS V
    let z := openRawRationalWindingClass X (V ⊓ U) (g.comp (topMap q.hom.left))
      (fun y => hg (q.hom.left y))
    relativeCohomologyMap ℚ 2 q.inv
      (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X (Opens.infLELeft V U) 2
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X (Opens.infLELeft V U))
              ComplexShape.embeddingUpNat)) 1 z)) =
    windingRelativeClass (V : Set X) S h := by
  dsimp only
  let U : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩
  let q := openIntersectionPairIsoSupportComplement X S hS V
  let z := openRawRationalWindingClass X (V ⊓ U) (g.comp (topMap q.hom.left))
    (fun y => hg (q.hom.left y))
  exact (congrArg (relativeCohomologyMap ℚ 2 q.inv)
    (supportedSingularSectionCohomologyEquivRelative_boundary X U V 2 z)).symm.trans
      (supportedSingularSectionCohomologyEquivSupportComplement_winding_boundary X S hS V g hg h)
end ChernWinding
