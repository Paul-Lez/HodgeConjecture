/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DerivedRationalDeRhamCompatibility

/-!
# From a supported filtered component class to a public Hodge class

This is the final formal bridge from the supported geometric construction to
the public Hodge-class predicate.  Once the normalized supported de Rham class
of a component is shown to lie in the supported Hodge filtration, its ordinary
rational component class is a Hodge class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

local instance cycleComponentHodgeSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance cycleComponentHodgeGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

/-- The ordinary derived de Rham image of the normalized supported component
class is exactly the public de Rham image of its rational component class. -/
theorem cycleComponentSupportedDeRhamClass_forget_toPublic :
    derivedGlobalDeRhamAddEquivHypercohomology X (2 * (p : ℤ))
        (supportedDeRhamForgetSupport X
          (cycleComponentAnalyticClosedSupport X x) (2 * (p : ℤ))
            (cycleComponentSupportedDeRhamClass X x (d := d) hx)) =
      fieldToDeRhamCohomology ℚ X (2 * (p : ℤ))
        (cycleComponentSheafClass X x (d := d) hx) := by
  rw [cycleComponentSupportedDeRhamClass]
  rw [rationalSupportedToPublicDeRham_forgetSupport]
  rw [cycleComponentSheafClass_eq_forgetSupport]
  rfl

/-- A supported filtered lift of the normalized component class proves the
public `IsHodgeClass` assertion for the constructed rational component class. -/
theorem cycleComponentSheafClass_isHodge_of_supported
    (h : cycleComponentSupportedDeRhamClass X x (d := d) hx ∈
      supportedHodgeFiltration X (cycleComponentAnalyticClosedSupport X x)
        (p : ℤ) (2 * (p : ℤ))) :
    IsHodgeClass ℚ X p (cycleComponentSheafClass X x (d := d) hx) := by
  change fieldToDeRhamCohomology ℚ X (2 * (p : ℤ))
      (cycleComponentSheafClass X x (d := d) hx) ∈
        hodgeFiltration X (p : ℤ) (2 * (p : ℤ))
  rw [← cycleComponentSupportedDeRhamClass_forget_toPublic
    X x (d := d) hx]
  exact derivedGlobalFilteredRange_mem_hodgeFiltration X p (2 * (p : ℤ))
    (cycleComponentSupportedDeRhamClass_forget_mem_globalFilteredRange
      X x (d := d) hx h)

end AlgebraicGeometry.ComplexPoint
