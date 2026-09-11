/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison

/-!
# The sheaf Borel--Moore fundamental class of a cycle component

The constructed sheaf cycle class of a component transports to ambient chain-sheaf
Borel--Moore homology along the Alexander--Poincaré comparison, giving a normalized
fundamental class there.

The statement of the Hodge conjecture reaches the cycle class through
`cycleComponentSheafSupportedClass`, not through its Borel--Moore image, so this route and
the `ComplexSheafBorelMoore` development under it sit outside the statement layer.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] cycleComponentSheafClassAnalyticTopology

variable (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

/-- The normalized fundamental class in ACTUAL ambient chain-sheaf
Borel–Moore homology, obtained through the constructed orientation shift.
It is not an element of a supplied replacement homology group. -/
def cycleComponentSheafBorelMooreFundamentalClass :
    ComplexAmbientSheafBorelMooreHomology X d (cycleComponentAnalyticClosedSupport X x)
      (2 * ((d - p : ℕ) : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
    (cycleComponentAnalyticClosedSupport X x) p
    (cycleComponentSheafClass_codimension_le X x (d := d) hx)).symm
      (cycleComponentSheafSupportedClass X x (d := d) hx)

/-- The constructed Alexander–Poincaré map sends the fundamental class to
the exact normalized supported class, with no comparison hypothesis. -/
@[simp]
theorem cycleComponentSheafBorelMooreFundamentalClass_duality :
    complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafSupportedClass X x (d := d) hx :=
  AddEquiv.apply_symm_apply _ _

/-- The ordinary class is also exactly the actual ambient Borel–Moore
cycle-class route. The ordinary-target comparison is proved, not an input. -/
theorem cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology :
    complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafClass X x (d := d) hx := by
  change forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx)) = _
  rw [cycleComponentSheafBorelMooreFundamentalClass_duality,
    cycleComponentSheafClass_eq_forgetSupport]

end AlgebraicGeometry.ComplexPoint
