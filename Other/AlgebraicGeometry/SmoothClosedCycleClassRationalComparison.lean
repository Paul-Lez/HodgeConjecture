/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedCycleClass
public import Other.AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Smooth closed-cycle classes in the repository's ordinary rational cohomology

The literal source section is transported through the constructed chain-sheaf
pushforward, normalized ambient orientation, and proved support-cone comparison.
Thus the output is the existing `FieldCohomology`, not a supplied target group.

This is the smooth closed-immersion case. No assertion about singular components,
point-coclass comparison, or rational-equivalence descent is made here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

noncomputable local instance smoothClosedRationalClassAnalyticTopology
    (Y : Over (Spec (.of ℂ))) : TopologicalSpace (ComplexPoint Y) :=
  Point.analyticTopology

variable (Z X : Over (Spec (.of ℂ)))
  (i : Z ⟶ X) [IsClosedImmersion i.left]
  (e d : ℕ) [SmoothOfRelativeDimension e Z.hom] [SmoothOfRelativeDimension d X.hom]
  [T2Space (ComplexPoint Z)] [T2Space (ComplexPoint X)]

/-- The actual smooth closed-cycle construction, linear in its rational multiplicity,
with the repository's ordinary rational cohomology as codomain. -/
def smoothClosedRationalCycleClassMap :
    ℚ →ₗ[ℚ] FieldCohomology ℚ X (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  ((complexAmbientSheafBorelMooreToFieldCohomology X d ⊤ (2 * (e : ℤ))).comp
    (smoothClosedWholeSupportBorelMooreClassMap Z X i e d).hom).toRatLinearMap

/-- Multiplicity one is the literal source constant-one section, with both complex
orientations already constructed. -/
def smoothClosedRationalCycleClass :
    FieldCohomology ℚ X (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedRationalCycleClassMap Z X i e d 1

set_option maxRecDepth 2048 in
/-- The ordinary rational class is obtained from the actual Borel–Moore class,
without an independently specified class or comparison. -/
@[simp]
lemma smoothClosedRationalCycleClass_eq_borelMoore :
    smoothClosedRationalCycleClass Z X i e d =
      complexAmbientSheafBorelMooreToFieldCohomology X d ⊤ (2 * (e : ℤ))
        (smoothClosedWholeSupportBorelMooreClass Z X i e d) := rfl

/-- Arbitrary rational multiplicities have their expected scalar action. -/
@[simp]
lemma smoothClosedRationalCycleClassMap_apply (q : ℚ) :
    smoothClosedRationalCycleClassMap Z X i e d q =
      q • smoothClosedRationalCycleClass Z X i e d := by
  simpa [smoothClosedRationalCycleClass] using
    map_smul (smoothClosedRationalCycleClassMap Z X i e d) q (1 : ℚ)

/-- Specialize the proved dimension arithmetic to codimension `p`. -/
def smoothClosedRationalCycleClassMapInCodimension (p : ℕ) (hdim : e + p = d) :
    ℚ →ₗ[ℚ] FieldCohomology ℚ X (2 * (p : ℤ)) := by
  have hdeg : 2 * (d : ℤ) - 2 * (e : ℤ) = 2 * (p : ℤ) := by omega
  exact hdeg ▸ smoothClosedRationalCycleClassMap Z X i e d

/-- The rational ordinary class of a smooth closed codimension-`p` immersion. -/
def smoothClosedRationalCycleClassInCodimension (p : ℕ) (hdim : e + p = d) :
    FieldCohomology ℚ X (2 * (p : ℤ)) :=
  smoothClosedRationalCycleClassMapInCodimension Z X i e d p hdim 1

@[simp]
lemma smoothClosedRationalCycleClassMapInCodimension_apply (p : ℕ) (hdim : e + p = d)
    (q : ℚ) :
    smoothClosedRationalCycleClassMapInCodimension Z X i e d p hdim q =
      q • smoothClosedRationalCycleClassInCodimension Z X i e d p hdim := by
  simpa [smoothClosedRationalCycleClassInCodimension] using
    map_smul (smoothClosedRationalCycleClassMapInCodimension Z X i e d p hdim) q (1 : ℚ)

end AlgebraicGeometry.ComplexPoint
