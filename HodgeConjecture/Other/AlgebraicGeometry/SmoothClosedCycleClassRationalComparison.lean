/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedCycleClass
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable local instance smoothClosedRationalClassAnalyticTopology
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) : TopologicalSpace (ComplexPoint Y sY) :=
  Point.analyticTopology

variable {Z X : Scheme} (sZ : Z ⟶ Spec (.of ℂ)) (sX : X ⟶ Spec (.of ℂ))
  (i : Z ⟶ X) (hi : i ≫ sX = sZ) [IsClosedImmersion i]
  (e d : ℕ) [SmoothOfRelativeDimension e sZ] [SmoothOfRelativeDimension d sX]
  [T2Space (ComplexPoint Z sZ)] [T2Space (ComplexPoint X sX)]

/-- The actual smooth closed-cycle construction, linear in its rational multiplicity,
with the repository's ordinary rational cohomology as codomain. -/
def smoothClosedRationalCycleClassMap :
    ℚ →ₗ[ℚ] FieldCohomology ℚ sX (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  ((complexAmbientSheafBorelMooreToFieldCohomology sX d ⊤ (2 * (e : ℤ))).comp
    (smoothClosedWholeSupportBorelMooreClassMap sZ sX i hi e d).hom).toRatLinearMap

/-- Multiplicity one is the literal source constant-one section, with both complex
orientations already constructed. -/
def smoothClosedRationalCycleClass :
    FieldCohomology ℚ sX (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedRationalCycleClassMap sZ sX i hi e d 1

set_option maxRecDepth 2048 in
/-- The ordinary rational class is obtained from the actual Borel–Moore class,
without an independently specified class or comparison. -/
@[simp]
lemma smoothClosedRationalCycleClass_eq_borelMoore :
    smoothClosedRationalCycleClass sZ sX i hi e d =
      complexAmbientSheafBorelMooreToFieldCohomology sX d ⊤ (2 * (e : ℤ))
        (smoothClosedWholeSupportBorelMooreClass sZ sX i hi e d) := rfl

/-- Arbitrary rational multiplicities have their expected scalar action. -/
@[simp]
lemma smoothClosedRationalCycleClassMap_apply (q : ℚ) :
    smoothClosedRationalCycleClassMap sZ sX i hi e d q =
      q • smoothClosedRationalCycleClass sZ sX i hi e d := by
  simpa [smoothClosedRationalCycleClass] using
    map_smul (smoothClosedRationalCycleClassMap sZ sX i hi e d) q (1 : ℚ)

/-- Specialize the proved dimension arithmetic to codimension `p`. -/
def smoothClosedRationalCycleClassMapInCodimension (p : ℕ) (hdim : e + p = d) :
    ℚ →ₗ[ℚ] FieldCohomology ℚ sX (2 * (p : ℤ)) := by
  have hdeg : 2 * (d : ℤ) - 2 * (e : ℤ) = 2 * (p : ℤ) := by omega
  exact hdeg ▸ smoothClosedRationalCycleClassMap sZ sX i hi e d

/-- The rational ordinary class of a smooth closed codimension-`p` immersion. -/
def smoothClosedRationalCycleClassInCodimension (p : ℕ) (hdim : e + p = d) :
    FieldCohomology ℚ sX (2 * (p : ℤ)) :=
  smoothClosedRationalCycleClassMapInCodimension sZ sX i hi e d p hdim 1

@[simp]
lemma smoothClosedRationalCycleClassMapInCodimension_apply (p : ℕ) (hdim : e + p = d)
    (q : ℚ) :
    smoothClosedRationalCycleClassMapInCodimension sZ sX i hi e d p hdim q =
      q • smoothClosedRationalCycleClassInCodimension sZ sX i hi e d p hdim := by
  simpa [smoothClosedRationalCycleClassInCodimension] using
    map_smul (smoothClosedRationalCycleClassMapInCodimension sZ sX i hi e d p hdim) q (1 : ℚ)

end AlgebraicGeometry.ComplexPoint
