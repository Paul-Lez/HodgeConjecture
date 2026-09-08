/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ComplexSheafBorelMoore
public import HodgeConjecture.Other.AlgebraicGeometry.DerivedSupportRationalComparison

/-!
# The constructed ambient Borel–Moore map into the existing rational cohomology API

The comparison is the actual complex-orientation duality followed by the constructed
injective-resolution/support-cone equivalence. Forgetting support then lands in the
repository's `FieldCohomology` itself, with no supplied duality or comparison argument.

This module transports Borel–Moore classes; it does not produce fundamental classes
for general algebraic components. Agreement with the separate actual derived-global
support-forgetting route and the existing normalized point coclass are further
comparison theorems, not assumptions or claims of this adapter.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

local instance complexBorelMooreRationalComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

/-- The actual derived-support groups agree with the existing rational support API,
through its constructed resolution and cone comparison. -/
def complexDerivedSupportedCohomologyAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X structureMap)) (n : ℤ) :
    ComplexDerivedSupportedCohomology structureMap Z n ≃+
      RationalCohomologyWithSupport structureMap Z n :=
  derivedRationalSupportAddEquiv structureMap Z n

variable [SmoothOfRelativeDimension d structureMap] [T2Space (ComplexPoint X structureMap)]

/-- The smooth-ambient Borel–Moore comparison with the existing rational support
cohomology, derived from geometric orientation and actual supported resolutions. -/
def complexAmbientSheafBorelMooreAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ≃+
      RationalCohomologyWithSupport structureMap Z (2 * (d : ℤ) - i) :=
  (complexAmbientSheafBorelMooreHomologyIso structureMap d Z i).addCommGroupIsoToAddEquiv.trans
    (complexDerivedSupportedCohomologyAddEquivRationalSupport structureMap Z (2 * (d : ℤ) - i))

/-- The cycle-degree comparison lands in degree `2p` using the proved shift arithmetic. -/
def complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X structureMap)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z
        (2 * ((d - p : ℕ) : ℤ)) ≃+
      RationalCohomologyWithSupport structureMap Z (2 * (p : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeIso structureMap d Z p hp).addCommGroupIsoToAddEquiv.trans
    (complexDerivedSupportedCohomologyAddEquivRationalSupport structureMap Z (2 * (p : ℤ)))

/-- An explicit additive map from actual ambient Borel–Moore homology to the
repository's ordinary rational cohomology. It requires a class, not a duality datum. -/
def complexAmbientSheafBorelMooreToFieldCohomology
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i →+
      FieldCohomology ℚ structureMap (2 * (d : ℤ) - i) :=
  (forgetSupport structureMap (Z : Set (ComplexPoint X structureMap))
    (2 * (d : ℤ) - i)).comp
      (complexAmbientSheafBorelMooreAddEquivRationalSupport structureMap d Z i).toAddMonoidHom

/-- Cycle-degree transport into the existing ordinary cohomology API. No global
component class or local-purity theorem is silently supplied by this map. -/
def complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology
    (Z : Closeds (ComplexPoint X structureMap)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z
        (2 * ((d - p : ℕ) : ℤ)) →+
      FieldCohomology ℚ structureMap (2 * (p : ℤ)) :=
  (forgetSupport structureMap (Z : Set (ComplexPoint X structureMap))
    (2 * (p : ℤ))).comp
      (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
        structureMap d Z p hp).toAddMonoidHom

end AlgebraicGeometry.ComplexPoint
