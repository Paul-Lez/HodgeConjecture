/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexSheafBorelMooreForget
public import Other.AlgebraicGeometry.DerivedSupportRationalForget

/-!
# The constructed ambient Borel–Moore map into the existing rational cohomology API

The comparison is the actual complex-orientation duality followed by the constructed
injective-resolution/support-cone equivalence. Forgetting support then lands in the
repository's `FieldCohomology` itself, with no supplied duality or comparison argument.

This module transports Borel–Moore classes; it does not produce fundamental classes
for general algebraic components. Agreement with the actual derived-global
support-forgetting route is proved below, using the normalized support-cone
comparison including its sign. Agreement with the existing point coclass for a
particular fundamental-class construction remains a separate comparison theorem.
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The existing-cohomology adapter is exactly the actual derived support-forgetting
map transported through the constructed ordinary cohomology comparison. In
particular no independent sign or scalar is chosen at the final adapter. -/
theorem complexAmbientSheafBorelMooreToFieldCohomology_eq_derivedForget
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ)
    (x : ComplexAmbientSheafBorelMooreHomology structureMap d Z i) :
    complexAmbientSheafBorelMooreToFieldCohomology structureMap d Z i x =
      derivedRationalCohomologyAddEquiv structureMap (2 * (d : ℤ) - i)
        (complexAmbientSheafBorelMooreToCohomology structureMap d Z i x) := by
  exact (derivedRationalSupportAddEquiv_forgetSupport structureMap Z (2 * (d : ℤ) - i)
    ((complexAmbientSheafBorelMooreHomologyIso structureMap d Z i).hom x)).symm

end AlgebraicGeometry.ComplexPoint
