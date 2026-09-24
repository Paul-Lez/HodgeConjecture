/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierDataRepresents
public import Other.AlgebraicGeometry.AnalytificationModules
public import Other.AlgebraicGeometry.HolomorphicLineBundleModule
public import Other.AlgebraicGeometry.Cycle.SheafClass

/-!
# The divisor–Chern compatibility statement
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- Some Cartier data representing an algebraic model of a unit-sheaf extension has the
extension's rational first Chern class as its constructed cycle class. -/
def HasDivisorClassOfSomeCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ c : Scheme.CartierData X.left, c.Represents L ∧
      sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass

/-- Every Cartier datum representing an algebraic model has the extension's rational first
Chern class as its constructed cycle class. -/
def HasDivisorClassOfCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass

end AlgebraicGeometry.ComplexPoint
