/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DivisorClassCompatibility

/-!
# The hypotheses of the Lefschetz reduction
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- Every rational degree-two class is a rational multiple of an integral class. -/
def HasIntegralDenominatorClearing : Prop :=
  ∀ α : H^2(X; ℚ), ∃ (m : ℤ) (β : H^2(X; ℤ)),
    m ≠ 0 ∧ integralToRationalCohomology X 2 β = m • α

/-- The holomorphic section sheaf of every unit-sheaf extension is the analytification of an
algebraic invertible sheaf. -/
def HasAlgebraicModel : Prop :=
  ∀ E : HolomorphicUnitExtension X (dim X.left),
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)

/-- An algebraic invertible sheaf analytifying to the section sheaf of a unit-sheaf extension
is represented by an integral codimension-one cycle whose constructed class is the rational
image of the extension's first Chern class. -/
def HasDivisorOfAlgebraicModel : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ D : codimensionCycleSubgroup X.left 1,
      sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 D =
        integralToRationalCohomology X 2 E.firstChernClass

/-- The first Chern class of every unit-sheaf extension is the constructed class of an integral
codimension-one cycle. -/
def HasDivisorOfUnitExtension : Prop :=
  ∀ E : HolomorphicUnitExtension X (dim X.left),
    ∃ D : codimensionCycleSubgroup X.left 1,
      sheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 D =
        integralToRationalCohomology X 2 E.firstChernClass

end AlgebraicGeometry.ComplexPoint
