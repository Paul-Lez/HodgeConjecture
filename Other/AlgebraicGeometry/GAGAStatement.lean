/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationModules
public import Other.TauCeti.SheafOfModules.Invertible
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-!
# The line-bundle GAGA statement

This file states the algebraization property used by the Lefschetz reduction.  Its proof is
developed independently of the analytic construction of a particular line bundle.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every invertible holomorphic module sheaf is the analytification of an algebraic invertible
sheaf. -/
def AnalyticLineBundlesAlgebraize : Prop :=
  ∀ M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)),
    TauCeti.SheafOfModules.IsInvertible M →
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ M)

end AlgebraicGeometry.ComplexPoint
