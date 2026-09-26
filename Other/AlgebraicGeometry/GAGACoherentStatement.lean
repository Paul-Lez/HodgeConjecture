/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.GAGAStatement
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Basic

/-!
# Coherent-sheaf GAGA statement

This file isolates the existence part of coherent GAGA needed to algebraize analytic line bundles.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Every coherent holomorphic module sheaf is the analytification of a coherent algebraic
module sheaf. -/
def AnalyticCoherentSheavesAlgebraize : Prop :=
  ∀ M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)),
    M.IsCoherent →
      ∃ F : X.left.Modules, F.IsCoherent ∧
        Nonempty ((moduleAnalytification X (dim X.left)).obj F ≅ M)

end AlgebraicGeometry.ComplexPoint
