/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.AnalyticSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! The holomorphic structure sheaf, regarded as a sheaf of rings. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance holomorphicRingSheafTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

def holomorphicRingSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) RingCat :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ CommRingCat RingCat)).obj (holomorphicFunctionSheaf X d)

end AlgebraicGeometry.ComplexPoint
