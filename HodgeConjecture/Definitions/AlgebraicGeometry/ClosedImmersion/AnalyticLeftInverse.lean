/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Analytic local left inverses from actual section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts. In particular derivative injectivity is proved, not supplied as
an immersion or purity field.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

/-- The actual inclusion written in the canonical intrinsic and ambient complex charts. -/
def inclusionInComplexCharts (z : ComplexPoint Y) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => localChart X d (Point.map i z)
    (Point.map i ((localChart Y m z).symm v))

end AlgebraicGeometry.ComplexPoint
