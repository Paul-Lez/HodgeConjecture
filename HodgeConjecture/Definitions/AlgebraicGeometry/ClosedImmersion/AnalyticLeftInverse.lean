/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Analytic local left inverses from section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts, and in particular the inclusion has injective derivative.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

/-- Let `i : Y → X` be a morphism of smooth complex schemes of respective dimensions `m` and `d`,
and let `z ∈ Y(ℂ)`. If `eY` and `eX` are the chosen analytic charts at `z` and `i(z)`, this is
the coordinate expression `eX ∘ i ∘ eY⁻¹ : ℂ^m → ℂ^d`, valid where both charts are defined. -/
def inclusionInComplexCharts (z : ComplexPoint Y) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => localChart X d (Point.map i z)
    (Point.map i ((localChart Y m z).symm v))

end AlgebraicGeometry.ComplexPoint
