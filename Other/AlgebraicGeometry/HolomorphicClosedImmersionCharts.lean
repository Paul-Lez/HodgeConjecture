/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z z' : ComplexPoint Y)

/-- For a point in a genuine overlap, the normal derivative has a constructed complex
linear inverse. Only membership in the actual overlap is required. -/
def closedImmersionNormalTransitionDerivativeEquiv (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    (Fin (d - m) → ℂ) ≃L[ℂ] (Fin (d - m) → ℂ) :=
  normalTransitionDerivativeEquiv
    (closedImmersionNormalTransition X Y i m d z z') a ha
    (closedImmersionNormalTransition_preserves_support X Y i m d z z')
    (analyticAt_closedImmersionNormalTransition X Y i m d z z' (a, 0) ha)
    (analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (a, 0) ha)

@[simp] theorem closedImmersionNormalTransitionDerivativeEquiv_apply (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition X Y i m d z z').source)
    (v : Fin (d - m) → ℂ) :
    closedImmersionNormalTransitionDerivativeEquiv X Y i m d z z' a ha v =
      (fderiv ℂ (closedImmersionNormalTransition X Y i m d z z')
        (a, 0) (0, v)).2 := rfl

end AlgebraicGeometry.ComplexPoint
