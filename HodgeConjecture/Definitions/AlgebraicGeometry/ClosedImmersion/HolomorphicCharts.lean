/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.NormalCoordinates
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.HolomorphicNormalTransition

/-!
# Holomorphic support-flattening charts

Restricting to the open loci where a normal coordinate change and its inverse are analytic
upgrades centerwise analyticity to analyticity throughout each selected chart. All coordinate
changes come from the smooth closed immersion constructed earlier.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

/-- Let `E` and `F` be complex Banach spaces and `e` a homeomorphism between open subsets of them.
This is the open set of points `x` in the source where `e` is complex analytic at `x` and its
inverse is complex analytic at `e(x)`. -/
def biAnalyticLocus : Set E :=
  {x | AnalyticAt ℂ e x} ∩ (e.source ∩ e ⁻¹' {y | AnalyticAt ℂ e.symm y})

theorem biAnalyticLocus_isOpen : IsOpen e.biAnalyticLocus :=
  (isOpen_analyticAt ℂ e).inter (e.isOpen_inter_preimage (isOpen_analyticAt ℂ e.symm))

/-- Let `E` and `F` be complex Banach spaces and `e` a homeomorphism between open subsets. Restrict
its source to those `x` where both `e` at `x` and `e⁻¹` at `e(x)` are complex analytic. This is
the resulting homeomorphism between open subsets, analytic in both directions. -/
def biAnalyticRestrict : OpenPartialHomeomorph E F :=
  e.restrOpen e.biAnalyticLocus e.biAnalyticLocus_isOpen

end OpenPartialHomeomorph

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. Let `P` be the chosen left inverse of the coordinate derivative of
`i`. This continuous complex linear equivalence `ℂ^m × ker P ≃ ℂ^m × ℂ^{d-m}` leaves the first
coordinate fixed and uses a chosen basis on the normal space `ker P`. -/
def closedImmersionNormalCoordinatesLinearEquiv :
    ((Fin m → ℂ) ×
      (closedImmersionDerivativeProjection X Y i m d z).ker) ≃L[ℂ]
        ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
    (closedImmersionNormalKernelEquiv X Y i m d z)

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. This local homeomorphism changes coordinates in `ℂ^d` near the
chart image of `i(z)` to tangent and normal coordinates in `ℂ^m × ℂ^{d-m}`. It inverts the
parametrization `(v,w) ↦ g(v)+w`, where `g` represents `i`, then identifies the chosen normal
space with `ℂ^{d-m}`. -/
def closedImmersionNormalCoordinateChange :
    OpenPartialHomeomorph (Fin d → ℂ) ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionNormalChart X Y i m d z).symm.trans
    (closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toHomeomorph.toOpenPartialHomeomorph

/-- Let `i : Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. This chart maps a neighborhood of `i(z)` in `X(ℂ)` into `ℂ^m ×
ℂ^{d-m}`, with the image of `Y(ℂ)` equal to the zero set of the normal coordinate on the source.
The coordinate change from an ambient analytic chart and its inverse are holomorphic throughout
their domains. -/
def closedImmersionHolomorphicFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  ((localChart X d (Point.map i z)).trans
    (closedImmersionNormalCoordinateChange X Y i m d z).biAnalyticRestrict).restrOpen
      (closedImmersionStandardFlatteningChart X Y i m d z).source
      (closedImmersionStandardFlatteningChart X Y i m d z).open_source

end AlgebraicGeometry.ComplexPoint
