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

/-- The actual open locus on which both directions of a coordinate change are analytic. -/
def biAnalyticLocus : Set E :=
  {x | AnalyticAt ℂ e x} ∩ (e.source ∩ e ⁻¹' {y | AnalyticAt ℂ e.symm y})

theorem biAnalyticLocus_isOpen : IsOpen e.biAnalyticLocus :=
  (isOpen_analyticAt ℂ e).inter (e.isOpen_inter_preimage (isOpen_analyticAt ℂ e.symm))

/-- Restricting to this proved open set introduces no analytic-equivalence input. -/
def biAnalyticRestrict : OpenPartialHomeomorph E F :=
  e.restrOpen e.biAnalyticLocus e.biAnalyticLocus_isOpen

theorem biAnalyticRestrict_mem_source_iff (x : E) :
    x ∈ e.biAnalyticRestrict.source ↔
      x ∈ e.source ∧ AnalyticAt ℂ e x ∧ AnalyticAt ℂ e.symm (e x) := by
  change (x ∈ e.source ∧ AnalyticAt ℂ e x ∧ x ∈ e.source ∧ AnalyticAt ℂ e.symm (e x)) ↔ _
  aesop

end OpenPartialHomeomorph

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The actual complex-linear identification of tangent and normal product coordinates. -/
def closedImmersionNormalCoordinatesLinearEquiv :
    ((Fin m → ℂ) ×
      (closedImmersionDerivativeProjection X Y i m d z).ker) ≃L[ℂ]
        ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
    (closedImmersionNormalKernelEquiv X Y i m d z)

/-- The normal coordinate change inside the canonical ambient complex chart. -/
def closedImmersionNormalCoordinateChange :
    OpenPartialHomeomorph (Fin d → ℂ) ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionNormalChart X Y i m d z).symm.trans
    (closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toHomeomorph.toOpenPartialHomeomorph

/-- An actual support-flattening chart whose normal coordinate change is holomorphic in
both directions throughout its source. It contains the distinguished support point. -/
def closedImmersionHolomorphicFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  ((localChart X d (Point.map i z)).trans
    (closedImmersionNormalCoordinateChange X Y i m d z).biAnalyticRestrict).restrOpen
      (closedImmersionStandardFlatteningChart X Y i m d z).source
      (closedImmersionStandardFlatteningChart X Y i m d z).open_source

theorem closedImmersionHolomorphicFlatteningChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (Point.map i) ↔
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y).2 = 0 :=
  closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.2

variable (z' : ComplexPoint Y)

end AlgebraicGeometry.ComplexPoint
