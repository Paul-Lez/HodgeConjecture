/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
public import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset
public import Mathlib.Topology.NoetherianSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The singular filtration of a cycle component

The singular locus of the cycle component at `x` carries the canonical finite filtration by closed
subsets whose successive differences are smooth. This file records its stages as closed subsets of
the component, their images in `X.left`, and the complex points of `X` over those images.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (x : X.left)

/-- The `k`-th stage of the canonical smooth filtration of the singular locus of the cycle
component at `x`. -/
abbrev cycleComponentSingularFiltration (k : ℕ) : Closeds (X.left.pointClosure x) :=
  reducedSmoothClosedFiltration (X.left.pointClosureι x ≫ X.hom)
    (singularLocusClosed (X.left.pointClosureι x ≫ X.hom)) k

/-- The image in `X.left` of the `k`-th stage of the singular filtration of the cycle component
at `x`. -/
def cycleComponentAmbientSingularFiltration (k : ℕ) : Closeds X.left :=
  ⟨X.left.pointClosureι x '' (cycleComponentSingularFiltration X x k : Set _),
    (X.left.pointClosureι x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularFiltration X x k).isClosed⟩

@[simp]
lemma coe_cycleComponentAmbientSingularFiltration (k : ℕ) :
    (cycleComponentAmbientSingularFiltration X x k : Set X.left) =
      X.left.pointClosureι x '' (cycleComponentSingularFiltration X x k : Set _) :=
  rfl

namespace ComplexPoint

/-- The complex points of `X` over the `k`-th stage of the singular filtration of the cycle
component at `x`. -/
def cycleComponentAnalyticSingularFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  (cycleComponentAmbientSingularFiltration X x k).preimage Point.continuous_underlying

@[simp]
lemma coe_cycleComponentAnalyticSingularFiltration (k : ℕ) :
    (cycleComponentAnalyticSingularFiltration X x k : Set (ComplexPoint X)) =
      Point.underlying ⁻¹' (cycleComponentAmbientSingularFiltration X x k : Set X.left) :=
  rfl

@[simp]
lemma mem_cycleComponentAnalyticSingularFiltration {z : ComplexPoint X} {k : ℕ} :
    z ∈ cycleComponentAnalyticSingularFiltration X x k ↔
      z.underlying ∈ cycleComponentAmbientSingularFiltration X x k :=
  Iff.rfl

end ComplexPoint

end AlgebraicGeometry
