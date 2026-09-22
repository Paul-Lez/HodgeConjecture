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

namespace AlgebraicGeometry.CycleComponent

variable (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (x : X.left)

/-- The `k`-th stage of the canonical smooth filtration of the singular locus of the cycle
component at `x`. -/
abbrev singularFiltration (k : ℕ) : Closeds (X.left.pointClosure x) :=
  reducedSmoothClosedFiltration (X.left.pointClosureι x ≫ X.hom)
    (singularLocusClosed (X.left.pointClosureι x ≫ X.hom)) k

/-- The image in `X.left` of the `k`-th stage of the singular filtration of the cycle component
at `x`. -/
def ambientSingularFiltration (k : ℕ) : Closeds X.left :=
  ⟨X.left.pointClosureι x '' (singularFiltration X x k : Set _),
    (X.left.pointClosureι x).isClosedEmbedding.isClosedMap _
      (singularFiltration X x k).isClosed⟩

@[simp]
lemma coe_ambientSingularFiltration (k : ℕ) :
    (ambientSingularFiltration X x k : Set X.left) =
      X.left.pointClosureι x '' (singularFiltration X x k : Set _) :=
  rfl

/-- `Z_sing,k(ℂ)`: the complex points of `X` over the `k`-th stage of the singular filtration of
the cycle component at `x`. The singular locus is the stage `k = 0`, written `x‾ˢⁱⁿᵍ(ℂ)`. -/
def analyticSingularFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  (ambientSingularFiltration X x k).preimage Point.continuous_underlying

@[inherit_doc analyticSingularFiltration]
scoped notation3:max x:max "‾ˢⁱⁿᵍ[" k "](ℂ)" => analyticSingularFiltration _ x k

@[inherit_doc analyticSingularFiltration]
scoped notation3:max x:max "‾ˢⁱⁿᵍ(ℂ)" => analyticSingularFiltration _ x 0

@[simp]
lemma coe_analyticSingularFiltration (k : ℕ) :
    (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X)) =
      Point.underlying ⁻¹' (ambientSingularFiltration X x k : Set X.left) :=
  rfl

@[simp]
lemma mem_analyticSingularFiltration {z : ComplexPoint X} {k : ℕ} :
    z ∈ x‾ˢⁱⁿᵍ[k](ℂ) ↔
      z.underlying ∈ ambientSingularFiltration X x k :=
  Iff.rfl

end AlgebraicGeometry.CycleComponent
