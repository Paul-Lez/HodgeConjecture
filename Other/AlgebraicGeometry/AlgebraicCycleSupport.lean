/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import Other.AlgebraicGeometry.ChowGroup

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Geometric support of a whole algebraic cycle

`HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport` constructs the support of a
single irreducible component, which is what the statement of the conjecture needs. This file
assembles those into the support of an arbitrary algebraic cycle, and records the corresponding
statements for the carrier of a principal divisor.

It belongs in `Other` because it is stated in terms of `AlgebraicCycle` and `PrincipalDivisor`:
the conjecture is currently phrased with the span of individual component classes, so nothing
here is reachable from the statement. Once the cycle-class map is proved to kill principal-divisor
relations and descends to the rational Chow group, this is the support theory that descent will
be stated over.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

/-- The integral projective variety defined by one generic point of a smooth projective variety. -/
def cycleComponentVariety
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IntegralProjectiveComplexVariety where
  scheme := cycleComponent X.left x
  isIntegral := inferInstance
  structureMap := cycleComponentι X.left x ≫ X.hom
  projective := cycleComponent_projective X x

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    c.support.Finite := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ

/-- The underlying closed support of an algebraic cycle: the union of the closures of all generic
points having nonzero coefficient. -/
def algebraicCycleSupport {R : Type*} [Zero R] (X : Scheme)
    (c : AlgebraicCycle X R) : Set X :=
  ⋃ x ∈ c.support, closure {x}

/-- The support of the pushforward of a principal divisor lies in the image of its carrier. -/
lemma PrincipalDivisor.pushforwardCycle_support_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    D.pushforwardCycle.support ⊆ Set.range D.inclusion := by
  unfold PrincipalDivisor.pushforwardCycle AlgebraicCycle.map
  apply Function.locallyFinsupp.support_map_subset_of_forall_mem
    (s := Set.univ) (t := Set.range D.inclusion)
  · exact Set.subset_univ _
  · exact fun x _ _ => ⟨x, rfl⟩

/-- The geometric support of a pushed-forward principal divisor lies in its closed carrier. -/
lemma PrincipalDivisor.algebraicCycleSupport_pushforwardCycle_subset_range
    {X : Scheme} {p : ℕ} (D : PrincipalDivisor X p) :
    algebraicCycleSupport X D.pushforwardCycle ⊆ Set.range D.inclusion := by
  let := D.isClosedImmersion
  rw [algebraicCycleSupport, Set.iUnion₂_subset_iff]
  intro x hx
  refine closure_minimal ?_ D.inclusion.isClosedEmbedding.isClosed_range
  simpa only [Set.singleton_subset_iff] using D.pushforwardCycle_support_subset_range hx

/-- The complex points lying over the geometric support of an algebraic cycle. -/
def analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : AlgebraicCycle X.left R) : Set (ComplexPoint X) :=
  Point.underlying ⁻¹' algebraicCycleSupport X.left c

/-- The complex points lying over the closed carrier of a principal divisor. -/
def principalDivisorCarrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) : Set (ComplexPoint X) :=
  (@Point.underlying ℂ _ _ X) ⁻¹' Set.range D.inclusion

/-- The analytic support of a principal-divisor carrier is closed. -/
lemma isClosed_principalDivisorCarrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) :
    IsClosed (principalDivisorCarrierSupport X D) := by
  let := D.isClosedImmersion
  let Z : TopologicalSpace.Closeds X.left :=
    ⟨Set.range D.inclusion, D.inclusion.isClosedEmbedding.isClosed_range⟩
  exact isClosed_complexPoint_underlying_preimage X Z

/-- The analytic support of a pushed-forward principal divisor lies over its carrier. -/
lemma analyticCycleSupport_pushforwardCycle_subset_carrierSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p : ℕ} (D : PrincipalDivisor X.left p) :
    analyticCycleSupport X D.pushforwardCycle ⊆
      principalDivisorCarrierSupport X D :=
  fun _ hz => D.algebraicCycleSupport_pushforwardCycle_subset_range hz

/-- The analytic support of a cycle is the union of the analytic supports of its nonzero
components. -/
lemma analyticCycleSupport_eq_iUnion {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    analyticCycleSupport X c =
      ⋃ x ∈ c.support, cycleComponentSupport X x := by
  ext z
  simp [analyticCycleSupport, algebraicCycleSupport, cycleComponentSupport]

/-- The analytic support of an algebraic cycle on a projective variety is closed. -/
lemma isClosed_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    IsClosed (analyticCycleSupport X c) := by
  rw [analyticCycleSupport_eq_iUnion]
  exact (algebraicCycle_support_finite X c).isClosed_biUnion fun x _ =>
    isClosed_cycleComponentSupport X x

lemma cycleComponentSupport_subset_analyticCycleSupport {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R)
    (x : X.left) (hx : c x ≠ 0) :
    cycleComponentSupport X x ⊆ analyticCycleSupport X c :=
  fun _ hz => Set.mem_iUnion₂.mpr ⟨x, Function.mem_support.mpr hx, hz⟩

@[simp]
lemma algebraicCycleSupport_zero {R : Type*} [Zero R] (X : Scheme) :
    algebraicCycleSupport X (0 : AlgebraicCycle X R) = ∅ := by
  simp [algebraicCycleSupport]
  exact fun _ => rfl

@[simp]
lemma analyticCycleSupport_zero {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    analyticCycleSupport X (0 : AlgebraicCycle X.left R) = ∅ := by
  simp [analyticCycleSupport]

end AlgebraicGeometry
