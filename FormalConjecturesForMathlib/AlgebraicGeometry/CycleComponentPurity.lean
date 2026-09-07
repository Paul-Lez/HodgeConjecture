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

public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentClosedPointDimension
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Local dual classes on cycle components

The local fundamental class obtained from exact coordinates on the smooth locus of a cycle
component is nonzero.  Since it generates local homology, there is a unique local cohomology
class evaluating to one on it, and that normalized dual class generates cohomology supported at
the chosen point.

This is intrinsic purity on the smooth component neighborhood.  It does not yet give ambient
purity in codimension `p`: that requires a Thom or Gysin comparison between the intrinsic local
homology in degree `2 * (d - p)` and ambient cohomology supported on the component in degree
`2 * p`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- The normalized dual of a nonzero vector. -/
def normalizedDual (z : M) (hz : z ≠ 0) : Module.Dual R M :=
  Classical.choose (Module.Projective.exists_dual_eq_one R hz)

@[simp]
lemma normalizedDual_apply_self (z : M) (hz : z ≠ 0) :
    (normalizedDual (R := R) z hz) z = (1 : R) :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one R hz)

/-- A normalized dual is unique when its distinguished vector generates the module. -/
lemma normalizedDual_unique {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤)
    (φ : Module.Dual R M) (hφ : φ z = 1) :
    φ = normalizedDual z hz := by
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp [hφ]

/-- The normalized dual of a homology generator generates the full dual space. -/
lemma span_normalizedDual_eq_top {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) :
    Submodule.span R {normalizedDual (R := R) z hz} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff R]
  intro φ
  refine ⟨φ z, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero (n : ℕ) :
    standardComplexLocalClass n ≠ 0 := by
  rw [standardComplexLocalClass_ne_zero_iff]
  by_cases hn : n = 0
  · subst n
    exact standardLocalClass_zero_ne_zero
  · exact standardLocalClass_ne_zero_of_pos (n * 2) (Nat.mul_pos (Nat.pos_of_ne_zero hn) (by
      norm_num))

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

noncomputable local instance {Y : Scheme} {g : Y ⟶ Spec (.of ℂ)} :
    TopologicalSpace (ComplexPoint Y g) := ComplexPoint.analyticTopology

variable {d n : ℕ} {V : SmoothProjectiveComplexVariety} {x : V.scheme}
  [SmoothOfRelativeDimension d V.structureMap]
  (C : CycleComponentSeparateLocalCoordinates V x d n)

/-- The local homology class transported from the exact component chart is nonzero. -/
lemma neighborhoodLocalClass_ne_zero : C.neighborhoodLocalClass ≠ 0 := by
  let _ : IsAffine C.componentNeighborhood.toScheme :=
    C.componentNeighborhood_isAffine
  let _ : T2Space
      (ComplexPoint C.componentNeighborhood.toScheme C.neighborhoodStructureMap) :=
    ComplexPoint.t2Space_of_isAffine C.neighborhoodStructureMap
  have hinjective : Function.Injective C.neighborhoodLocalHomologyMap :=
    (chartModelEmbedding_relativeHomologyMap_bijective
      n C.neighborhoodProjectionChart C.neighborhoodPoint
        C.neighborhoodPoint_mem_projectionChart_source).1
  intro hzero
  apply standardComplexLocalClass_ne_zero n
  apply hinjective
  simpa only [neighborhoodLocalClass, map_zero] using hzero

/-- Cohomology of the component neighborhood supported at its selected smooth point. -/
abbrev neighborhoodPointSupportedCohomology :=
  CohomologyWithSupport ℚ
    (TopCat.of (ComplexPoint C.componentNeighborhood.toScheme C.neighborhoodStructureMap))
    {C.neighborhoodPoint} (2 * n)

/-- The unique local cohomology class normalized to evaluate to one on the transported local
fundamental class. -/
def neighborhoodLocalCoclass : C.neighborhoodPointSupportedCohomology :=
  normalizedDual C.neighborhoodLocalClass C.neighborhoodLocalClass_ne_zero

@[simp]
lemma neighborhoodLocalCoclass_apply_localClass :
    C.neighborhoodLocalCoclass C.neighborhoodLocalClass = 1 := by
  exact normalizedDual_apply_self C.neighborhoodLocalClass
    C.neighborhoodLocalClass_ne_zero

/-- The normalized local coclass generates cohomology supported at the selected smooth point of
the component neighborhood. -/
lemma span_neighborhoodLocalCoclass_eq_top :
    Submodule.span ℚ {C.neighborhoodLocalCoclass} = ⊤ := by
  exact span_normalizedDual_eq_top C.neighborhoodLocalClass_ne_zero
    C.span_neighborhoodLocalClass_eq_top

/-- The local normalization condition characterizes the component's local coclass. -/
lemma neighborhoodLocalCoclass_unique
    (β : C.neighborhoodPointSupportedCohomology)
    (hβ : β C.neighborhoodLocalClass = 1) :
    β = C.neighborhoodLocalCoclass := by
  exact normalizedDual_unique C.neighborhoodLocalClass_ne_zero
    C.span_neighborhoodLocalClass_eq_top β hβ

/-- Every codimension-`p` component of a smooth complex `d`-fold has an exact smooth local
coordinate package whose normalized point-supported coclass generates local cohomology. -/
lemma exists_span_neighborhoodLocalCoclass_eq_top
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p) :
    ∃ C : CycleComponentSeparateLocalCoordinates V x d (d - p),
      C.neighborhoodLocalCoclass C.neighborhoodLocalClass = 1 ∧
        Submodule.span ℚ {C.neighborhoodLocalCoclass} = ⊤ := by
  obtain ⟨C, -⟩ := exists_span_neighborhoodLocalClass_eq_top V x d p hx
  exact ⟨C, C.neighborhoodLocalCoclass_apply_localClass,
    C.span_neighborhoodLocalCoclass_eq_top⟩

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
