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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationLocallyContractible
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationSecondCountable
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Prerequisites for finite homology of compact manifolds

A compact strongly locally contractible space has a finite open cover subordinate to
contractible neighborhoods. This applies to a dimensioned smooth projective complex
analytification. We also prove the algebraic reduction from a degreewise finite chain model
quasi-isomorphic to singular chains to finite-dimensional singular homology.

The missing step between these results is a finite-good-cover, finite-CW, or triangulation
comparison theorem. Mathlib does not currently provide that theorem. The corresponding endpoint
in `sphere-six-complex` is `compactCOneManifoldFiniteCWModelAtDimension`, which is explicitly
axiomatized and is not used here.

The proof of finite generation of the homology of a degreewise finite complex is adapted from
[`SphereSixComplex/Topology/CellularChainModel.lean`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/CellularChainModel.lean),
copyright its contributors and used under that repository's Apache-2.0 license.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Limits Set Topology

universe u

namespace AlgebraicTopology

/-- A finite family of open sets covering `X`, each contained in a contractible neighborhood. -/
structure FiniteContractibleNeighborhoodCover (X : Type u) [TopologicalSpace X] where
  /-- The finite indexing type. -/
  ι : Type u
  /-- The index type is finite. -/
  finite_index : Finite ι
  /-- A chosen center for each member of the cover. -/
  center : ι → X
  /-- The open members of the cover. -/
  openSet : ι → Set X
  /-- Contractible neighborhoods containing the corresponding open members. -/
  contractibleNeighborhood : ι → Set X
  /-- Each member of the cover is open. -/
  isOpen_openSet : ∀ i, IsOpen (openSet i)
  /-- Each center belongs to its open member. -/
  center_mem_openSet : ∀ i, center i ∈ openSet i
  /-- Each open member lies in its contractible neighborhood. -/
  openSet_subset : ∀ i, openSet i ⊆ contractibleNeighborhood i
  /-- Each contractible set is a neighborhood of its center. -/
  contractibleNeighborhood_mem_nhds : ∀ i,
    contractibleNeighborhood i ∈ 𝓝 (center i)
  /-- Each containing neighborhood is contractible. -/
  contractible : ∀ i, ContractibleSpace (contractibleNeighborhood i)
  /-- The open members cover the space. -/
  iUnion_openSet : ⋃ i, openSet i = Set.univ

/-- A compact strongly locally contractible space admits a finite open cover whose members lie
inside contractible neighborhoods. -/
theorem nonempty_finiteContractibleNeighborhoodCover
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [StronglyLocallyContractibleSpace X] :
    Nonempty (FiniteContractibleNeighborhoodCover X) := by
  classical
  have hlocal : ∀ x : X, ∃ U C : Set X,
      IsOpen U ∧ x ∈ U ∧ U ⊆ C ∧ C ∈ 𝓝 x ∧ ContractibleSpace C := by
    intro x
    obtain ⟨C, ⟨hC, hCcontractible⟩, -⟩ :=
      (StronglyLocallyContractibleSpace.contractible_basis x).mem_iff.mp univ_mem
    obtain ⟨U, hUC, hUopen, hxU⟩ := mem_nhds_iff.mp hC
    exact ⟨U, C, hUopen, hxU, hUC, hC, hCcontractible⟩
  let U : X → Set X := fun x ↦ (hlocal x).choose
  let C : X → Set X := fun x ↦ (hlocal x).choose_spec.choose
  have hUopen (x : X) : IsOpen (U x) := (hlocal x).choose_spec.choose_spec.1
  have hxU (x : X) : x ∈ U x := (hlocal x).choose_spec.choose_spec.2.1
  have hUC (x : X) : U x ⊆ C x := (hlocal x).choose_spec.choose_spec.2.2.1
  have hCnhds (x : X) : C x ∈ 𝓝 x :=
    (hlocal x).choose_spec.choose_spec.2.2.2.1
  have hC (x : X) : ContractibleSpace (C x) :=
    (hlocal x).choose_spec.choose_spec.2.2.2.2
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  let ι := {x : X // x ∈ t}
  let _ : Fintype ι := t.fintypeCoeSort
  refine ⟨{
    ι := ι
    finite_index := inferInstance
    center := fun i ↦ i.1
    openSet := fun i ↦ U i.1
    contractibleNeighborhood := fun i ↦ C i.1
    isOpen_openSet := fun i ↦ hUopen i.1
    center_mem_openSet := fun i ↦ hxU i.1
    openSet_subset := fun i ↦ hUC i.1
    contractibleNeighborhood_mem_nhds := fun i ↦ hCnhds i.1
    contractible := fun i ↦ hC i.1
    iUnion_openSet := ?_ }⟩
  apply Set.Subset.antisymm (subset_univ _)
  intro x _
  have hx := ht (show x ∈ (Set.univ : Set X) from trivial)
  simp only [mem_iUnion] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  obtain ⟨hyt, hxy⟩ := hy
  exact ⟨⟨y, hyt⟩, hxy⟩

/-- Homology of a chain complex of finite-dimensional vector spaces is finite-dimensional in
each degree where the chain group is finite-dimensional. -/
theorem module_finite_homology_of_finite_chain_group
    (R : Type u) [Field R] (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (h : Module.Finite R (C.X n)) : Module.Finite R (C.homology n) := by
  let _ := h
  let i : C.cycles n →ₗ[R] C.X n := (HomologicalComplex.iCycles C n).hom
  have hi : Function.Injective i := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  have hcycles : Module.Finite R (C.cycles n) :=
    Module.Finite.of_injective i hi
  let _ := hcycles
  let q : C.cycles n →ₗ[R] C.homology n := (HomologicalComplex.homologyπ C n).hom
  have hq : Function.Surjective q := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  exact Module.Finite.of_surjective q hq

/-- A degreewise finite chain complex quasi-isomorphic to singular chains proves that singular
homology is finite-dimensional. -/
theorem singularHomology_module_finite_of_finite_quasiIso
    (R : Type u) [Field R] (X : TopCat.{u})
    (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).obj X) [QuasiIso f]
    (hC : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R (Singular.Homology R X n) := by
  let _ : Module.Finite R (C.homology n) :=
    module_finite_homology_of_finite_chain_group R C n (hC n)
  exact Module.Finite.equiv
    (asIso (HomologicalComplex.homologyMap f n)).toLinearEquiv

end AlgebraicTopology

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

open AlgebraicTopology

/-- A dimensioned smooth projective complex analytification admits a finite open cover whose
members lie inside contractible neighborhoods. -/
noncomputable def finiteContractibleNeighborhoodCover
    (V : DimensionedSmoothProjectiveComplexVariety) :
    FiniteContractibleNeighborhoodCover V.analyticPoint :=
  Classical.choice (nonempty_finiteContractibleNeighborhoodCover V.analyticPoint)

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
