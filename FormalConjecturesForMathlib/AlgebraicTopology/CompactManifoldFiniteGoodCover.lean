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

public import FormalConjecturesForMathlib.AlgebraicTopology.CompactManifoldFiniteHomology
public import Mathlib.Topology.ShrinkingLemma

/-!
# Finite contractible covers of compact manifolds

A compact charted space modeled on a real normed space has a finite cover by open contractible
sets: pull open balls in the model space back through charts, then take a finite subcover. In a
normal space the shrinking lemma produces another finite open cover whose closures lie in the
contractible members of the first cover. Thus every nonempty finite intersection of the shrunk
cover has nullhomotopic inclusion into the ambient space through any one of its contractible
carriers.

This is not a finite good cover: this file does not prove that finite intersections of the cover
members are contractible or acyclic. Such a good-cover theorem, a smooth triangulation theorem,
or a finite-CW comparison remains necessary to deduce finite generation of singular homology.
Mathlib currently has none of these bridges. Pull request #132 of `sphere-six-complex` only derives
homological finiteness after a finite cellular chain model and its singular comparison have been
provided; its unproved cellular comparison is not used here.
-/

@[expose] public noncomputable section

open Set Topology

universe u v

namespace AlgebraicTopology

/-- A finite open cover all of whose members are contractible. This does not require their
nonempty finite intersections to be contractible. -/
structure FiniteOpenContractibleCover (X : Type u) [TopologicalSpace X] where
  /-- The finite indexing type. -/
  ι : Type u
  /-- The index type is finite. -/
  finite_index : Finite ι
  /-- The open members of the cover. -/
  openSet : ι → Set X
  /-- Each cover member is open. -/
  isOpen_openSet : ∀ i, IsOpen (openSet i)
  /-- Each cover member is contractible. -/
  contractible : ∀ i, ContractibleSpace (openSet i)
  /-- The members cover the ambient space. -/
  iUnion_openSet : ⋃ i, openSet i = Set.univ

/-- Every point of a charted space modeled on a real normed space has an open contractible
neighborhood. -/
theorem exists_open_contractible_nhds_of_chartedSpace
    (E : Type v) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ContractibleSpace U := by
  let e := chartAt E x
  have hxsource : x ∈ e.source := mem_chart_source E x
  have hxtarget : e x ∈ e.target := e.map_source hxsource
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtarget
  let B : Set E := Metric.ball (e x) r
  let U : Set X := e.symm '' B
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBtarget : B ⊆ e.target := hball
  have hUopen : IsOpen U :=
    e.isOpen_symm_image_iff_of_subset_target hBtarget |>.mpr hBopen
  have hxB : e x ∈ B := Metric.mem_ball_self hr
  have hxU : x ∈ U := by
    refine ⟨e x, hxB, ?_⟩
    exact e.left_inv hxsource
  have hBcontractible : ContractibleSpace B :=
    Convex.contractibleSpace (_root_.convex_ball (e x) r) ⟨e x, hxB⟩
  let h : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hBtarget rfl
  have hUcontractible : ContractibleSpace U := h.symm.contractibleSpace
  exact ⟨U, hUopen, hxU, hUcontractible⟩

/-- A compact charted space modeled on a real normed space has a finite open cover by
contractible sets. -/
theorem nonempty_finiteOpenContractibleCover
    (E : Type v) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [CompactSpace X] :
    Nonempty (FiniteOpenContractibleCover X) := by
  classical
  have hlocal : ∀ x : X, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ ContractibleSpace U :=
    exists_open_contractible_nhds_of_chartedSpace E X
  let U : X → Set X := fun x ↦ (hlocal x).choose
  have hUopen (x : X) : IsOpen (U x) := (hlocal x).choose_spec.1
  have hxU (x : X) : x ∈ U x := (hlocal x).choose_spec.2.1
  have hUcontractible (x : X) : ContractibleSpace (U x) :=
    (hlocal x).choose_spec.2.2
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  let ι := {x : X // x ∈ t}
  let _ : Fintype ι := t.fintypeCoeSort
  refine ⟨{
    ι := ι
    finite_index := inferInstance
    openSet := fun i ↦ U i.1
    isOpen_openSet := fun i ↦ hUopen i.1
    contractible := fun i ↦ hUcontractible i.1
    iUnion_openSet := ?_ }⟩
  apply Set.Subset.antisymm (subset_univ _)
  intro x _
  have hx := ht (show x ∈ (Set.univ : Set X) from trivial)
  simp only [mem_iUnion] at hx ⊢
  obtain ⟨y, hyt, hxy⟩ := hx
  exact ⟨⟨y, hyt⟩, hxy⟩

/-- A finite open cover equipped with open contractible carriers. The closure of each cover
member lies in its carrier. -/
structure FiniteContractibleCarrierCover (X : Type u) [TopologicalSpace X] where
  /-- The finite indexing type. -/
  ι : Type u
  /-- The index type is finite. -/
  finite_index : Finite ι
  /-- The shrunk open members of the cover. -/
  openSet : ι → Set X
  /-- Open contractible carriers of the shrunk cover members. -/
  carrier : ι → Set X
  /-- Each shrunk member is open. -/
  isOpen_openSet : ∀ i, IsOpen (openSet i)
  /-- Each carrier is open. -/
  isOpen_carrier : ∀ i, IsOpen (carrier i)
  /-- The closure of each shrunk member lies in its carrier. -/
  closure_subset_carrier : ∀ i, closure (openSet i) ⊆ carrier i
  /-- Each carrier is contractible. -/
  contractible_carrier : ∀ i, ContractibleSpace (carrier i)
  /-- The shrunk members still cover the ambient space. -/
  iUnion_openSet : ⋃ i, openSet i = Set.univ

namespace FiniteOpenContractibleCover

variable {X : Type u}

/-- A finite open contractible cover of a normal space has a shrinking whose closures remain
inside the original contractible members. -/
theorem nonempty_shrink [TopologicalSpace X] [NormalSpace X]
    (F : FiniteOpenContractibleCover X) :
    Nonempty (FiniteContractibleCarrierCover X) := by
  let _ : Finite F.ι := F.finite_index
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset F.isOpen_openSet
      (fun _ ↦ Set.toFinite _) F.iUnion_openSet
  exact ⟨{
    ι := F.ι
    finite_index := F.finite_index
    openSet := V
    carrier := F.openSet
    isOpen_openSet := hVopen
    isOpen_carrier := F.isOpen_openSet
    closure_subset_carrier := hVclosure
    contractible_carrier := F.contractible
    iUnion_openSet := hVcover }⟩

end FiniteOpenContractibleCover

/-- A compact normal charted space modeled on a real normed space has a finite open cover with
contractible carriers containing the closures of its members. -/
theorem nonempty_finiteContractibleCarrierCover
    (E : Type v) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [CompactSpace X] [NormalSpace X] :
    Nonempty (FiniteContractibleCarrierCover X) := by
  obtain ⟨F⟩ := nonempty_finiteOpenContractibleCover E X
  exact F.nonempty_shrink

namespace FiniteContractibleCarrierCover

variable {X : Type u}

/-- The intersection of the members indexed by a finite set. The empty intersection is the whole
ambient space. -/
def intersection [TopologicalSpace X] (F : FiniteContractibleCarrierCover X)
    (s : Finset F.ι) : Set X :=
  ⋂ i ∈ s, F.openSet i

/-- The closure of a nonempty finite intersection lies in the contractible carrier of every
participating cover member. -/
theorem closure_intersection_subset_carrier [TopologicalSpace X]
    (F : FiniteContractibleCarrierCover X) (s : Finset F.ι)
    (i : F.ι) (hi : i ∈ s) : closure (F.intersection s) ⊆ F.carrier i := by
  apply (closure_mono ?_).trans (F.closure_subset_carrier i)
  intro x hx
  simp only [intersection, mem_iInter] at hx
  exact hx i hi

/-- The inclusion of a nonempty finite intersection into the ambient space is nullhomotopic: it
factors through the contractible carrier of any participating cover member. This does not say
that the intersection itself is contractible. -/
theorem intersection_inclusion_nullhomotopic [TopologicalSpace X]
    (F : FiniteContractibleCarrierCover X) (s : Finset F.ι)
    (i : F.ι) (hi : i ∈ s) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(F.intersection s, X)).Nullhomotopic := by
  have hs : F.intersection s ⊆ F.carrier i :=
    subset_closure.trans (F.closure_intersection_subset_carrier s i hi)
  let j : C(F.intersection s, F.carrier i) := ContinuousMap.inclusion hs
  let k : C(F.carrier i, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hnullj : j.Nullhomotopic := by
    let _ : ContractibleSpace (F.carrier i) := F.contractible_carrier i
    simpa only [ContinuousMap.id_comp] using
      (id_nullhomotopic (F.carrier i)).comp_left j
  have hnull := hnullj.comp_right k
  have hcomp : k.comp j =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(F.intersection s, X)) := by
    ext y
    rfl
  rw [← hcomp]
  exact hnull

end FiniteContractibleCarrierCover

end AlgebraicTopology

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

open AlgebraicTopology

/-- A dimensioned smooth projective complex analytification has a finite open cover whose members
have closures contained in open contractible carriers. -/
noncomputable def finiteContractibleCarrierCover
    (V : DimensionedSmoothProjectiveComplexVariety) :
    FiniteContractibleCarrierCover V.analyticPoint := by
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    ComplexPoint.analyticChartedSpace V.structureMap V.dimension
  exact Classical.choice
    (nonempty_finiteContractibleCarrierCover
      (Fin V.dimension → ℂ) V.analyticPoint)

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
