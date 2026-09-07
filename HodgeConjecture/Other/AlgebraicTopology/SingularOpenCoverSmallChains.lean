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

public import HodgeConjecture.Other.AlgebraicTopology.SingularExcisionOpenCover
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Small chains for covers by open subsets

This file specializes the small-singular-chain theorem to a cover of an open subset by open
subsets of an ambient topological space. This is the form used by sheaf descent.
-/

@[expose] public noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AlgebraicTopology.Singular

variable {ι : Type} (X : TopCat) (U : Opens X) (V : ι → Opens X)

/-- An open subset of `X`, regarded as a subset of the subspace `U`. -/
def openCoverSubset (i : ι) : Set U :=
  {x | x.1 ∈ V i}

/-- The subsets of `U` induced by opens of `X` are open in the subspace topology. -/
lemma isOpen_openCoverSubset (i : ι) : IsOpen (openCoverSubset X U V i) := by
  change IsOpen (Subtype.val ⁻¹' (V i : Set X))
  exact (V i).2.preimage continuous_subtype_val

/-- If the opens have supremum `U`, their induced subsets cover the subspace `U`. -/
lemma iUnion_openCoverSubset_eq_univ (hV : ⨆ i, V i = U) :
    ⋃ i, openCoverSubset X U V i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.1 ∈ ⨆ i, V i := by
    rw [hV]
    exact x.2
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- The cover-small inclusion for a cover of an open subspace is a quasi-isomorphism. -/
theorem openCoverSmallChainQuasiIsomorphism (hV : ⨆ i, V i = U) :
    CoverSmallChainQuasiIsomorphism (TopCat.of U) (openCoverSubset X U V) :=
  coverSmallChainQuasiIsomorphism_of_openCover (TopCat.of U) (openCoverSubset X U V)
    (isOpen_openCoverSubset X U V) (iUnion_openCoverSubset_eq_univ X U V hV)

/-- The cover-small inclusion for a cover of an open subspace is a chain-homotopy equivalence. -/
theorem openCoverSmallChainApproximation (hV : ⨆ i, V i = U) :
    CoverSmallChainApproximation (TopCat.of U) (openCoverSubset X U V) :=
  coverSmallChainApproximation_of_openCover (TopCat.of U) (openCoverSubset X U V)
    (isOpen_openCoverSubset X U V) (iUnion_openCoverSubset_eq_univ X U V hV)

end AlgebraicTopology.Singular
