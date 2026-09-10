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

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Basic facts about standard simplices

Small shared utilities about the simplicial standard simplex `Δ[n]` and the convex standard
simplex `stdSimplex ℝ X`. They are collected here because several otherwise unrelated subtrees
need them.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The universal top-dimensional simplex of `Δ[n]`: the unique nondegenerate simplex in the top
dimension. -/
noncomputable def standardSimplexTopSimplex (n : ℕ) :
    (Δ[n] : SSet.{0}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))

/-- An injective reindexing has zero coefficient away from its image. -/
theorem stdSimplex_map_apply_eq_zero_of_notMem_range
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : stdSimplex ℝ X) (y : Y)
    (hy : y ∉ Set.range f) :
    stdSimplex.map f w y = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact (hy ⟨x, (Finset.mem_filter.mp hx).2⟩).elim

end AlgebraicTopology.Singular
