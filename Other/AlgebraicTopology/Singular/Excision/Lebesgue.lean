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

public import Mathlib.AlgebraicTopology.SingularSet
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Lebesgue

/-!
# Lebesgue, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Lebesgue`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
noncomputable section
open Set
namespace AlgebraicTopology.Singular

/-- Any nonempty subset of the standard simplex whose diameter is smaller than a pulled-back
Lebesgue number maps into one member of the original cover. -/
public theorem singularSimplex_image_subset_cover_of_diam_lt
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    {s : Set (stdSimplex ℝ (Fin (n + 1)))}
    (hsne : s.Nonempty) (hsbounded : Bornology.IsBounded s) :
    ∃ δ > 0, Metric.diam s < δ →
      ∃ i, X.toSSetObjEquiv _ x '' s ⊆ U i := by
  obtain ⟨δ, hδ, hLeb⟩ :=
    singularSimplex_openCover_lebesgueNumber X U hUopen hUcover n x
  refine ⟨δ, hδ, fun hdiam ↦ ?_⟩
  obtain ⟨w, hw⟩ := hsne
  obtain ⟨i, hi⟩ := hLeb w
  refine ⟨i, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hi (Metric.mem_ball.mpr ((Metric.dist_le_diam_of_mem hsbounded hy hw).trans_lt hdiam))

end AlgebraicTopology.Singular
end
end
