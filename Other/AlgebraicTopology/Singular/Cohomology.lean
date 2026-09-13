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

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-!
# Cohomology, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicTopology.Singular

/-- Over a field a continuous map is determined on cohomology by its effect on homology:
universal coefficients is natural, and an injective equivalence. -/
lemma cohomologyMap_eq_of_homologyMap_eq (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ)
    {f g : X ⟶ Y} (h : homologyMap R n f = homologyMap R n g) :
    cohomologyMap R n f = cohomologyMap R n g := by
  ext α
  refine (cohomologyEquivDualHomology R X n).injective (LinearMap.ext fun z => ?_)
  rw [cohomologyEquivDualHomology_cohomologyMap, cohomologyEquivDualHomology_cohomologyMap,
    h]

end AlgebraicTopology.Singular
end
