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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.CoverSmallQuasiIso
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineRelativeMesh
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineSupport
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.OpenCover

/-!
# OpenCover, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.OpenCover`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace AlgebraicTopology.Singular
variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The cover-small inclusion is a quasi-isomorphism for every open cover. -/
public theorem coverSmallChainQuasiIsomorphism_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coverSmallIntegralSingularChainInclusion X U) :=
  coverSmallChainQuasiIsomorphism_of_eventuallySmall X U
    (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

end AlgebraicTopology.Singular
end
end
