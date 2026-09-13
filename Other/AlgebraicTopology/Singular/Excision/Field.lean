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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.Field

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

@[expose] public noncomputable section

namespace AlgebraicTopology.Singular

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- Rational small-chain inclusion induces an isomorphism on homology in every degree. -/
def coverSmallRationalSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallRationalSingularChainComplex X U).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).homology n :=
  (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).toHomologyIso n

lemma coverSmallRationalSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallRationalSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallRationalSingularChainInclusion X U) n := by
  dsimp [coverSmallRationalSingularHomologyIso_of_openCover]
  change HomologicalComplex.homologyMap
      (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom n = _
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom]

end AlgebraicTopology.Singular
