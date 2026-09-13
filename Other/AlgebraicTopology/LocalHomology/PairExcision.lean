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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativePairExcision

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Set
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- The canonical isomorphism on relative homology induced by inclusion of an open
neighborhood of the distinguished point. -/
def neighborhoodPointComplementRelativeHomologyIso
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    RelativeHomology ℚ (neighborhoodPointComplementPair U x) n ≅
      RelativeHomology ℚ (pointComplementPair x) n := by
  let : QuasiIso
      ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) :=
    neighborhoodPointComplement_relativeChainMap_quasiIso U x hU hx
  exact isoOfQuasiIsoAt
    ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) n

end AlgebraicTopology.Singular
