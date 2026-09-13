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

public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass

/-!
# A standard local fundamental cycle

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FundamentalClass`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

attribute [fun_prop] stdSimplex.continuous_map

/-- The alternating sum of the faces of the standard affine `(n + 1)`-simplex, regarded as a
chain in punctured Euclidean space. -/
def standardSubspaceBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val • standardSubspaceFaceChain n i

end AlgebraicTopology.Singular

end

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

attribute [fun_prop] stdSimplex.continuous_map

lemma standardLocalCycle_inclusion (d : ℕ) :
    standardLocalCycle d ≫ (standardLocalRelativeChainComplex d).iCycles d =
      standardLocalChain d :=
  (standardLocalRelativeChainComplex d).liftCycles_i (standardLocalChain d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary d)

end AlgebraicTopology.Singular
