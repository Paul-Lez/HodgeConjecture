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

public import HodgeConjecture.Definitions.Algebra.Homology.LinearDual
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
/-!
# The short-complex model of singular cochain cohomology

Singular cohomology is *defined* in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology` as the homology of the singular
cochain complex, that is by dualising the chain complex. This file records the equivalent
description that only mentions the degree-`n` short complex of the singular chain complex: its
reversed linear dual has the same homology.

That short-complex model is what the chain-homotopy machinery of
`HodgeConjecture.Definitions.Algebra.Homology.LinearDual` produces, so it is the convenient shape
for comparison results such as subdivision invariance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Singular cochain cohomology in degree `n`, expressed through the reversed algebraic-dual of
the degree-`n` short complex of the singular chain complex. -/
abbrev CochainCohomology (n : ℕ) : ModuleCat.{u} R :=
  ((SingularChainComplex R X).sc n).linearDual.homology

/-- The short-complex model computes singular cohomology: the degree-`n` short complex of the
singular cochain complex is the reversed dual of the degree-`n` short complex of the singular
chain complex. -/
def cochainCohomologyEquiv (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R] Cohomology R X n :=
  (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    (SingularChainComplex R X) n)).toLinearEquiv.symm

end AlgebraicTopology.Singular
