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

public import HodgeConjecture.Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Singular chains of contractible spaces

A topological homotopy equivalence induces a homotopy equivalence of singular chain complexes.
Consequently, the singular chain complex of a contractible space is exact in every positive
degree. The comparison with a point uses Mathlib's explicit calculation for totally disconnected
spaces.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u

namespace AlgebraicTopology

variable (R : Type u) [Field R]

/-- The singular chain complex of a contractible space is homotopy equivalent to that of a
point. -/
def contractibleSingularChainHomotopyEquiv
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (TopCat.of X))
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (TopCat.of (ULift.{u} Unit))) := by
  let e : X ≃ₕ ULift.{u} Unit :=
    (Classical.choice (ContractibleSpace.hequiv_unit X)).trans
      (Homeomorph.ulift.{u, 0}.symm.toHomotopyEquiv)
  exact singularChainHomotopyEquivOfHomotopyEquiv (ModuleCat.of R R) e

/-- Positive-degree singular chains of a contractible space are exact. -/
lemma singularChainComplex_exactAt_of_contractible
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) :
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
      (TopCat.of X)).ExactAt n := by
  let e := contractibleSingularChainHomotopyEquiv R X
  rw [exactAt_iff_of_quasiIsoAt e.hom n]
  exact singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (ModuleCat.{u} R) n (ModuleCat.of R R) (TopCat.of (ULift.{u} Unit)) hn

end AlgebraicTopology
