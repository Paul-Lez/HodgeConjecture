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

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Constructions used only in proofs

These were built to prove the results about the definitions in
`HodgeConjecture.Definitions.Algebra.Homology.LinearDual`.
The statement of the conjecture never inspects them: every path from the statement to one
of them runs through a proof, so proof irrelevance makes their bodies immaterial.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u


namespace HomologicalComplex

variable {R : Type u} [Field R]

attribute [simp] HomologicalComplex.linearDualCochainComplex_X

attribute [local implicit_reducible] shortComplexFunctor' shortComplexFunctor

variable {K L M : ChainComplex (ModuleCat.{u} R) ℕ}

lemma ModuleCat.ofHom_sub.{v} {R : Type*} [Ring R] {M N : Type v} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N) :
    ModuleCat.ofHom (f - g) = ModuleCat.ofHom f - ModuleCat.ofHom g := rfl

open Homotopy in
/-- Algebraic duality sends a chain homotopy contravariantly to a cochain homotopy. -/
def linearDualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (linearDualMap f) (linearDualMap g) where
  hom i j := ModuleCat.ofHom (h.hom j i).hom.dualMap
  zero i j hij := by simp [h.zero j i hij]
  comm i := by
    cases i with
    | zero =>
      rw [dNext_cochainComplex, prevD_zero_cochainComplex, linearDualCochainComplex_d_succ]
      have h' : f.f 0 - g.f 0 = h.hom 0 1 ≫ L.d 1 0 := by
        simpa [dNext_zero_chainComplex _, prevD_chainComplex _, ← sub_eq_iff_eq_add] using h.comm 0
      simp [← ModuleCat.ofHom_comp, LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, ← h',
        LinearMap.dualMap_sub, ModuleCat.ofHom_sub]
    | succ n =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        have h': f.f (n + 1) - g.f (n + 1) = h.hom (n + 1) (n + 1 + 1) ≫
            L.d (n + 1 + 1) (n + 1) + K.d (n + 1) n ≫ h.hom n (n + 1) := by
          simpa [dNext_succ_chainComplex _, prevD_chainComplex _, ← sub_eq_iff_eq_add,
            add_comm (K.d _ _ ≫ _)] using h.comm (n + 1)
        simp [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_add, LinearMap.dualMap_comp_dualMap,
          ← ModuleCat.hom_comp, ← LinearMap.dualMap_add, ← ModuleCat.hom_add, ← h']

/-- Algebraic duality sends a chain-homotopy equivalence contravariantly to a cochain-homotopy
equivalence. -/
def linearDualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv L.linearDualCochainComplex K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (linearDualMap_comp e.inv e.hom).symm).trans <|
      (linearDualHomotopy e.homotopyInvHomId).trans <|
        Homotopy.ofEq (linearDualMap_id L)
  homotopyInvHomId :=
    (Homotopy.ofEq (linearDualMap_comp e.hom e.inv).symm).trans <|
      (linearDualHomotopy e.homotopyHomInvId).trans <|
        Homotopy.ofEq (linearDualMap_id K)

end HomologicalComplex

