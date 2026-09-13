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

public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDual
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Singular chains of contractible spaces

A topological homotopy equivalence induces a homotopy equivalence of singular chain complexes.
Consequently, the singular chain complex of a contractible space is exact in every positive
degree, and so — because a chain homotopy equivalence dualises — is the singular *cochain*
complex. The cochain statement is the one that matters for sheaf-theoretic comparisons, and
deducing it from the homotopy equivalence rather than from exactness of the chain complex is what
makes it hold over an arbitrary commutative ring: exactness alone does not survive dualisation
over a ring.

The comparison with a point uses Mathlib's explicit calculation for totally disconnected
spaces.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u

namespace AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- A topological homotopy equivalence induces a homotopy equivalence of singular chain
complexes. -/
def singularChainHomotopyEquivOfHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (TopCat.of X))
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (TopCat.of Y)) := by
  let F := (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have hX : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) :=
    Classical.choice e.left_inv
  have hY : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) :=
    Classical.choice e.right_inv
  refine
    { hom := F.map f
      inv := F.map g
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · exact (Homotopy.ofEq (F.map_comp f g).symm).trans
      ((hX.singularChainComplexFunctorObjMap (ModuleCat.of R R)).trans
        (Homotopy.ofEq (F.map_id (TopCat.of X))))
  · exact (Homotopy.ofEq (F.map_comp g f).symm).trans
      ((hY.singularChainComplexFunctorObjMap (ModuleCat.of R R)).trans
        (Homotopy.ofEq (F.map_id (TopCat.of Y))))

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
  exact singularChainHomotopyEquivOfHomotopyEquiv R e

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

/-- Positive-degree singular cochains of a contractible space are exact.

Dualising the homotopy equivalence with a point, rather than dualising exactness of the chain
complex, keeps this true over an arbitrary commutative ring. -/
lemma singularCochainComplex_exactAt_of_contractible
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    HomologicalComplex.ExactAt
      ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (TopCat.of X)).linearDualCochainComplex) (n + 1) := by
  -- `C_*(X)` is chain homotopy equivalent to the coefficients placed in degree zero: contract
  -- `X` to a point, then use Mathlib's calculation of the chains of a totally disconnected space.
  let e := HomologicalComplex.linearDualHomotopyEquiv
    ((contractibleSingularChainHomotopyEquiv R X).trans <|
      (HomotopyEquiv.ofIso (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{u} R) (ModuleCat.of R R) (TopCat.of (ULift.{u} Unit)))).trans
        (ChainComplex.alternatingConstHomotopyEquiv _))
  rw [← exactAt_iff_of_quasiIsoAt e.hom (n + 1)]
  refine HomologicalComplex.ExactAt.of_isZero ?_
  have h := HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
    (∐ fun _ : TopCat.of (ULift.{u} Unit) => ModuleCat.of R R) (n + 1) (by simp)
  have : Subsingleton
      (((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (∐ fun _ : TopCat.of (ULift.{u} Unit) => ModuleCat.of R R)).X (n + 1)) :=
    ModuleCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_of_subsingleton (M := ModuleCat.of R (Module.Dual R _))

/-- Exactness of the singular cochain complex of a contractible space, in the concrete form that
every closed cochain in positive degree is a coboundary. -/
lemma singularChain_dual_range_eq_ker_of_contractible
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    LinearMap.range
        ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
          (TopCat.of X)).d (n + 1) n).hom.dualMap =
      LinearMap.ker
        ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
          (TopCat.of X)).d (n + 2) (n + 1)).hom.dualMap := by
  have h := singularCochainComplex_exactAt_of_contractible R X n
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at h
  exact h.moduleCat_range_eq_ker

end AlgebraicTopology
