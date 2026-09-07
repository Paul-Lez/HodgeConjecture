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

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Singular chains of maps between contractible spaces

Every specified continuous map between two contractible spaces is the forward map of a
homotopy equivalence. Consequently its singular-chain map is a quasi-isomorphism with an
arbitrary coefficient object in `AddCommGrpCat`.

The proofs are adapted from
[`SphereSixComplex.Topology.ContractibleSingularMapQuasiIso`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/ContractibleSingularMapQuasiIso.lean),
released under the Apache License 2.0. The standard-simplex corollary from that file is omitted:
its source is the separate, large simplicial-to-singular comparison development, which has not
been ported here.
-/

@[expose] public noncomputable section

open CategoryTheory ContinuousMap

namespace AlgebraicTopology

variable {X Y : Type}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Replacing the forward map of a homotopy equivalence by a homotopic continuous map preserves
the homotopy equivalence. -/
def homotopyEquivOfHomotopicTo
    (f : C(X, Y)) (e : X ≃ₕ Y) (h : f.Homotopic e.toFun) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := (ContinuousMap.Homotopic.comp (.refl e.invFun) h).trans e.left_inv
  right_inv := (ContinuousMap.Homotopic.comp h (.refl e.invFun)).trans e.right_inv

/-- Any specified continuous map between contractible spaces is the forward map of a homotopy
equivalence. -/
def homotopyEquivOfMapBetweenContractibleSpaces
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) : X ≃ₕ Y := by
  let e := Classical.choice (ContractibleSpace.hequiv X Y)
  let hnull := id_nullhomotopic Y
  let y := Classical.choose hnull
  let hy := Classical.choose_spec hnull
  have hf : f.Homotopic (ContinuousMap.const X y) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      ContinuousMap.Homotopic.comp hy (.refl f)
  have he : e.toFun.Homotopic (ContinuousMap.const X y) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      ContinuousMap.Homotopic.comp hy (.refl e.toFun)
  exact homotopyEquivOfHomotopicTo f e (hf.trans he.symm)

/-- A topological homotopy equivalence induces a homotopy equivalence between singular chain
complexes with an arbitrary coefficient object in `AddCommGrpCat`. -/
def singularChainHomotopyEquivOfHomotopyEquivAddCommGrp
    (R : AddCommGrpCat) (e : X ≃ₕ Y) :
    HomotopyEquiv
      (((singularChainComplexFunctor AddCommGrpCat).obj R).obj (TopCat.of X))
      (((singularChainComplexFunctor AddCommGrpCat).obj R).obj (TopCat.of Y)) := by
  let F := (singularChainComplexFunctor AddCommGrpCat).obj R
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
      (hX.singularChainComplexFunctorObjMap R |>.trans
        (Homotopy.ofEq (F.map_id (TopCat.of X))))
  · exact (Homotopy.ofEq (F.map_comp g f).symm).trans
      (hY.singularChainComplexFunctorObjMap R |>.trans
        (Homotopy.ofEq (F.map_id (TopCat.of Y))))

/-- Applying singular chains with arbitrary abelian-group coefficients to the forward map of a
homotopy equivalence gives a quasi-isomorphism. -/
theorem singularChainMap_quasiIso_of_homotopyEquiv
    (R : AddCommGrpCat) (e : X ≃ₕ Y) :
    QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R) := by
  let E := singularChainHomotopyEquivOfHomotopyEquivAddCommGrp R e
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (E.toHomologyIso k).hom
  infer_instance

/-- The singular-chain map of any continuous map between contractible spaces is a
quasi-isomorphism with arbitrary abelian-group coefficients. -/
theorem singularChainMap_quasiIso_of_contractibleSpaces
    [ContractibleSpace X] [ContractibleSpace Y]
    (R : AddCommGrpCat) (f : C(X, Y)) :
    QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom f)) R) := by
  exact singularChainMap_quasiIso_of_homotopyEquiv R
    (homotopyEquivOfMapBetweenContractibleSpaces f)

end AlgebraicTopology
