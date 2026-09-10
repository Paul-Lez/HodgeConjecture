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

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences and singular homology

Mathlib knows that homotopic maps induce homotopic maps on singular chains
(`TopCat.Homotopy.singularChainComplexFunctorObjMap`). This file packages the immediate
consequence for a homotopy *equivalence*, in a form polymorphic in the coefficient category.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits
open scoped ContinuousMap

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological homotopy equivalence induces a homotopy equivalence of singular chain
complexes, with coefficients in an arbitrary object of `C`. -/
noncomputable def singularChainHomotopyEquivOfHomotopyEquiv (R : C) (e : X ≃ₕ Y) :
    HomotopyEquiv (((singularChainComplexFunctor C).obj R).obj (TopCat.of X))
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of Y)) := by
  let F := (singularChainComplexFunctor C).obj R
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have hX : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := Classical.choice e.left_inv
  have hY : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := Classical.choice e.right_inv
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

/-- A topological homotopy equivalence induces an isomorphism on singular homology, with
coefficients in an arbitrary object of `C`. -/
noncomputable def singularHomologyIsoOfHomotopyEquiv [CategoryWithHomology C]
    (R : C) (k : ℕ) (e : X ≃ₕ Y) :
    ((singularHomologyFunctor C k).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C k).obj R).obj (TopCat.of Y) :=
  (singularChainHomotopyEquivOfHomotopyEquiv R e).toHomologyIso k

end AlgebraicTopology
