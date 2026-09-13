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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Chain

/-!
# Chain, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Chain`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
universe u
namespace AlgebraicTopology.Singular
variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- The chain-complex-level identification of stalks before and after sheafification.
This is not yet an identification with the local relative homology at `x`. -/
def singularChainSheafificationStalkIso (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R X) ≅
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X)) := by
  let f := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (singularChainSheafificationUnit R X)
  have : ∀ n, IsIso (f.f n) := fun n ↦
    singularChainSheafificationUnit_stalk_isIso R X x n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

end AlgebraicTopology.Singular
end
