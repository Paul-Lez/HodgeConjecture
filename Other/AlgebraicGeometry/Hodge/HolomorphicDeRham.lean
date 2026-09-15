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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.HolomorphicDeRham
import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify
import HodgeConjecture.Mathlib.Topology.Sheaves.StalkExact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# HolomorphicDeRham, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold
namespace AlgebraicGeometry.ComplexPoint
open Point
variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Conjugating twice is the identity on the constant complex presheaf. -/
lemma conjConstantComplexPresheaf_comp_self :
    conjConstantComplexPresheaf X ≫ conjConstantComplexPresheaf X =
      𝟙 (constantComplexAddCommGrpPresheaf X) := by
  ext U : 2
  change (starRingEnd ℂ).toAddMonoidHom.comp (starRingEnd ℂ).toAddMonoidHom = AddMonoidHom.id ℂ
  exact AddMonoidHom.ext Complex.conj_conj

/-- Conjugating twice is the identity on the constant complex sheaf. -/
lemma conjConstantComplexSheaf_comp_self :
    conjConstantComplexSheaf X ≫ conjConstantComplexSheaf X =
      𝟙 𝓒(↧(ComplexPoint X); ℂ) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) ≫
    (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) = _
  rw [← Functor.map_comp, conjConstantComplexPresheaf_comp_self]
  exact (presheafToSheaf J AddCommGrpCat).map_id _

/-- Conjugating twice is the identity in degree zero. -/
lemma conjConstantComplexComplex_comp_self :
    conjConstantComplexComplex X ≫ conjConstantComplexComplex X = 𝟙 _ := by
  unfold conjConstantComplexComplex
  rw [← Functor.map_comp, conjConstantComplexSheaf_comp_self]
  exact (CochainComplex.single₀ _).map_id _

/-- Conjugating twice is the identity on the integer-indexed constant complex. -/
lemma conjConstantComplexSheafComplexInt_comp_self :
    conjConstantComplexSheafComplexInt X ≫ conjConstantComplexSheafComplexInt X = 𝟙 _ := by
  change (((CochainComplex.Plus.single₀ _).map (conjConstantComplexSheaf X) ≫
      (CochainComplex.Plus.single₀ _).map (conjConstantComplexSheaf X))).hom =
    𝟙 (constantComplexSheafComplexInt X)
  rw [← Functor.map_comp, conjConstantComplexSheaf_comp_self]
  exact congrArg (fun f ↦ f.hom)
    ((CochainComplex.Plus.single₀ _).map_id 𝓒(↧(ComplexPoint X); ℂ))

end AlgebraicGeometry.ComplexPoint
end
