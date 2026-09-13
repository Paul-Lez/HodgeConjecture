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

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import HodgeConjecture.Lemmas.Algebra.Homology.HomComplexPostcompNaturality

/-!
# HomComplexPostcompNaturality, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.Algebra.Homology.HomComplexPostcompNaturality`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.HomComplex
variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ} (f : L ⟶ M)

/-- Postcomposition by an actual chain map, on the entire Hom complex. -/
def postcompMap : HomComplex K L ⟶ HomComplex K M where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' _ _ := Cochain.add_comp _ _ _ _ }
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z f m

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit cycles and cohomology-class maps describe the homology map
of postcomposition. -/
def postcompLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (postcompMap K f)) (leftHomologyData K L n) (leftHomologyData K M n) where
  φK := AddCommGrpCat.ofHom (postcompCocycle K f n)
  φH := AddCommGrpCat.ofHom (postcompClass K f n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K M n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (postcompCocycle K f n) ≫ (leftHomologyData K M n).i =
        (leftHomologyData K L n).i ≫ (postcompMap K f).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
      (postcompMap K f)).comm₁₂.symm
  commπ := rfl

/-- The Hom-complex homology/cohomology-class equivalence is natural under
postcomposition by a chain map. -/
lemma homologyAddEquiv_postcompMap (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K M n (HomologicalComplex.homologyMap (postcompMap K f) n x) =
      postcompClass K f n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (postcompLeftHomologyMapData K f n).homologyMap_comm x

end CochainComplex.HomComplex
end
