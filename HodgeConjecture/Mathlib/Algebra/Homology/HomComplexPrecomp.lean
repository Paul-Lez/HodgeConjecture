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
public import HodgeConjecture.Mathlib.Algebra.Homology.HomComplexSingle

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Precomposition on the Hom complex

For a chain map `g : K' → K`, precomposition `Hom^•(K, L) → Hom^•(K', L)` is a map of complexes.
It induces a map on cohomology classes that matches the map on homology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  {K K' : CochainComplex C ℤ} (g : K' ⟶ K) (L : CochainComplex C ℤ)

/-- Precomposition with a chain map, on the Hom complex. -/
def precompMap : HomComplex K L ⟶ HomComplex K' L where
  f n := AddCommGrpCat.ofHom
    { toFun z := (Cochain.ofHom g).comp z (zero_add n)
      map_zero' := by simp
      map_add' _ _ := Cochain.comp_add _ _ _ _ }
  comm' n m _ := by
    ext z
    exact δ_ofHom_comp g z m

/-- Precomposition with a chain map, on cocycles. -/
def precompCocycle (n : ℤ) : Cocycle K L n →+ Cocycle K' L n where
  toFun z := z.precomp g
  map_zero' := by ext; simp [Cocycle.precomp]
  map_add' x y := by ext; simp [Cocycle.precomp, Cochain.comp_add]

/-- Precomposition with a chain map, on cohomology classes. -/
def precompClass (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K' L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L n).comp (precompCocycle g L n)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.precomp g) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, (Cochain.ofHom g).comp a (zero_add m), ?_⟩
      rw [δ_ofHom_comp, ha]
      rfl)

@[simp]
lemma precompClass_mk (n : ℤ) (z : Cocycle K L n) :
    precompClass g L n (CohomologyClass.mk z) = CohomologyClass.mk (z.precomp g) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocycle and cohomology-class maps of precomposition describe its homology map. -/
def precompLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map (precompMap g L))
      (leftHomologyData K L n) (leftHomologyData K' L n) where
  φK := AddCommGrpCat.ofHom (precompCocycle g L n)
  φH := AddCommGrpCat.ofHom (precompClass g L n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K' L n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (precompCocycle g L n) ≫ (leftHomologyData K' L n).i =
        (leftHomologyData K L n).i ≫ (precompMap g L).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map
      (precompMap g L)).comm₁₂.symm
  commπ := rfl

lemma homologyAddEquiv_precompMap (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K' L n (HomologicalComplex.homologyMap (precompMap g L) n x) =
      precompClass g L n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (precompLeftHomologyMapData g L n).homologyMap_comm x

variable [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with `g[0]` on `Hom^•(X[0], K)` is precomposition with `g` on `n ↦ Hom(X, K^n)`. -/
lemma precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda {X X' : C} (g : X' ⟶ X)
    (K : CochainComplex C ℤ) :
    precompMap ((CochainComplex.singleFunctor C 0).map g) K ≫
        (fromSingleZeroIsoPreadditiveCoyoneda X' K).hom =
      (fromSingleZeroIsoPreadditiveCoyoneda X K).hom ≫
        (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) ℤᵘᵖ).app K := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext (fun z => ?_)
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
      ((Cochain.ofHom ((CochainComplex.singleFunctor C 0).map g)).comp
        (Cochain.fromSingleMk f (zero_add n)) (zero_add n)) =
    g ≫ Cochain.fromSingleEquiv (zero_add n) (Cochain.fromSingleMk f (zero_add n))
  rw [← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

end CochainComplex.HomComplex

end
