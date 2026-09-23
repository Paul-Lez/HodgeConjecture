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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Restriction of singular cochains through direct image

For an open embedding `j : U → X`, restriction of singular cochains from `X` to `U` is a map of
cochain complexes of sheaves `C^•_X → j_* C^•_U`, natural with respect to sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory Filter TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] {U X : TopCat.{u}} (j : U ⟶ X)

def preimageOpenToOpen (V : Opens X) :
    (Opens.toTopCat U).obj ((Opens.map j).obj V) ⟶ (Opens.toTopCat X).obj V :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨j x.1, x.2⟩,
      Continuous.subtype_mk (j.hom.continuous.comp continuous_subtype_val) _⟩

noncomputable def preimageOpenChainMap (V : Opens X) :
    (openSingularChainComplexFunctor R U).obj ((Opens.map j).obj V) ⟶
      (openSingularChainComplexFunctor R X).obj V :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map (preimageOpenToOpen j V)

lemma preimageOpenChainMap_naturality {V W : Opens X} (i : V ⟶ W) :
    (openSingularChainComplexFunctor R U).map ((Opens.map j).map i) ≫
        preimageOpenChainMap R j W =
      preimageOpenChainMap R j V ≫ (openSingularChainComplexFunctor R X).map i := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  change F.map ((Opens.toTopCat U).map ((Opens.map j).map i)) ≫
      F.map (preimageOpenToOpen j W) =
    F.map (preimageOpenToOpen j V) ≫ F.map ((Opens.toTopCat X).map i)
  rw [← F.map_comp, ← F.map_comp]
  congr 1

noncomputable def singularRestrictionToRawPushforward (n : ℕ) :
    singularCochainPresheaf R X n ⟶
      (Opens.map j).op ⋙ singularCochainPresheaf R U n where
  app V := AddCommGrpCat.ofHom
    ((preimageOpenChainMap R j V.unop).f n).hom.dualMap.toAddMonoidHom
  naturality {V W} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change OpenCochains R X V n at φ
    apply LinearMap.ext
    intro c
    change φ
        (((((openSingularChainComplexFunctor R X).map i.unop).f n).hom)
          (((preimageOpenChainMap R j W.unop).f n).hom c)) =
      φ
        ((((preimageOpenChainMap R j V.unop).f n).hom)
          ((((openSingularChainComplexFunctor R U).map
            ((Opens.map j).map i.unop)).f n).hom c))
    exact congrArg φ (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f n) (preimageOpenChainMap_naturality R j i.unop)).symm c)

noncomputable def singularRestrictionPresheaf (n : ℕ) :
    singularCochainPresheaf R X n ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U n)).obj :=
  singularRestrictionToRawPushforward R j n ≫
    Functor.whiskerLeft (Opens.map j).op
      (toSheafify (Opens.grothendieckTopology U) (singularCochainPresheaf R U n))

noncomputable def singularRestrictionSheaf (n : ℕ) :
    singularCochainSheaf R X n ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U n) :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (singularCochainSheaf R U n)).property⟩

lemma toSheafify_comp_singularRestrictionSheaf (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf R X n) ≫
      (singularRestrictionSheaf R j n).hom =
        singularRestrictionPresheaf R j n :=
  toSheafify_sheafifyLift (J := Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (singularCochainSheaf R U n)).property)

lemma singularRestrictionToRawPushforward_coboundary (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularRestrictionToRawPushforward R j (n + 1) =
      singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op (singularCochainCoboundary R U n) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains R X V n at φ
  apply LinearMap.ext
  intro c
  exact congrArg φ (ConcreteCategory.congr_hom
    ((preimageOpenChainMap R j V.unop).comm (n + 1) n) c)

set_option backward.isDefEq.respectTransparency false in
lemma singularRestrictionPresheaf_coboundary (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularRestrictionPresheaf R j (n + 1) =
      singularRestrictionPresheaf R j n ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
          (singularCochainSheafCoboundary R U n)).hom := by
  change singularCochainCoboundary R X n ≫
        singularRestrictionToRawPushforward R j (n + 1) ≫
          Functor.whiskerLeft (Opens.map j).op
            (toSheafify (Opens.grothendieckTopology U)
              (singularCochainPresheaf R U (n + 1))) =
    singularRestrictionToRawPushforward R j n ≫
      Functor.whiskerLeft (Opens.map j).op
        (toSheafify (Opens.grothendieckTopology U)
          (singularCochainPresheaf R U n)) ≫
      Functor.whiskerLeft (Opens.map j).op
        ((singularCochainSheafCoboundary R U n).hom)
  calc
    _ = (singularCochainCoboundary R X n ≫
          singularRestrictionToRawPushforward R j (n + 1)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U (n + 1))) := (Category.assoc _ _ _).symm
    _ = (singularRestrictionToRawPushforward R j n ≫
          Functor.whiskerLeft (Opens.map j).op
            (singularCochainCoboundary R U n)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U (n + 1))) := by
      rw [singularRestrictionToRawPushforward_coboundary]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (singularCochainCoboundary R U n ≫
            toSheafify (Opens.grothendieckTopology U)
              (singularCochainPresheaf R U (n + 1))) := by
      rw [Category.assoc, Functor.whiskerLeft_comp]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U n) ≫
              (singularCochainSheafCoboundary R U n).hom) := by
      rw [toSheafify_naturality]
      rfl
    _ = _ := by
      rw [Functor.whiskerLeft_comp]

noncomputable def singularRestrictionSheafComplex :
    singularCochainSheafComplex R X ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (singularCochainSheafComplex R U) where
  f n := singularRestrictionSheaf R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [singularCochainSheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      singularCochainSheafComplex_d]
    apply Sheaf.hom_ext
    let η := singularCochainCoboundary R X i ≫
      singularRestrictionPresheaf R j (i + 1)
    apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
      (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U (i + 1))).property) _ ?_).trans
    · apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
        (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
          (singularCochainSheaf R U (i + 1))).property) _ ?_).symm
      unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X i) ≫
          (singularCochainSheafCoboundary R X i).hom ≫
          (singularRestrictionSheaf R j (i + 1)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X i) ≫
              (singularCochainSheafCoboundary R X i).hom) ≫
            (singularRestrictionSheaf R j (i + 1)).hom :=
          (Category.assoc _ _ _).symm
        _ = (singularCochainCoboundary R X i ≫
              toSheafify (Opens.grothendieckTopology X)
                (singularCochainPresheaf R X (i + 1))) ≫
            (singularRestrictionSheaf R j (i + 1)).hom := by
          rw [toSheafify_naturality]
          rfl
        _ = singularCochainCoboundary R X i ≫
            (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X (i + 1)) ≫
              (singularRestrictionSheaf R j (i + 1)).hom) :=
          Category.assoc _ _ _
        _ = _ := by rw [toSheafify_comp_singularRestrictionSheaf]
    · unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X i) ≫
          (singularRestrictionSheaf R j i).hom ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
            (singularCochainSheafCoboundary R U i)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X i) ≫
              (singularRestrictionSheaf R j i).hom) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (singularCochainSheafCoboundary R U i)).hom :=
          (Category.assoc _ _ _).symm
        _ = singularRestrictionPresheaf R j i ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (singularCochainSheafCoboundary R U i)).hom := by
          rw [toSheafify_comp_singularRestrictionSheaf]
        _ = _ := (singularRestrictionPresheaf_coboundary R j i).symm

end AlgebraicTopology.Singular

end
