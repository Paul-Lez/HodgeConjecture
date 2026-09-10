import Other.AlgebraicTopology.SingularProductDegreeOne
import Mathlib.Topology.Category.TopCat.Limits.Products

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

#check Limits.prodComparison
#check CartesianMonoidalCategory.prodComparisonIso
#check TopCat.prodIsoProd
#check TopCat.prodIsoProd_hom_apply
#check TopCat.prodIsoProd_inv_fst
#check TopCat.toSSet

example (X Y : TopCat.{u}) : IsIso (prodComparison TopCat.toSSet X Y) := by
  infer_instance

noncomputable example (X Y : TopCat.{u}) :
    TopCat.toSSet.obj (X ⨯ Y) ≅
      (TopCat.toSSet.obj X ⨯ TopCat.toSSet.obj Y) :=
  asIso (prodComparison TopCat.toSSet X Y)

-- Does the categorical SSet product reduce to its cartesian monoidal product?
noncomputable example (X Y : TopCat.{u}) :
    TopCat.toSSet.obj (X ⊗ Y) ≅
      (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) :=
  CartesianMonoidalCategory.prodComparisonIso TopCat.toSSet X Y

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

noncomputable def testComparison (X Y : TopCat.{u}) :
    TopCat.toSSet.obj (X ⊗ Y) ≅
      (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) :=
  CartesianMonoidalCategory.prodComparisonIso TopCat.toSSet X Y

noncomputable def testShuffle {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1) :
    Simplicial.ChainGroup R (TopCat.toSSet.obj (X ⊗ Y)) 2 :=
  ((SSet.chainComplexMap (testComparison X Y).inv (ModuleCat.of R R)).f 2).hom
    (Simplicial.degreeOneShuffle R c d)

lemma testShuffle_boundary {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0) :
    Simplicial.boundary R 1 (testShuffle R c d) = 0 := by
  let e := testComparison X Y
  let F := SSet.chainComplexMap e.inv (ModuleCat.of R R)
  have hz := Simplicial.boundary_degreeOneShuffle_eq_zero R c d hc hd
  have hcomm := ConcreteCategory.congr_hom (F.comm 2 1)
    (Simplicial.degreeOneShuffle R c d)
  change Simplicial.boundary R 1 (testShuffle R c d) = 0
  change (((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
      (ModuleCat.of R R)).d 2 1).hom
        ((F.f 2).hom (Simplicial.degreeOneShuffle R c d)) = 0
  have hcomm' :
      (((TopCat.toSSet.obj (X ⊗ Y)).chainComplex
          (ModuleCat.of R R)).d 2 1).hom
          ((F.f 2).hom (Simplicial.degreeOneShuffle R c d)) =
        (F.f 1).hom (Simplicial.boundary R 1
          (Simplicial.degreeOneShuffle R c d)) := by
    simpa only [ConcreteCategory.comp_apply, Simplicial.boundary] using hcomm
  rw [hcomm', hz, map_zero]

noncomputable def testExternal {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1) :
    Simplicial.Cochain R (TopCat.toSSet.obj (X ⊗ Y)) 2 :=
  Simplicial.cochainMap R (testComparison X Y).hom 2
    (Simplicial.degreeOneExternalCochain R phi psi)

lemma testExternal_shuffle {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1) :
    testExternal R phi psi (testShuffle R c d) = phi c * psi d := by
  rw [testExternal, Simplicial.cochainMap_apply, testShuffle]
  have hi :
      ((SSet.chainComplexMap (testComparison X Y).hom (ModuleCat.of R R)).f 2).hom
          (((SSet.chainComplexMap (testComparison X Y).inv (ModuleCat.of R R)).f 2).hom
            (Simplicial.degreeOneShuffle R c d)) =
        Simplicial.degreeOneShuffle R c d := by
    let G := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
    have hmaps : G.map (testComparison X Y).inv ≫ G.map (testComparison X Y).hom =
        𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id]
      exact G.map_id _
    have hcomponent := congrArg (fun f => f.f 2) hmaps
    have happ := ConcreteCategory.congr_hom hcomponent
      (Simplicial.degreeOneShuffle R c d)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ConcreteCategory.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_id,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using happ
  rw [hi]
  exact Simplicial.degreeOneExternalCochain_shuffle R phi psi hphi hpsi c d

lemma testExternal_cocycle {X Y : TopCat.{u}}
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0) :
    Simplicial.coboundary R 2 (testExternal R phi psi) = 0 := by
  rw [testExternal, Simplicial.coboundary_cochainMap,
    Simplicial.coboundary_degreeOneExternalCochain R phi psi hphi hpsi,
    map_zero]

noncomputable def testShuffleHomologyClass {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0) :
    Homology R (X ⊗ Y) 2 :=
  Simplicial.homologyClassOfTwoCycle R (testShuffle R c d)
    (testShuffle_boundary R c d hc hd)

theorem testShuffleHomologyClass_ne_zero {X Y : TopCat.{u}}
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 1)
    (d : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 1)
    (hc : Simplicial.boundary R 0 c = 0)
    (hd : Simplicial.boundary R 0 d = 0)
    (phi : Simplicial.Cochain R (TopCat.toSSet.obj X) 1)
    (psi : Simplicial.Cochain R (TopCat.toSSet.obj Y) 1)
    (hphi : Simplicial.coboundary R 1 phi = 0)
    (hpsi : Simplicial.coboundary R 1 psi = 0)
    (hphi_eval : phi c ≠ 0) (hpsi_eval : psi d ≠ 0) :
    testShuffleHomologyClass R c d hc hd ≠ 0 := by
  apply Simplicial.homologyClassOfTwoCycle_ne_zero R
    (testShuffle R c d)
    (testShuffle_boundary R c d hc hd)
    (testExternal R phi psi)
    (testExternal_cocycle R phi psi hphi hpsi)
  rw [testExternal_shuffle R phi psi hphi hpsi c d]
  exact mul_ne_zero hphi_eval hpsi_eval

end AlgebraicTopology.Singular
