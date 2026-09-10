import Other.AlgebraicTopology.SingularProductCoefficientChange

open CategoryTheory Limits
open AlgebraicTopology
open scoped Simplicial

namespace AlgebraicTopology.Singular

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma homologyMap_homologyClassOfTwoCycle
    (R : Type) [Field R] {X Y : TopCat} (f : X ⟶ Y)
    (c : Simplicial.ChainGroup R (TopCat.toSSet.obj X) 2)
    (hc : Simplicial.boundary R 1 c = 0) :
    homologyMap R 2 f (Simplicial.homologyClassOfTwoCycle R c hc) =
      Simplicial.homologyClassOfTwoCycle R
        (((SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of R R)).f 2).hom c)
        (by
          have h := ConcreteCategory.congr_hom
            ((SSet.chainComplexMap (TopCat.toSSet.map f)
              (ModuleCat.of R R)).comm 2 1) c
          change _ = 0
          rw [show Simplicial.boundary R 1
              (((SSet.chainComplexMap (TopCat.toSSet.map f)
                (ModuleCat.of R R)).f 2).hom c) =
              (((SSet.chainComplexMap (TopCat.toSSet.map f)
                (ModuleCat.of R R)).f 1).hom
                (Simplicial.boundary R 1 c)) by
              simpa only [Simplicial.boundary, ConcreteCategory.comp_apply] using h,
            hc, map_zero]) := by
  let KX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)
  let KY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)
  let F := SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)
  let SX := KX.sc 2
  let SY := KY.sc 2
  have hcX : c ∈ LinearMap.ker SX.g.hom := by
    change (KX.d 2 ((ComplexShape.down ℕ).next 2)).hom c = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    exact hc
  let zX : LinearMap.ker SX.g.hom := ⟨c, hcX⟩
  let cY : Simplicial.ChainGroup R (TopCat.toSSet.obj Y) 2 := (F.f 2).hom c
  have hcY : cY ∈ LinearMap.ker SY.g.hom := by
    change (KY.d 2 ((ComplexShape.down ℕ).next 2)).hom cY = 0
    rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
    have h := ConcreteCategory.congr_hom (F.comm 2 1) c
    have hc' : (KX.d 2 1).hom c = 0 := hc
    change (KY.d 2 1).hom ((F.f 2).hom c) = 0
    rw [show (KY.d 2 1).hom ((F.f 2).hom c) =
        (F.f 1).hom ((KX.d 2 1).hom c) by
      simpa only [ConcreteCategory.comp_apply] using h,
      hc', map_zero]
  let zY : LinearMap.ker SY.g.hom := ⟨cY, hcY⟩
  let SF := (HomologicalComplex.shortComplexFunctor
    (ModuleCat R) (ComplexShape.down ℕ) 2).map F
  have hnat := ShortComplex.moduleCatHomologyClass_naturality SF zX
  change (HomologicalComplex.homologyMap F 2).hom
      (SX.moduleCatHomologyClass zX) = SY.moduleCatHomologyClass zY
  rw [show (HomologicalComplex.homologyMap F 2).hom
      (SX.moduleCatHomologyClass zX) =
        SY.moduleCatHomologyClass (ShortComplex.moduleCatCycleMap SF zX) by
      exact hnat]
  congr 1

local instance coefficientNaturalityModuleHomology (X : TopCat) (n : ℕ) :
    Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance coefficientNaturalityTowerHomology (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

theorem qToCHomology_naturality_degreeTwo {X Y : TopCat} (f : X ⟶ Y)
    (z : Homology ℚ X 2) :
    homologyMap ℂ 2 f (qToCHomology X 2 z) =
      qToCHomology Y 2 (homologyMap ℚ 2 f z) := by
  obtain ⟨c, hc, rfl⟩ := exists_rationalTwoCycleRepresenting X z
  rw [qToCHomology_homologyClassOfTwoCycle]
  rw [homologyMap_homologyClassOfTwoCycle]
  rw [homologyMap_homologyClassOfTwoCycle]
  rw [qToCHomology_homologyClassOfTwoCycle]
  congr 1
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (qToCChainGroup_naturality f 2)) c

theorem rationalToComplexCohomologyMap_naturality_degreeTwo
    {X Y : TopCat} (f : X ⟶ Y) (beta : Cohomology ℚ Y 2) :
    rationalToComplexCohomologyMap X 2 (cohomologyMap ℚ 2 f beta) =
      cohomologyMap ℂ 2 f (rationalToComplexCohomologyMap Y 2 beta) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange X 2).inductionOn w
    (fun w =>
      rationalToComplexCohomologyMap X 2 (cohomologyMap ℚ 2 f beta) w =
        cohomologyMap ℂ 2 f (rationalToComplexCohomologyMap Y 2 beta) w)
  · simp
  · intro z
    rw [cohomologyMap_apply, qToCHomology_naturality_degreeTwo]
    exact ((qToCHomology_isBaseChange X 2).toDual_comp_apply
      (cohomologyMap ℚ 2 f beta) z).trans
        ((qToCHomology_isBaseChange Y 2).toDual_comp_apply beta
          (homologyMap ℚ 2 f z)).symm
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

end

end AlgebraicTopology.Singular
