import Other.AlgebraicTopology.SingularCochainCoefficientBaseChange

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

#check HomologicalComplex.homologyMap_comp
#check ShortComplex.mapHomologyIso_hom_naturality
#check HomologicalComplex.shortComplexFunctor
#check Functor.mapHomologicalComplex
#check SSet.chainComplexMap
#check restrictedCChainsHomologyIso
#check qToCChainGroup_naturality

def testQMap {X Y : TopCat} (f : X ⟶ Y) : QChains X ⟶ QChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)

def testCMap {X Y : TopCat} (f : X ⟶ Y) : CChains X ⟶ CChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)

def testRestrictedCMap {X Y : TopCat} (f : X ⟶ Y) :
    RestrictedCChains X ⟶ RestrictedCChains Y :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (testCMap f)

theorem test_qToCChainMap_naturality {X Y : TopCat} (f : X ⟶ Y) :
    qToCChainMap X ≫ testRestrictedCMap f =
      testQMap f ≫ qToCChainMap Y := by
  ext n
  exact ConcreteCategory.congr_hom (qToCChainGroup_naturality f n) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_restrictedCChainsHomologyIso_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (testRestrictedCMap f) n ≫
        (restrictedCChainsHomologyIso Y n).hom =
      (restrictedCChainsHomologyIso X n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (HomologicalComplex.homologyMap (testCMap f) n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℂ)
      (ComplexShape.down ℕ) n).map (testCMap f))
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_qToCHomology_naturality_hom
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom (qToCHomology X n) ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (HomologicalComplex.homologyMap (testCMap f) n) =
      HomologicalComplex.homologyMap (testQMap f) n ≫
        ModuleCat.ofHom (qToCHomology Y n) := by
  change (HomologicalComplex.homologyMap (qToCChainMap X) n ≫
      (restrictedCChainsHomologyIso X n).hom) ≫ _ =
    _ ≫ (HomologicalComplex.homologyMap (qToCChainMap Y) n ≫
      (restrictedCChainsHomologyIso Y n).hom)
  rw [Category.assoc, ← test_restrictedCChainsHomologyIso_naturality f n]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
  rw [test_qToCChainMap_naturality f]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_qToCHomology_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (z : Homology ℚ X n) :
    homologyMap ℂ n f (qToCHomology X n z) =
      qToCHomology Y n (homologyMap ℚ n f z) := by
  exact ConcreteCategory.congr_hom (test_qToCHomology_naturality_hom f n) z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem test_rationalToComplexCohomologyMap_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (beta : Cohomology ℚ Y n) :
    rationalToComplexCohomologyMap X n (cohomologyMap ℚ n f beta) =
      cohomologyMap ℂ n f (rationalToComplexCohomologyMap Y n beta) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange X n).inductionOn w
    (fun w =>
      rationalToComplexCohomologyMap X n (cohomologyMap ℚ n f beta) w =
        cohomologyMap ℂ n f (rationalToComplexCohomologyMap Y n beta) w)
  · simp
  · intro z
    rw [cohomologyMap_apply, test_qToCHomology_naturality]
    exact ((qToCHomology_isBaseChange X n).toDual_comp_apply
      (cohomologyMap ℚ n f beta) z).trans
        ((qToCHomology_isBaseChange Y n).toDual_comp_apply beta
          (homologyMap ℚ n f z)).symm
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

end AlgebraicTopology.Singular
