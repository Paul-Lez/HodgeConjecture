import Other.AlgebraicGeometry.SheafBorelMoorePointForget

@[expose] noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _
local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

variable [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]

local instance :
    (singularChainSheafCochainComplex ℚ
      (TopCat.of (ComplexPoint X))).IsGE (-((2 * d : ℕ) : ℤ)) :=
  complexChainSheaf_isGE X d

abbrev wholeChainSections : CochainComplex AddCommGrpCat ℤ :=
  ((TopCat.Sheaf.closedSupportSections (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj
      (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))

def wholeChainPointCocycle (x : ComplexPoint X) :
    (HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ) ⟶
      wholeChainSections X :=
  pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x ≫
    (((TopCat.Sheaf.closedSupportSectionsMap
      (TopCat.of (ComplexPoint X))
      (show sheafBorelMoorePointSupport X x ≤
        (⊤ : Closeds (ComplexPoint X)) from le_top)).mapHomologicalComplex
          (.up ℤ)).app
      (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X))))

def derivedAugmentationOfWholeChains
    (a : wholeChainSections X ⟶
      (HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ))
    [IsIso (TopCat.Sheaf.termwiseToDerivedClosedSupport
      (TopCat.of (ComplexPoint X))
      (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
      (-((2 * d : ℕ) : ℤ)) ⊤)] :
    complexAmbientSheafBorelMooreObject X d ⊤ ⟶
      (DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ) :=
  DerivedCategory.Plus.ι.preimage
    (inv (TopCat.Sheaf.termwiseToDerivedClosedSupport
      (TopCat.of (ComplexPoint X))
      (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
      (-((2 * d : ℕ) : ℤ)) ⊤) ≫ DerivedCategory.Q.map a)

theorem point_comp_derivedAugmentationOfWholeChains
    (x : ComplexPoint X)
    (a : wholeChainSections X ⟶
      (HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ))
    [IsIso (TopCat.Sheaf.termwiseToDerivedClosedSupport
      (TopCat.of (ComplexPoint X))
      (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
      (-((2 * d : ℕ) : ℤ)) ⊤)]
    (ha : wholeChainPointCocycle X x ≫ a = 𝟙 _) :
    sheafBorelMoorePointTopMorphism X d x ≫
      derivedAugmentationOfWholeChains X d a = 𝟙 _ := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp, sheafBorelMoorePointTopMorphism_underlying]
  simp only [derivedAugmentationOfWholeChains, Functor.map_preimage, Category.assoc,
    IsIso.hom_inv_id_assoc]
  have hqa := congrArg DerivedCategory.Q.map ha
  dsimp only [wholeChainPointCocycle] at hqa
  simp only [Functor.map_comp, Category.assoc] at hqa
  erw [hqa]
  calc
    _ = 𝟙 (DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj
          (AddCommGrpCat.of ℚ))) := DerivedCategory.Q.map_id _
    _ = 𝟙 (DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj
          (AddCommGrpCat.of ℚ))) := by rfl
    _ = _ := (DerivedCategory.Plus.ι.map_id _).symm

end AlgebraicGeometry.ComplexPoint
