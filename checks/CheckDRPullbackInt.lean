import Other.AlgebraicGeometry.HolomorphicDeRhamPullback
import Other.Algebra.Homology.MapExtend
import Other.AlgebraicTopology.SingularChainSheafPushforward
import Other.AlgebraicTopology.SheafCohomologyWithSupport

@[expose] noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (f : X ⟶ Y)

def checkComplexConstantRestrictionComplex :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y)))).obj
        (constantComplexSheaf Y) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀
          (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
          (constantComplexSheaf X)) :=
  (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y)))).map
      (TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
        (AddCommGrpCat.of ℂ)) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      (ComplexShape.up ℕ) 0).inv.app (constantComplexSheaf X)

def checkComplexConstantRestrictionComplexInt :
    constantComplexSheafComplexInt Y ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (constantComplexSheafComplexInt X) :=
  HomologicalComplex.extendMap
      (checkComplexConstantRestrictionComplex X Y f)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      ((CochainComplex.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X))
      ComplexShape.embeddingUpNat).inv

def checkHolomorphicDeRhamPullbackComplexInt
    [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] :
    holomorphicDeRhamComplexInt Y ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X Y f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (holomorphicDeRhamComplexInt X) :=
  HomologicalComplex.extendMap
      (holomorphicDeRhamPullbackComplex X Y f (dim X.left) (dim Y.left))
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat (analyticMapTopCat X Y f))
      (holomorphicDeRhamComplex X (dim X.left))
      ComplexShape.embeddingUpNat).inv

theorem checkConstantsToHolomorphicDeRhamComplex_naturality
    (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] :
    constantsToHolomorphicDeRhamComplex Y e ≫
        holomorphicDeRhamPullbackComplex X Y f d e =
      checkComplexConstantRestrictionComplex X Y f ≫
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
          (constantsToHolomorphicDeRhamComplex X d)) := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · change constantsToHolomorphicDeRhamZeroSheaf Y e ≫
        holomorphicFormPullbackSheaf X Y f d e 0 =
      TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
          (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (constantsToHolomorphicDeRhamZeroSheaf X d)
    exact constantsToHolomorphicDeRhamZeroSheaf_naturality X Y f d e
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantComplexSheaf Y) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

theorem checkConstantsToHolomorphicDeRhamComplexInt_naturality
    [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] :
    constantsToHolomorphicDeRhamComplexInt Y ≫
        holomorphicDeRhamPullbackComplexInt X Y f =
      checkComplexConstantRestrictionComplexInt X Y f ≫
        (((TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (constantsToHolomorphicDeRhamComplexInt X)) := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticMapTopCat X Y f)
  let K := (CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
      (constantComplexSheaf X)
  let L := holomorphicDeRhamComplex X (dim X.left)
  let E := ComplexShape.embeddingUpNat
  apply (cancel_mono
    (HomologicalComplex.mapExtendCanonicalIso F L E).hom).1
  dsimp only [checkComplexConstantRestrictionComplexInt,
    checkHolomorphicDeRhamPullbackComplexInt,
    holomorphicDeRhamPullbackComplexInt,
    constantsToHolomorphicDeRhamComplexInt,
    constantComplexSheafComplexInt,
    holomorphicDeRhamComplexInt]
  simp only [F, L, E, Category.assoc, Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.mapExtendCanonicalIso_naturality]
  simp only [Category.comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [← HomologicalComplex.extendMap_comp,
    checkConstantsToHolomorphicDeRhamComplex_naturality]
  rw [HomologicalComplex.extendMap_comp]

end AlgebraicGeometry.ComplexPoint
