import Other.AlgebraicGeometry.HolomorphicDeRhamPullback
import Other.AlgebraicTopology.SheafCohomologyWithSupport

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (f : X ⟶ Y) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom]
  [SmoothOfRelativeDimension e Y.hom]

theorem check_constantsToHolomorphicDeRhamZero_naturality :
    constantsToHolomorphicDeRhamZero Y e ≫
        holomorphicFormPullbackPresheaf X Y f d e 0 =
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (constantsToHolomorphicDeRhamZero X d) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact holomorphicFormPullback_ofConstant X Y f d e U c

theorem check_constantsToHolomorphicDeRhamZeroSheaf_naturality :
    constantsToHolomorphicDeRhamZeroSheaf Y e ≫
        holomorphicFormPullbackSheaf X Y f d e 0 =
      TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
          (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticMapTopCat X Y f)).map
            (constantsToHolomorphicDeRhamZeroSheaf X d) := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact (((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticMapTopCat X Y f)).obj
        (holomorphicDeRhamSheaf X d 0)).property)
  change toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (constantComplexAddCommGrpPresheaf Y) ≫
      (constantsToHolomorphicDeRhamZeroSheaf Y e).hom ≫
      (holomorphicFormPullbackSheaf X Y f d e 0).hom =
    toSheafify
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint Y)))
        (constantComplexAddCommGrpPresheaf Y) ≫
      (TopCat.Sheaf.constantRestriction (analyticMapTopCat X Y f)
        (AddCommGrpCat.of ℂ)).hom ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        ((constantsToHolomorphicDeRhamZeroSheaf X d).hom)
  dsimp only [constantsToHolomorphicDeRhamZeroSheaf]
  dsimp only [constantComplexAddCommGrpPresheaf]
  rw [← Category.assoc, ← toSheafify_naturality,
    Category.assoc, toSheafify_comp_holomorphicFormPullbackSheaf]
  have hconst := congrArg (fun k ↦ k ≫
      Functor.whiskerLeft (Opens.map (analyticMapTopCat X Y f)).op
        (((presheafToSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          AddCommGrpCat).map
            (constantsToHolomorphicDeRhamZero X d)).hom))
    (TopCat.Sheaf.toSheafify_constantRestriction
      (analyticMapTopCat X Y f) (AddCommGrpCat.of ℂ))
  conv_rhs => rw [← Category.assoc]
  rw [hconst]
  unfold holomorphicFormPullbackToPushforwardPresheaf
  rw [← Category.assoc,
    check_constantsToHolomorphicDeRhamZero_naturality X Y f d e]
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp]
  rw [toSheafify_naturality]
  rfl

end AlgebraicGeometry.ComplexPoint
