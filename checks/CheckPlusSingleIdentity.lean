import Other.AlgebraicGeometry.SheafBorelMoorePointForget

@[expose] noncomputable section
open CategoryTheory

local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
example :
    DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ)) =
      DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
example :
    (𝟙 (DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ)))) =
      𝟙 (DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
example :
    DerivedCategory.Q.map
        (𝟙 ((HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj (AddCommGrpCat.of ℚ))) =
      DerivedCategory.Plus.ι.map
        (𝟙 ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ))) := by
  calc
    _ = 𝟙 (DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat (.up ℤ) 0).obj
          (AddCommGrpCat.of ℚ))) := DerivedCategory.Q.map_id _
    _ = 𝟙 (DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj
          (AddCommGrpCat.of ℚ))) := by rfl
    _ = _ := (DerivedCategory.Plus.ι.map_id _).symm
