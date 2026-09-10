import Other.AlgebraicTopology.SingularDegreeOneExternalFunctoriality

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
theorem test_external_naturality
    {X X' Y Y' : TopCat.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1) :
    cohomologyMap R 2 (f ⊗ₘ g)
        (degreeOneExternalCohomologyBilinear R X Y alpha beta) =
      degreeOneExternalCohomologyBilinear R X' Y'
        (cohomologyMap R 1 f alpha) (cohomologyMap R 1 g beta) := by
  apply LinearMap.ext
  intro z
  unfold degreeOneExternalCohomologyBilinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, cohomologyMap_apply]
  let h := f ⊗ₘ g
  let a := cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X Y) alpha
  let b := cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X Y) beta
  have hcap := standardCapCohomologyLinear_naturality R h 1 1 a z
  have ha : cohomologyMap R 1 h a =
      cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X' Y')
        (cohomologyMap R 1 f alpha) := by
    dsimp only [h, a]
    calc
      _ = cohomologyMap R 1 ((f ⊗ₘ g) ≫
          SemiCartesianMonoidalCategory.fst X Y) alpha := by
        rw [cohomologyMap_comp]
        rfl
      _ = cohomologyMap R 1 (SemiCartesianMonoidalCategory.fst X' Y' ≫ f)
          alpha := by rw [CartesianMonoidalCategory.tensorHom_fst]
      _ = _ := by
        rw [cohomologyMap_comp]
        rfl
  have hb : cohomologyMap R 1 h b =
      cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X' Y')
        (cohomologyMap R 1 g beta) := by
    dsimp only [h, b]
    calc
      _ = cohomologyMap R 1 ((f ⊗ₘ g) ≫
          SemiCartesianMonoidalCategory.snd X Y) beta := by
        rw [cohomologyMap_comp]
        rfl
      _ = cohomologyMap R 1 (SemiCartesianMonoidalCategory.snd X' Y' ≫ g)
          beta := by rw [CartesianMonoidalCategory.tensorHom_snd]
      _ = _ := by
        rw [cohomologyMap_comp]
        rfl
  change b (standardCapCohomologyLinear R (X ⊗ Y) 1 1 a
    (homologyMap R 2 h z)) = _
  calc
    _ = b (homologyMap R 1 h
        (standardCapCohomologyLinear R (X' ⊗ Y') 1 1
          (cohomologyMap R 1 h a) z)) := congrArg b hcap.symm
    _ = (cohomologyMap R 1 h b)
        (standardCapCohomologyLinear R (X' ⊗ Y') 1 1
          (cohomologyMap R 1 h a) z) := rfl
    _ = _ := by
      rw [ha, hb]
      rfl

end AlgebraicTopology.Singular
