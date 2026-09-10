import Other.AlgebraicTopology.SingularDegreeOneExternalFunctoriality

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

theorem test_external_bilinear_smul
    (X Y : TopCat.{u}) (a b : R)
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1) :
    degreeOneExternalCohomologyBilinear R X Y (a • alpha) (b • beta) =
      (a * b) • degreeOneExternalCohomologyBilinear R X Y alpha beta := by
  rw [map_smul, map_smul]
  change b • (a • degreeOneExternalCohomologyBilinear R X Y alpha beta) = _
  rw [smul_smul, mul_comm b a]

theorem test_external_eigen
    {X Y : TopCat.{u}} (f : X ⟶ X) (g : Y ⟶ Y)
    (alpha : Cohomology R X 1) (beta : Cohomology R Y 1)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (a b : R)
    (hf : cohomologyMap R 1 f alpha = a • alpha)
    (hg : cohomologyMap R 1 g beta = b • beta) :
    cohomologyMap R 2 (f ⊗ₘ g)
        (degreeOneExternalCohomologyClassOfNonzero R alpha beta halpha hbeta) =
      (a * b) •
        degreeOneExternalCohomologyClassOfNonzero R alpha beta halpha hbeta := by
  rw [degreeOneExternalCohomologyClassOfNonzero_eq_bilinear,
    degreeOneExternalCohomologyBilinear_naturality, hf, hg,
    test_external_bilinear_smul]

end AlgebraicTopology.Singular
