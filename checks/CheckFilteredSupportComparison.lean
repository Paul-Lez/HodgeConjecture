import Other.AlgebraicGeometry.FilteredSupportInjectiveComparison
import Other.AlgebraicGeometry.DerivedSupportRationalConeComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ComplexPoint

variable (X : Over (AlgebraicGeometry.Spec (.of ℂ)))
  [AlgebraicGeometry.IsIntegral X.left]
  [AlgebraicGeometry.Smooth X.hom]

#check TopCat.Sheaf.ambientConstantInjectiveResolution
#check CategoryTheory.InjectiveResolution.mono
#check CategoryTheory.InjectiveResolution.ι_mono
#check HomologicalComplex.mono_extendMap
#check HomologicalComplex.extendMap_mono

example : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE (-1) := by
  letI : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
    unfold constantFieldSheafComplexInt
    infer_instance
  exact (constantFieldSheafComplexInt ℚ X).isStrictlyGE_of_ge (-1) 0 (by omega)
