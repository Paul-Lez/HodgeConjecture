import Other.AlgebraicGeometry.FilteredCycleComponentSupport
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

open CategoryTheory Limits TopologicalSpace
namespace AlgebraicGeometry.ComplexPoint
@[expose] noncomputable section

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
local instance : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local notation "JX" => Opens.grothendieckTopology (TopCat.of (ComplexPoint X))

#synth (constantSheaf JX AddCommGrpCat).Additive
-- #synth PreservesFiniteLimits (constantSheaf JX AddCommGrpCat)
#synth PreservesFiniteColimits (constantSheaf JX AddCommGrpCat)
#check Functor.mapDerivedCategory
#check CategoryTheory.Adjunction.derived
#check constantSheafAdj
#check TopCat.Sheaf.supportEvaluation
#check Sheaf.ΓNatIsoSheafSections
#check CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
#check CochainComplex.liftToInjective
#check CochainComplex.comp_liftToInjective
#check HomologicalComplex.IsStrictlyGE.of_le
#check HomologicalComplex.isStrictlyGE_of_le
#check CochainComplex.isStrictlyGE_of_le

end
end AlgebraicGeometry.ComplexPoint
