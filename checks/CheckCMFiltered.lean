import Other.AlgebraicGeometry.ExplicitEllipticGlobalOneForms
import Other.AlgebraicGeometry.ExplicitEllipticCMTopology
import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint

#check TopCat.Sheaf.integerConstantHomEquivGlobalSections_naturality
#check Abelian.Ext.mk₀
#check Abelian.Ext.homEquiv₀
#check Abelian.Ext.addEquiv₀
#check Abelian.Ext.comp
#check AlgebraicGeometry.ComplexPoint.sheafExtHypercohomologyEquiv
#check AlgebraicGeometry.ComplexPoint.topHolomorphicFormFilteredEquiv
#check AlgebraicGeometry.ComplexPoint.topHodgeFilteredComplexIsoSingle
#check AlgebraicGeometry.ComplexPoint.topHodgeFilteredTermIso
#check AlgebraicGeometry.ComplexPoint.hodgeFilteredDeRhamComplexScalar
#check AlgebraicGeometry.ComplexPoint.scalarHolomorphicDeRhamComplexInt
#check AlgebraicGeometry.ComplexPoint.scalarHolomorphicDeRhamPresheaf
#check AlgebraicGeometry.ComplexPoint.hypercohomologyMap
#check AlgebraicGeometry.ComplexPoint.hypercohomologyMap_comp_apply
#check HomologicalComplex.stupidTruncMap
#check HomologicalComplex.stupidTruncXIso
#check HomologicalComplex.extendXIso
#check Localization.SmallShiftedHom.postcompEquiv
#check Localization.SmallShiftedHom.postcompEquiv_apply
#check Localization.SmallShiftedHom.equiv_comp
#check CategoryTheory.ShiftedHom.comp
#check TopCat.Presheaf.IsCompatible
#check TopCat.Sheaf.eq_of_locally_eq'
#check TopCat.Sheaf.existsUnique_gluing'

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

example
    (a b : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquiv X (a + b) =
      topHolomorphicFormFilteredEquiv X a + topHolomorphicFormFilteredEquiv X b := by
  unfold topHolomorphicFormFilteredEquiv
  simp only [Equiv.trans_apply]
  let F := holomorphicDeRhamSheaf X (dim X.left) (dim X.left)
  rw [show (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm (a + b) =
      (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm a +
        (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm b by
    exact (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).symm.map_add a b]
  rw [show Abelian.Ext.homEquiv₀.symm
      ((TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm a +
        (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm b) =
      Abelian.Ext.homEquiv₀.symm
          ((TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm a) +
        Abelian.Ext.homEquiv₀.symm
          ((TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm b) by
    exact (Abelian.Ext.addEquiv₀ (X := constantIntegerSheaf X) (Y := F)).symm.map_add _ _]
  simp only [F]
  simp

end AlgebraicGeometry.ComplexPoint

