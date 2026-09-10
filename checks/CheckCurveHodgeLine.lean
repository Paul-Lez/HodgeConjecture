import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass
import Other.AlgebraicGeometry.ExplicitEllipticGlobalOneForms
import Other.AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

#check TopCat.Sheaf.integerConstantHomEquivGlobalSections_naturality
#check Localization.SmallShiftedHom.postcompEquiv_apply
#check Localization.SmallShiftedHom.postcompEquiv_symm_apply
#check hypercohomologyMap_comp_apply
#check sheafExtHypercohomologyEquiv
#check Abelian.Ext.homEquiv₀
#check Abelian.Ext.addEquiv₀

variable (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

theorem check_concentrated_naturality
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] (f : K ⟶ K) :
    f ≫ (concentratedSheafComplexIsoSingle X K n).hom =
      (concentratedSheafComplexIsoSingle X K n).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) n).map (f.f n) := by
  ext i
  by_cases hi : i = n
  · subst i
    dsimp [concentratedSheafComplexIsoSingle]
    erw [HomologicalComplex.single_map_f_self]
    simp
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt

theorem check_topHodgeFilteredComplexIsoSingle_scalar (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar X (dim X.left) c ≫
        (topHodgeFilteredComplexIsoSingle X).hom =
      (topHodgeFilteredComplexIsoSingle X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).map
            ((topHodgeFilteredTermIso X).inv ≫
              (hodgeFilteredDeRhamComplexScalar X (dim X.left) c).f
                (dim X.left) ≫
              (topHodgeFilteredTermIso X).hom) := by
  rw [topHodgeFilteredComplexIsoSingle]
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc,
    check_concentrated_naturality X _ (dim X.left)
      (hodgeFilteredDeRhamComplexScalar X (dim X.left) c)]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ComplexPoint
