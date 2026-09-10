import Other.AlgebraicGeometry.TopHodgeFilteredClass

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

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
    simp only [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    erw [HomologicalComplex.single_map_f_self]
    simp
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt

theorem check_topHodgeFilteredTermIso_scalar (c : ℂ) :
    (hodgeFilteredDeRhamComplexScalar X (dim X.left) c).f (dim X.left) ≫
        (topHodgeFilteredTermIso X).hom =
      (topHodgeFilteredTermIso X).hom ≫
        (scalarHolomorphicDeRhamComplex X (dim X.left) c).f (dim X.left) := by
  have htrunc :
      (hodgeFilteredDeRhamComplexScalar X (dim X.left) c).f (dim X.left) ≫
          ((holomorphicDeRhamComplexInt X).stupidTruncXIso
            (ComplexShape.embeddingUpIntGE (dim X.left)) (i := 0) (by simp)).hom =
        ((holomorphicDeRhamComplexInt X).stupidTruncXIso
            (ComplexShape.embeddingUpIntGE (dim X.left)) (i := 0) (by simp)).hom ≫
          (scalarHolomorphicDeRhamComplexInt X c).f (dim X.left) := by
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
      (scalarHolomorphicDeRhamComplexInt X c)
      (ComplexShape.embeddingUpIntGE (dim X.left)) (by simp)
  unfold hodgeFilteredDeRhamComplexScalar hodgeFilteredDeRhamComplex at htrunc ⊢
  dsimp only [topHodgeFilteredTermIso, Iso.trans_hom]
  rw [← Category.assoc, htrunc, Category.assoc]
  unfold scalarHolomorphicDeRhamComplexInt
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := dim X.left) (i' := (dim X.left : ℤ)) rfl]
  simp

end AlgebraicGeometry.ComplexPoint
