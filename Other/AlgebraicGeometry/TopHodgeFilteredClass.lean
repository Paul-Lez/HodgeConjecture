/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SheafExtHypercohomology
public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison

/-!
# Global top forms and the highest filtered hypercohomology group

The holomorphic de Rham complex vanishes above the complex dimension. Its highest
nonzero stupid truncation is therefore the top-form sheaf in that degree. Global
top forms identify with hypercohomology of this truncation in the same degree.

This identifies the filtered source group. It makes no assertion about injectivity
of the map from filtered to full de Rham hypercohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- A sheaf complex concentrated in one degree is the single complex on its term there. -/
def concentratedSheafComplexIsoSingle
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    K ≅ (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) n).obj (K.X n) where
  hom := HomologicalComplex.mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) =>
    (K.isZero_of_isStrictlyGE n i (by omega)).eq_of_src _ _)
  inv := HomologicalComplex.mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) =>
    (K.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt _ _)
  hom_inv_id := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i n
    · apply (K.isZero_of_isStrictlyGE n i hi).eq_of_src
    · simp
    · apply (K.isZero_of_isStrictlyLE n i hi).eq_of_tgt
  inv_hom_id := by
    ext i
    by_cases hi : i = n
    · subst i
      simp
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _

/-- The remaining term of the top stupid truncation is the actual top-form sheaf. -/
def topHodgeFilteredTermIso :
    (hodgeFilteredDeRhamComplex X (dim X.left)).X (dim X.left) ≅
      holomorphicDeRhamSheaf X (dim X.left) (dim X.left) :=
  (holomorphicDeRhamComplexInt X).stupidTruncXIso
      (ComplexShape.embeddingUpIntGE (dim X.left)) (i := 0) (by simp) ≪≫
    (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
      (i := dim X.left) rfl

/-- The highest nonzero filtered complex is the top-form sheaf placed in top degree. -/
def topHodgeFilteredComplexIsoSingle :
    hodgeFilteredDeRhamComplex X (dim X.left) ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (dim X.left)).obj
        (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)) := by
  letI : (hodgeFilteredDeRhamComplex X (dim X.left)).IsStrictlyGE (dim X.left) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  letI : (hodgeFilteredDeRhamComplex X (dim X.left)).IsStrictlyLE (dim X.left) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  exact concentratedSheafComplexIsoSingle X _ (dim X.left) ≪≫
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) (dim X.left)).mapIso
      (topHodgeFilteredTermIso X)

/-- Reindex hypercohomology along an equality of cohomological degrees. -/
def hypercohomologyReindexEquiv
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) {i j : ℤ} (h : i = j) :
    Hypercohomology X K i ≃ Hypercohomology X K j := by
  subst j
  exact Equiv.refl _

omit [IsIntegral X.left] [Smooth X.hom] in
@[simp] theorem hypercohomologyReindexEquiv_zero
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) {i j : ℤ} (h : i = j) :
    hypercohomologyReindexEquiv X K h 0 = 0 := by
  subst j
  rfl

/-- Global top forms are exactly the top-degree hypercohomology of the top truncation. -/
def topHolomorphicFormFilteredEquiv :
    (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤) ≃
      FilteredDeRhamHypercohomology X (dim X.left) (dim X.left) := by
  let F := holomorphicDeRhamSheaf X (dim X.left) (dim X.left)
  let e₀ : (constantIntegerSheaf X ⟶ F) ≃ Abelian.Ext.{1} (constantIntegerSheaf X) F 0 :=
    Abelian.Ext.homEquiv₀.symm
  exact (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm.trans
    (e₀.trans
      ((sheafExtHypercohomologyEquiv X F (dim X.left) 0).trans
        ((hypercohomologyReindexEquiv X _ (zero_add _)).trans
      (Localization.SmallShiftedHom.postcompEquiv
      (topHodgeFilteredComplexIsoSingle X).inv (by
        change QuasiIso (topHodgeFilteredComplexIsoSingle X).inv
        infer_instance)))))

/-- The top-form comparison sends the zero section to the zero filtered class. -/
@[simp] theorem topHolomorphicFormFilteredEquiv_zero :
    topHolomorphicFormFilteredEquiv X 0 = 0 := by
  let F := holomorphicDeRhamSheaf X (dim X.left) (dim X.left)
  have hsection : (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm 0 = 0 :=
    (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F).symm.map_zero
  have hext : (Abelian.Ext.homEquiv₀.symm (0 : constantIntegerSheaf X ⟶ F) :
      Abelian.Ext.{1} (constantIntegerSheaf X) F 0) = 0 :=
    (Abelian.Ext.addEquiv₀ (X := constantIntegerSheaf X) (Y := F)).symm.map_zero
  simp only [topHolomorphicFormFilteredEquiv, Equiv.trans_apply]
  rw [hsection]
  erw [hext]
  rw [sheafExtHypercohomologyEquiv_zero]
  erw [hypercohomologyReindexEquiv_zero X _ (zero_add (dim X.left : ℤ))]
  exact (hypercohomologyMap X (topHodgeFilteredComplexIsoSingle X).inv (dim X.left)).map_zero

/-- Every nonzero global top form gives a nonzero class in the top filtered source group. -/
theorem topHolomorphicFormFilteredEquiv_ne_zero
    {ω : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)}
    (hω : ω ≠ 0) : topHolomorphicFormFilteredEquiv X ω ≠ 0 := by
  intro h
  apply hω
  apply (topHolomorphicFormFilteredEquiv X).injective
  exact h.trans (topHolomorphicFormFilteredEquiv_zero X).symm

/-- The same comparison with an explicitly known dimension. -/
def topHolomorphicFormFilteredEquivOfDimension (d : ℕ) (hd : dim X.left = d)
    [SmoothOfRelativeDimension d X.hom] :
    (holomorphicDeRhamSheaf X d d).obj.obj (.op ⊤) ≃
      FilteredDeRhamHypercohomology X d d := by
  subst d
  exact topHolomorphicFormFilteredEquiv X

@[simp] theorem topHolomorphicFormFilteredEquivOfDimension_zero
    (d : ℕ) (hd : dim X.left = d) [SmoothOfRelativeDimension d X.hom] :
    topHolomorphicFormFilteredEquivOfDimension X d hd 0 = 0 := by
  subst d
  exact topHolomorphicFormFilteredEquiv_zero X

end AlgebraicGeometry.ComplexPoint
