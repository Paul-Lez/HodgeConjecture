/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExponentialConnectingResolution
public import Other.AlgebraicGeometry.TopHodgeFilteredClass

/-!
# Scalar naturality of the top Hodge-filtration comparison

This file records the chain-level naturality facts needed to compare scalar
multiplication on global top forms with scalar multiplication on the highest stupid
truncation of the holomorphic de Rham complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Scalar multiplication on the actual sheaf of top-degree holomorphic forms. -/
def topHolomorphicFormScalarSheafMap (c : ℂ) :
    holomorphicDeRhamSheaf X (dim X.left) (dim X.left) ⟶
      holomorphicDeRhamSheaf X (dim X.left) (dim X.left) :=
  (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
    (scalarHolomorphicDeRhamPresheaf X (dim X.left) (dim X.left) c)

/-- The canonical identification of a complex concentrated in one degree with a
single-object complex is natural in endomorphisms. -/
theorem concentratedSheafComplexIsoSingle_naturality
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

/-- The identification of the top term of the highest stupid truncation with the
top-form sheaf intertwines the two scalar maps. -/
theorem topHodgeFilteredTermIso_scalar (c : ℂ) :
    (hodgeFilteredDeRhamComplexScalar X (dim X.left) c).f (dim X.left) ≫
        (topHodgeFilteredTermIso X).hom =
      (topHodgeFilteredTermIso X).hom ≫
        topHolomorphicFormScalarSheafMap X c := by
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
  rfl

/-- The identification of the highest filtered complex with the top-form sheaf in
one degree intertwines scalar multiplication. -/
theorem topHodgeFilteredComplexIsoSingle_scalar (c : ℂ) :
    hodgeFilteredDeRhamComplexScalar X (dim X.left) c ≫
        (topHodgeFilteredComplexIsoSingle X).hom =
      (topHodgeFilteredComplexIsoSingle X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).map
            (topHolomorphicFormScalarSheafMap X c) := by
  letI : (hodgeFilteredDeRhamComplex X (dim X.left)).IsStrictlyGE
      (dim X.left) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  letI : (hodgeFilteredDeRhamComplex X (dim X.left)).IsStrictlyLE
      (dim X.left) := by
    unfold hodgeFilteredDeRhamComplex
    infer_instance
  dsimp only [topHodgeFilteredComplexIsoSingle, Iso.trans_hom]
  rw [← Category.assoc, concentratedSheafComplexIsoSingle_naturality,
    Category.assoc]
  simp only [Category.assoc]
  apply (cancel_epi (concentratedSheafComplexIsoSingle X
    (hodgeFilteredDeRhamComplex X (dim X.left)) (dim X.left)).hom).mpr
  change (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
      (dim X.left)).map
        ((hodgeFilteredDeRhamComplexScalar X (dim X.left) c).f
          (dim X.left)) ≫
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).map (topHodgeFilteredTermIso X).hom =
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
      (dim X.left)).map (topHodgeFilteredTermIso X).hom ≫
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).map (topHolomorphicFormScalarSheafMap X c)
  rw [← Functor.map_comp]
  rw [topHodgeFilteredTermIso_scalar]
  simp only [Functor.map_comp, Category.assoc]

local instance topScalarNaturalityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

open Localization

local instance topScalarNaturalitySmallHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    HasSmallLocalizedHom.{1} (analyticQuasiIsomorphisms X) K L :=
  hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
    (analyticQuasiIsomorphisms X) ℤ K L

private theorem topScalar_smallShiftedHom_comp_mk
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {a b c : ℤ}
    (α : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L a)
    (f : L ⟶ M⟦b⟧) (h : b + a = c) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) h =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X)
        (f⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' _ b a c h).inv.app M)) := by
  simp only [SmallShiftedHom.comp, SmallShiftedHom.shift, SmallShiftedHom.mk,
    SmallHom.shift, LocalizerMorphism.smallHomMap_mk, SmallHom.mk_comp_mk]

private theorem topScalar_hypercohomologyMap_smallHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X) (f⟦n⟧')) := by
  change SmallShiftedHom.comp α
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (ShiftedHom.mk₀ 0 rfl f)) _ = _
  rw [topScalar_smallShiftedHom_comp_mk]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id]

/-- Reindexing cohomological degree commutes with the map induced by a map of
complexes. -/
theorem hypercohomologyReindexEquiv_naturality
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L)
    {i j : ℤ} (h : i = j) (a : Hypercohomology X K i) :
    hypercohomologyReindexEquiv X L h (hypercohomologyMap X f i a) =
      hypercohomologyMap X f j (hypercohomologyReindexEquiv X K h a) := by
  subst j
  rfl

/-- In cohomological degree zero, the Ext-to-hypercohomology comparison is
natural in the target sheaf. -/
theorem sheafExtHypercohomologyEquiv_naturality_zero
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (j : ℤ)
    (a : Abelian.Ext.{1} (constantIntegerSheaf X) F 0) :
    sheafExtHypercohomologyEquiv X G j 0
        (a.comp (Abelian.Ext.mk₀ s) rfl) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) j).map s) ((0 : ℤ) + j)
        (sheafExtHypercohomologyEquiv X F j 0 a) := by
  rw [sheafExtHypercohomologyEquiv_smallHom,
    sheafExtHypercohomologyEquiv_smallHom,
    topScalar_hypercohomologyMap_smallHom]
  unfold Abelian.Ext.comp Abelian.Ext.mk₀ SmallShiftedHom.mk₀
  rw [topScalar_smallShiftedHom_comp_mk]
  simp only [SmallHom.comp_assoc]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id,
    SmallHom.mk_comp_mk]
  congr 1
  erw [CategoryTheory.shiftFunctorAdd'_zero_add_inv_app]
  simp [sheafSingleShiftIso]

/-- A global top form viewed first as a class in the corresponding one-term
complex. -/
def topHolomorphicFormSingleClass
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    Hypercohomology X
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).obj
          (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)))
      (dim X.left) :=
  hypercohomologyReindexEquiv X _ (zero_add (dim X.left : ℤ))
    (sheafExtHypercohomologyEquiv X
      (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))
      (dim X.left) 0
      (Abelian.Ext.homEquiv₀.symm
        ((TopCat.Sheaf.integerConstantHomEquivGlobalSections
          (holomorphicDeRhamSheaf X (dim X.left) (dim X.left))).symm w)))

/-- The global-top-form equivalence is the one-term class followed by the inverse
of the highest-truncation comparison. -/
theorem topHolomorphicFormFilteredEquiv_eq
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquiv X w =
      hypercohomologyMap X (topHodgeFilteredComplexIsoSingle X).inv
        (dim X.left) (topHolomorphicFormSingleClass X w) := by
  rfl

/-- Scalar multiplication on a global top form is carried to the corresponding
map of one-term complexes. -/
theorem topHolomorphicFormSingleClass_scalar (c : ℂ)
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    topHolomorphicFormSingleClass X
        ((topHolomorphicFormScalarSheafMap X c).hom.app (.op ⊤) w) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).map (topHolomorphicFormScalarSheafMap X c))
        (dim X.left) (topHolomorphicFormSingleClass X w) := by
  let F := holomorphicDeRhamSheaf X (dim X.left) (dim X.left)
  let s := topHolomorphicFormScalarSheafMap X c
  let g := (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm w
  have hg : (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).symm
        (s.hom.app (.op ⊤) w) = g ≫ s := by
    apply (TopCat.Sheaf.integerConstantHomEquivGlobalSections F).injective
    rw [Equiv.apply_symm_apply,
      TopCat.Sheaf.integerConstantHomEquivGlobalSections_naturality,
      Equiv.apply_symm_apply]
  have he : (Abelian.Ext.homEquiv₀.symm (g ≫ s) :
        Abelian.Ext.{1} (constantIntegerSheaf X) F 0) =
      (Abelian.Ext.homEquiv₀.symm g :
        Abelian.Ext.{1} (constantIntegerSheaf X) F 0).comp
          (Abelian.Ext.mk₀ s) rfl := by
    simp only [Abelian.Ext.homEquiv₀_symm_apply,
      Abelian.Ext.mk₀_comp_mk₀]
  have hnat := congrArg
    (hypercohomologyReindexEquiv X
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).obj F) (zero_add (dim X.left : ℤ)))
    (sheafExtHypercohomologyEquiv_naturality_zero X s
      (dim X.left) (Abelian.Ext.homEquiv₀.symm g))
  have hnat' :
      (hypercohomologyReindexEquiv X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).obj F) (zero_add (dim X.left : ℤ)))
        (sheafExtHypercohomologyEquiv X F (dim X.left) 0
          (Abelian.Ext.homEquiv₀.symm (g ≫ s))) =
      (hypercohomologyReindexEquiv X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).obj F) (zero_add (dim X.left : ℤ)))
        (hypercohomologyMap X
          ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
            (dim X.left)).map s) (0 + (dim X.left : ℤ))
          (sheafExtHypercohomologyEquiv X F (dim X.left) 0
            (Abelian.Ext.homEquiv₀.symm g))) := by
    exact (congrArg
      (fun e => (hypercohomologyReindexEquiv X _
        (zero_add (dim X.left : ℤ)))
          (sheafExtHypercohomologyEquiv X F (dim X.left) 0 e)) he).trans hnat
  unfold topHolomorphicFormSingleClass
  rw [hg]
  exact hnat'.trans
    (hypercohomologyReindexEquiv_naturality X
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).map s) (zero_add (dim X.left : ℤ)) _)

/-- The top-form comparison intertwines scalar multiplication on global forms
with scalar multiplication on the highest filtered de Rham complex. -/
theorem topHolomorphicFormFilteredEquiv_scalar (c : ℂ)
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquiv X
        ((topHolomorphicFormScalarSheafMap X c).hom.app (.op ⊤) w) =
      hypercohomologyMap X
        (hodgeFilteredDeRhamComplexScalar X (dim X.left) c) (dim X.left)
        (topHolomorphicFormFilteredEquiv X w) := by
  let e := topHodgeFilteredComplexIsoSingle X
  let a := hodgeFilteredDeRhamComplexScalar X (dim X.left) c
  let s := (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
    (dim X.left)).map (topHolomorphicFormScalarSheafMap X c)
  have hcompat : s ≫ e.inv = e.inv ≫ a := by
    calc
      s ≫ e.inv = e.inv ≫ (e.hom ≫ s) ≫ e.inv := by simp [Category.assoc]
      _ = e.inv ≫ (a ≫ e.hom) ≫ e.inv := by
        rw [topHodgeFilteredComplexIsoSingle_scalar]
      _ = e.inv ≫ a := by simp [Category.assoc]
  rw [topHolomorphicFormFilteredEquiv_eq,
    topHolomorphicFormSingleClass_scalar]
  rw [← hypercohomologyMap_comp_apply, hcompat,
    hypercohomologyMap_comp_apply]
  rw [← topHolomorphicFormFilteredEquiv_eq]

end AlgebraicGeometry.ComplexPoint
