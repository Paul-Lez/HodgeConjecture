import Other.AlgebraicGeometry.TopHodgeFilteredScalarNaturality
import Other.AlgebraicGeometry.ExponentialConnectingResolution

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

local instance checkHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

open Localization

local instance checkSmallHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    HasSmallLocalizedHom.{1} (analyticQuasiIsomorphisms X) K L :=
  hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
    (analyticQuasiIsomorphisms X) ℤ K L

private theorem check_smallShiftedHom_comp_mk
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {a b c : ℤ}
    (α : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L a)
    (f : L ⟶ M⟦b⟧) (h : b + a = c) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) h =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X)
        (f⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' _ b a c h).inv.app M)) := by
  simp only [SmallShiftedHom.comp, SmallShiftedHom.shift, SmallShiftedHom.mk,
    SmallHom.shift, LocalizerMorphism.smallHomMap_mk, SmallHom.mk_comp_mk]

private theorem check_hypercohomologyMap_smallHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X) (f⟦n⟧')) := by
  change SmallShiftedHom.comp α
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (ShiftedHom.mk₀ 0 rfl f)) _ = _
  rw [check_smallShiftedHom_comp_mk]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id]

private theorem check_hypercohomologyReindexEquiv_naturality
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L)
    {i j : ℤ} (h : i = j) (a : Hypercohomology X K i) :
    hypercohomologyReindexEquiv X L h (hypercohomologyMap X f i a) =
      hypercohomologyMap X f j (hypercohomologyReindexEquiv X K h a) := by
  subst j
  rfl

example {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (j : ℤ) :
    ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)⟦(0 : ℤ)⟧' ≫
        (sheafSingleShiftIso X G j 0).hom =
      (sheafSingleShiftIso X F j 0).hom ≫
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) j).map s)⟦(0 : ℤ) + j⟧' := by
  simp [sheafSingleShiftIso]

theorem check_sheafExtHypercohomologyEquiv_naturality_zero
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (j : ℤ)
    (a : Abelian.Ext.{1} (constantIntegerSheaf X) F 0) :
    sheafExtHypercohomologyEquiv X G j 0
        (a.comp (Abelian.Ext.mk₀ s) rfl) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) j).map s) ((0 : ℤ) + j)
        (sheafExtHypercohomologyEquiv X F j 0 a) := by
  rw [sheafExtHypercohomologyEquiv_smallHom,
    sheafExtHypercohomologyEquiv_smallHom,
    check_hypercohomologyMap_smallHom]
  unfold Abelian.Ext.comp Abelian.Ext.mk₀ SmallShiftedHom.mk₀
  rw [check_smallShiftedHom_comp_mk]
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

def check_topSingleClass
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

theorem check_topHolomorphicFormFilteredEquiv_eq
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquiv X w =
      hypercohomologyMap X (topHodgeFilteredComplexIsoSingle X).inv
        (dim X.left) (check_topSingleClass X w) := by
  rfl

theorem check_topSingleClass_scalar (c : ℂ)
    (w : (holomorphicDeRhamSheaf X (dim X.left) (dim X.left)).obj.obj (.op ⊤)) :
    check_topSingleClass X
        ((topHolomorphicFormScalarSheafMap X c).hom.app (.op ⊤) w) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
          (dim X.left)).map (topHolomorphicFormScalarSheafMap X c))
        (dim X.left) (check_topSingleClass X w) := by
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
    (check_sheafExtHypercohomologyEquiv_naturality_zero X s
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
  unfold check_topSingleClass
  rw [hg]
  exact hnat'.trans
    (check_hypercohomologyReindexEquiv_naturality X
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X)
        (dim X.left)).map s) (zero_add (dim X.left : ℤ)) _)

example (c : ℂ)
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
  rw [check_topHolomorphicFormFilteredEquiv_eq,
    check_topSingleClass_scalar]
  rw [← hypercohomologyMap_comp_apply, hcompat,
    hypercohomologyMap_comp_apply]
  rw [← check_topHolomorphicFormFilteredEquiv_eq]

end

end AlgebraicGeometry.ComplexPoint
