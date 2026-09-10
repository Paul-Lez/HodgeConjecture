module

public import Other.AlgebraicGeometry.ExponentialConnectingResolution

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point Localization

variable (X : Over (Spec (.of ℂ)))

local instance checkGeneralNaturalityDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance checkGeneralNaturalitySmallHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    HasSmallLocalizedHom.{1} (analyticQuasiIsomorphisms X) K L :=
  hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
    (analyticQuasiIsomorphisms X) ℤ K L

theorem sheafSingleShiftIso_naturality
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (j : ℤ) (n : ℕ) :
    (((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)⟦(n : ℤ)⟧' ≫
        (sheafSingleShiftIso X G j n).hom) =
      (sheafSingleShiftIso X F j n).hom ≫
        (((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) j).map s)⟦(n : ℤ) + j⟧') := by
  let E := CochainComplex.singleFunctors (AnalyticAdditiveSheaf X)
  change ((E.functor 0).map s)⟦(n : ℤ)⟧' ≫
      (E.shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).hom.app G ≫
        (E.shiftIso ((n : ℤ) + j) (-(n : ℤ)) j (by omega)).inv.app G =
    (E.shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).hom.app F ≫
      (E.shiftIso ((n : ℤ) + j) (-(n : ℤ)) j (by omega)).inv.app F ≫
        ((E.functor j).map s)⟦(n : ℤ) + j⟧'
  have h₀ :=
    (E.shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).hom.naturality s
  have h₁ :=
    (E.shiftIso ((n : ℤ) + j) (-(n : ℤ)) j (by omega)).inv.naturality s
  simp only [Functor.comp_map] at h₀ h₁
  rw [← Category.assoc, h₀, Category.assoc, h₁]

private theorem extNaturality_smallShiftedHom_comp_mk
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {a b c : ℤ}
    (α : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L a)
    (f : L ⟶ M⟦b⟧) (h : b + a = c) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) h =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X)
        (f⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' _ b a c h).inv.app M)) := by
  simp only [SmallShiftedHom.comp, SmallShiftedHom.shift, SmallShiftedHom.mk,
    SmallHom.shift, LocalizerMorphism.smallHomMap_mk, SmallHom.mk_comp_mk]

private theorem extNaturality_hypercohomologyMap_smallHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X) (f⟦n⟧')) := by
  change SmallShiftedHom.comp α
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (ShiftedHom.mk₀ 0 rfl f)) _ = _
  rw [extNaturality_smallShiftedHom_comp_mk]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id]

private theorem extNaturality_constantExt_comp_mk₀_smallHom
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (n : ℕ)
    (a : Abelian.Ext.{1} (constantIntegerSheaf X) F n) :
    a.comp (Abelian.Ext.mk₀ s) (Nat.add_zero n) =
      SmallHom.comp a (SmallHom.mk (analyticQuasiIsomorphisms X)
        (((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)⟦(n : ℤ)⟧')) := by
  unfold Abelian.Ext.comp Abelian.Ext.mk₀
  apply (SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
    SmallHom.equiv_comp, SmallHom.equiv_mk]
  rw [ShiftedHom.comp_mk₀]
  rw [SmallShiftedHom.equiv_apply (L := DerivedCategory.Q)
    (f := SmallHom.comp a (SmallHom.mk (analyticQuasiIsomorphisms X)
      (((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)⟦(n : ℤ)⟧'))),
    SmallHom.equiv_comp, SmallHom.equiv_mk]
  rw [SmallShiftedHom.equiv_apply (L := DerivedCategory.Q) (f := a)]
  simp only [Category.assoc]
  exact congrArg
    (fun q => (SmallHom.equiv (analyticQuasiIsomorphisms X)
      DerivedCategory.Q) a ≫ q)
    ((DerivedCategory.Q.commShiftIso (n : ℤ)).hom.naturality
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)).symm

theorem sheafExtHypercohomologyEquiv_naturality
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (j : ℤ) (n : ℕ)
    (a : Abelian.Ext.{1} (constantIntegerSheaf X) F n) :
    sheafExtHypercohomologyEquiv X G j n
        (a.comp (Abelian.Ext.mk₀ s) (Nat.add_zero n)) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) j).map s)
        ((n : ℤ) + j)
        (sheafExtHypercohomologyEquiv X F j n a) := by
  rw [sheafExtHypercohomologyEquiv_smallHom,
    sheafExtHypercohomologyEquiv_smallHom,
    extNaturality_hypercohomologyMap_smallHom]
  rw [extNaturality_constantExt_comp_mk₀_smallHom]
  simp only [SmallHom.comp_assoc, SmallHom.mk_comp_mk]
  congr 2
  rw [sheafSingleShiftIso_naturality X s j n]

end AlgebraicGeometry.ComplexPoint
