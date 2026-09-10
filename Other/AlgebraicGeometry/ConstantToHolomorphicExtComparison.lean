/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.FirstHodgeObstructionConstantComparison
public import Other.AlgebraicGeometry.ExponentialConnectingResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Constant-to-holomorphic cohomology as postcomposition in sheaf Ext

This file identifies the map from complex constant-sheaf cohomology to
holomorphic-function cohomology with postcomposition by the inclusion of
constant holomorphic functions.  It supplies the comparison needed to match a
Betti class presented in the constant complex with a Mayer--Vietoris extension
presented in the holomorphic-function sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point Localization

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local instance constantExtHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance constantExtSmallHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    HasSmallLocalizedHom.{1} (analyticQuasiIsomorphisms X) K L :=
  hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
    (analyticQuasiIsomorphisms X) ℤ K L

/-- The extended complex-valued constant sheaf complex is the complex
constant sheaf placed in integer degree zero. -/
def constantComplexComplexIsoSingle :
    constantComplexSheafComplexInt X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantComplexSheaf X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (constantComplexSheaf X) 0 0 rfl

/-- The inclusion of the complex constant sheaf into the additive sheaf of
holomorphic functions. -/
def constantComplexToHolomorphicFunctionSheaf :
    constantComplexSheaf X ⟶
      holomorphicAdditiveFunctionSheaf X (dim X.left) :=
  constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
    inv (holomorphicFunctionToZeroFormSheaf X (dim X.left))

set_option maxHeartbeats 800000 in
/-- The direct map of integer-indexed complexes is the map of single
complexes induced by the inclusion of constant holomorphic functions. -/
theorem complexConstantsToHolomorphicFunctionComplexInt_eq_single :
    complexConstantsToHolomorphicFunctionComplexInt X =
      (constantComplexComplexIsoSingle X).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (constantComplexToHolomorphicFunctionSheaf X) := by
  rw [← cancel_epi (constantComplexComplexIsoSingle X).inv,
    Iso.inv_hom_id_assoc]
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    complexConstantsToHolomorphicFunctionComplexInt,
    deRhamToHolomorphicFunctions, CochainComplex.toDegreeZero_f_zero]
  erw [HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0
    (deRhamDegreeZeroIsoFunctions X).hom]
  erw [HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0
    (constantComplexToHolomorphicFunctionSheaf X)]
  rw [show (constantComplexComplexIsoSingle X).inv.f 0 =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        (constantComplexSheaf X) 0 0 rfl).inv.f 0 by rfl]
  rw [HomologicalComplex.extendSingleIso_inv_f]
  unfold constantsToHolomorphicDeRhamComplexInt
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  simp only [constantsToHolomorphicDeRhamComplex,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    deRhamDegreeZeroIsoFunctions, Iso.trans_hom,
    constantComplexToHolomorphicFunctionSheaf, Category.assoc]
  simp

/-- Complex constant-sheaf cohomology in a natural-number degree, presented
as an actual sheaf Ext group. -/
def complexConstantCohomologyExtEquiv (n : ℕ) :
    ComplexConstantCohomology X (n : ℤ) ≃
      Abelian.Ext.{1} (constantIntegerSheaf X) (constantComplexSheaf X) n :=
  (Localization.SmallShiftedHom.postcompEquiv
      (constantComplexComplexIsoSingle X).hom (by
        let : IsIso (constantComplexComplexIsoSingle X).hom :=
          (constantComplexComplexIsoSingle X).isIso_hom
        exact ⟨fun _ ↦ inferInstance⟩)).trans
    (sheafExtHypercohomologyEquiv X (constantComplexSheaf X) 0 n).symm

private theorem constantExt_smallShiftedHom_comp_mk
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {a b c : ℤ}
    (α : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L a)
    (f : L ⟶ M⟦b⟧) (h : b + a = c) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) h =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X)
        (f⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' _ b a c h).inv.app M)) := by
  simp only [SmallShiftedHom.comp, SmallShiftedHom.shift, SmallShiftedHom.mk,
    SmallHom.shift, LocalizerMorphism.smallHomMap_mk, SmallHom.mk_comp_mk]

private theorem constantExt_hypercohomologyMap_smallHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α =
      SmallHom.comp α
        (SmallHom.mk (analyticQuasiIsomorphisms X) (f⟦n⟧')) := by
  change SmallShiftedHom.comp α
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (ShiftedHom.mk₀ 0 rfl f)) _ = _
  rw [constantExt_smallShiftedHom_comp_mk]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app,
    CategoryTheory.shiftFunctorZero', eqToIso_refl, Iso.refl_trans,
    ← CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id]

private theorem constantExt_comp_mk₀_smallHom
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

/-- The degree-zero-placement sheaf-Ext/hypercohomology comparison is natural
under postcomposition by a map of target sheaves, in every Ext degree. -/
theorem sheafExtHypercohomologyEquiv_naturality_zeroPlacement
    {F G : AnalyticAdditiveSheaf X} (s : F ⟶ G) (n : ℕ)
    (a : Abelian.Ext.{1} (constantIntegerSheaf X) F n) :
    sheafExtHypercohomologyEquiv X G 0 n
        (a.comp (Abelian.Ext.mk₀ s) (Nat.add_zero n)) =
      hypercohomologyMap X
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map s)
        (n : ℤ)
        (sheafExtHypercohomologyEquiv X F 0 n a) := by
  rw [sheafExtHypercohomologyEquiv_smallHom,
    sheafExtHypercohomologyEquiv_smallHom,
    sheafSingleShiftIso_zero, sheafSingleShiftIso_zero,
    constantExt_hypercohomologyMap_smallHom]
  rw [constantExt_comp_mk₀_smallHom]
  simp only [Iso.refl_hom, SmallHom.comp_mk_id, SmallHom.comp_assoc]

/-- Presenting a complex constant class as sheaf Ext and then returning to
hypercohomology is exactly postcomposition with the canonical single-complex
comparison. -/
theorem sheafExtHypercohomologyEquiv_complexConstantCohomologyExtEquiv
    (n : ℕ) (a : ComplexConstantCohomology X (n : ℤ)) :
    sheafExtHypercohomologyEquiv X (constantComplexSheaf X) 0 n
        (complexConstantCohomologyExtEquiv X n a) =
      hypercohomologyMap X (constantComplexComplexIsoSingle X).hom
        (n : ℤ) a := by
  unfold complexConstantCohomologyExtEquiv
  simp only [Equiv.trans_apply]
  calc
    _ = (Localization.SmallShiftedHom.postcompEquiv
          (constantComplexComplexIsoSingle X).hom (by
            let : IsIso (constantComplexComplexIsoSingle X).hom :=
              (constantComplexComplexIsoSingle X).isIso_hom
            exact ⟨fun _ ↦ inferInstance⟩)) a :=
      (sheafExtHypercohomologyEquiv X (constantComplexSheaf X) 0 n).apply_symm_apply _
    _ = _ := rfl

/-- The map from complex constant cohomology to holomorphic-function
cohomology is literally postcomposition of the corresponding sheaf Ext class
by the inclusion of constant holomorphic functions. -/
theorem complexConstantToHolomorphicFunctionCohomology_eq_ext_postcomp
    (n : ℕ) (a : ComplexConstantCohomology X (n : ℤ)) :
    complexConstantToHolomorphicFunctionCohomology X (n : ℤ) a =
      sheafExtHypercohomologyEquiv X
        (holomorphicAdditiveFunctionSheaf X (dim X.left)) 0 n
        ((complexConstantCohomologyExtEquiv X n a).comp
          (Abelian.Ext.mk₀ (constantComplexToHolomorphicFunctionSheaf X))
          (Nat.add_zero n)) := by
  rw [sheafExtHypercohomologyEquiv_naturality_zeroPlacement,
    sheafExtHypercohomologyEquiv_complexConstantCohomologyExtEquiv]
  unfold complexConstantToHolomorphicFunctionCohomology
  rw [complexConstantsToHolomorphicFunctionComplexInt_eq_single,
    hypercohomologyMap_comp_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
