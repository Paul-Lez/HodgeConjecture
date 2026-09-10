/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Analytic sheaf cohomology and Ext

The project computes hypercohomology with the constant integer complex extended from natural
degrees. Ext uses single complexes in integer degrees. The canonical extension isomorphisms
identify these presentations and respect maps of coefficient sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance analyticSheafExtHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A sheaf concentrated in degree zero and then extended to integer degrees. -/
abbrev analyticSheafComplexInt (F : AnalyticAdditiveSheaf X) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj F).extend
    ComplexShape.embeddingUpNat

/-- Extension of a degree-zero sheaf complex agrees with the single complex in integer degrees. -/
def analyticSheafComplexIntIsoSingle (F : AnalyticAdditiveSheaf X) :
    analyticSheafComplexInt X F ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl

/-- A map of sheaves as a map of the extended degree-zero complexes. -/
def analyticSheafComplexIntMap {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) :
    analyticSheafComplexInt X F ⟶ analyticSheafComplexInt X G :=
  HomologicalComplex.extendMap ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map f)
    ComplexShape.embeddingUpNat

/-- Maps of extended sheaf complexes preserve composition. -/
theorem analyticSheafComplexIntMap_comp
    {F G H : AnalyticAdditiveSheaf X} (f : F ⟶ G) (g : G ⟶ H) :
    analyticSheafComplexIntMap X (f ≫ g) =
      analyticSheafComplexIntMap X f ≫ analyticSheafComplexIntMap X g := by
  simp only [analyticSheafComplexIntMap, Functor.map_comp, HomologicalComplex.extendMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The extension/single comparison is natural in the coefficient sheaf. -/
theorem analyticSheafComplexIntIsoSingle_naturality
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) :
    analyticSheafComplexIntMap X f ≫ (analyticSheafComplexIntIsoSingle X G).hom =
      (analyticSheafComplexIntIsoSingle X F).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  dsimp only [analyticSheafComplexIntMap, analyticSheafComplexIntIsoSingle,
    HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ _
    (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))]
  simp [HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.single_map_f_self,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]

/-- Sheaf cohomology in a nonnegative degree agrees with Ext from the constant integer sheaf. -/
def analyticSheafCohomologyEquivExt (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X (analyticSheafComplexInt X F) n ≃
      Abelian.Ext.{1} (constantIntegerSheaf X) F n :=
  (Localization.SmallShiftedHom.precompEquiv
      (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv
      (by change QuasiIso _; infer_instance)).trans
    (Localization.SmallShiftedHom.postcompEquiv
      (analyticSheafComplexIntIsoSingle X F).hom
      (by change QuasiIso _; infer_instance))

/-- The map induced on hypercohomology is composition with the coefficient map. -/
theorem hypercohomologyMap_apply
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α = α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f)
      (zero_add n) := rfl

/-- An isomorphism of complexes induces an injective map on hypercohomology. -/
theorem hypercohomologyMap_injective_of_isIso
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) [IsIso f]
    (n : ℤ) : Function.Injective (hypercohomologyMap X f n) := by
  intro α β h
  have h' := congrArg (hypercohomologyMap X (inv f) n) h
  simpa only [← hypercohomologyMap_comp_apply, IsIso.hom_inv_id,
    hypercohomologyMap_id, AddMonoidHom.id_apply] using h'

/-- The comparison is precomposition and postcomposition by the canonical complex isomorphisms. -/
theorem analyticSheafCohomologyEquivExt_apply (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X F n α =
      ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv).comp α
          (add_zero (n : ℤ))).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (analyticSheafComplexIntIsoSingle X F).hom) (zero_add (n : ℤ)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology/Ext comparison respects maps of coefficient sheaves. -/
theorem analyticSheafCohomologyEquivExt_naturality
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) (n : ℕ)
    (α : Hypercohomology X (analyticSheafComplexInt X F) n) :
    analyticSheafCohomologyEquivExt X G n
        (hypercohomologyMap X (analyticSheafComplexIntMap X f) n α) =
      (analyticSheafCohomologyEquivExt X F n α).comp (Abelian.Ext.mk₀ f) (add_zero n) := by
  rw [analyticSheafCohomologyEquivExt_apply, analyticSheafCohomologyEquivExt_apply]
  rw [hypercohomologyMap_apply]
  dsimp only [Abelian.Ext.comp, Abelian.Ext.mk₀]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  simp only [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, analyticSheafComplexIntIsoSingle_naturality]
  simp [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison carries the zero cohomology class to zero. -/
@[simp]
theorem analyticSheafCohomologyEquivExt_zero (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    analyticSheafCohomologyEquivExt X F n 0 = 0 := by
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) (DerivedCategory.Q (C := AnalyticAdditiveSheaf X))).injective
  change _ = (0 : Abelian.Ext.{1} (constantIntegerSheaf X) F n).hom
  rw [Abelian.Ext.zero_hom]
  rw [analyticSheafCohomologyEquivExt_apply]
  simp only [Localization.SmallShiftedHom.equiv_comp]
  erw [hypercohomologyEquiv_zero X (analyticSheafComplexInt X F) (n : ℤ)]
  simp

end AlgebraicGeometry.ComplexPoint
