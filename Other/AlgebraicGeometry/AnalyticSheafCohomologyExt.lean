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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance analyticSheafExtHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf s) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf s)

/-- A sheaf concentrated in degree zero and then extended to integer degrees. -/
abbrev analyticSheafComplexInt (F : AnalyticAdditiveSheaf s) :
    CochainComplex (AnalyticAdditiveSheaf s) ℤ :=
  ((CochainComplex.single₀ (AnalyticAdditiveSheaf s)).obj F).extend
    ComplexShape.embeddingUpNat

/-- Extension of a degree-zero sheaf complex agrees with the single complex in integer degrees. -/
def analyticSheafComplexIntIsoSingle (F : AnalyticAdditiveSheaf s) :
    analyticSheafComplexInt s F ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj F :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl

/-- A map of sheaves as a map of the extended degree-zero complexes. -/
def analyticSheafComplexIntMap {F G : AnalyticAdditiveSheaf s} (f : F ⟶ G) :
    analyticSheafComplexInt s F ⟶ analyticSheafComplexInt s G :=
  HomologicalComplex.extendMap ((CochainComplex.single₀ (AnalyticAdditiveSheaf s)).map f)
    ComplexShape.embeddingUpNat

/-- Maps of extended sheaf complexes preserve composition. -/
theorem analyticSheafComplexIntMap_comp
    {F G H : AnalyticAdditiveSheaf s} (f : F ⟶ G) (g : G ⟶ H) :
    analyticSheafComplexIntMap s (f ≫ g) =
      analyticSheafComplexIntMap s f ≫ analyticSheafComplexIntMap s g := by
  simp only [analyticSheafComplexIntMap, Functor.map_comp, HomologicalComplex.extendMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The extension/single comparison is natural in the coefficient sheaf. -/
theorem analyticSheafComplexIntIsoSingle_naturality
    {F G : AnalyticAdditiveSheaf s} (f : F ⟶ G) :
    analyticSheafComplexIntMap s f ≫ (analyticSheafComplexIntIsoSingle s G).hom =
      (analyticSheafComplexIntIsoSingle s F).hom ≫
        (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  dsimp only [analyticSheafComplexIntMap, analyticSheafComplexIntIsoSingle,
    HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ _
    (rfl : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ))]
  simp [HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.single_map_f_self,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors]

/-- Sheaf cohomology in a nonnegative degree agrees with Ext from the constant integer sheaf. -/
def analyticSheafCohomologyEquivExt (F : AnalyticAdditiveSheaf s) (n : ℕ) :
    Hypercohomology s (analyticSheafComplexInt s F) n ≃
      Abelian.Ext.{1} (constantIntegerSheaf s) F n :=
  (Localization.SmallShiftedHom.precompEquiv
      (analyticSheafComplexIntIsoSingle s (constantIntegerSheaf s)).inv
      (by change QuasiIso _; infer_instance)).trans
    (Localization.SmallShiftedHom.postcompEquiv
      (analyticSheafComplexIntIsoSingle s F).hom
      (by change QuasiIso _; infer_instance))

/-- The map induced on hypercohomology is composition with the coefficient map. -/
theorem hypercohomologyMap_apply
    {K L : CochainComplex (AnalyticAdditiveSheaf s) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology s K n) :
    hypercohomologyMap s f n α = α.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms s) 0 rfl f)
      (zero_add n) := rfl

/-- An isomorphism of complexes induces an injective map on hypercohomology. -/
theorem hypercohomologyMap_injective_of_isIso
    {K L : CochainComplex (AnalyticAdditiveSheaf s) ℤ} (f : K ⟶ L) [IsIso f]
    (n : ℤ) : Function.Injective (hypercohomologyMap s f n) := by
  intro α β h
  have h' := congrArg (hypercohomologyMap s (inv f) n) h
  simpa only [← hypercohomologyMap_comp_apply, IsIso.hom_inv_id,
    hypercohomologyMap_id, AddMonoidHom.id_apply] using h'

/-- The comparison is precomposition and postcomposition by the canonical complex isomorphisms. -/
theorem analyticSheafCohomologyEquivExt_apply (F : AnalyticAdditiveSheaf s) (n : ℕ)
    (α : Hypercohomology s (analyticSheafComplexInt s F) n) :
    analyticSheafCohomologyEquivExt s F n α =
      ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms s) 0 rfl
        (analyticSheafComplexIntIsoSingle s (constantIntegerSheaf s)).inv).comp α
          (add_zero (n : ℤ))).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms s) 0 rfl
          (analyticSheafComplexIntIsoSingle s F).hom) (zero_add (n : ℤ)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology/Ext comparison respects maps of coefficient sheaves. -/
theorem analyticSheafCohomologyEquivExt_naturality
    {F G : AnalyticAdditiveSheaf s} (f : F ⟶ G) (n : ℕ)
    (α : Hypercohomology s (analyticSheafComplexInt s F) n) :
    analyticSheafCohomologyEquivExt s G n
        (hypercohomologyMap s (analyticSheafComplexIntMap s f) n α) =
      (analyticSheafCohomologyEquivExt s F n α).comp (Abelian.Ext.mk₀ f) (add_zero n) := by
  rw [analyticSheafCohomologyEquivExt_apply, analyticSheafCohomologyEquivExt_apply]
  rw [hypercohomologyMap_apply]
  dsimp only [Abelian.Ext.comp, Abelian.Ext.mk₀]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms s) (DerivedCategory.Q (C := AnalyticAdditiveSheaf s))).injective
  simp only [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, analyticSheafComplexIntIsoSingle_naturality]
  simp [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison carries the zero cohomology class to zero. -/
@[simp]
theorem analyticSheafCohomologyEquivExt_zero (F : AnalyticAdditiveSheaf s) (n : ℕ) :
    analyticSheafCohomologyEquivExt s F n 0 = 0 := by
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms s) (DerivedCategory.Q (C := AnalyticAdditiveSheaf s))).injective
  change _ = (0 : Abelian.Ext.{1} (constantIntegerSheaf s) F n).hom
  rw [Abelian.Ext.zero_hom]
  rw [analyticSheafCohomologyEquivExt_apply]
  simp only [Localization.SmallShiftedHom.equiv_comp]
  erw [hypercohomologyEquiv_zero s (analyticSheafComplexInt s F) (n : ℤ)]
  simp

end AlgebraicGeometry.ComplexPoint
