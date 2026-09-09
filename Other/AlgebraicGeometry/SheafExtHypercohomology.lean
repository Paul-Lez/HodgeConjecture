/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Sheaf Ext and the analytic hypercohomology convention

The comparison retains the actual constant integer sheaf and explicitly accounts for the
cochain degree in which the target sheaf is placed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance sheafExtHasDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf s) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf s)

instance analyticHasExt : HasExt.{1} (AnalyticAdditiveSheaf s) := by
  intro F G
  infer_instance

/-- The actual extended constant integer complex is the integer sheaf in degree zero. -/
def constantIntegerComplexIsoSingle :
    constantIntegerSheafComplexInt s ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj (constantIntegerSheaf s) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (constantIntegerSheaf s) 0 0 rfl

/-- The shift accounting for placement of a sheaf in an arbitrary cochain degree. -/
def sheafSingleShiftIso (F : AnalyticAdditiveSheaf s) (j : ℤ) (n : ℕ) :
    ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj F)⟦(n : ℤ)⟧ ≅
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F)⟦(n : ℤ) + j⟧ :=
  ((CochainComplex.singleFunctors (AnalyticAdditiveSheaf s)).shiftIso
    (n : ℤ) (-(n : ℤ)) 0 (by omega)).app F ≪≫
    (((CochainComplex.singleFunctors (AnalyticAdditiveSheaf s)).shiftIso
      ((n : ℤ) + j) (-(n : ℤ)) j (by omega)).app F).symm

/-- Actual sheaf Ext is the hypercohomology of a single sheaf, with its placement degree
included in the total cohomology degree. -/
def sheafExtHypercohomologyEquiv (F : AnalyticAdditiveSheaf s) (j : ℤ) (n : ℕ) :
    Abelian.Ext.{1} (constantIntegerSheaf s) F n ≃
      Hypercohomology s
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F) ((n : ℤ) + j) :=
  (Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q).trans
    (((DerivedCategory.Q.mapIso (constantIntegerComplexIsoSingle s).symm).homCongr
      (DerivedCategory.Q.mapIso (sheafSingleShiftIso s F j n))).trans
        (Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q).symm)

/-- The change of cochain conventions sends the zero Ext class to zero. -/
@[simp]
theorem sheafExtHypercohomologyEquiv_zero (F : AnalyticAdditiveSheaf s) (j : ℤ) (n : ℕ) :
    sheafExtHypercohomologyEquiv s F j n 0 = 0 := by
  let e := Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q
    (X := constantIntegerSheafComplexInt s)
    (Y := ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F)⟦(n : ℤ) + j⟧)
  have hext : Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q
      (0 : Abelian.Ext.{1} (constantIntegerSheaf s) F n) = 0 := by
    apply (cancel_mono ((DerivedCategory.Q.commShiftIso (n : ℤ)).hom.app
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj F))).1
    have h : (0 : Abelian.Ext.{1} (constantIntegerSheaf s) F n).hom = 0 :=
      Abelian.Ext.zero_hom _ _ _
    change Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q
      (0 : Abelian.Ext.{1} (constantIntegerSheaf s) F n) ≫
        (DerivedCategory.Q.commShiftIso (n : ℤ)).hom.app
          ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) 0).obj F) = 0 at h
    simpa only [zero_comp] using h
  have hhyper : e (0 : Hypercohomology s
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F) ((n : ℤ) + j)) = 0 := by
    apply (cancel_mono ((DerivedCategory.Q.commShiftIso ((n : ℤ) + j)).hom.app
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F))).1
    have h := hypercohomologyEquiv_zero s
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F) ((n : ℤ) + j)
    change e (0 : Hypercohomology s
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F) ((n : ℤ) + j)) ≫
        (DerivedCategory.Q.commShiftIso ((n : ℤ) + j)).hom.app
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf s) j).obj F) = 0 at h
    simpa only [zero_comp] using h
  apply e.injective
  rw [hhyper]
  change e (e.symm (DerivedCategory.Q.map (constantIntegerComplexIsoSingle s).hom ≫
    Localization.SmallHom.equiv (analyticQuasiIsomorphisms s) DerivedCategory.Q
      (0 : Abelian.Ext.{1} (constantIntegerSheaf s) F n) ≫
        DerivedCategory.Q.map (sheafSingleShiftIso s F j n).hom)) = 0
  rw [e.apply_symm_apply, hext, zero_comp, comp_zero]

end AlgebraicGeometry.ComplexPoint
