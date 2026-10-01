/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.CohomologySection
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SectionRestrictionCone

/-! # Naturality of the canonical cohomology-sheaf section comparison -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The canonical evaluation/homology comparison respects open restriction. -/
@[reassoc]
lemma sectionCohomologyPresheafOnOpenIso_inv_naturality
    (n : ℤ) {V W : Opens X} (a : W ⟶ V) :
    (sectionCohomologyPresheaf X K n).map a.op ≫
      (sectionCohomologyPresheafOnOpenIso X K n W).inv =
    (sectionCohomologyPresheafOnOpenIso X K n V).inv ≫
      homologyMap (sectionComplexRestriction X ℤᵘᵖ K a) n := by
  let P : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex ℤᵘᵖ).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := P.sc n
  change ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op).app S.homology ≫
      (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))).inv =
    (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))).inv ≫
      ShortComplex.homologyMap
        (S.mapNatTrans ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op))
  rw [NatTrans.app_homology]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TopCat.Sheaf

end
