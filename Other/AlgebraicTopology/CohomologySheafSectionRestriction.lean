/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SupportedSingularCohomologySheafComparison

/-!
# Open-restriction naturality of canonical cohomology-sheaf sections

The map from cohomology of sections to sections of the cohomology sheaf is
constructed by exact sheafification. This proves its compatibility with actual
restrictions, without assuming that evaluation on opens is exact.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

/-- The canonical section-to-cohomology-sheaf map commutes with literal open restriction. -/
@[reassoc]
theorem sectionCohomologyToSheafSection_restriction
    (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (n : ℤ) {V W : Opens X} (a : W ⟶ V) :
    HomologicalComplex.homologyMap (sectionComplexRestriction X (.up ℤ) K a) n ≫
        sectionCohomologyToSheafSection X K n W =
      sectionCohomologyToSheafSection X K n V ≫ (K.homology n).obj.map a.op := by
  let eV := sectionCohomologyPresheafOnOpenIso X K n V
  let eW := sectionCohomologyPresheafOnOpenIso X K n W
  have h := sectionCohomologyPresheafOnOpenIso_inv_naturality X K n a
  have h' :
      HomologicalComplex.homologyMap (sectionComplexRestriction X (.up ℤ) K a) n ≫
          eW.hom = eV.hom ≫ (sectionCohomologyPresheaf X K n).map a.op := by
    apply (cancel_mono eW.inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h]
    simp
  dsimp only [sectionCohomologyToSheafSection]
  rw [← Category.assoc, h', Category.assoc,
    (sectionCohomologyPresheafToSheaf X K n).naturality]
  simp only [eV, Category.assoc]

end TopCat.Sheaf
