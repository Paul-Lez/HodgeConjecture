/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

local instance extImageHasDerivedCategory :
    HasDerivedCategory
      (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _

local instance extImageAnalyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

private def constantIntegerComparisonExtImage :=
  Localization.SmallShiftedHom.mk₀Inv (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)

private def constantFieldComparisonExtImage :=
  Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantFieldSheafComplexIntIsoSingle ℚ X).hom

set_option maxHeartbeats 800000 in
lemma hypercohomologyAddEquivConstantCohomology_ext_hom
    (n : ℕ) (β : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n) :
    Abelian.Ext.hom (hypercohomologyAddEquivConstantCohomology ℚ X n β) =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).inv ≫
        (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
          DerivedCategory.Q β) ≫
        (shiftFunctor _ (n : ℤ)).map
          (DerivedCategory.Q.map (constantFieldSheafComplexIntIsoSingle ℚ X).hom) := by
  change
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (Localization.SmallShiftedHom.chgUniv.{0}
          (((constantIntegerComparisonExtImage X).comp β (add_zero _)).comp
            (constantFieldComparisonExtImage X) (zero_add _))) = _
  dsimp only [constantIntegerComparisonExtImage, constantFieldComparisonExtImage]
  simp only [Localization.SmallShiftedHom.equiv_chgUniv, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀Inv,
    Localization.SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀]
  have h_iso :
      (Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
        (constantIntegerSheafComplexIntIsoSingleULift X).hom
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).inv =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).inv := by
    apply (cancel_epi (DerivedCategory.Q.map
      (constantIntegerSheafComplexIntIsoSingleULift X).hom)).1
    simp
  rw [Category.assoc, h_iso]

end AlgebraicGeometry.ComplexPoint

end
