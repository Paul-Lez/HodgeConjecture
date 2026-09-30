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

public import Other.AlgebraicGeometry.Cohomology.SupportConeForget
public import Other.AlgebraicGeometry.HypercohomologyExtImage

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

attribute [local instance] rationalConeForgetSheafDerivedCategory HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5
  TopCat.Sheaf.integerConstantSingleComplex ComplexShape.embeddingUpNat


/-! The old cone module supplies the ambient equivalence as a definition. This lemma exposes its
    Ext-to-global-sections factorization for the Ext comparison with the ordinary pair. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_apply
    (n : ℕ) (α : H^n(X; ℚ)) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n α =
      hypercohomologyAddEquivGlobalSectionsKInjective X
        (ambientRationalInjectiveComplex X) (n : ℤ)
        (hypercohomologyMap X (ambientRationalInjectiveAugmentation X) (n : ℤ)
          ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm α)) := by
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_eq_extModel
    (n : ℕ) (α : H^n(X; ℚ)) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n α =
      ((HomologicalComplex.homologyMapIso (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
        (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveComplex X)) n).addCommGroupIsoToAddEquiv)
        ((CochainComplex.HomComplex.homologyAddEquiv
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)) :
              CochainComplex (AnalyticAdditiveSheaf X) ℤ)
            (ambientRationalInjectiveComplex X) n).symm
          (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)) :
              CochainComplex (AnalyticAdditiveSheaf X) ℤ)
            (ambientRationalInjectiveComplex X) n
            (DerivedCategory.Q.map
                ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
                  ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
                    (show AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) from
                      (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom))) ≫
      Abelian.Ext.hom α ≫
              (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) (n : ℤ)).map
                (DerivedCategory.Q.map (ambientRationalInjectiveSingleAugmentation X))))) := by
  obtain ⟨β, rfl⟩ := (hypercohomologyAddEquivConstantCohomology ℚ X n).surjective α
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_apply, AddEquiv.symm_apply_apply]
  dsimp only [hypercohomologyAddEquivGlobalSectionsKInjective,
    hypercohomologyAddEquivDerived, hypercohomologyMap, Hypercohomology,
    AddEquiv.trans_apply]
  dsimp only [TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective,
    AddEquiv.trans_apply]
  let e := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
      (TopCat.of (ComplexPoint X)) (ambientRationalInjectiveComplex X)) n
    |>.addCommGroupIsoToAddEquiv)
  change e _ = e _
  rw [e.injective.eq_iff]
  rw [(CochainComplex.HomComplex.homologyAddEquiv
    (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
    (ambientRationalInjectiveComplex X) n).symm.injective.eq_iff]
  rw [(CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
    (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))
    (ambientRationalInjectiveComplex X) n).injective.eq_iff]
  simp only [isoHomCongrAddEquiv_apply]
  change DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (β.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (ambientRationalInjectiveAugmentation X)) (zero_add (n : ℤ))) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  erw [hypercohomologyAddEquivConstantCohomology_ext_hom]
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.comp_mk₀]
  have hu : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
        (show AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) from
          (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom)) ≫
      (constantIntegerSheafComplexIntIsoSingleULift X).inv =
        (constantIntegerSheafComplexIntIsoSingle X).inv := by
    apply (cancel_mono (constantIntegerSheafComplexIntIsoSingleULift X).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [constantIntegerSheafComplexIntIsoSingleULift,
      constantIntegerSheafComplexIntIsoSingle, Iso.trans_hom]
    erw [Iso.inv_hom_id_assoc]
    rfl
  have hq : (constantFieldSheafComplexIntIsoSingle ℚ X).hom ≫
      ambientRationalInjectiveSingleAugmentation X = ambientRationalInjectiveAugmentation X := by
    rw [ambientRationalInjectiveSingleAugmentation, Iso.hom_inv_id_assoc]
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, hu, hq]

end AlgebraicGeometry.ComplexPoint

end
