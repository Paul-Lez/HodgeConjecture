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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel

/-!
# SupportConeInjectiveModel, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ))

/-- The support-cone comparison preserves the connecting morphism used to
forget support, with the ambient augmentation on its target. -/
@[reassoc]
lemma rationalSupportConeToAmbientInjectiveCone_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalSupportConeToAmbientInjectiveCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle
        (ambientRationalInjectiveRestriction X Z hZ)).mor₃ =
    (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z)).mor₃ ≫
      (ambientRationalInjectiveAugmentation X)⟦(1 : ℤ)⟧' :=
  (CochainComplex.mappingCone.triangleMap _ _
    (ambientRationalInjectiveAugmentation X) (𝟙 _)
    (by simpa using (ambientRationalAugmentation_comp_restriction X Z hZ).symm)).comm₃.symm

set_option backward.isDefEq.respectTransparency false in
/-- The group-cone comparison preserves its connecting morphism with the
identity on the ambient global sections. -/
@[reassoc]
lemma supportConeToAmbientInjectiveGlobalCone_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    supportConeToAmbientInjectiveGlobalCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
            (ambientRationalInjectiveRestriction X Z hZ))).mor₃ =
    (CochainComplex.mappingCone.triangle
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g).mor₃ := by
  have h := (CochainComplex.mappingCone.triangleMap
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (ambientRationalInjectiveComplex X)).g
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
        (ambientRationalInjectiveRestriction X Z hZ)) (𝟙 _)
    (globalAmbientRationalOpenResolutionComparison X Z hZ)
    (show _ = _ from by
      let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
      change Γ.map _ ≫ Γ.map _ = 𝟙 _ ≫ Γ.map _
      rw [Category.id_comp, ← Functor.map_comp,
        supportRestriction_comp_openResolutionComparison])).comm₃
  exact h.symm.trans ((congrArg (fun f =>
    (CochainComplex.mappingCone.triangle
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g).mor₃ ≫ f)
    ((shiftFunctor (CochainComplex AddCommGrpCat ℤ) (1 : ℤ)).map_id _)).trans
      (Category.comp_id _))

end AlgebraicGeometry.ComplexPoint
end
