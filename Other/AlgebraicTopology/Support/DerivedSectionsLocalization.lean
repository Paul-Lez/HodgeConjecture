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

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsLocalization

/-!
# DerivedSectionsLocalization, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsLocalization`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
namespace TopCat.Sheaf
variable (X : TopCat.{u}) (U : Opens X)
attribute [local instance] derivedSupportLocalizationSheafDerivedCategory
attribute [local instance] derivedSupportLocalizationGroupDerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The derived unit identifies the actual `D⁺` supported-sections functor
with its termwise value on a bounded-below injective complex. The displayed
comparison takes values in the ambient derived category via its full inclusion. -/
def derivedClosedSupportInjectiveModelIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedClosedSupportSections X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).X₁ :=
  (DerivedCategory.Plus.ι.mapIso
    (asIso ((derivedClosedSupportSectionsUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I))))).symm ≪≫
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app _

end TopCat.Sheaf
end
