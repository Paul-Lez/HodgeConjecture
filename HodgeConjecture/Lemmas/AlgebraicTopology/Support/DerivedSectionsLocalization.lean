/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization

/-!
# The actual localization sequence on injective coefficient complexes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- The actual support inclusion followed by restriction-pushforward. -/
def supportRestrictionShortComplex (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((sheafSectionsSupportedOutsideInclusion X U).app F)
    ((toOpenRestrictionPushforward X U).app F)
    (sheafSectionsSupportedOutsideInclusion_restriction X U F)

set_option backward.isDefEq.respectTransparency false in
/-- The localization sequence is short exact for an injective coefficient sheaf.
The first map is literally its defining kernel inclusion. -/
private lemma supportRestrictionShortComplex_shortExact (F : Sheaf AddCommGrpCat.{u} X)
    [Injective F] : (supportRestrictionShortComplex X U F).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι _))
  epi_g := inferInstanceAs (Epi ((toOpenRestrictionPushforward X U).app F))

/-- The sequence of sections on `V`, with the actual supported-sections inclusion
and actual restriction map. -/
def supportRestrictionSectionsShortComplex (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex AddCommGrpCat.{u} :=
  (supportRestrictionShortComplex X U F).map (supportEvaluation X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on every open set preserves this particular localization sequence
for injective coefficients. This does not assert that evaluation is exact in
general. -/
private lemma supportRestrictionSectionsShortComplex_shortExact (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    (supportRestrictionSectionsShortComplex X U V F).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  mono_f := mono_of_isLimit_fork
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  epi_g := toOpenRestrictionPushforward_app_epi X U F V

/-- A termwise injective complex gives an actual short exact localization
sequence of complexes of sheaves. -/
private lemma supportRestrictionComplexShortComplex_shortExact
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (supportRestrictionComplexShortComplex X U K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportRestrictionShortComplex_shortExact X U (K.X n)

/-- The support/restriction sequence is short exact even after taking sections
on an arbitrary open set, for a termwise injective coefficient complex. -/
lemma supportRestrictionSectionsComplexShortComplex_shortExact (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (supportRestrictionSectionsComplexShortComplex X U V K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportRestrictionSectionsShortComplex_shortExact X U V (K.X n)

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

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

attribute [local instance] derivedSupportLocalizationSheafDerivedCategory

attribute [local instance] derivedSupportLocalizationGroupDerivedCategory

end TopCat.Sheaf
