/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSections
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import Other.Algebra.Homology.DerivedCategory.MappingCoconeShortExact

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Canonical localization comparison to the homotopy fiber of actual
restriction, on a coefficient complex. -/
def supportRestrictionToFiber (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (supportRestrictionSectionsComplexShortComplex X U V K).X₁ ⟶
      CochainComplex.mappingCocone
        (supportRestrictionSectionsComplexShortComplex X U V K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

/-- Injectivity proves that the canonical localization comparison is a
quasi-isomorphism; no duality or acyclicity certificate is supplied. -/
lemma supportRestrictionToFiber_quasiIso (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (supportRestrictionToFiber X U V K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (supportRestrictionSectionsComplexShortComplex_shortExact X U V K)

/-- The analogous canonical localization comparison before global sections. -/
def sheafSupportRestrictionToFiber
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (supportRestrictionComplexShortComplex X U K).X₁ ⟶
      CochainComplex.mappingCocone (supportRestrictionComplexShortComplex X U K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

set_option backward.isDefEq.respectTransparency false in
lemma sheafSupportRestrictionToFiber_quasiIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (sheafSupportRestrictionToFiber X U K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _ <|
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
      dsimp [supportRestrictionComplexShortComplex]
      exact
        { exact := ShortComplex.exact_kernel _
          mono_f := inferInstanceAs (Mono (kernel.ι _))
          epi_g := inferInstanceAs (Epi ((toOpenRestrictionPushforward X U).app (K.X n))) }

attribute [local instance] derivedSupportLocalizationSheafDerivedCategory

attribute [local instance] derivedSupportLocalizationGroupDerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Localization for the actual derived support functor, evaluated on a
bounded-below injective model. The fiber is built from actual restriction, not
an unrelated morphism between isomorphic cohomology groups. -/
def derivedClosedSupportInjectiveFiberIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedClosedSupportSections X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCocone
          (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
            (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
              (.up ℤ)).obj I.obj)).g) := by
  let : ∀ n, Injective
      ((((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
        (.up ℤ)).obj I.obj).X n) := fun n => (I.obj.X n).property
  have := supportRestrictionToFiber_quasiIso X Z.compl ⊤
    (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
      (.up ℤ)).obj I.obj)
  exact derivedClosedSupportInjectiveModelIso X Z I ≪≫
    asIso (DerivedCategory.Q.map (supportRestrictionToFiber X Z.compl ⊤ _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-valued derived unit on a bounded-below injective model. -/
def derivedSheafSupportInjectiveModelIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedSheafSectionsWithClosedSupport X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (supportRestrictionComplexShortComplex X Z.compl
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).X₁ :=
  (DerivedCategory.Plus.ι.mapIso
    (asIso ((derivedSheafSectionsWithClosedSupportUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I))))).symm ≪≫
    (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheaf-valued localization for the actual derived support functor on a
bounded-below injective model, through the canonical restriction fiber. -/
def derivedSheafSupportInjectiveFiberIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedSheafSectionsWithClosedSupport X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCocone
          (supportRestrictionComplexShortComplex X Z.compl
            (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
              (.up ℤ)).obj I.obj)).g) := by
  let : ∀ n, Injective
      ((((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
        (.up ℤ)).obj I.obj).X n) := fun n => (I.obj.X n).property
  have := sheafSupportRestrictionToFiber_quasiIso X Z.compl
    (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
      (.up ℤ)).obj I.obj)
  exact derivedSheafSupportInjectiveModelIso X Z I ≪≫
    asIso (DerivedCategory.Q.map (sheafSupportRestrictionToFiber X Z.compl _))
/-- The localization comparison preserves the actual support-forgetting map,
including its sign. -/
@[reassoc (attr := simp)]
lemma supportRestrictionToFiber_fst (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    supportRestrictionToFiber X U V K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionSectionsComplexShortComplex X U V K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

@[reassoc (attr := simp)]
lemma sheafSupportRestrictionToFiber_fst
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    sheafSupportRestrictionToFiber X U K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionComplexShortComplex X U K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedClosedSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedClosedSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedClosedSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedClosedSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedSheafSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedSheafSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedSheafSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionComplexShortComplex X Z.compl
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedSheafSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]
end TopCat.Sheaf
