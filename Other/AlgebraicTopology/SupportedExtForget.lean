/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Mathlib.Algebra.Homology.HomComplexPrecomp
public import Other.AlgebraicTopology.FreeAbelianTerminalEvaluation

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pair-sheaf Hom-complex model forgets support by the actual inclusion of sections. -/
lemma homComplexPairSheafIsoSupportedSections_forget
    (Y : TopCat.{0}) (U : Opens Y) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ) :
    (homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq _) K).hom ≫
        (supportRestrictionSectionsComplexShortComplex Y U ⊤ K).f =
      CochainComplex.HomComplex.precompMap
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat Y) 0).map
          ((constantFunctor Y).map (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom ≫
            (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
              (J := Opens.grothendieckTopology Y) (T := (⊤ : Opens Y)) isTerminalTop).inv ≫
            cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
              (Opens.grothendieckTopology Y)).map (homOfLE (le_top : U ≤ ⊤))))) K ≫
        (homComplexSingleIntegerIsoGlobalSections Y K).hom := by
  dsimp only [homComplexSingleIntegerIsoGlobalSections, Iso.trans_hom]
  rw [← Category.assoc,
    CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda]
  dsimp only [homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [Category.assoc, Category.assoc]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  ext φ
  change (((sheafSectionsSupportedOutsideInclusion Y U).app (K.X n)).hom.app (op ⊤))
      ((pairSheafHomIsoSupportedSections Y U ⊤ U (top_inf_eq _) (K.X n)).hom φ) =
    integerConstantHomAddEquivGlobalSections (K.X n)
      (((constantFunctor Y).map (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom ≫
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
          (J := Opens.grothendieckTopology Y) (T := (⊤ : Opens Y)) isTerminalTop).inv ≫
        cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology Y)).map (homOfLE (le_top : U ≤ ⊤)))) ≫ φ)
  rw [Category.assoc, Category.assoc,
    integerConstantHomAddEquivGlobalSections_freeAbelianTerminal]
  exact ConcreteCategory.congr_hom
    (pairSheafHomIsoSupportedSections_hom_inclusion Y U ⊤ U (top_inf_eq _) (K.X n)) φ

end TopCat.Sheaf
