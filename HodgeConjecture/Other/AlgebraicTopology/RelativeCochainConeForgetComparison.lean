/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.RelativeCochainConeNaturality
public import HodgeConjecture.Other.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality

/-!
# Ordinary-target compatibility of the two relative cone comparisons

The legacy triangle completion and the explicit natural cone lift need not
be identified as maps of relative cohomology groups. Both respect the actual
cone connecting morphism. Consequently their composites with the actual
inclusion of dual relative cochains into ambient cochains agree.

This is an ordinary-target comparison, not a claim of general naturality or
canonicity for the legacy completed triangle map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopPair.{u})

/-- The legacy triangle completion respects the same negative shifted
relative-to-ambient inclusion as the explicit canonical lift. -/
@[reassoc]
theorem relativeDualShiftIsoCochainCone_hom_connecting :
    (relativeDualShiftIsoCochainCone R X).hom ≫
        (CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X)).mor₃ =
      -((HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).map
        (relativeDualCochainShortComplexInt R X).f)⟦(1 : ℤ)⟧' := by
  exact relativeDualShiftIsoCochainCone_hom_comp_mor₃ R X

/-- Inverting the legacy completion retains the prescribed sign on the
actual inclusion into ambient cochains. -/
@[reassoc]
theorem relativeDualShiftIsoCochainCone_inv_inclusion :
    (relativeDualShiftIsoCochainCone R X).inv ≫
        ((HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).map
          (relativeDualCochainShortComplexInt R X).f)⟦(1 : ℤ)⟧' =
      -(CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X)).mor₃ := by
  have h := congrArg (fun f => (relativeDualShiftIsoCochainCone R X).inv ≫ f)
    (relativeDualShiftIsoCochainCone_hom_connecting R X)
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Preadditive.comp_neg] at h
  rw [h, neg_neg]

/-- After passing to integer-graded homology, the legacy comparison followed
by actual inclusion is exactly the negative cone connecting map. -/
theorem relativeCochainConeHomologyIsoDualRelativeInt_inclusion (n : ℕ) :
    -((relativeCochainConeHomologyIsoDualRelativeInt R X n).hom ≫
        HomologicalComplex.homologyMap (relativeDualCochainShortComplexInt R X).f (n : ℤ)) =
      (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle (relativeCochainRestrictionInt R X)).mor₃
        ((n : ℤ) - 1) (n : ℤ) (by omega) := by
  let Q := HomotopyCategory.quotient (ModuleCat R) (.up ℤ)
  let H := HomotopyCategory.homologyFunctor (ModuleCat R) (.up ℤ) 0
  let Hc := HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) 0
  let F (j : ℤ) := HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) j
  let S := relativeDualCochainShortComplexInt R X
  let C := CochainComplex.mappingCone (relativeCochainRestrictionInt R X)
  let e := relativeDualShiftIsoCochainCone R X
  have hn : (1 : ℤ) + ((n : ℤ) - 1) = (n : ℤ) := by omega
  have hF : (F (n : ℤ)).hom.app S.X₁ ≫ HomologicalComplex.homologyMap S.f (n : ℤ) =
      (H.shift (n : ℤ)).map (Q.map S.f) ≫ (F (n : ℤ)).hom.app S.X₂ :=
    ((F (n : ℤ)).hom.naturality S.f).symm
  change -((F ((n : ℤ) - 1)).inv.app C ≫
    (H.shift ((n : ℤ) - 1)).map e.inv ≫
    (H.shiftIso 1 ((n : ℤ) - 1) (n : ℤ) hn).hom.app (Q.obj S.X₁) ≫
    (F (n : ℤ)).hom.app S.X₁ ≫ HomologicalComplex.homologyMap S.f (n : ℤ)) = _
  rw [hF]
  rw [← H.shiftIso_hom_naturality_assoc 1 ((n : ℤ) - 1) (n : ℤ) hn (Q.map S.f)]
  rw [← Functor.map_comp_assoc, relativeDualShiftIsoCochainCone_inv_inclusion]
  simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  change (F ((n : ℤ) - 1)).inv.app C ≫
    H.shiftMap (ShiftedHom.map
      (CochainComplex.mappingCone.triangle (relativeCochainRestrictionInt R X)).mor₃ Q)
      ((n : ℤ) - 1) (n : ℤ) hn ≫ (F (n : ℤ)).hom.app S.X₂ = _
  rw [HomotopyCategory.homologyFunctor_shiftMap]
  change (F ((n : ℤ) - 1)).inv.app C ≫ (F ((n : ℤ) - 1)).hom.app C ≫
    Hc.shiftMap (CochainComplex.mappingCone.triangle (relativeCochainRestrictionInt R X)).mor₃
      ((n : ℤ) - 1) (n : ℤ) hn ≫
    (F (n : ℤ)).inv.app S.X₂ ≫ (F (n : ℤ)).hom.app S.X₂ = _
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The explicit canonical inverse has the same actual ordinary-target
normalization as the legacy cone comparison. No point-case dimension argument
or equality of the two relative equivalences is needed for this statement. -/
theorem relativeCochainCone_legacy_canonical_inclusion (n : ℕ) :
    (relativeCochainConeHomologyIsoDualRelativeInt R X n).hom ≫
        HomologicalComplex.homologyMap (relativeDualCochainShortComplexInt R X).f (n : ℤ) =
      (relativeDualCochainHomologyIsoCone R X n).inv ≫
        HomologicalComplex.homologyMap (relativeDualCochainShortComplexInt R X).f (n : ℤ) := by
  apply neg_injective
  rw [relativeCochainConeHomologyIsoDualRelativeInt_inclusion]
  exact (CochainComplex.mappingCocone.inv_homologyMap_shiftedLiftShortComplex_connecting
    (relativeDualCochainShortComplexInt R X)
    (relativeDualCochainShortComplexInt_shortExact R X)
    ((n : ℤ) - 1) (n : ℤ) (by omega)).symm

end AlgebraicTopology.Singular
