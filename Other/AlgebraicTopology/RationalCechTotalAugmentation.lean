/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.IntegralCechTotalAugmentation
public import Other.AlgebraicTopology.RationalFirstQuadrantTotalization
public import Other.AlgebraicTopology.FirstQuadrantSingleZeroTotal

/-!
# Rational Čech total augmentation

This is the coefficient-`ℚ` form of the augmented-Čech comparison.  It deliberately works in
`ModuleCat ℚ`, rather than first proving an integral result and then invoking an informal change
of coefficients.  Consequently its linear dual is the cochain model containing the literal
rational winding cocycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace AlgebraicTopology

/-- Rational chains applied in the inner simplicial direction to an augmented Čech nerve. -/
public noncomputable abbrev rationalCechAugmentedChains (A : Arrow SSet) :
    SimplicialObject.Augmented (ChainComplex (ModuleCat ℚ) ℕ) :=
  cechAugmentedChains (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) A

/-- The rational Čech--simplicial first-quadrant bicomplex of an arrow of simplicial sets. -/
public noncomputable def rationalCechBicomplex (A : Arrow SSet) :
    FirstQuadrantBicomplex (ModuleCat ℚ) :=
  AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj (rationalCechAugmentedChains A))

/-- The outer rational Čech augmentation before totalization. -/
public noncomputable def rationalCechOuterAugmentation (A : Arrow SSet) :
    rationalCechBicomplex A ⟶
      (ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).obj
        (A.right.chainComplex (ModuleCat.of ℚ ℚ)) :=
  AlternatingFaceMapComplex.ε.app (rationalCechAugmentedChains A)

/-- The totalized rational Čech augmentation. -/
public noncomputable def rationalCechTotalAugmentation (A : Arrow SSet) :
    (rationalCechBicomplex A).total (ComplexShape.down ℕ) ⟶
      HomologicalComplex₂.total
        ((ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).obj
          (A.right.chainComplex (ModuleCat.of ℚ ℚ))) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map (rationalCechOuterAugmentation A)
    (ComplexShape.down ℕ)

/-- Rational coefficients on the augmented Čech nerve of the arrow evaluated in inner degree
`q`. -/
public noncomputable abbrev rationalCechEvaluationCech
    (A : Arrow SSet) (q : ℕ) : SimplicialObject.Augmented (ModuleCat ℚ) :=
  ((SimplicialObject.Augmented.whiskering (Type 0) (ModuleCat ℚ)).obj
    (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
      (cechPresentationEvaluationArrow A q).augmentedCechNerve

/-- An objectwise-surjective arrow gives an extra degeneracy after evaluation with rational
coefficients. -/
public noncomputable def rationalCechEvaluationExtraDegeneracyOfSurjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (rationalCechEvaluationCech A q) :=
  (Arrow.AugmentedCechNerve.extraDegeneracy
    (cechPresentationEvaluationArrow A q)
    (cechPresentationEvaluationSplitEpiOfSurjective A hA q)).map
      (sigmaConst.obj (ModuleCat.of ℚ ℚ))

/-- Each evaluated rational Čech row contracts onto the evaluated target. -/
public noncomputable def rationalCechRowHomotopyEquivOfSurjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (rationalCechEvaluationCech A q)))
      ((ChainComplex.single₀ (ModuleCat ℚ)).obj
        (SimplicialObject.Augmented.point.obj
          (rationalCechEvaluationCech A q))) :=
  (rationalCechEvaluationExtraDegeneracyOfSurjective A hA q).homotopyEquiv

/-- Each evaluated rational Čech-row augmentation is a quasi-isomorphism. -/
public theorem rationalCechRowAugmentation_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (rationalCechEvaluationCech A q)) :=
  (rationalCechRowHomotopyEquivOfSurjective A hA q).quasiIso_hom

/-- Applying rational coefficients to the evaluation isomorphism identifies an actual horizontal
Čech row with the separately evaluated augmented Čech nerve. -/
public noncomputable def rationalCechAugmentedRowIso
    (A : Arrow SSet) (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering (Type 0) (ModuleCat ℚ)).obj
      (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
        (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
          ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve) ≅
      rationalCechEvaluationCech A q :=
  Functor.mapIso _ (cechPresentationAugmentedEvaluationIso A q)

set_option backward.isDefEq.respectTransparency false in
/-- The actual horizontal row of the rational outer augmentation is canonically isomorphic, as
an arrow, to the evaluated augmentation contracted by the extra degeneracy. -/
public noncomputable def rationalCechRowArrowIso
    (A : Arrow SSet) (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
        (rationalCechOuterAugmentation A) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app
        (rationalCechEvaluationCech A q)) := by
  let e := rationalCechAugmentedRowIso A q
  let X := ((SimplicialObject.Augmented.whiskering (Type 0) (ModuleCat ℚ)).obj
    (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
      (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve)
  let F := HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) q
  let Y := SimplicialObject.Augmented.drop.obj (rationalCechAugmentedChains A)
  let l₀ : firstQuadrantHorizontalRow (rationalCechBicomplex A) q ≅
      AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj X) :=
    eqToIso (Functor.congr_obj (map_alternatingFaceMapComplex F) Y)
  let r₀ : firstQuadrantHorizontalRow
      ((ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).obj
        (A.right.chainComplex (ModuleCat.of ℚ ℚ))) q ≅
      (ChainComplex.single₀ (ModuleCat ℚ)).obj
        (SimplicialObject.Augmented.point.obj X) :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app
        (A.right.chainComplex (ModuleCat.of ℚ ℚ))
  let e₀ : Arrow.mk (firstQuadrantHorizontalRowMap
      (rationalCechOuterAugmentation A) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app X) :=
    Arrow.isoMk' _ _ l₀ r₀ (by
      ext n x
      rcases n with _ | n
      · simp [l₀, r₀, X, F, Y, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow, rationalCechOuterAugmentation,
          rationalCechBicomplex, rationalCechAugmentedChains,
          AlternatingFaceMapComplex.ε_app_f_zero]
        rfl
      · simp [l₀, r₀, X, F, Y, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow, rationalCechOuterAugmentation,
          rationalCechBicomplex,
          AlternatingFaceMapComplex.ε_app_f_succ])
  let e₁ := Arrow.isoMk'
    (AlternatingFaceMapComplex.ε.app X)
    (AlternatingFaceMapComplex.ε.app (rationalCechEvaluationCech A q))
    ((alternatingFaceMapComplex (ModuleCat ℚ)).mapIso
      (SimplicialObject.Augmented.drop.mapIso e))
    ((ChainComplex.single₀ (ModuleCat ℚ)).mapIso
      (SimplicialObject.Augmented.point.mapIso e))
    (AlternatingFaceMapComplex.ε.naturality e.hom)
  exact e₀ ≪≫ e₁

set_option linter.style.haveILetI false in
/-- The totalized rational Čech augmentation of an objectwise-surjective arrow of simplicial
sets is a quasi-isomorphism. -/
public theorem rationalCechTotalAugmentation_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n)) :
    QuasiIso (rationalCechTotalAugmentation A) := by
  apply firstQuadrantTotal_quasiIso_of_rows (rationalCechOuterAugmentation A)
  intro q
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app
      (rationalCechEvaluationCech A q)) :=
    rationalCechRowAugmentation_quasiIso_of_surjective A hA q
  exact quasiIso_of_arrow_mk_iso
    (AlternatingFaceMapComplex.ε.app (rationalCechEvaluationCech A q))
    (firstQuadrantHorizontalRowMap (rationalCechOuterAugmentation A) q)
    (rationalCechRowArrowIso A q).symm

/-- The canonical rational Čech total augmentation, with codomain the ordinary rational
singular chain complex of the target simplicial set. -/
public noncomputable def rationalCechTotalAugmentationToTarget (A : Arrow SSet) :
    (rationalCechBicomplex A).total (ComplexShape.down ℕ) ⟶
      A.right.chainComplex (ModuleCat.of ℚ ℚ) :=
  rationalCechTotalAugmentation A ≫
    firstQuadrantTotalToSingleZeroGeneric
      (A.right.chainComplex (ModuleCat.of ℚ ℚ))

set_option linter.style.haveILetI false in
/-- For an objectwise-surjective arrow, the canonical rational Čech total augmentation to its
target chain complex is a quasi-isomorphism. -/
public theorem rationalCechTotalAugmentationToTarget_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n)) :
    QuasiIso (rationalCechTotalAugmentationToTarget A) := by
  letI : QuasiIso (rationalCechTotalAugmentation A) :=
    rationalCechTotalAugmentation_quasiIso_of_surjective A hA
  letI : IsIso (firstQuadrantTotalToSingleZeroGeneric
      (A.right.chainComplex (ModuleCat.of ℚ ℚ))) :=
    (firstQuadrantSingleZeroTotalIsoGeneric
      (A.right.chainComplex (ModuleCat.of ℚ ℚ))).isIso_hom
  exact quasiIso_comp _ _

namespace Singular

/-- The rational Čech total augmentation of the canonical cover-small presentation is a
quasi-isomorphism. -/
public theorem coverSmallRationalCechTotalAugmentationToTarget_quasiIso
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    QuasiIso (rationalCechTotalAugmentationToTarget
      (Arrow.mk (coverSmallPresentation X U))) :=
  rationalCechTotalAugmentationToTarget_quasiIso_of_surjective
    (Arrow.mk (coverSmallPresentation X U))
    (coverSmallPresentation_app_surjective X U)

end Singular

end AlgebraicTopology
