/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

public import Other.AlgebraicTopology.CechNerveEvaluation
public import Other.AlgebraicTopology.FirstQuadrantRowwiseTotalization
public import Other.AlgebraicTopology.SingularCoverSmallPresentation

import Mathlib.Logic.Equiv.PartialEquiv

/-!
This module generalizes the rowwise Čech globalization in Paul Lezeau's
`sphere-six-complex`, files `BoundarySevenCechRowIdentificationsProof.lean` and
`BoundarySevenCechLowAssemblyProof.lean`, commit
`b200b3fa92c64b73f3f212026f191f85364f05e3`.

# Integral Čech total augmentation

Let `A` be an arrow of simplicial sets which is surjective in every simplicial degree.  After
evaluation, a chosen section gives the augmented Čech nerve an extra degeneracy.  Hence every
horizontal row of its integral Čech--simplicial bicomplex contracts onto the corresponding
degree of the target chain complex.  The first-quadrant rowwise-totalization theorem then shows
that the totalized Čech augmentation is a quasi-isomorphism.

We first retain the direct-sum total of the bicomplex concentrated in horizontal degree zero,
which is the actual target produced by functorial totalization.  An explicit two-sided chain
isomorphism then identifies it with the ordinary integral chain complex of the target.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace AlgebraicTopology

/-- Integral chains applied in the inner simplicial direction to an augmented Čech nerve. -/
public noncomputable def integralCechAugmentedChains (A : Arrow SSet) :
    SimplicialObject.Augmented (ChainComplex AddCommGrpCat ℕ) :=
  ((SimplicialObject.Augmented.whiskering SSet
    (ChainComplex AddCommGrpCat ℕ)).obj
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ))).obj
        A.augmentedCechNerve

/-- The integral Čech--simplicial first-quadrant bicomplex of an arrow of simplicial sets. -/
public noncomputable def integralCechBicomplex (A : Arrow SSet) :
    FirstQuadrantBicomplex :=
  AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj (integralCechAugmentedChains A))

/-- The outer Čech augmentation before totalization. -/
public noncomputable def integralCechOuterAugmentation (A : Arrow SSet) :
    integralCechBicomplex A ⟶
      (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj
        (A.right.chainComplex (AddCommGrpCat.of ℤ)) :=
  AlternatingFaceMapComplex.ε.app (integralCechAugmentedChains A)

/-- The totalized integral Čech augmentation. -/
public noncomputable def integralCechTotalAugmentation (A : Arrow SSet) :
    (integralCechBicomplex A).total (ComplexShape.down ℕ) ⟶
      HomologicalComplex₂.total
        ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj
          (A.right.chainComplex (AddCommGrpCat.of ℤ))) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map (integralCechOuterAugmentation A)
    (ComplexShape.down ℕ)

/-- Integral coefficients on the augmented Čech nerve of the arrow evaluated in inner degree
`q`. -/
public noncomputable abbrev integralCechEvaluationCech
    (A : Arrow SSet) (q : ℕ) : SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (cechPresentationEvaluationArrow A q).augmentedCechNerve

/-- An objectwise-surjective arrow evaluates to a split epimorphism of types. -/
public noncomputable def cechPresentationEvaluationSplitEpiOfSurjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) : SplitEpi (cechPresentationEvaluationArrow A q).hom := by
  let h := hA (Opposite.op (SimplexCategory.mk q))
  exact
    { section_ := ↾fun z ↦ Function.surjInv h z
      id := by
        ext z
        exact Function.rightInverse_surjInv h z }

/-- The evaluated Čech nerve of an objectwise-surjective arrow has an extra degeneracy. -/
public noncomputable def integralCechEvaluationExtraDegeneracyOfSurjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (integralCechEvaluationCech A q) :=
  (Arrow.AugmentedCechNerve.extraDegeneracy
    (cechPresentationEvaluationArrow A q)
    (cechPresentationEvaluationSplitEpiOfSurjective A hA q)).map
      (sigmaConst.obj (AddCommGrpCat.of ℤ))

/-- Each evaluated integral Čech row contracts onto the evaluated target. -/
public noncomputable def integralCechRowHomotopyEquivOfSurjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (integralCechEvaluationCech A q)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (integralCechEvaluationCech A q))) :=
  (integralCechEvaluationExtraDegeneracyOfSurjective A hA q).homotopyEquiv

/-- Each evaluated integral Čech-row augmentation is a quasi-isomorphism. -/
public theorem integralCechRowAugmentation_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n))
    (q : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (integralCechEvaluationCech A q)) :=
  (integralCechRowHomotopyEquivOfSurjective A hA q).quasiIso_hom

/-- Applying integral coefficients to the evaluation isomorphism identifies an actual
horizontal Čech row with the separately evaluated augmented Čech nerve. -/
public noncomputable def integralCechAugmentedRowIso
    (A : Arrow SSet) (q : ℕ) :
    ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
        (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
          ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
            (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve) ≅
      integralCechEvaluationCech A q :=
  Functor.mapIso _ (cechPresentationAugmentedEvaluationIso A q)

set_option backward.isDefEq.respectTransparency false in
/-- The actual horizontal row of the outer augmentation is canonically isomorphic, as an
arrow, to the evaluated augmentation contracted by the extra degeneracy. -/
public noncomputable def integralCechRowArrowIso
    (A : Arrow SSet) (q : ℕ) :
    Arrow.mk (firstQuadrantHorizontalRowMap
        (integralCechOuterAugmentation A) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app
        (integralCechEvaluationCech A q)) := by
  let e := integralCechAugmentedRowIso A q
  let X := ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (((SimplicialObject.Augmented.whiskering SSet (Type 0)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
          (Opposite.op (SimplexCategory.mk q)))).obj A.augmentedCechNerve)
  let F := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q
  let Y := SimplicialObject.Augmented.drop.obj (integralCechAugmentedChains A)
  let l₀ : firstQuadrantHorizontalRow (integralCechBicomplex A) q ≅
      AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj X) :=
    eqToIso (Functor.congr_obj (map_alternatingFaceMapComplex F) Y)
  let r₀ : firstQuadrantHorizontalRow
      ((ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj
        (A.right.chainComplex (AddCommGrpCat.of ℤ))) q ≅
      (ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj X) :=
    (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app
        (A.right.chainComplex (AddCommGrpCat.of ℤ))
  let e₀ : Arrow.mk (firstQuadrantHorizontalRowMap
      (integralCechOuterAugmentation A) q) ≅
      Arrow.mk (AlternatingFaceMapComplex.ε.app X) :=
    Arrow.isoMk' _ _ l₀ r₀ (by
      ext n x
      rcases n with _ | n
      · simp [l₀, r₀, X, F, Y, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow, integralCechOuterAugmentation,
          integralCechBicomplex, integralCechAugmentedChains,
          SSet.chainComplexFunctor,
          AlternatingFaceMapComplex.ε_app_f_zero]
        change (AddCommGrpCat.Hom.hom
            ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
              ((A.augmentedCechNerve.hom.app
                (Opposite.op (SimplexCategory.mk 0))).app
                  (Opposite.op (SimplexCategory.mk q))))) x =
          (AddCommGrpCat.Hom.hom
            ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
              ((A.augmentedCechNerve.hom.app
                (Opposite.op (SimplexCategory.mk 0))).app
                  (Opposite.op (SimplexCategory.mk q))))) x
        rfl
      · simp [l₀, r₀, X, F, Y, firstQuadrantHorizontalRowMap,
          firstQuadrantHorizontalRow, integralCechOuterAugmentation,
          integralCechBicomplex,
          AlternatingFaceMapComplex.ε_app_f_succ])
  let e₁ := Arrow.isoMk'
    (AlternatingFaceMapComplex.ε.app X)
    (AlternatingFaceMapComplex.ε.app (integralCechEvaluationCech A q))
    ((alternatingFaceMapComplex AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.drop.mapIso e))
    ((ChainComplex.single₀ AddCommGrpCat).mapIso
      (SimplicialObject.Augmented.point.mapIso e))
    (by exact AlternatingFaceMapComplex.ε.naturality e.hom)
  exact e₀ ≪≫ e₁

set_option linter.style.haveILetI false in
/-- The totalized integral Čech augmentation of an objectwise-surjective arrow of simplicial
sets is a quasi-isomorphism. -/
public theorem integralCechTotalAugmentation_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n)) :
    QuasiIso (integralCechTotalAugmentation A) := by
  apply firstQuadrantTotal_quasiIso_of_rows (integralCechOuterAugmentation A)
  intro q
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app
      (integralCechEvaluationCech A q)) :=
    integralCechRowAugmentation_quasiIso_of_surjective A hA q
  exact quasiIso_of_arrow_mk_iso
    (AlternatingFaceMapComplex.ε.app (integralCechEvaluationCech A q))
    (firstQuadrantHorizontalRowMap (integralCechOuterAugmentation A) q)
    (integralCechRowArrowIso A q).symm

/-- Put a chain complex in horizontal degree zero of a first-quadrant bicomplex. -/
public noncomputable abbrev firstQuadrantSingleZeroBicomplex
    (K : FirstQuadrantChainComplex) : FirstQuadrantBicomplex :=
  (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj K

/-- The degree-zero horizontal column is canonically the original chain complex. -/
public noncomputable def firstQuadrantSingleZeroColumnIso
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).X 0 ≅ K :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 K

/-- The canonical inclusion of the horizontal zero column into the total complex. -/
public noncomputable def firstQuadrantZeroColumnToTotal
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).X 0 ⟶
      (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) where
  f n := (firstQuadrantSingleZeroBicomplex K).ιTotal
    (ComplexShape.down ℕ) 0 n n (by simp)
  comm' := by
    intro i j hij
    change _ ≫
      ((firstQuadrantSingleZeroBicomplex K).D₁
        (ComplexShape.down ℕ) i j +
       (firstQuadrantSingleZeroBicomplex K).D₂
        (ComplexShape.down ℕ) i j) =
      ((firstQuadrantSingleZeroBicomplex K).X 0).d i j ≫ _
    rw [Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    have hd₁ : (firstQuadrantSingleZeroBicomplex K).d₁
        (ComplexShape.down ℕ) 0 i j = 0 := by
      apply HomologicalComplex₂.d₁_eq_zero
      simp
    rw [hd₁, zero_add]
    rw [HomologicalComplex₂.d₂_eq
      (firstQuadrantSingleZeroBicomplex K)
      (ComplexShape.down ℕ) 0 hij j (by simp)]
    change (ComplexShape.down ℕ).ε 0 • _ = _
    rw [ComplexShape.ε_zero, one_smul]

/-- Include the unique nonzero column into its total complex. -/
public noncomputable def firstQuadrantSingleZeroToTotal
    (K : FirstQuadrantChainComplex) :
    K ⟶ (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) :=
  (firstQuadrantSingleZeroColumnIso K).inv ≫ firstQuadrantZeroColumnToTotal K

set_option backward.isDefEq.respectTransparency false in
/-- Componentwise projection from a horizontal-zero total complex. -/
public noncomputable def firstQuadrantSingleZeroTotalComponent
    (K : FirstQuadrantChainComplex) (n p q : ℕ)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    ((firstQuadrantSingleZeroBicomplex K).X p).X q ⟶ K.X n := by
  rcases p with _ | p
  · change 0 + q = n at hpq
    simp only [zero_add] at hpq
    subst n
    exact (firstQuadrantSingleZeroColumnIso K).hom.f q
  · exact 0

@[simp]
public theorem firstQuadrantSingleZeroTotalComponent_zero
    (K : FirstQuadrantChainComplex) (q : ℕ) :
    firstQuadrantSingleZeroTotalComponent K q 0 q (by simp) =
      (firstQuadrantSingleZeroColumnIso K).hom.f q := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Project the total complex supported in horizontal degree zero back to its unique column. -/
public noncomputable def firstQuadrantTotalToSingleZero
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) ⟶ K where
  f n := (firstQuadrantSingleZeroBicomplex K).totalDesc
    (firstQuadrantSingleZeroTotalComponent K n)
  comm' := by
    intro i j hij
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rcases p with _ | p
    · have hqi : q = i := by simpa using hpq
      subst q
      rw [← Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      simp only [firstQuadrantSingleZeroTotalComponent_zero]
      rw [(firstQuadrantSingleZeroColumnIso K).hom.comm i j]
      change ((firstQuadrantSingleZeroBicomplex K).X 0).d i j ≫
          (firstQuadrantSingleZeroColumnIso K).hom.f j =
        (firstQuadrantSingleZeroBicomplex K).ιTotal
            (ComplexShape.down ℕ) 0 i i (by simp) ≫
            ((firstQuadrantSingleZeroBicomplex K).D₁
                (ComplexShape.down ℕ) i j +
              (firstQuadrantSingleZeroBicomplex K).D₂
                (ComplexShape.down ℕ) i j) ≫ _
      rw [← Category.assoc, Preadditive.comp_add,
        HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.ι_D₂]
      have hd₁ : (firstQuadrantSingleZeroBicomplex K).d₁
          (ComplexShape.down ℕ) 0 i j = 0 := by
        apply HomologicalComplex₂.d₁_eq_zero
        simp
      rw [hd₁, zero_add]
      rw [HomologicalComplex₂.d₂_eq
        (firstQuadrantSingleZeroBicomplex K)
        (ComplexShape.down ℕ) 0 hij j (by simp)]
      simp
    · have hzcol : IsZero
          ((firstQuadrantSingleZeroBicomplex K).X (p + 1)) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 K (p + 1) (by lia)
      have hz : IsZero
          (((firstQuadrantSingleZeroBicomplex K).X (p + 1)).X q) :=
        (HomologicalComplex.eval AddCommGrpCat
          (ComplexShape.down ℕ) q).map_isZero hzcol
      exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Projection after inclusion is the identity of the unique column. -/
public theorem firstQuadrantSingleZeroToTotal_comp_projection
    (K : FirstQuadrantChainComplex) :
    firstQuadrantSingleZeroToTotal K ≫ firstQuadrantTotalToSingleZero K =
      𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (firstQuadrantSingleZeroBicomplex K).ιTotal
      (ComplexShape.down ℕ) 0 n n (by simp) ≫
      (firstQuadrantSingleZeroBicomplex K).totalDesc _ = 𝟙 _
  rw [HomologicalComplex₂.ι_totalDesc]
  simp [firstQuadrantSingleZeroTotalComponent,
    firstQuadrantSingleZeroColumnIso]

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion after projection is the identity of the total complex. -/
public theorem firstQuadrantTotalToSingleZero_comp_inclusion
    (K : FirstQuadrantChainComplex) :
    firstQuadrantTotalToSingleZero K ≫ firstQuadrantSingleZeroToTotal K =
      𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rcases p with _ | p
  · have hqn : n = q := by simpa using hpq.symm
    cases hqn
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    dsimp only [firstQuadrantTotalToSingleZero,
      firstQuadrantSingleZeroToTotal]
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [firstQuadrantSingleZeroTotalComponent,
      firstQuadrantSingleZeroColumnIso]
    rfl
  · have hzcol : IsZero
        ((firstQuadrantSingleZeroBicomplex K).X (p + 1)) :=
      HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 K (p + 1) (by lia)
    have hz : IsZero
        (((firstQuadrantSingleZeroBicomplex K).X (p + 1)).X q) :=
      (HomologicalComplex.eval AddCommGrpCat
        (ComplexShape.down ℕ) q).map_isZero hzcol
    exact hz.eq_of_src _ _

/-- The total of a first-quadrant bicomplex concentrated in horizontal degree zero is
canonically isomorphic to its sole column. -/
public noncomputable def firstQuadrantSingleZeroTotalIso
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) ≅ K where
  hom := firstQuadrantTotalToSingleZero K
  inv := firstQuadrantSingleZeroToTotal K
  hom_inv_id := firstQuadrantTotalToSingleZero_comp_inclusion K
  inv_hom_id := firstQuadrantSingleZeroToTotal_comp_projection K

/-- The canonical integral Čech total augmentation with codomain the ordinary integral chain
complex of the target simplicial set. -/
public noncomputable def integralCechTotalAugmentationToTarget (A : Arrow SSet) :
    (integralCechBicomplex A).total (ComplexShape.down ℕ) ⟶
      A.right.chainComplex (AddCommGrpCat.of ℤ) :=
  integralCechTotalAugmentation A ≫
    firstQuadrantTotalToSingleZero
      (A.right.chainComplex (AddCommGrpCat.of ℤ))

set_option linter.style.haveILetI false in
/-- For an objectwise-surjective arrow, the canonical integral Čech total augmentation to its
target chain complex is a quasi-isomorphism. -/
public theorem integralCechTotalAugmentationToTarget_quasiIso_of_surjective
    (A : Arrow SSet)
    (hA : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (A.hom.app n)) :
    QuasiIso (integralCechTotalAugmentationToTarget A) := by
  letI : QuasiIso (integralCechTotalAugmentation A) :=
    integralCechTotalAugmentation_quasiIso_of_surjective A hA
  letI : IsIso (firstQuadrantTotalToSingleZero
      (A.right.chainComplex (AddCommGrpCat.of ℤ))) :=
    (firstQuadrantSingleZeroTotalIso
      (A.right.chainComplex (AddCommGrpCat.of ℤ))).isIso_hom
  exact quasiIso_comp _ _

namespace Singular

/-- The totalized integral Čech augmentation of the canonical cover-small presentation is a
quasi-isomorphism. -/
public theorem coverSmallIntegralCechTotalAugmentation_quasiIso
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    QuasiIso (integralCechTotalAugmentation
      (Arrow.mk (coverSmallPresentation X U))) :=
  integralCechTotalAugmentation_quasiIso_of_surjective
    (Arrow.mk (coverSmallPresentation X U))
    (coverSmallPresentation_app_surjective X U)

/-- The canonical Čech total augmentation of a cover-small presentation to its integral
singular chain complex is a quasi-isomorphism. -/
public theorem coverSmallIntegralCechTotalAugmentationToTarget_quasiIso
    {ι : Type} (X : TopCat) (U : ι → Set X) :
    QuasiIso (integralCechTotalAugmentationToTarget
      (Arrow.mk (coverSmallPresentation X U))) :=
  integralCechTotalAugmentationToTarget_quasiIso_of_surjective
    (Arrow.mk (coverSmallPresentation X U))
    (coverSmallPresentation_app_surjective X U)

end Singular

end AlgebraicTopology
