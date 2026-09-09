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

public import Other.AlgebraicTopology.SingularCoverSmall
public import Mathlib.Algebra.Homology.QuasiIso

/-!
This module generalizes the cover-presentation argument in Paul Lezeau's
`sphere-six-complex`, file `BoundarySevenFaceNeighborhoodComparison.lean`, commit
`b2be78876f2d93b914756d8e7e7d82fbe9fa1a23`.

# The canonical presentation of cover-small singular simplices

For a family of subsets `U`, the coproduct of the singular sets of its members maps onto the
cover-small singular subcomplex.  This is surjective in every simplicial degree.  Evaluating in
one degree therefore gives a split epimorphism of types (using choice), whose augmented Čech
nerve has an extra degeneracy.  Applying free integral coefficients yields the standard
horizontal row contraction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace AlgebraicTopology.Singular

section

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The coproduct of the singular simplicial sets of all cover members. -/
public noncomputable abbrev coverSmallPresentationSource : SSet :=
  sigmaObj (fun i : ι ↦ TopCat.toSSet.obj (TopCat.of (U i)))

/-- The canonical presentation of the cover-small singular simplicial set. -/
public noncomputable def coverSmallPresentation :
    coverSmallPresentationSource X U ⟶ coverSmallSingularSubcomplex X U :=
  Sigma.desc fun i ↦ coverMemberToSmallSingularSet X U i

@[reassoc (attr := simp)]
public theorem coverSmallPresentation_iota (i : ι) :
    Sigma.ι (fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))) i ≫
        coverSmallPresentation X U =
      coverMemberToSmallSingularSet X U i :=
  Sigma.ι_desc _ _

/-- The canonical cover-small presentation is surjective in every simplicial degree. -/
public theorem coverSmallPresentation_app_surjective
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((coverSmallPresentation X U).app n) := by
  intro z
  obtain ⟨i, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage X U z.1).mp z.2
  refine ⟨(Sigma.ι
    (fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))) i).app n y, ?_⟩
  apply Subtype.ext
  have hcat :
      Sigma.ι (fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))) i ≫
          coverSmallPresentation X U ≫
          (coverSmallSingularSubcomplex X U).ι =
        TopCat.toSSet.map (topologicalSubsetInclusion X (U i)) := by
    rw [← Category.assoc, coverSmallPresentation_iota,
      coverMemberToSmallSingularSet_comp_inclusion]
  exact (ConcreteCategory.congr_hom (congr_app hcat n) y).trans hy

/-- The canonical presentation is an epimorphism of simplicial sets. -/
public instance coverSmallPresentation_epi : Epi (coverSmallPresentation X U) := by
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [CategoryTheory.epi_iff_surjective]
  exact coverSmallPresentation_app_surjective X U n

/-- The cover presentation evaluated in one simplicial degree. -/
public noncomputable def coverSmallPresentationEvaluationArrow
    (n : SimplexCategoryᵒᵖ) : Arrow (Type 0) :=
  Arrow.mk ((coverSmallPresentation X U).app n)

/-- A chosen section of the degreewise-surjective evaluated presentation. -/
public noncomputable def coverSmallPresentationEvaluationSplitEpi
    (n : SimplexCategoryᵒᵖ) :
    SplitEpi (coverSmallPresentationEvaluationArrow X U n).hom := by
  let h := coverSmallPresentation_app_surjective X U n
  exact
    { section_ := ↾fun z ↦ Function.surjInv h z
      id := by
        ext z
        exact Function.rightInverse_surjInv h z }

/-- The evaluated augmented Čech nerve of the cover presentation has an extra degeneracy. -/
public noncomputable def coverSmallPresentationEvaluationExtraDegeneracy
    (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (coverSmallPresentationEvaluationArrow X U n).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (coverSmallPresentationEvaluationArrow X U n)
    (coverSmallPresentationEvaluationSplitEpi X U n)

/-- Integral coefficients on the evaluated augmented Čech nerve. -/
public noncomputable abbrev coverSmallIntegralEvaluationCech
    (k : ℕ) : SimplicialObject.Augmented AddCommGrpCat :=
  ((SimplicialObject.Augmented.whiskering (Type 0) AddCommGrpCat).obj
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj
      (coverSmallPresentationEvaluationArrow X U
        (Opposite.op (SimplexCategory.mk k))).augmentedCechNerve

/-- Integral coefficients preserve the extra degeneracy. -/
public noncomputable def coverSmallIntegralEvaluationExtraDegeneracy
    (k : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (coverSmallIntegralEvaluationCech X U k) :=
  (coverSmallPresentationEvaluationExtraDegeneracy X U
    (Opposite.op (SimplexCategory.mk k))).map
      (sigmaConst.obj (AddCommGrpCat.of ℤ))

/-- Every integral horizontal Čech row contracts onto the corresponding cover-small chain
group. -/
public noncomputable def coverSmallIntegralCechRowHomotopyEquiv
    (k : ℕ) :
    HomotopyEquiv
      (AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (coverSmallIntegralEvaluationCech X U k)))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (SimplicialObject.Augmented.point.obj
          (coverSmallIntegralEvaluationCech X U k))) :=
  (coverSmallIntegralEvaluationExtraDegeneracy X U k).homotopyEquiv

/-- Each evaluated integral Čech-row augmentation is a quasi-isomorphism. -/
public theorem coverSmallIntegralCechRowAugmentation_quasiIso
    (k : ℕ) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (coverSmallIntegralEvaluationCech X U k)) :=
  (coverSmallIntegralCechRowHomotopyEquiv X U k).quasiIso_hom

end

end AlgebraicTopology.Singular
