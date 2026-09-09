/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.ChartNeighborhoodOrientation

/-!
# Normalization of actual point parametrizations inside a complex chart

Point excision compares any actual target-neighborhood parametrization with the standard
compressed chart parametrization, provided its ambient coordinate action preserves the
specified translated complex class. The resulting comparison preserves the exact local
class, including its scale and sign.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (d : ℕ)

/-- Every actual injective complex-linear endomorphism preserves the fixed complex class. -/
theorem centeredComplexLinear_preserves_standardComplexLocalClass
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (hL : Function.Injective L) :
    relativeHomologyMap ℚ (2 * d) (centeredComplexEmbeddingPair d L L.continuous hL 0)
      (standardComplexLocalClass d) = standardComplexLocalClass d := by
  let A := complexMatrixOfContinuousLinearMap d L
  have hAL : (A.mulVecLin.toContinuousLinearMap :
      (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = L := by
    apply ContinuousLinearMap.ext
    intro w
    exact complexMatrixOfContinuousLinearMap_mulVec d L w
  apply relativeHomologyMap_complexDifferentiable_standardComplexLocalClass d A
    (complexMatrixOfContinuousLinearMap_det_ne_zero d L hL)
  rw [hAL]
  simpa only [add_zero] using L.hasFDerivAt.sub_const (L 0)

variable {M : Type} [TopologicalSpace M]
  (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

/-- The inverse chart on its target, with the exact ambient basepoint as codomain. -/
def chartTargetInverseAtSourcePairMap :
    neighborhoodPointComplementPair e.target (e x) ⟶ pointComplementPair x := by
  have hne (v : {v : e.target | v.1 ≠ e x}) : e.symm v.1.1 ≠ x := by
    intro h
    apply v.2
    calc
      v.1.1 = e (e.symm v.1.1) := (e.right_inv v.1.2).symm
      _ = e x := congrArg e h
  exact TopPair.ofHom
    (TopCat.ofHom ⟨fun v => e.symm v.1, e.symm.continuousOn.domRestrict⟩)
    (TopCat.ofHom ⟨fun v => ⟨e.symm v.1.1, hne v⟩,
      (e.symm.continuousOn.domRestrict.comp continuous_subtype_val).subtype_mk hne⟩) rfl

/-- The canonical radial target parametrization followed by the inverse chart is exactly
the original chart-model pair map. -/
lemma radialTargetPointPairMap_chartTargetInverseAtSource :
    radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
      (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
      (OpenPartialHomeomorph.univBall_apply_zero _ _) ≫
        chartTargetInverseAtSourcePairMap d e x = chartModelEmbeddingPair d e x hx := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext v
    apply Subtype.ext
    change e.symm (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) (v.1 + 0)) = _
    rw [add_zero]
    rfl
  · ext v
    have h (w : Fin d → ℂ) :
        e.symm (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) (w + 0)) =
          e.symm (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) w) := by
      rw [add_zero]
    exact h v

/-- A normalized actual coordinate parametrization gives the exact chart-local class.
The only comparison used in this proof is genuine point-neighborhood excision. -/
theorem chartTargetPointPairMap_localClass
    (P : standardComplexPuncturedPair d ⟶ neighborhoodPointComplementPair e.target (e x))
    (hP : relativeHomologyMap ℚ (2 * d)
      (P ≫ neighborhoodPointComplementPairMap e.target (e x)) (standardComplexLocalClass d) =
      relativeHomologyMap ℚ (2 * d)
        (translationPointComplementPairMap (Fin d → ℂ) (e x)) (standardComplexLocalClass d)) :
    relativeHomologyMap ℚ (2 * d) (P ≫ chartTargetInverseAtSourcePairMap d e x)
      (standardComplexLocalClass d) = localClassOfChart d e x hx := by
  let Q := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
    (OpenPartialHomeomorph.univBall_apply_zero _ _)
  have hPQ : relativeHomologyMap ℚ (2 * d) P (standardComplexLocalClass d) =
      relativeHomologyMap ℚ (2 * d) Q (standardComplexLocalClass d) := by
    apply (neighborhoodPointComplement_relativeHomologyMap_bijective e.target (e x)
      e.open_target (e.map_source hx) (2 * d)).1
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hP]
    exact (radialTargetPointPairMap_normalization d e.target (e x) (chartRadius d e x hx)
      (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) 0 (e x)
      (OpenPartialHomeomorph.univBall_apply_zero _ _)).symm
  rw [relativeHomologyMap_comp, LinearMap.comp_apply, hPQ,
    ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  change relativeHomologyMap ℚ (2 * d)
    (Q ≫ chartTargetInverseAtSourcePairMap d e x) (standardComplexLocalClass d) = _
  rw [show Q ≫ chartTargetInverseAtSourcePairMap d e x = chartModelEmbeddingPair d e x hx
    from radialTargetPointPairMap_chartTargetInverseAtSource d e x hx]
  rfl

end AlgebraicTopology.Singular
