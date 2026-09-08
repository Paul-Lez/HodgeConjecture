/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionPointNormalCoordinates
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentPointPurity
public import HodgeConjecture.Other.AlgebraicTopology.ChartTargetPointClassNormalization

/-!
# Exact point normalization of the general smooth normal-purity construction

The actual zero-dimensional normal-purity parametrization has the complex orientation
of the existing point class. The proof computes its coordinate map, uses complex-linear
orientation invariance and positive radial normalization, and then applies genuine point
excision. Thus the general normal coclass restricts to the existing point coclass with
exact coefficient `1`, not just up to a nonzero rational factor.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme}
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ sX = sY) (d : ℕ)
  [SmoothOfRelativeDimension 0 sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i] (z : ComplexPoint Y sY)
  (V : Opens (ComplexPoint X sX)) (hzV : Point.map i hi z ∈ V)

/-- The actual normal parametrization factored through the genuine ambient chart target. -/
def smoothClosedPointNormalTargetPairMap :
    standardComplexPuncturedPair d ⟶
      neighborhoodPointComplementPair (localChart sX d (Point.map i hi z)).target
        (localChart sX d (Point.map i hi z) (Point.map i hi z)) := by
  let c := localChart sX d (Point.map i hi z) (Point.map i hi z)
  let L := closedImmersionPointNormalLinearMap sX sY i hi d z
  let r := smoothClosedPointNormalRadius sX sY i hi d z V hzV
  let R := OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r
  have hmem (w : Fin d → ℂ) : c + L (R w) ∈
      (localChart sX d (Point.map i hi z)).target := by
    rw [← smoothClosedPointNormalModelPairMap_coordinates sX sY i hi d z V hzV w]
    exact (localChart sX d (Point.map i hi z)).map_source
      (smoothClosedPointNormalModelPairMap_mem_chartSource sX sY i hi d z V hzV w)
  have hne (w : Fin d → ℂ) (hw : w ≠ 0) : c + L (R w) ≠ c := by
    intro h
    apply hw
    apply injective_complexUnivBall d 0 r
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    apply closedImmersionPointNormalLinearMap_injective sX sY i hi d z
    simpa only [map_zero] using add_left_cancel (h.trans (add_zero c).symm)
  have hcont : Continuous (fun w => c + L (R w)) :=
    continuous_const.add (L.continuous.comp (continuous_complexUnivBall d 0 r))
  exact TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨c + L (R w), hmem w⟩, hcont.subtype_mk hmem⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨c + L (R w.1), hmem w.1⟩, hne w.1 w.2⟩,
      ((hcont.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩) rfl

/-- The inverse-chart factor recovers the exact general normal-purity pair map. -/
theorem smoothClosedPointNormalTargetPairMap_inverseChart :
    smoothClosedPointNormalTargetPairMap sX sY i hi d z V hzV ≫
      chartTargetInverseAtSourcePairMap d (localChart sX d (Point.map i hi z))
        (Point.map i hi z) = smoothClosedPointNormalModelPairMap sX sY i hi d z V hzV := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    exact (smoothClosedPointNormalModelPairMap_apply sX sY i hi d z V hzV w.1).symm
  · ext w
    exact (smoothClosedPointNormalModelPairMap_apply sX sY i hi d z V hzV w).symm

/-- Ambient coordinates expose the positive radial, complex-linear, and translation factors. -/
theorem smoothClosedPointNormalTargetPairMap_comp_inclusion :
    smoothClosedPointNormalTargetPairMap sX sY i hi d z V hzV ≫
      neighborhoodPointComplementPairMap (localChart sX d (Point.map i hi z)).target
        (localChart sX d (Point.map i hi z) (Point.map i hi z)) =
      centeredComplexEmbeddingPair d
        (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (smoothClosedPointNormalRadius sX sY i hi d z V hzV))
        (continuous_complexUnivBall d 0 _) (injective_complexUnivBall d 0 _) 0 ≫
      centeredComplexEmbeddingPair d (closedImmersionPointNormalLinearMap sX sY i hi d z)
        (closedImmersionPointNormalLinearMap sX sY i hi d z).continuous
        (closedImmersionPointNormalLinearMap_injective sX sY i hi d z) 0 ≫
      translationPointComplementPairMap (Fin d → ℂ)
        (localChart sX d (Point.map i hi z) (Point.map i hi z)) := by
  let c := localChart sX d (Point.map i hi z) (Point.map i hi z)
  let L := closedImmersionPointNormalLinearMap sX sY i hi d z
  let r := smoothClosedPointNormalRadius sX sY i hi d z V hzV
  have h (w : Fin d → ℂ) :
      c + L (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r w) =
        L (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r (w + 0) -
          OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r 0 + 0) - L 0 + c := by
    simp only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero, map_zero]
    exact add_comm _ _
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    exact h w.1
  · ext w
    exact h w

/-- The actual normal model sends the fixed standard class to the exact ambient chart class. -/
theorem smoothClosedPointNormalModelPairMap_localClass :
    relativeHomologyMap ℚ (2 * d) (smoothClosedPointNormalModelPairMap sX sY i hi d z V hzV)
      (standardComplexLocalClass d) =
        localClassOfChart d (localChart sX d (Point.map i hi z)) (Point.map i hi z)
          (mem_localChart_source sX d (Point.map i hi z)) := by
  rw [← smoothClosedPointNormalTargetPairMap_inverseChart]
  apply chartTargetPointPairMap_localClass
  rw [smoothClosedPointNormalTargetPairMap_comp_inclusion, relativeHomologyMap_comp,
    LinearMap.comp_apply, centeredComplexUnivBall_preserves_standardComplexLocalClass d 0 _
      (smoothClosedPointNormalRadius_pos sX sY i hi d z V hzV) 0,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    centeredComplexLinear_preserves_standardComplexLocalClass]

/-- The actual normal class restricts to the old precisely normalized local point class. -/
theorem smoothClosedPointNormalClass_to_analyticPointLocalHomologyClass :
    relativeHomologyMap ℚ (2 * d) (smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV)
      (smoothClosedSupportNormalClass sX sY i hi 0 d z V hzV) =
        analyticPointLocalHomologyClass sX d (Point.map i hi z) := by
  have hclass : smoothClosedSupportNormalClass sX sY i hi 0 d z V hzV =
      relativeHomologyMap ℚ (2 * d)
        (normalSliceSection (Fin 0 → ℂ) d ≫
          (smoothClosedSupportNeighborhoodPairIso sX sY i hi 0 d z V hzV).hom)
        (standardComplexLocalClass d) := by
    rw [relativeHomologyMap_comp]
    rfl
  rw [hclass, ← LinearMap.comp_apply, ← relativeHomologyMap_comp, Category.assoc]
  exact smoothClosedPointNormalModelPairMap_localClass sX sY i hi d z V hzV

variable [IsProjective sX]

/-- The old point coclass evaluates to exactly one on the actual general normal class.
This theorem computes the normalization; it does not postulate a trace comparison. -/
@[simp]
theorem analyticPointLocalCoclass_apply_smoothClosedPointNormalClass :
    relativeCohomologyMap ℚ (2 * d) (smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV)
      (analyticPointLocalCoclass sX d (Point.map i hi z))
      (smoothClosedSupportNormalClass sX sY i hi 0 d z V hzV) = 1 := by
  rw [relativeCohomologyMap_apply,
    smoothClosedPointNormalClass_to_analyticPointLocalHomologyClass,
    analyticPointLocalCoclass_apply_localClass]

/-- The general normal-purity coclass, in zero source dimension, agrees exactly with
the existing point coclass pulled back along the actual local inclusion. -/
theorem smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass :
    smoothClosedSupportNormalCoclass sX sY i hi 0 d z V hzV =
      relativeCohomologyMap ℚ (2 * d)
        (smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV)
        (analyticPointLocalCoclass sX d (Point.map i hi z)) := by
  symm
  apply smoothClosedSupportNormalCoclass_unique
  exact analyticPointLocalCoclass_apply_smoothClosedPointNormalClass sX sY i hi d z V hzV

/-- The exact comparison also preserves every rational multiplicity. -/
theorem smoothClosedPointNormalCoclass_smul_eq_analyticPointLocalCoclass (q : ℚ) :
    q • smoothClosedSupportNormalCoclass sX sY i hi 0 d z V hzV =
      relativeCohomologyMap ℚ (2 * d)
        (smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV)
        (q • analyticPointLocalCoclass sX d (Point.map i hi z)) := by
  rw [map_smul, smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass]

end AlgebraicGeometry.ComplexPoint
