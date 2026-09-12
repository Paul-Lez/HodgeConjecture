/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ClosedImmersionPointNormalCoordinates
public import Other.AlgebraicGeometry.CycleComponentPointPurity
public import Other.AlgebraicTopology.ChartTargetPointClassNormalization

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

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (d : ℕ)
  [SmoothOfRelativeDimension 0 Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)
  (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- The actual normal parametrization factored through the genuine ambient chart target. -/
def smoothClosedPointNormalTargetPairMap :
    standardComplexPuncturedPair d ⟶
      neighborhoodPointComplementPair (localChart X d (Point.map i z)).target
        (localChart X d (Point.map i z) (Point.map i z)) := by
  let c := localChart X d (Point.map i z) (Point.map i z)
  let L := closedImmersionPointNormalLinearMap X Y i d z
  let r := smoothClosedPointNormalRadius X Y i d z V hzV
  let R := OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r
  have hmem (w : Fin d → ℂ) : c + L (R w) ∈
      (localChart X d (Point.map i z)).target := by
    rw [← smoothClosedPointNormalModelPairMap_coordinates X Y i d z V hzV w]
    exact (localChart X d (Point.map i z)).map_source
      (smoothClosedPointNormalModelPairMap_mem_chartSource X Y i d z V hzV w)
  have hne (w : Fin d → ℂ) (hw : w ≠ 0) : c + L (R w) ≠ c := by
    intro h
    apply hw
    apply injective_complexUnivBall d 0 r
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    apply closedImmersionPointNormalLinearMap_injective X Y i d z
    simpa only [map_zero] using add_left_cancel (h.trans (add_zero c).symm)
  have hcont : Continuous (fun w => c + L (R w)) :=
    continuous_const.add (L.continuous.comp (continuous_complexUnivBall d 0 r))
  exact TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨c + L (R w), hmem w⟩, hcont.subtype_mk hmem⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨c + L (R w.1), hmem w.1⟩, hne w.1 w.2⟩,
      ((hcont.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩) rfl

/-- The inverse-chart factor recovers the exact general normal-purity pair map. -/
theorem smoothClosedPointNormalTargetPairMap_inverseChart :
    smoothClosedPointNormalTargetPairMap X Y i d z V hzV ≫
      chartTargetInverseAtSourcePairMap d (localChart X d (Point.map i z))
        (Point.map i z) = smoothClosedPointNormalModelPairMap X Y i d z V hzV := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    exact Subtype.ext (smoothClosedPointNormalModelPairMap_apply X Y i d z V hzV w.1).symm
  · ext w
    exact (smoothClosedPointNormalModelPairMap_apply X Y i d z V hzV w).symm

/-- Ambient coordinates expose the positive radial, complex-linear, and translation factors. -/
theorem smoothClosedPointNormalTargetPairMap_comp_inclusion :
    smoothClosedPointNormalTargetPairMap X Y i d z V hzV ≫
      neighborhoodPointComplementPairMap (localChart X d (Point.map i z)).target
        (localChart X d (Point.map i z) (Point.map i z)) =
      centeredComplexEmbeddingPair d
        (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
          (smoothClosedPointNormalRadius X Y i d z V hzV))
        (continuous_complexUnivBall d 0 _) (injective_complexUnivBall d 0 _) 0 ≫
      centeredComplexEmbeddingPair d (closedImmersionPointNormalLinearMap X Y i d z)
        (closedImmersionPointNormalLinearMap X Y i d z).continuous
        (closedImmersionPointNormalLinearMap_injective X Y i d z) 0 ≫
      translationPointComplementPairMap (Fin d → ℂ)
        (localChart X d (Point.map i z) (Point.map i z)) := by
  let c := localChart X d (Point.map i z) (Point.map i z)
  let L := closedImmersionPointNormalLinearMap X Y i d z
  let r := smoothClosedPointNormalRadius X Y i d z V hzV
  have h (w : Fin d → ℂ) :
      c + L (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r w) =
        L (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r (w + 0) -
          OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r 0 + 0) - L 0 + c := by
    simp only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero, map_zero]
    exact add_comm _ _
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    exact Subtype.ext (h w.1)
  · ext w
    exact h w

/-- The actual normal model sends the fixed standard class to the exact ambient chart class. -/
theorem smoothClosedPointNormalModelPairMap_localClass :
    relativeHomologyMap ℚ (2 * d) (smoothClosedPointNormalModelPairMap X Y i d z V hzV)
      (standardComplexLocalClass d) =
        localClassOfChart d (localChart X d (Point.map i z)) (Point.map i z)
          (mem_localChart_source X d (Point.map i z)) := by
  rw [← smoothClosedPointNormalTargetPairMap_inverseChart]
  apply chartTargetPointPairMap_localClass
  rw [smoothClosedPointNormalTargetPairMap_comp_inclusion, relativeHomologyMap_comp,
    LinearMap.comp_apply, centeredComplexUnivBall_preserves_standardComplexLocalClass d 0 _
      (smoothClosedPointNormalRadius_pos X Y i d z V hzV) 0,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    centeredComplexLinear_preserves_standardComplexLocalClass]

/-- The actual normal class restricts to the old precisely normalized local point class. -/
theorem smoothClosedPointNormalClass_to_analyticPointLocalHomologyClass :
    relativeHomologyMap ℚ (2 * d) (smoothClosedPointNeighborhoodPairMap X Y i d z V hzV)
      (smoothClosedSupportNormalClass X Y i 0 d z V hzV) =
        analyticPointLocalHomologyClass X d (Point.map i z) := by
  have hclass : smoothClosedSupportNormalClass X Y i 0 d z V hzV =
      relativeHomologyMap ℚ (2 * d)
        (normalSliceSection (Fin 0 → ℂ) d ≫
          (smoothClosedSupportNeighborhoodPairIso X Y i 0 d z V hzV).hom)
        (standardComplexLocalClass d) := by
    rw [relativeHomologyMap_comp]
    rfl
  rw [hclass, ← LinearMap.comp_apply, ← relativeHomologyMap_comp, Category.assoc]
  exact smoothClosedPointNormalModelPairMap_localClass X Y i d z V hzV

variable [IsProjective X.hom]

/-- The old point coclass evaluates to exactly one on the actual general normal class.
This theorem computes the normalization; it does not postulate a trace comparison. -/
@[simp]
theorem analyticPointLocalCoclass_apply_smoothClosedPointNormalClass :
    relativeCohomologyEquivDualHomology ℚ
        (smoothClosedSupportNeighborhoodPair X Y i 0 d z V hzV) (2 * d)
        (relativeCohomologyMap ℚ (2 * d)
          (smoothClosedPointNeighborhoodPairMap X Y i d z V hzV)
          (analyticPointLocalCoclass X d (Point.map i z)))
      (smoothClosedSupportNormalClass X Y i 0 d z V hzV) = 1 := by
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    smoothClosedPointNormalClass_to_analyticPointLocalHomologyClass,
    analyticPointLocalCoclass_apply_localClass]

/-- The general normal-purity coclass, in zero source dimension, agrees exactly with
the existing point coclass pulled back along the actual local inclusion. -/
theorem smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass :
    smoothClosedSupportNormalCoclass X Y i 0 d z V hzV =
      relativeCohomologyMap ℚ (2 * d)
        (smoothClosedPointNeighborhoodPairMap X Y i d z V hzV)
        (analyticPointLocalCoclass X d (Point.map i z)) :=
  (smoothClosedSupportNormalCoclass_unique X Y i 0 d z V hzV _
    (analyticPointLocalCoclass_apply_smoothClosedPointNormalClass X Y i d z V hzV)).symm

/-- The exact comparison also preserves every rational multiplicity. -/
theorem smoothClosedPointNormalCoclass_smul_eq_analyticPointLocalCoclass (q : ℚ) :
    q • smoothClosedSupportNormalCoclass X Y i 0 d z V hzV =
      relativeCohomologyMap ℚ (2 * d)
        (smoothClosedPointNeighborhoodPairMap X Y i d z V hzV)
        (q • analyticPointLocalCoclass X d (Point.map i z)) := by
  rw [map_smul, smoothClosedPointNormalCoclass_eq_analyticPointLocalCoclass]

end AlgebraicGeometry.ComplexPoint
