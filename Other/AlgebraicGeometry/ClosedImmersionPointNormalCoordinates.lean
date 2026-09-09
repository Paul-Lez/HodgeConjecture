/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import Other.AlgebraicTopology.ChartNeighborhoodOrientation

/-!
# The actual zero-dimensional normal parametrization

When the source has complex dimension zero, its constructed normal parametrization is
the ambient complex chart inverse preceded by a translation and an injective complex-
linear map. The chosen normal-space coordinates therefore retain the standard complex
orientation; they cannot introduce a sign or an arbitrary rational scaling of the class.
These formulas concern the general normal-coordinate construction specialized to `m=0`.
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

/-- The actual complex-linear normal-coordinate inclusion in source dimension zero. -/
def closedImmersionPointNormalLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  (closedImmersionDerivativeProjection sX sY i hi 0 d z).ker.subtypeL.comp
    (closedImmersionNormalKernelEquiv sX sY i hi 0 d z).symm.toContinuousLinearMap

/-- Injectivity comes from the actual kernel-coordinate equivalence, not a homology choice. -/
theorem closedImmersionPointNormalLinearMap_injective :
    Function.Injective (closedImmersionPointNormalLinearMap sX sY i hi d z) :=
  Subtype.val_injective.comp (closedImmersionNormalKernelEquiv sX sY i hi 0 d z).symm.injective

/-- In zero tangent dimension the intrinsic coordinates are unique; the raw normal chart
is precisely translation of the actual complex-linear normal parametrization. -/
theorem closedImmersionPointNormalChart_apply (w : Fin d → ℂ) :
    closedImmersionNormalChart sX sY i hi 0 d z
      (0, (closedImmersionNormalKernelEquiv sX sY i hi 0 d z).symm w) =
        localChart sX d (Point.map i hi z) (Point.map i hi z) +
          closedImmersionPointNormalLinearMap sX sY i hi d z w := by
  rw [closedImmersionNormalChart_apply]
  change inclusionInComplexCharts sX sY i hi 0 d z 0 + _ = _
  rw [show (0 : Fin 0 → ℂ) = localChart sY 0 z z from Subsingleton.elim _ _,
    inclusionInComplexCharts_at_center]
  rfl

/-- The inverse of the actual standard flattening chart retains that same affine formula. -/
theorem closedImmersionPointStandardFlatteningChart_symm (w : Fin d → ℂ) :
    (closedImmersionStandardFlatteningChart sX sY i hi 0 d z).symm (0, w) =
      (localChart sX d (Point.map i hi z)).symm
        (localChart sX d (Point.map i hi z) (Point.map i hi z) +
          closedImmersionPointNormalLinearMap sX sY i hi d z w) := by
  change (localChart sX d (Point.map i hi z)).symm
    (closedImmersionNormalChart sX sY i hi 0 d z
      (0, (closedImmersionNormalKernelEquiv sX sY i hi 0 d z).symm w)) = _
  rw [closedImmersionPointNormalChart_apply]

/-- On the actual flattening source, ambient coordinates are the same affine normal map. -/
theorem closedImmersionPointStandardFlatteningChart_coordinates
    (y : ComplexPoint X sX)
    (hy : y ∈ (closedImmersionStandardFlatteningChart sX sY i hi 0 d z).source) :
    localChart sX d (Point.map i hi z) y =
      localChart sX d (Point.map i hi z) (Point.map i hi z) +
        closedImmersionPointNormalLinearMap sX sY i hi d z
          ((closedImmersionStandardFlatteningChart sX sY i hi 0 d z) y).2 := by
  rw [closedImmersionStandardFlatteningChart_source] at hy
  have h := (closedImmersionNormalChart sX sY i hi 0 d z).right_inv hy.1.2
  let n := (closedImmersionNormalChart sX sY i hi 0 d z).symm
    (localChart sX d (Point.map i hi z) y)
  change inclusionInComplexCharts sX sY i hi 0 d z n.1 + n.2 = _ at h
  rw [show n.1 = localChart sY 0 z z from Subsingleton.elim _ _,
    inclusionInComplexCharts_at_center] at h
  rw [closedImmersionStandardFlatteningChart_apply, closedImmersionFlatteningChart_apply]
  dsimp only [closedImmersionPointNormalLinearMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply, Prod.snd]
  erw [ContinuousLinearEquiv.symm_apply_apply]
  exact h.symm

/-- Radial compression is unchanged by inserting the unique zero tangent coordinate. -/
theorem univBall_zeroTangent_apply (r : ℝ) (hr : 0 < r) (w : Fin d → ℂ) :
    OpenPartialHomeomorph.univBall ((0 : Fin 0 → ℂ), (0 : Fin d → ℂ)) r (0, w) =
      ((0 : Fin 0 → ℂ), OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r w) := by
  have hzero : ‖(![] : Fin 0 → ℂ)‖ = 0 := by
    exact norm_eq_zero.mpr (Subsingleton.elim _ _)
  simp [OpenPartialHomeomorph.univBall, hr, OpenPartialHomeomorph.univUnitBall_apply,
    Prod.norm_def, Prod.smul_mk, Prod.mk_add_mk]
  rw [hzero, max_eq_right (norm_nonneg w)]

variable (V : Opens (ComplexPoint X sX)) (hzV : Point.map i hi z ∈ V)

/-- The neighborhood pair of the general normal-purity construction maps to the ambient
point-complement pair by the actual inclusion. -/
def smoothClosedPointNeighborhoodPairMap :
    smoothClosedSupportNeighborhoodPair sX sY i hi 0 d z V hzV ⟶
      pointComplementPair (Point.map i hi z) :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w => ⟨w.1.1, fun h => w.2 ⟨z, h.symm⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) rfl

/-- The normal-purity parametrization specialized to zero tangent dimension, followed
by the genuine ambient point-complement inclusion. -/
def smoothClosedPointNormalModelPairMap :
    standardComplexPuncturedPair d ⟶ pointComplementPair (Point.map i hi z) :=
  normalSliceSection (Fin 0 → ℂ) d ≫
    (smoothClosedSupportNeighborhoodPairIso sX sY i hi 0 d z V hzV).hom ≫
      smoothClosedPointNeighborhoodPairMap sX sY i hi d z V hzV

/-- The general purity neighborhood radius, without replacing its choice. -/
abbrev smoothClosedPointNormalRadius : ℝ :=
  flattenedSupportRadius (Fin 0 → ℂ) d
    (smoothClosedSupportRestrictionChart sX sY i hi 0 d z V) (Point.map i hi z)
    (smoothClosedSupportRestrictionChart_mem_source sX sY i hi 0 d z V hzV)

theorem smoothClosedPointNormalRadius_pos : 0 < smoothClosedPointNormalRadius sX sY i hi d z V hzV :=
  flattenedSupportRadius_pos _ _ _ _ _

/-- The actual normal-model map has the explicitly normalized linear-radial formula. -/
theorem smoothClosedPointNormalModelPairMap_apply (w : Fin d → ℂ) :
    TopPair.Hom.fst (smoothClosedPointNormalModelPairMap sX sY i hi d z V hzV) w =
      (localChart sX d (Point.map i hi z)).symm
        (localChart sX d (Point.map i hi z) (Point.map i hi z) +
          closedImmersionPointNormalLinearMap sX sY i hi d z
            (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
              (smoothClosedPointNormalRadius sX sY i hi d z V hzV) w)) := by
  change (smoothClosedSupportRestrictionChart sX sY i hi 0 d z V).symm
    (OpenPartialHomeomorph.univBall
      (smoothClosedSupportRestrictionChart sX sY i hi 0 d z V (Point.map i hi z))
      (smoothClosedPointNormalRadius sX sY i hi d z V hzV) (0, w)) = _
  rw [smoothClosedSupportRestrictionChart_center,
    show localChart sY 0 z z = (0 : Fin 0 → ℂ) from Subsingleton.elim _ _,
    univBall_zeroTangent_apply d _ (smoothClosedPointNormalRadius_pos sX sY i hi d z V hzV)]
  exact closedImmersionPointStandardFlatteningChart_symm sX sY i hi d z _

/-- The actual normal-model image lies in the chosen ambient complex chart source. -/
theorem smoothClosedPointNormalModelPairMap_mem_chartSource (w : Fin d → ℂ) :
    TopPair.Hom.fst (smoothClosedPointNormalModelPairMap sX sY i hi d z V hzV) w ∈
      (localChart sX d (Point.map i hi z)).source := by
  have h := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d
    (smoothClosedSupportRestrictionChart sX sY i hi 0 d z V) (Point.map i hi z)
    (smoothClosedSupportRestrictionChart_mem_source sX sY i hi 0 d z V hzV)
    (flattenedSupportHomeomorph (Fin 0 → ℂ) d
      (smoothClosedSupportRestrictionChart sX sY i hi 0 d z V) (Point.map i hi z)
      (smoothClosedSupportRestrictionChart_mem_source sX sY i hi 0 d z V hzV) (0, w)).2
  have h' := h.1
  rw [closedImmersionStandardFlatteningChart_source] at h'
  exact h'.1.1

/-- The actual normal-model coordinates are precisely the positive radial compression
followed by the actual complex-linear normal identification and translation. -/
theorem smoothClosedPointNormalModelPairMap_coordinates (w : Fin d → ℂ) :
    localChart sX d (Point.map i hi z)
      (TopPair.Hom.fst (smoothClosedPointNormalModelPairMap sX sY i hi d z V hzV) w) =
        localChart sX d (Point.map i hi z) (Point.map i hi z) +
          closedImmersionPointNormalLinearMap sX sY i hi d z
            (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
              (smoothClosedPointNormalRadius sX sY i hi d z V hzV) w) := by
  let e := smoothClosedSupportRestrictionChart sX sY i hi 0 d z V
  let hx := smoothClosedSupportRestrictionChart_mem_source sX sY i hi 0 d z V hzV
  let y := flattenedSupportHomeomorph (Fin 0 → ℂ) d e (Point.map i hi z) hx (0, w)
  have hy := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e
    (Point.map i hi z) hx y.2
  change localChart sX d (Point.map i hi z) y = _
  rw [closedImmersionPointStandardFlatteningChart_coordinates sX sY i hi d z y hy.1]
  have hc := flattenedSupportHomeomorph_coordinates (Fin 0 → ℂ) d e
    (Point.map i hi z) hx (0, w)
  change closedImmersionStandardFlatteningChart sX sY i hi 0 d z y = _ at hc
  rw [show e (Point.map i hi z) = ((0 : Fin 0 → ℂ), (0 : Fin d → ℂ)) by
    dsimp [e]
    rw [smoothClosedSupportRestrictionChart_center]
    exact Prod.ext (Subsingleton.elim _ _) rfl,
    univBall_zeroTangent_apply d _ (smoothClosedPointNormalRadius_pos sX sY i hi d z V hzV)] at hc
  rw [hc]

end AlgebraicGeometry.ComplexPoint
