/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import HodgeConjecture.Lemmas.AlgebraicTopology.ChartNeighborhoodOrientation

/-!
# The zero-dimensional normal parametrization

When the source has complex dimension zero, its normal parametrization is the ambient
complex chart inverse preceded by a translation and an injective complex-linear map. The
normal-space coordinates therefore carry the standard complex orientation, and the class
is normalized exactly. These formulas specialize the general normal-coordinate
construction to `m = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (d : ℕ)
  [SmoothOfRelativeDimension 0 Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The actual complex-linear normal-coordinate inclusion in source dimension zero. -/
def closedImmersionPointNormalLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  (closedImmersionDerivativeProjection X Y i 0 d z).ker.subtypeL.comp
    (closedImmersionNormalKernelEquiv X Y i 0 d z).symm.toContinuousLinearMap

/-- Injectivity comes from the actual kernel-coordinate equivalence, not a homology choice. -/
theorem closedImmersionPointNormalLinearMap_injective :
    Function.Injective (closedImmersionPointNormalLinearMap X Y i d z) :=
  Subtype.val_injective.comp (closedImmersionNormalKernelEquiv X Y i 0 d z).symm.injective

/-- In zero tangent dimension the intrinsic coordinates are unique; the raw normal chart
is precisely translation of the actual complex-linear normal parametrization. -/
theorem closedImmersionPointNormalChart_apply (w : Fin d → ℂ) :
    closedImmersionNormalChart X Y i 0 d z
      (0, (closedImmersionNormalKernelEquiv X Y i 0 d z).symm w) =
        localChart X d (Point.map i z) (Point.map i z) +
          closedImmersionPointNormalLinearMap X Y i d z w := by
  rw [closedImmersionNormalChart_apply]
  change inclusionInComplexCharts X Y i 0 d z 0 + _ = _
  rw [show (0 : Fin 0 → ℂ) = localChart Y 0 z z from Subsingleton.elim _ _,
    inclusionInComplexCharts_at_center]
  rfl

/-- The inverse of the actual standard flattening chart retains that same affine formula. -/
theorem closedImmersionPointStandardFlatteningChart_symm (w : Fin d → ℂ) :
    (closedImmersionStandardFlatteningChart X Y i 0 d z).symm (0, w) =
      (localChart X d (Point.map i z)).symm
        (localChart X d (Point.map i z) (Point.map i z) +
          closedImmersionPointNormalLinearMap X Y i d z w) := by
  change (localChart X d (Point.map i z)).symm
    (closedImmersionNormalChart X Y i 0 d z
      (0, (closedImmersionNormalKernelEquiv X Y i 0 d z).symm w)) = _
  rw [closedImmersionPointNormalChart_apply]

/-- On the actual flattening source, ambient coordinates are the same affine normal map. -/
theorem closedImmersionPointStandardFlatteningChart_coordinates
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionStandardFlatteningChart X Y i 0 d z).source) :
    localChart X d (Point.map i z) y =
      localChart X d (Point.map i z) (Point.map i z) +
        closedImmersionPointNormalLinearMap X Y i d z
          ((closedImmersionStandardFlatteningChart X Y i 0 d z) y).2 := by
  rw [closedImmersionStandardFlatteningChart_source] at hy
  have h := (closedImmersionNormalChart X Y i 0 d z).right_inv hy.1.2
  let n := (closedImmersionNormalChart X Y i 0 d z).symm
    (localChart X d (Point.map i z) y)
  change inclusionInComplexCharts X Y i 0 d z n.1 + n.2 = _ at h
  rw [show n.1 = localChart Y 0 z z from Subsingleton.elim _ _,
    inclusionInComplexCharts_at_center] at h
  rw [closedImmersionStandardFlatteningChart_apply, closedImmersionFlatteningChart_apply]
  dsimp only [closedImmersionPointNormalLinearMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply, Prod.snd]
  erw [ContinuousLinearEquiv.symm_apply_apply]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Radial compression is unchanged by inserting the unique zero tangent coordinate. -/
theorem univBall_zeroTangent_apply (r : ℝ) (hr : 0 < r) (w : Fin d → ℂ) :
    OpenPartialHomeomorph.univBall ((0 : Fin 0 → ℂ), (0 : Fin d → ℂ)) r (0, w) =
      ((0 : Fin 0 → ℂ), OpenPartialHomeomorph.univBall (0 : Fin d → ℂ) r w) := by
  have hzero : ‖(![] : Fin 0 → ℂ)‖ = 0 := norm_eq_zero.mpr (Subsingleton.elim _ _)
  simp [OpenPartialHomeomorph.univBall, hr, OpenPartialHomeomorph.univUnitBall_apply,
    Prod.norm_def, Prod.smul_mk, Prod.mk_add_mk]
  rw [hzero, max_eq_right (norm_nonneg w)]

variable (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- The neighborhood pair of the general normal-purity construction maps to the ambient
point-complement pair by the actual inclusion. -/
def smoothClosedPointNeighborhoodPairMap :
    smoothClosedSupportNeighborhoodPair X Y i 0 d z V hzV ⟶
      pointComplementPair (Point.map i z) :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w => ⟨w.1.1, fun h => w.2 ⟨z, h.symm⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) rfl

/-- The normal-purity parametrization specialized to zero tangent dimension, followed
by the genuine ambient point-complement inclusion. -/
def smoothClosedPointNormalModelPairMap :
    standardComplexPuncturedPair d ⟶ pointComplementPair (Point.map i z) :=
  normalSliceSection (Fin 0 → ℂ) d ≫
    (smoothClosedSupportNeighborhoodPairIso X Y i 0 d z V hzV).hom ≫
      smoothClosedPointNeighborhoodPairMap X Y i d z V hzV

/-- The general purity neighborhood radius, without replacing its choice. -/
abbrev smoothClosedPointNormalRadius : ℝ :=
  flattenedSupportRadius (Fin 0 → ℂ) d
    (smoothClosedSupportRestrictionChart X Y i 0 d z V) (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i 0 d z V hzV)

theorem smoothClosedPointNormalRadius_pos : 0 < smoothClosedPointNormalRadius X Y i d z V hzV :=
  flattenedSupportRadius_pos _ _ _ _ _

/-- The actual normal-model map has the explicitly normalized linear-radial formula. -/
theorem smoothClosedPointNormalModelPairMap_apply (w : Fin d → ℂ) :
    TopPair.Hom.fst (smoothClosedPointNormalModelPairMap X Y i d z V hzV) w =
      (localChart X d (Point.map i z)).symm
        (localChart X d (Point.map i z) (Point.map i z) +
          closedImmersionPointNormalLinearMap X Y i d z
            (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
              (smoothClosedPointNormalRadius X Y i d z V hzV) w)) := by
  change (smoothClosedSupportRestrictionChart X Y i 0 d z V).symm
    (OpenPartialHomeomorph.univBall
      (smoothClosedSupportRestrictionChart X Y i 0 d z V (Point.map i z))
      (smoothClosedPointNormalRadius X Y i d z V hzV) (0, w)) = _
  rw [smoothClosedSupportRestrictionChart_center,
    show localChart Y 0 z z = (0 : Fin 0 → ℂ) from Subsingleton.elim _ _,
    univBall_zeroTangent_apply d _ (smoothClosedPointNormalRadius_pos X Y i d z V hzV)]
  exact closedImmersionPointStandardFlatteningChart_symm X Y i d z _

/-- The actual normal-model image lies in the chosen ambient complex chart source. -/
theorem smoothClosedPointNormalModelPairMap_mem_chartSource (w : Fin d → ℂ) :
    TopPair.Hom.fst (smoothClosedPointNormalModelPairMap X Y i d z V hzV) w ∈
      (localChart X d (Point.map i z)).source := by
  have h := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d
    (smoothClosedSupportRestrictionChart X Y i 0 d z V) (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i 0 d z V hzV)
    (flattenedSupportHomeomorph (Fin 0 → ℂ) d
      (smoothClosedSupportRestrictionChart X Y i 0 d z V) (Point.map i z)
      (smoothClosedSupportRestrictionChart_mem_source X Y i 0 d z V hzV) (0, w)).2
  have h' := h.1
  rw [closedImmersionStandardFlatteningChart_source] at h'
  exact h'.1.1

/-- The actual normal-model coordinates are precisely the positive radial compression
followed by the actual complex-linear normal identification and translation. -/
theorem smoothClosedPointNormalModelPairMap_coordinates (w : Fin d → ℂ) :
    localChart X d (Point.map i z)
      (TopPair.Hom.fst (smoothClosedPointNormalModelPairMap X Y i d z V hzV) w) =
        localChart X d (Point.map i z) (Point.map i z) +
          closedImmersionPointNormalLinearMap X Y i d z
            (OpenPartialHomeomorph.univBall (0 : Fin d → ℂ)
              (smoothClosedPointNormalRadius X Y i d z V hzV) w) := by
  let e := smoothClosedSupportRestrictionChart X Y i 0 d z V
  let hx := smoothClosedSupportRestrictionChart_mem_source X Y i 0 d z V hzV
  let y := flattenedSupportHomeomorph (Fin 0 → ℂ) d e (Point.map i z) hx (0, w)
  have hy := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) d e
    (Point.map i z) hx y.2
  change localChart X d (Point.map i z) y = _
  rw [closedImmersionPointStandardFlatteningChart_coordinates X Y i d z y hy.1]
  have hc := flattenedSupportHomeomorph_coordinates (Fin 0 → ℂ) d e
    (Point.map i z) hx (0, w)
  change closedImmersionStandardFlatteningChart X Y i 0 d z y = _ at hc
  rw [show e (Point.map i z) = ((0 : Fin 0 → ℂ), (0 : Fin d → ℂ)) by
    dsimp [e]
    rw [smoothClosedSupportRestrictionChart_center]
    exact Prod.ext (Subsingleton.elim _ _) rfl,
    univBall_zeroTangent_apply d _ (smoothClosedPointNormalRadius_pos X Y i d z V hzV)] at hc
  rw [hc]

end AlgebraicGeometry.ComplexPoint
