/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexAnalyticMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Analytic local left inverses from actual section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts. In particular derivative injectivity is proved, not supplied as
an immersion or purity field.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- Any family of sections on an intrinsic open lifts, after restriction, on a single
affine ambient neighborhood of the selected point. The lifts come from the actual
surjective closed-immersion map on affine sections. -/
theorem Scheme.Hom.exists_affine_local_section_lifts
    {J : Type*} (V : Y.Opens) (s : J → Γ(Y, V)) (y : Y) (hy : y ∈ V) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hUV : i ⁻¹ᵁ U ≤ V),
      i y ∈ U ∧ ∃ r : J → Γ(X, U),
        ∀ j, i.app U (r j) = Y.presheaf.map (homOfLE hUV).op (s j) := by
  obtain ⟨W, hW, hpre⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hyW : i y ∈ W := by
    have : y ∈ i ⁻¹' W := hpre ▸ hy
    exact this
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyW hW
  have hUV : i ⁻¹ᵁ U ≤ V := by
    intro z hz
    have : z ∈ i ⁻¹' W := hUW hz
    exact (show z ∈ (V : Set Y) from hpre ▸ this)
  choose r hr using fun j => i.app_surjective U hU
    (Y.presheaf.map (homOfLE hUV).op (s j))
  exact ⟨U, hU, hUV, hyU, r, hr⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme}
  (structureMapX : X ⟶ Spec (.of ℂ)) (structureMapY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ structureMapX = structureMapY) (m d : ℕ)
  [SmoothOfRelativeDimension m structureMapY] [SmoothOfRelativeDimension d structureMapX]

/-- The actual inclusion written in the canonical intrinsic and ambient complex charts. -/
def inclusionInComplexCharts (z : ComplexPoint Y structureMapY) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => localChart structureMapX d (Point.map i hi z)
    (Point.map i hi ((localChart structureMapY m z).symm v))

@[simp] theorem inclusionInComplexCharts_at_center (z : ComplexPoint Y structureMapY) :
    inclusionInComplexCharts structureMapX structureMapY i hi m d z
      (localChart structureMapY m z z) =
        localChart structureMapX d (Point.map i hi z) (Point.map i hi z) := by
  unfold inclusionInComplexCharts
  rw [(localChart structureMapY m z).left_inv (mem_localChart_source structureMapY m z)]

/-- Analyticity is inherited from the actual morphism of smooth schemes. -/
theorem analyticAt_inclusionInComplexCharts (z : ComplexPoint Y structureMapY) :
    AnalyticAt ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
      (localChart structureMapY m z z) := by
  apply analyticAt_localChart_symm_map structureMapY structureMapX i hi m d z
    ((localChart structureMapY m z).map_source (mem_localChart_source structureMapY m z))
  rw [(localChart structureMapY m z).left_inv (mem_localChart_source structureMapY m z)]
  exact mem_localChart_source structureMapX d (Point.map i hi z)

/-- A smooth closed immersion has an actual analytic local left inverse in complex
coordinates. It is constructed by lifting the intrinsic coordinate sections, not assumed
from an analytic-immersion structure. -/
theorem exists_analytic_localLeftInverse_of_isClosedImmersion [IsClosedImmersion i]
    (z : ComplexPoint Y structureMapY) :
    ∃ L : (Fin d → ℂ) → (Fin m → ℂ),
      AnalyticAt ℂ L
        (inclusionInComplexCharts structureMapX structureMapY i hi m d z
          (localChart structureMapY m z z)) ∧
      (L ∘ inclusionInComplexCharts structureMapX structureMapY i hi m d z) =ᶠ[
        𝓝 (localChart structureMapY m z z)] id := by
  let D := localEtaleCoordinates structureMapY m z
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using
      mem_localEtaleCoordinates structureMapY m z
  obtain ⟨U, _hU, hUV, hzU, r, hr⟩ := i.exists_affine_local_section_lifts
    D.ambientCoordinateOpen D.ambientCoordinateSection z.underlying hzD
  let eY := localChart structureMapY m z
  let eX := localChart structureMapX d (Point.map i hi z)
  let L : (Fin d → ℂ) → (Fin m → ℂ) :=
    fun w j => Point.evaluate U (r j) (eX.symm w)
  have hzY : z ∈ eY.source := mem_localChart_source structureMapY m z
  have hzX : Point.map i hi z ∈ eX.source :=
    mem_localChart_source structureMapX d (Point.map i hi z)
  have hzYt : eY z ∈ eY.target := eY.map_source hzY
  have hzXt : eX (Point.map i hi z) ∈ eX.target := eX.map_source hzX
  refine ⟨L, ?_, ?_⟩
  · rw [inclusionInComplexCharts_at_center]
    apply AnalyticAt.pi
    intro j
    apply analyticAt_localChart_symm_evaluate structureMapX d (Point.map i hi z) hzXt U (r j)
    change eX.symm (eX (Point.map i hi z)) ∈ Point.overOpen U
    rw [eX.left_inv hzX]
    exact hzU
  · have hc : ContinuousAt (fun v => Point.map i hi (eY.symm v)) (eY z) :=
      (Point.continuous_map i hi).continuousAt.comp (eY.continuousAt_symm hzYt)
    have hX : ∀ᶠ v in 𝓝 (eY z), Point.map i hi (eY.symm v) ∈ eX.source := by
      apply hc (eX.open_source.mem_nhds _)
      change Point.map i hi (eY.symm (eY z)) ∈ eX.source
      rw [eY.left_inv hzY]
      exact hzX
    have hU : ∀ᶠ v in 𝓝 (eY z), Point.map i hi (eY.symm v) ∈ Point.overOpen U := by
      apply hc ((Point.isOpen_overOpen U).mem_nhds _)
      change Point.map i hi (eY.symm (eY z)) ∈ Point.overOpen U
      rw [eY.left_inv hzY]
      exact hzU
    filter_upwards [eY.open_target.mem_nhds hzYt, hX, hU] with v hvY hvX hvU
    funext j
    change Point.evaluate U (r j)
      (eX.symm (eX (Point.map i hi (eY.symm v)))) = v j
    rw [eX.left_inv hvX, Point.evaluate_map, hr]
    rw [← Point.evaluate_res hUV (D.ambientCoordinateSection j) (eY.symm v)
      ((Point.mem_overOpen_map_iff i hi _ U).mp hvU)]
    rw [← localChart_apply_component_eq_evaluate structureMapY m z (eY.symm v)
      (eY.map_target hvY) j]
    exact congrFun (eY.right_inv hvY) j

/-- The derivative of a smooth closed immersion has an actual continuous-linear left
inverse, obtained by differentiating the constructed analytic local left inverse. -/
theorem exists_leftInverse_fderiv_inclusionInComplexCharts [IsClosedImmersion i]
    (z : ComplexPoint Y structureMapY) :
    ∃ P : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ),
      P.comp (fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
        (localChart structureMapY m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
  obtain ⟨L, hL, hleft⟩ :=
    exists_analytic_localLeftInverse_of_isClosedImmersion structureMapX structureMapY i hi m d z
  let φ := inclusionInComplexCharts structureMapX structureMapY i hi m d z
  let a := localChart structureMapY m z z
  refine ⟨fderiv ℂ L (φ a), ?_⟩
  have hφ := analyticAt_inclusionInComplexCharts structureMapX structureMapY i hi m d z
  have hc := hL.differentiableAt.hasFDerivAt.comp a hφ.differentiableAt.hasFDerivAt
  exact (hc.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id a)

/-- Derivative injectivity for the actual chart-written closed immersion, with no
assumed immersion, cotangent comparison, regular-sequence, or flattening data. -/
theorem injective_fderiv_inclusionInComplexCharts [IsClosedImmersion i]
    (z : ComplexPoint Y structureMapY) :
    Function.Injective
      (fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
        (localChart structureMapY m z z)) := by
  obtain ⟨P, hP⟩ :=
    exists_leftInverse_fderiv_inclusionInComplexCharts structureMapX structureMapY i hi m d z
  have hleft : Function.LeftInverse P
      (fderiv ℂ (inclusionInComplexCharts structureMapX structureMapY i hi m d z)
        (localChart structureMapY m z z)) :=
    fun v => DFunLike.congr_fun hP v
  exact hleft.injective

end AlgebraicGeometry.ComplexPoint
