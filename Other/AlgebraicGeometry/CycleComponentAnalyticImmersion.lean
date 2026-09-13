/-
Copyright 2026 The Formal Conjectures Authors.

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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
public import Other.AlgebraicGeometry.CycleComponentAnalyticEmbedding
public import Other.AlgebraicGeometry.CycleComponentLocalOrientationCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.Geometry.Manifold.Immersion

/-!
# The analytic half of the cycle-component immersion problem

The exact component coordinates constructed on the smooth locus are independent of the ambient
algebraic coordinates.  This file proves that, despite that independence, the actual inclusion of
the component is complex analytic when written in those component coordinates and any of the
canonical ambient charts.

This is the analytic half of simultaneous local straightening.  The remaining input is that the
inclusion is an immersion.  In the current library, `Manifold.IsImmersionAt` already packages the
desired simultaneous charts, but there is no bridge from the closed immersion of schemes at a
smooth component point to injectivity of the analytic derivative (or directly to
`Manifold.IsImmersionAt`).
-/

@[expose] public noncomputable section

open CategoryTheory Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry
namespace CycleComponentSeparateLocalCoordinates

variable {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d n : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]

variable (C : CycleComponentSeparateLocalCoordinates V.over x d n)

/-! ### Maps out of the exact component chart -/

/-- Each coordinate of a morphism from the affine component neighborhood to a smooth complex
scheme is analytic when the source is written in the retained exact component coordinates. -/
lemma analyticAt_neighborhoodProjectionChart_symm_map_component
    {Y : Over (Spec (.of ℂ))} (f : C.neighborhoodScheme ⟶ Y)
    (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (y : ComplexPoint Y) {w : Fin n → ℂ}
    (hw : w ∈ C.neighborhoodProjectionChart.target)
    (hmap : Point.map f (C.neighborhoodProjectionChart.symm w) ∈
      (ComplexPoint.localChart Y e y).source)
    (i : Fin e) :
    AnalyticAt ℂ
      (fun v ↦ ComplexPoint.localChart Y e y
        (Point.map f (C.neighborhoodProjectionChart.symm v)) i) w := by
  let D := ComplexPoint.localEtaleCoordinates Y e y
  have htargetOpen : Point.map f (C.neighborhoodProjectionChart.symm w) ∈
      Point.overOpen D.ambientCoordinateOpen := by
    have hmem := ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source
      Y e y (Point.map f (C.neighborhoodProjectionChart.symm w)) hmap
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hsourceOpen : C.neighborhoodProjectionChart.symm w ∈
      Point.overOpen (f.left ⁻¹ᵁ D.ambientCoordinateOpen) :=
    (Point.mem_overOpen_map_iff f _ D.ambientCoordinateOpen).mp htargetOpen
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_evaluate hw
    (f.left ⁻¹ᵁ D.ambientCoordinateOpen)
    (f.left.app D.ambientCoordinateOpen (D.ambientCoordinateSection i)) hsourceOpen
  have hcontinuous : ContinuousAt
      (fun v ↦ Point.map f (C.neighborhoodProjectionChart.symm v)) w :=
    (Point.continuous_map f).continuousAt.comp
      (C.neighborhoodProjectionChart.continuousAt_symm hw)
  have heventually :
      (fun v ↦ Point.map f (C.neighborhoodProjectionChart.symm v)) ⁻¹'
          (ComplexPoint.localChart Y e y).source ∈ nhds w :=
    hcontinuous ((ComplexPoint.localChart Y e y).open_source.mem_nhds hmap)
  apply ha.congr
  filter_upwards [heventually] with v hv
  rw [ComplexPoint.localChart_apply_component_eq_evaluate Y e y
    (Point.map f (C.neighborhoodProjectionChart.symm v)) hv i]
  exact Point.evaluate_map f D.ambientCoordinateOpen
    (D.ambientCoordinateSection i) (C.neighborhoodProjectionChart.symm v) |>.symm

/-- A morphism from the affine component neighborhood to a smooth complex scheme is analytic in
the exact component chart and a canonical target chart. -/
lemma analyticAt_neighborhoodProjectionChart_symm_map
    {Y : Over (Spec (.of ℂ))} (f : C.neighborhoodScheme ⟶ Y)
    (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
    (y : ComplexPoint Y) {w : Fin n → ℂ}
    (hw : w ∈ C.neighborhoodProjectionChart.target)
    (hmap : Point.map f (C.neighborhoodProjectionChart.symm w) ∈
      (ComplexPoint.localChart Y e y).source) :
    AnalyticAt ℂ
      (fun v ↦ ComplexPoint.localChart Y e y
        (Point.map f (C.neighborhoodProjectionChart.symm v))) w :=
  AnalyticAt.pi fun i ↦
    C.analyticAt_neighborhoodProjectionChart_symm_map_component
      f e y hw hmap i

/-! ### The actual cycle-component inclusion -/

/-- The scheme map from the affine component-coordinate neighborhood into the ambient variety. -/
def neighborhoodToAmbientSchemeMap : C.componentNeighborhood.toScheme ⟶ V.over.left :=
  C.componentNeighborhood.ι ≫ (componentSmoothLocus V.over x).ι ≫
    cycleComponentι V.over.left x

/-- Algebraically, the neighborhood-to-ambient map is formally unramified: it is a composite of
two open immersions and a closed immersion.  What is missing is the comparison identifying this
algebraic cotangent statement with injectivity of the derivative of the analytic map. -/
noncomputable instance neighborhoodToAmbientSchemeMap_formallyUnramified :
    FormallyUnramified C.neighborhoodToAmbientSchemeMap := by
  dsimp only [neighborhoodToAmbientSchemeMap]
  infer_instance

/-- The neighborhood-to-ambient scheme map respects the complex structure maps. -/
lemma neighborhoodToAmbientSchemeMap_over :
    C.neighborhoodToAmbientSchemeMap ≫ V.over.hom = C.neighborhoodStructureMap := by
  simp only [neighborhoodToAmbientSchemeMap, neighborhoodStructureMap,
    componentSmoothStructureMap, Category.assoc]

/-- The neighborhood-to-ambient morphism bundled over `Spec ℂ`. -/
def neighborhoodToAmbientOver : C.neighborhoodScheme ⟶ V.over :=
  Over.homMk C.neighborhoodToAmbientSchemeMap C.neighborhoodToAmbientSchemeMap_over

/-- The map on complex points from the affine component-coordinate neighborhood to the ambient
analytic variety. -/
def neighborhoodToAmbientPoint :
    ComplexPoint C.neighborhoodScheme → V.analyticPoint :=
  Point.map C.neighborhoodToAmbientOver

/-- Mapping from the affine neighborhood to the ambient variety factors through the reduced
cycle component. -/
lemma neighborhoodToAmbientPoint_eq_cycleComponentMap
    (z : ComplexPoint C.neighborhoodScheme) :
    C.neighborhoodToAmbientPoint z =
      cycleComponentMap V.over x (C.neighborhoodToComponentPoint z) :=
  Over.OverMorphism.ext rfl

/-- On analytic points, the neighborhood-to-ambient map is a topological embedding. -/
lemma neighborhoodToAmbientPoint_isEmbedding :
    IsEmbedding C.neighborhoodToAmbientPoint := by
  have heq : C.neighborhoodToAmbientPoint =
      cycleComponentMap V.over x ∘ C.neighborhoodToComponentPoint :=
    funext C.neighborhoodToAmbientPoint_eq_cycleComponentMap
  rw [heq]
  exact (ComplexPoint.cycleComponentMap_isClosedEmbedding V.over x).toIsEmbedding.comp
    C.neighborhoodToComponentPoint_isOpenEmbedding.toIsEmbedding

/-- The actual cycle-component inclusion is analytic in an exact intrinsic component chart and
the canonical ambient chart centered at the same point.  This proves analyticity, but not the
injective-derivative assertion needed by `Manifold.IsImmersionAt`. -/
theorem analyticAt_componentProjectionChart_symm_cycleComponentMap
    {w : Fin n → ℂ}
    (hw : w ∈ C.componentProjectionChart.target)
    (hmap : cycleComponentMap V.over x (C.componentProjectionChart.symm w) ∈
      (ComplexPoint.localChart V.over d (cycleComponentMap V.over x C.point)).source) :
    AnalyticAt ℂ
      (fun v ↦ ComplexPoint.localChart V.over d (cycleComponentMap V.over x C.point)
        (cycleComponentMap V.over x (C.componentProjectionChart.symm v))) w := by
  have hw' : w ∈ C.neighborhoodProjectionChart.target := by
    simpa only [componentProjectionChart,
      OpenPartialHomeomorph.lift_openEmbedding_target] using hw
  have hmap' : C.neighborhoodToAmbientPoint
      (C.neighborhoodProjectionChart.symm w) ∈
        (ComplexPoint.localChart V.over d (cycleComponentMap V.over x C.point)).source := by
    rw [C.neighborhoodToAmbientPoint_eq_cycleComponentMap,
      ← C.componentProjectionChart_symm_apply]
    exact hmap
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_map
    C.neighborhoodToAmbientOver d (cycleComponentMap V.over x C.point) hw' hmap'
  apply ha.congr
  filter_upwards with v
  have hv : Point.map C.neighborhoodToAmbientOver
      (C.neighborhoodProjectionChart.symm v) =
        cycleComponentMap V.over x (C.componentProjectionChart.symm v) := by
    change C.neighborhoodToAmbientPoint (C.neighborhoodProjectionChart.symm v) = _
    rw [C.neighborhoodToAmbientPoint_eq_cycleComponentMap,
      ← C.componentProjectionChart_symm_apply]
  rw [hv]

/-- At the distinguished smooth component point, the chart-written inclusion is analytic with no
extra neighborhood premise. -/
theorem analyticAt_componentProjectionChart_symm_cycleComponentMap_at_point :
    AnalyticAt ℂ
      (fun v ↦ ComplexPoint.localChart V.over d (cycleComponentMap V.over x C.point)
        (cycleComponentMap V.over x (C.componentProjectionChart.symm v)))
      (C.componentProjectionChart C.point) := by
  apply C.analyticAt_componentProjectionChart_symm_cycleComponentMap
  · exact C.componentProjectionChart.map_source
      C.point_mem_componentProjectionChart_source
  · rw [C.componentProjectionChart.left_inv
      C.point_mem_componentProjectionChart_source]
    exact ComplexPoint.mem_localChart_source V.over d
      (cycleComponentMap V.over x C.point)

end CycleComponentSeparateLocalCoordinates
end AlgebraicGeometry
