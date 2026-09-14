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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Analytic maps induced by morphisms of smooth complex schemes

A morphism of schemes over `Spec ℂ` induces a holomorphic map between the complex manifolds
constructed from algebraic étale coordinates.  In local charts, every target coordinate is a
regular function.  Its pullback is again regular, so analyticity follows from the chartwise
analyticity of regular-function evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
  (d e : ℕ)

/-- In algebraic coordinate charts, each component of a morphism of smooth complex schemes is
complex analytic. -/
lemma analyticAt_localChart_symm_map_component
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : Point ℂ X) {w : Fin d → ℂ}
    (hw : w ∈ (localChart X d z).target)
    (hmap : map f ((localChart X d z).symm w) ∈
      (localChart Y e (map f z)).source)
    (i : Fin e) :
    AnalyticAt ℂ
      (fun v ↦ localChart Y e (map f z)
        (map f ((localChart X d z).symm v)) i) w := by
  let D := localEtaleCoordinates Y e (map f z)
  have htargetOpen : map f ((localChart X d z).symm w) ∈
      overOpen D.ambientCoordinateOpen := by
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source
      Y e (map f z)
      (map f ((localChart X d z).symm w)) hmap
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hsourceOpen : (localChart X d z).symm w ∈
      overOpen (f.left ⁻¹ᵁ D.ambientCoordinateOpen) :=
    (mem_overOpen_map_iff f _ D.ambientCoordinateOpen).mp htargetOpen
  have ha := analyticAt_localChart_symm_evaluate X d z hw
    (f.left ⁻¹ᵁ D.ambientCoordinateOpen)
    (f.left.app D.ambientCoordinateOpen (D.ambientCoordinateSection i)) hsourceOpen
  have hcontinuous : ContinuousAt
      (fun v ↦ map f ((localChart X d z).symm v)) w :=
    (continuous_map f).continuousAt.comp
      ((localChart X d z).continuousAt_symm hw)
  have heventually :
      (fun v ↦ map f ((localChart X d z).symm v)) ⁻¹'
          (localChart Y e (map f z)).source ∈ 𝓝 w :=
    hcontinuous ((localChart Y e (map f z)).open_source.mem_nhds hmap)
  apply ha.congr
  filter_upwards [heventually] with v hv
  rw [localChart_apply_component_eq_evaluate Y e (map f z)
    (map f ((localChart X d z).symm v)) hv i]
  exact evaluate_map f D.ambientCoordinateOpen
    (D.ambientCoordinateSection i) ((localChart X d z).symm v) |>.symm

/-- In algebraic coordinate charts, the map induced by a morphism of smooth complex schemes is
complex analytic. -/
lemma analyticAt_localChart_symm_map
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom]
    (z : Point ℂ X) {w : Fin d → ℂ}
    (hw : w ∈ (localChart X d z).target)
    (hmap : map f ((localChart X d z).symm w) ∈
      (localChart Y e (map f z)).source) :
    AnalyticAt ℂ
      (fun v ↦ localChart Y e (map f z)
        (map f ((localChart X d z).symm v))) w :=
  AnalyticAt.pi fun i ↦ analyticAt_localChart_symm_map_component
    X Y f d e z hw hmap i

end AlgebraicGeometry.ComplexPoint
