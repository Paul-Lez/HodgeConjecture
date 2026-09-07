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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
public import HodgeConjecture.Lemmas.AlgebraicTopology.ChartLocalFundamentalClass
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Complex

/-!
# The topological manifold of complex points

If a complex scheme is smooth of relative dimension `d`, its constructed analytic complex-point
space is locally homeomorphic to `ℂ^d`. This file turns the chosen algebraic étale coordinates into
an actual `ChartedSpace (Fin d → ℂ)` structure. In particular, the complex points form a
topological manifold of real dimension `2 * d`.

The charts are not extra input. At a complex point we choose the affine étale coordinates supplied
by relative-dimensional smoothness, take a local inverse for the proven local homeomorphism, and
extend that chart from the corresponding analytic open subset to the ambient space.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

local instance complexManifoldTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

/-- The analytic open subset on which the chosen coordinates at `z` are defined. -/
abbrev coordinateNeighborhood [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) :=
  {w : ComplexPoint X structureMap //
    w ∈ overOpen ((localEtaleCoordinates structureMap d z).neighborhood)}

/-- The point `z` regarded as a point of its chosen coordinate neighborhood. -/
def pointInCoordinateNeighborhood [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) : coordinateNeighborhood structureMap d z :=
  ⟨z, mem_localEtaleCoordinates structureMap d z⟩

/-- A local coordinate homeomorphism on the chosen analytic open neighborhood. -/
def coordinateNeighborhoodChart [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) :
    OpenPartialHomeomorph (coordinateNeighborhood structureMap d z) (Fin d → ℂ) :=
  let D := localEtaleCoordinates structureMap d z
  D.ambientProjectionChart (pointInCoordinateNeighborhood structureMap d z)

lemma pointInCoordinateNeighborhood_mem_chart_source
    [SmoothOfRelativeDimension d structureMap] (z : ComplexPoint X structureMap) :
    pointInCoordinateNeighborhood structureMap d z ∈
      (coordinateNeighborhoodChart structureMap d z).source :=
  (localEtaleCoordinates structureMap d z).mem_ambientProjectionChart_source
    (pointInCoordinateNeighborhood structureMap d z)

/-- The chosen local chart at a complex point, extended from its analytic open neighborhood to the
whole complex-point space. -/
def localChart [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) :
    OpenPartialHomeomorph (ComplexPoint X structureMap) (Fin d → ℂ) :=
  (coordinateNeighborhoodChart structureMap d z).lift_openEmbedding
    (isOpen_overOpen ((localEtaleCoordinates structureMap d z).neighborhood)).isOpenEmbedding_subtypeVal

lemma mem_localChart_source [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) : z ∈ (localChart structureMap d z).source := by
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨pointInCoordinateNeighborhood structureMap d z,
    pointInCoordinateNeighborhood_mem_chart_source structureMap d z, rfl⟩

lemma mem_coordinateNeighborhood_of_mem_localChart_source
    [SmoothOfRelativeDimension d structureMap]
    (z w : ComplexPoint X structureMap) (hw : w ∈ (localChart structureMap d z).source) :
    w ∈ overOpen ((localEtaleCoordinates structureMap d z).neighborhood) := by
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hw
  obtain ⟨w', _, rfl⟩ := hw
  exact w'.2

@[simp]
lemma localChart_target [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) :
    (localChart structureMap d z).target =
      (coordinateNeighborhoodChart structureMap d z).target := by
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_target]

@[simp]
lemma localChart_symm_apply [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) (w : Fin d → ℂ) :
    (localChart structureMap d z).symm w =
      ((coordinateNeighborhoodChart structureMap d z).symm w).1 := by
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

lemma localChart_apply_of_mem [SmoothOfRelativeDimension d structureMap]
    (z w : ComplexPoint X structureMap) (hw : w ∈ (localChart structureMap d z).source) :
    localChart structureMap d z w =
      (localEtaleCoordinates structureMap d z).ambientAnalyticCoordinates
        ⟨w, mem_coordinateNeighborhood_of_mem_localChart_source structureMap d z w hw⟩ := by
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  rw [localChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact (localEtaleCoordinates structureMap d z).ambientProjectionChart_apply_of_mem
    (pointInCoordinateNeighborhood structureMap d z) w' hw'

/-- The canonical charted-space structure obtained from algebraic smooth coordinates. -/
@[instance_reducible]
def analyticChartedSpace [SmoothOfRelativeDimension d structureMap] :
    ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) where
  atlas := Set.range (localChart structureMap d)
  chartAt := localChart structureMap d
  mem_chart_source := mem_localChart_source structureMap d
  chart_mem_atlas z := ⟨z, rfl⟩

/-- Smooth complex points are topological complex manifolds of the specified dimension. -/
theorem isManifold_zero [SmoothOfRelativeDimension d structureMap] :
    @IsManifold ℂ _ (Fin d → ℂ) _ _ (Fin d → ℂ) _ 𝓘(ℂ, Fin d → ℂ) 0
      (ComplexPoint X structureMap) _ (analyticChartedSpace structureMap d) := by
  let _ : ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
    analyticChartedSpace structureMap d
  infer_instance

/-- Evaluation of a regular section near an inverse-chart point is complex analytic. -/
lemma analyticAt_localChart_symm_evaluate
    [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) {w : Fin d → ℂ}
    (hw : w ∈ (localChart structureMap d z).target)
    (V : X.Opens) (s : Γ(X, V))
    (hV : (localChart structureMap d z).symm w ∈ overOpen V) :
    AnalyticAt ℂ
      (fun v ↦ ComplexPoint.evaluate V s ((localChart structureMap d z).symm v)) w := by
  let D := localEtaleCoordinates structureMap d z
  let p := pointInCoordinateNeighborhood structureMap d z
  have hwD : w ∈ (D.ambientProjectionChart p).target := by
    simpa only [D, p, coordinateNeighborhoodChart, localChart_target] using hw
  have hVD : ((D.ambientProjectionChart p).symm w).1 ∈
      overOpen V := by
    simpa only [D, p, coordinateNeighborhoodChart, localChart_symm_apply] using hV
  simpa only [D, p, coordinateNeighborhoodChart, localChart_symm_apply] using
    D.analyticAt_ambientProjectionChart_symm_evaluate p hwD V s hVD

/-- On the source of a chart, each coordinate is evaluation of its defining regular section. -/
lemma localChart_apply_component_eq_evaluate
    [SmoothOfRelativeDimension d structureMap]
    (z q : ComplexPoint X structureMap) (hq : q ∈ (localChart structureMap d z).source)
    (i : Fin d) :
    localChart structureMap d z q i =
      ComplexPoint.evaluate
        (localEtaleCoordinates structureMap d z).ambientCoordinateOpen
        ((localEtaleCoordinates structureMap d z).ambientCoordinateSection i) q := by
  rw [localChart_apply_of_mem structureMap d z q hq]
  exact (localEtaleCoordinates structureMap d z).ambientAnalyticCoordinates_apply_eq_evaluate _ i

/-- Each component of a transition between the chosen algebraic charts is complex analytic. -/
lemma analyticAt_localChart_transition_component
    [SmoothOfRelativeDimension d structureMap]
    (z z' : ComplexPoint X structureMap) {w : Fin d → ℂ}
    (hw : w ∈ ((localChart structureMap d z).symm.trans
      (localChart structureMap d z')).source) (i : Fin d) :
    AnalyticAt ℂ
      (fun v ↦ localChart structureMap d z'
        ((localChart structureMap d z).symm v) i) w := by
  rw [OpenPartialHomeomorph.trans_source] at hw
  have hwtarget : w ∈ (localChart structureMap d z).target := hw.1
  have hsource : (localChart structureMap d z).symm w ∈
      (localChart structureMap d z').source := hw.2
  let D' := localEtaleCoordinates structureMap d z'
  have hV : (localChart structureMap d z).symm w ∈ overOpen D'.ambientCoordinateOpen := by
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source
      structureMap d z' ((localChart structureMap d z).symm w) hsource
    simpa only [D', LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hi := analyticAt_localChart_symm_evaluate structureMap d z hwtarget
    D'.ambientCoordinateOpen (D'.ambientCoordinateSection i) hV
  apply hi.congr
  have hcontinuous : ContinuousAt (localChart structureMap d z).symm w :=
    (localChart structureMap d z).continuousAt_symm hwtarget
  have heventually : (localChart structureMap d z).symm ⁻¹'
      (localChart structureMap d z').source ∈ 𝓝 w :=
    hcontinuous ((localChart structureMap d z').open_source.mem_nhds hsource)
  filter_upwards [heventually] with v hv
  exact (localChart_apply_component_eq_evaluate structureMap d z'
    ((localChart structureMap d z).symm v) hv i).symm

/-- A transition between the chosen algebraic charts is complex analytic. -/
lemma analyticAt_localChart_transition
    [SmoothOfRelativeDimension d structureMap]
    (z z' : ComplexPoint X structureMap) {w : Fin d → ℂ}
    (hw : w ∈ ((localChart structureMap d z).symm.trans
      (localChart structureMap d z')).source) :
    AnalyticAt ℂ
      (fun v ↦ localChart structureMap d z' ((localChart structureMap d z).symm v)) w :=
  AnalyticAt.pi fun i ↦ analyticAt_localChart_transition_component structureMap d z z' hw i

/-- Transition maps in the chosen atlas are holomorphic on their domains. -/
lemma contDiffOn_localChart_transition
    [SmoothOfRelativeDimension d structureMap]
    (z z' : ComplexPoint X structureMap) :
    ContDiffOn ℂ ω ((localChart structureMap d z).symm.trans
      (localChart structureMap d z'))
        (((localChart structureMap d z).symm.trans
          (localChart structureMap d z')).source) := by
  intro w hw
  change ContDiffWithinAt ℂ ω
    (fun v ↦ localChart structureMap d z' ((localChart structureMap d z).symm v))
      (((localChart structureMap d z).symm.trans
        (localChart structureMap d z')).source) w
  exact (analyticAt_localChart_transition structureMap d z z' hw).contDiffAt.contDiffWithinAt

/-- Smooth complex points form a holomorphic complex manifold of the specified dimension. -/
theorem isManifold_omega [SmoothOfRelativeDimension d structureMap] :
    @IsManifold ℂ _ (Fin d → ℂ) _ _ (Fin d → ℂ) _ 𝓘(ℂ, Fin d → ℂ) ω
      (ComplexPoint X structureMap) _ (analyticChartedSpace structureMap d) := by
  let _ : ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
    analyticChartedSpace structureMap d
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using
    contDiffOn_localChart_transition structureMap d z z'

/-- Every analytic neighborhood of a smooth complex point contains an open contractible
neighborhood. The smaller neighborhood is the inverse image of a Euclidean ball in the chosen
algebraic coordinate chart. -/
lemma exists_contractibleOpen_le [SmoothOfRelativeDimension d structureMap]
    (x : ComplexPoint X structureMap)
    (U : TopologicalSpace.Opens (ComplexPoint X structureMap)) (hxU : x ∈ U) :
    ∃ (V : TopologicalSpace.Opens (ComplexPoint X structureMap)),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  let e := localChart structureMap d x
  have hxsource : x ∈ e.source := mem_localChart_source structureMap d x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' (U : Set _)) :=
    e.isOpen_inter_preimage_symm U.2
  have hximage : e x ∈ e.target ∩ e.symm ⁻¹' (U : Set _) := by
    refine ⟨e.map_source hxsource, ?_⟩
    change e.symm (e x) ∈ (U : Set _)
    rw [e.left_inv hxsource]
    exact hxU
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (hopen.mem_nhds hximage)
  let V : TopologicalSpace.Opens (ComplexPoint X structureMap) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r,
      e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxV : x ∈ V := ⟨hxsource, Metric.mem_ball_self hr⟩
  have hVsource : (V : Set _) ⊆ e.source := Set.inter_subset_left
  have himage : e '' (V : Set _) = Metric.ball (e x) r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hy
      have hytarget : y ∈ e.target := (hball hy).1
      refine ⟨e.symm y, ⟨e.map_target hytarget, ?_⟩, e.right_inv hytarget⟩
      change e (e.symm y) ∈ Metric.ball (e x) r
      rw [e.right_inv hytarget]
      exact hy
  have hVcontractible : ContractibleSpace V := by
    let _ : ContractibleSpace (Metric.ball (e x) r) :=
      Metric.contractibleSpace_ball hr
    exact (e.homeomorphOfImageSubsetSource hVsource himage).contractibleSpace
  have hVU : V ≤ U := by
    intro z hz
    have hze : e z ∈ e.target ∩ e.symm ⁻¹' (U : Set _) := hball hz.2
    change z ∈ (U : Set _)
    have hzU : e.symm (e z) ∈ (U : Set _) := hze.2
    rw [e.left_inv hz.1] at hzU
    exact hzU
  exact ⟨V, hxV, hVcontractible, hVU⟩

/-- The analytic topology on the smooth complex-point space is locally path connected. -/
theorem locallyPathConnectedSpace [SmoothOfRelativeDimension d structureMap] :
    LocallyPathConnectedSpace (ComplexPoint X structureMap) := by
  refine ⟨fun x ↦ hasBasis_self.mpr fun S hS ↦ ?_⟩
  obtain ⟨U, hUS, hUopen, hxU⟩ := mem_nhds_iff.mp hS
  let Uo : TopologicalSpace.Opens (ComplexPoint X structureMap) := ⟨U, hUopen⟩
  obtain ⟨V, hxV, hVcontractible, hVU⟩ :=
    exists_contractibleOpen_le structureMap d x Uo hxU
  let _ : ContractibleSpace V := hVcontractible
  refine ⟨(V : Set _), V.2.mem_nhds hxV, ?_, ?_⟩
  · rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance
  · intro z hz
    exact hUS (hVU hz)

/-- The local fundamental class at a smooth complex point, constructed from its chosen algebraic
étale chart and the standard complex orientation. -/
def localFundamentalClass [SmoothOfRelativeDimension d structureMap]
    (z : ComplexPoint X structureMap) :
    AlgebraicTopology.Singular.RelativeHomology ℚ
      (AlgebraicTopology.Singular.pointComplementPair z) (2 * d) :=
  AlgebraicTopology.Singular.localClassOfChart d (localChart structureMap d z) z
    (mem_localChart_source structureMap d z)

end AlgebraicGeometry.ComplexPoint
