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

public import Other.AlgebraicGeometry.Cycle.Component.LocalOrientation
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance
public import Other.AlgebraicGeometry.Cycle.Component.LocalGenerator
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClass
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-!
# Coherence of exact cycle-component local orientations

Exact étale coordinate packages on the smooth locus of a cycle component give compatible
complex local homology classes.  The transition between two such packages is analytic because
each target coordinate is a regular-function evaluation on the overlap of their affine
neighborhoods.  The general analytic chart-transition invariance theorem then identifies their
normalized local classes.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry
namespace ClosedEmbeddingSeparateLocalCoordinates

open AlgebraicTopology.Singular

variable {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d n : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]

variable (C : ClosedEmbeddingSeparateLocalCoordinates i d n)

/-- Each exact coordinate of the affine source chart is evaluation of the corresponding
global regular function. -/
lemma neighborhoodProjectionChart_apply_eq_evaluate
    (z : ComplexPoint C.neighborhoodScheme)
    (hz : z ∈ C.neighborhoodProjectionChart.source) (k : Fin n) :
    C.neighborhoodProjectionChart z k =
      Point.evaluate ⊤ (C.coordinateRingHomOnNeighborhood (MvPolynomial.X k)) z := by
  rw [C.neighborhoodProjectionChart_apply_of_mem z hz]
  exact C.neighborhoodPointAlgHomHomeomorph_apply z _

/-- The open of the smooth locus on which a source coordinate is represented by a regular
section. -/
abbrev smoothCoordinateOpen : (sourceSmoothLocus i).toScheme.Opens :=
  C.sourceNeighborhood.ι ''ᵁ (⊤ : C.sourceNeighborhood.toScheme.Opens)

/-- A source coordinate, transported from its affine neighborhood to the smooth locus. -/
def smoothCoordinateSection (k : Fin n) :
    Γ((sourceSmoothLocus i).toScheme, C.smoothCoordinateOpen) :=
  (C.sourceNeighborhood.ι.appIso ⊤).inv
    (C.coordinateRingHomOnNeighborhood (MvPolynomial.X k))

/-- The inverse of the extended source chart is the inverse neighborhood chart followed by
the two open immersions. -/
@[simp]
lemma sourceProjectionChart_symm_apply (w : Fin n → ℂ) :
    C.sourceProjectionChart.symm w =
      C.neighborhoodToSourcePoint (C.neighborhoodProjectionChart.symm w) := by
  rw [sourceProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

/-- Canceling the common open immersion into the source identifies two lifts to its smooth
locus. -/
lemma smoothPoints_eq_of_neighborhoodToSourcePoint_eq
    (C' : ClosedEmbeddingSeparateLocalCoordinates i d n)
    (z : ComplexPoint C.neighborhoodScheme)
    (z' : ComplexPoint C'.neighborhoodScheme)
    (h : C.neighborhoodToSourcePoint z = C'.neighborhoodToSourcePoint z') :
    Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood) z =
      Point.map (ComplexPoint.openInclusion
        (sourceSmoothScheme i) C'.sourceNeighborhood) z' :=
  (ComplexPoint.isOpenEmbedding_map_open
    (Y)
    (sourceSmoothLocus i)).injective h

/-- If a smooth-locus point lies in the source of an extended source chart, that chart is
evaluation of its defining smooth-locus sections. -/
lemma sourceProjectionChart_apply_component_eq_evaluate
    (q : ComplexPoint (sourceSmoothScheme i))
    (hq : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) q ∈
      C.sourceProjectionChart.source) (k : Fin n) :
    C.sourceProjectionChart
        (Point.map (ComplexPoint.openInclusion
          (Y)
          (sourceSmoothLocus i)) q) k =
      Point.evaluate C.smoothCoordinateOpen
        (C.smoothCoordinateSection k) q := by
  rw [sourceProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨z, hz, heq⟩ := hq
  rw [← heq, sourceProjectionChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply,
    C.neighborhoodProjectionChart_apply_eq_evaluate z hz k]
  have hsmooth :
      Point.map (ComplexPoint.openInclusion
        (sourceSmoothScheme i) C.sourceNeighborhood) z = q :=
    (ComplexPoint.isOpenEmbedding_map_open
      (Y)
      (sourceSmoothLocus i)).injective heq
  rw [← hsmooth]
  exact (ComplexPoint.evaluate_openEquiv (sourceSmoothScheme i)
    C.sourceNeighborhood
    (C.coordinateRingHomOnNeighborhood (MvPolynomial.X k)) z).symm

/-- Membership in the extended chart source forces the corresponding smooth-locus point to lie
in the affine open on which the chart coordinates are represented. -/
lemma mem_smoothCoordinateOpen_of_mem_sourceProjectionChart_source
    (q : ComplexPoint (sourceSmoothScheme i))
    (hq : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) q ∈
      C.sourceProjectionChart.source) :
    q ∈ Point.overOpen C.smoothCoordinateOpen := by
  rw [sourceProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨z, _, heq⟩ := hq
  have hsmooth : Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood) z = q :=
    (ComplexPoint.isOpenEmbedding_map_open
      (Y)
      (sourceSmoothLocus i)).injective heq
  rw [← hsmooth]
  change (Point.map (ComplexPoint.openInclusion
    (sourceSmoothScheme i) C.sourceNeighborhood) z).underlying ∈
    C.sourceNeighborhood.ι ''ᵁ (⊤ : C.sourceNeighborhood.toScheme.Opens)
  rw [Point.underlying_map, Scheme.Opens.ι_image_top]
  exact z.underlying.property

/-- Evaluation of a regular section on the smooth locus is analytic along the inverse of an
exact component chart, provided the section is defined at the distinguished inverse-chart
point. -/
lemma analyticAt_sourceProjectionChart_symm_smoothEvaluate
    {w : Fin n → ℂ} (hw : w ∈ C.sourceProjectionChart.target)
    (W : (sourceSmoothLocus i).toScheme.Opens)
    (s : Γ((sourceSmoothLocus i).toScheme, W))
    (hW : Point.map (ComplexPoint.openInclusion
        (sourceSmoothScheme i) C.sourceNeighborhood)
        (C.neighborhoodProjectionChart.symm w) ∈ Point.overOpen W) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate W s
      (Point.map (ComplexPoint.openInclusion
        (sourceSmoothScheme i) C.sourceNeighborhood)
        (C.neighborhoodProjectionChart.symm v))) w := by
  have hw' : w ∈ C.neighborhoodProjectionChart.target := by
    simpa only [sourceProjectionChart,
      OpenPartialHomeomorph.lift_openEmbedding_target] using hw
  have hW' : C.neighborhoodProjectionChart.symm w ∈
      Point.overOpen (C.sourceNeighborhood.ι ⁻¹ᵁ W) :=
    (Point.mem_overOpen_map_iff (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood) _ W).mp hW
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_evaluate hw'
    (C.sourceNeighborhood.ι ⁻¹ᵁ W)
    (C.sourceNeighborhood.ι.app W s) hW'
  apply ha.congr
  filter_upwards with v
  exact (Point.evaluate_map (ComplexPoint.openInclusion
    (sourceSmoothScheme i) C.sourceNeighborhood) W s
    (C.neighborhoodProjectionChart.symm v)).symm

/-- Each coordinate of a transition between two exact source charts is complex analytic. -/
lemma analyticAt_sourceProjectionChart_transition_component
    (C' : ClosedEmbeddingSeparateLocalCoordinates i d n)
    {w : Fin n → ℂ}
    (hw : w ∈ (C.sourceProjectionChart.symm.trans
      C'.sourceProjectionChart).source) (k : Fin n) :
    AnalyticAt ℂ (fun v ↦ C'.sourceProjectionChart
      (C.sourceProjectionChart.symm v) k) w := by
  rw [OpenPartialHomeomorph.trans_source] at hw
  let q : ComplexPoint (sourceSmoothScheme i) :=
    Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood)
      (C.neighborhoodProjectionChart.symm w)
  have hqmap : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) q =
      C.sourceProjectionChart.symm w := rfl
  have hsource : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) q ∈
      C'.sourceProjectionChart.source := hqmap ▸ hw.2
  have hW : q ∈ Point.overOpen C'.smoothCoordinateOpen :=
    C'.mem_smoothCoordinateOpen_of_mem_sourceProjectionChart_source q hsource
  have ha := C.analyticAt_sourceProjectionChart_symm_smoothEvaluate hw.1
    C'.smoothCoordinateOpen (C'.smoothCoordinateSection k) hW
  apply ha.congr
  have hcontinuous : ContinuousAt C.sourceProjectionChart.symm w :=
    C.sourceProjectionChart.continuousAt_symm hw.1
  have heventually : C.sourceProjectionChart.symm ⁻¹'
      C'.sourceProjectionChart.source ∈ nhds w :=
    hcontinuous (C'.sourceProjectionChart.open_source.mem_nhds hw.2)
  filter_upwards [heventually] with v hv
  let qv : ComplexPoint (sourceSmoothScheme i) :=
    Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood)
      (C.neighborhoodProjectionChart.symm v)
  have hqvmap : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) qv =
      C.sourceProjectionChart.symm v := rfl
  have hv' : Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i)) qv ∈
      C'.sourceProjectionChart.source := by
    rwa [hqvmap]
  rw [← hqvmap]
  exact (C'.sourceProjectionChart_apply_component_eq_evaluate qv hv' k).symm

/-- A transition between two exact source charts is complex analytic on its overlap. -/
lemma analyticAt_sourceProjectionChart_transition
    (C' : ClosedEmbeddingSeparateLocalCoordinates i d n)
    {w : Fin n → ℂ}
    (hw : w ∈ (C.sourceProjectionChart.symm.trans
      C'.sourceProjectionChart).source) :
    AnalyticAt ℂ (fun v ↦ C'.sourceProjectionChart
      (C.sourceProjectionChart.symm v)) w :=
  AnalyticAt.pi fun k ↦
    C.analyticAt_sourceProjectionChart_transition_component C' hw k

/-- Any two exact source charts transport the normalized complex local class to the same
class at every point in their common source. -/
theorem localClassOfChart_sourceProjectionChart_eq
    (C' : ClosedEmbeddingSeparateLocalCoordinates i d n)
    (q : ComplexPoint Y)
    (hq : q ∈ C.sourceProjectionChart.source)
    (hq' : q ∈ C'.sourceProjectionChart.source) :
    localClassOfChart n C.sourceProjectionChart q hq =
      localClassOfChart n C'.sourceProjectionChart q hq' := by
  apply localClassOfChart_eq_of_analyticAt_transition n
  · apply C.analyticAt_sourceProjectionChart_transition C'
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨C.sourceProjectionChart.map_source hq, ?_⟩
    rw [Set.mem_preimage, C.sourceProjectionChart.left_inv hq]
    exact hq'
  · apply C'.analyticAt_sourceProjectionChart_transition C
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨C'.sourceProjectionChart.map_source hq', ?_⟩
    rw [Set.mem_preimage, C'.sourceProjectionChart.left_inv hq']
    exact hq

private lemma transport_localClassOfChart
    {M : Type} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (Fin n → ℂ))
    (q q' : M) (hq : q ∈ e.source) (hq' : q' ∈ e.source)
    (hpoint : q = q') :
    hpoint ▸ localClassOfChart n e q hq =
      localClassOfChart n e q' hq' := by
  subst q'
  rfl

private lemma transport_trans
    {A : Type} (F : A → Type) {a b c : A}
    (hab : a = b) (hbc : b = c) (u : F a) :
    hbc ▸ (hab ▸ u) = hab.trans hbc ▸ u := by
  subst b
  subst c
  rfl

/-- Exact coordinate packages centered at the same component point construct the same local
orientation class.  The equality transports the first class along equality of the centers. -/
theorem sourceLocalOrientationClass_eq_of_point_eq
    (C' : ClosedEmbeddingSeparateLocalCoordinates i d n)
    (hpoint : C.point = C'.point) :
    hpoint ▸ C.sourceLocalOrientationClass =
      C'.sourceLocalOrientationClass := by
  have hq' : C.point ∈ C'.sourceProjectionChart.source := by
    rw [hpoint]
    exact C'.point_mem_sourceProjectionChart_source
  have hlocal := C.localClassOfChart_sourceProjectionChart_eq C' C.point
    C.point_mem_sourceProjectionChart_source
    hq'
  unfold sourceLocalOrientationClass
  calc
    hpoint ▸ localClassOfChart n C.sourceProjectionChart C.point
        C.point_mem_sourceProjectionChart_source =
      hpoint ▸ localClassOfChart n C'.sourceProjectionChart C.point hq' :=
        congrArg (fun c ↦ hpoint ▸ c) hlocal
    _ = localClassOfChart n C'.sourceProjectionChart C'.point
        C'.point_mem_sourceProjectionChart_source :=
      transport_localClassOfChart C'.sourceProjectionChart C.point C'.point
        hq' C'.point_mem_sourceProjectionChart_source hpoint

/-- The local class produced by any exact package centered at a prescribed smooth point agrees
with the canonical class defined using the internally chosen package. -/
theorem sourceLocalOrientationClass_eq_closedEmbeddingComplexLocalOrientation
    (p : ℕ) (D : ClosedEmbeddingSeparateLocalCoordinates i d (d - p))
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint Y)
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i)
    (hpoint : D.point = z) :
    hpoint ▸ D.sourceLocalOrientationClass =
      ComplexPoint.closedEmbeddingComplexLocalOrientation V i d p hi z hz := by
  let C' := closedEmbeddingLocalCoordinatesAt V i d p hi z hz
  have hchoice : C'.point = z :=
    closedEmbeddingLocalCoordinatesAt_point V i d p hi z hz
  let hDC' : D.point = C'.point := hpoint.trans hchoice.symm
  have hlocal : hDC' ▸ D.sourceLocalOrientationClass =
      C'.sourceLocalOrientationClass :=
    D.sourceLocalOrientationClass_eq_of_point_eq C' hDC'
  have htransport := congrArg (fun c ↦ hchoice ▸ c) hlocal
  rw [transport_trans
    (fun q ↦ RelativeHomology ℚ (pointComplementPair q) (2 * (d - p)))
    hDC' hchoice D.sourceLocalOrientationClass] at htransport
  have hproof : hDC'.trans hchoice = hpoint := Subsingleton.elim _ _
  rw [hproof] at htransport
  simpa only [ComplexPoint.closedEmbeddingComplexLocalOrientation, C'] using htransport

end ClosedEmbeddingSeparateLocalCoordinates
end AlgebraicGeometry
