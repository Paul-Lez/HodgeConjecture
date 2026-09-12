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

public import Other.AlgebraicGeometry.CycleComponentLocalOrientation
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

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
namespace CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

noncomputable local instance componentCoherenceTopology {Y : Over (Spec (.of ℂ))} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d n : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]

variable (C : CycleComponentSeparateLocalCoordinates V.over x d n)

/-- Each exact coordinate of the affine component chart is evaluation of the corresponding
global regular function. -/
lemma neighborhoodProjectionChart_apply_eq_evaluate
    (z : ComplexPoint C.neighborhoodScheme)
    (hz : z ∈ C.neighborhoodProjectionChart.source) (i : Fin n) :
    C.neighborhoodProjectionChart z i =
      Point.evaluate ⊤ (C.coordinateRingHomOnNeighborhood (MvPolynomial.X i)) z := by
  rw [C.neighborhoodProjectionChart_apply_of_mem z hz]
  exact C.neighborhoodPointAlgHomHomeomorph_apply z _

/-- The open of the smooth locus on which a component coordinate is represented by a regular
section. -/
abbrev smoothCoordinateOpen : (componentSmoothLocus V.over x).toScheme.Opens :=
  C.componentNeighborhood.ι ''ᵁ (⊤ : C.componentNeighborhood.toScheme.Opens)

/-- A component coordinate, transported from its affine neighborhood to the smooth locus. -/
def smoothCoordinateSection (i : Fin n) :
    Γ((componentSmoothLocus V.over x).toScheme, C.smoothCoordinateOpen) :=
  (C.componentNeighborhood.ι.appIso ⊤).inv
    (C.coordinateRingHomOnNeighborhood (MvPolynomial.X i))

/-- The inverse of the extended component chart is the inverse neighborhood chart followed by
the two open immersions. -/
@[simp]
lemma componentProjectionChart_symm_apply (w : Fin n → ℂ) :
    C.componentProjectionChart.symm w =
      C.neighborhoodToComponentPoint (C.neighborhoodProjectionChart.symm w) := by
  rw [componentProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

/-- Canceling the common open immersion into the component identifies two lifts to its smooth
locus. -/
lemma smoothPoints_eq_of_neighborhoodToComponentPoint_eq
    (C' : CycleComponentSeparateLocalCoordinates V.over x d n)
    (z : ComplexPoint C.neighborhoodScheme)
    (z' : ComplexPoint C'.neighborhoodScheme)
    (h : C.neighborhoodToComponentPoint z = C'.neighborhoodToComponentPoint z') :
    Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood) z =
      Point.map (ComplexPoint.openInclusion
        (componentSmoothScheme V.over x) C'.componentNeighborhood) z' :=
  (ComplexPoint.isOpenEmbedding_map_open
    (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
    (componentSmoothLocus V.over x)).injective h

/-- If a smooth-locus point lies in the source of an extended component chart, that chart is
evaluation of its defining smooth-locus sections. -/
lemma componentProjectionChart_apply_component_eq_evaluate
    (q : ComplexPoint (componentSmoothScheme V.over x))
    (hq : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) q ∈
      C.componentProjectionChart.source) (i : Fin n) :
    C.componentProjectionChart
        (Point.map (ComplexPoint.openInclusion
          (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
          (componentSmoothLocus V.over x)) q) i =
      Point.evaluate C.smoothCoordinateOpen
        (C.smoothCoordinateSection i) q := by
  rw [componentProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨z, hz, heq⟩ := hq
  rw [← heq, componentProjectionChart,
    OpenPartialHomeomorph.lift_openEmbedding_apply,
    C.neighborhoodProjectionChart_apply_eq_evaluate z hz i]
  have hsmooth :
      Point.map (ComplexPoint.openInclusion
        (componentSmoothScheme V.over x) C.componentNeighborhood) z = q :=
    (ComplexPoint.isOpenEmbedding_map_open
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)).injective heq
  rw [← hsmooth]
  exact (ComplexPoint.evaluate_openEquiv (componentSmoothScheme V.over x)
    C.componentNeighborhood
    (C.coordinateRingHomOnNeighborhood (MvPolynomial.X i)) z).symm

/-- Membership in the extended chart source forces the corresponding smooth-locus point to lie
in the affine open on which the chart coordinates are represented. -/
lemma mem_smoothCoordinateOpen_of_mem_componentProjectionChart_source
    (q : ComplexPoint (componentSmoothScheme V.over x))
    (hq : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) q ∈
      C.componentProjectionChart.source) :
    q ∈ Point.overOpen C.smoothCoordinateOpen := by
  rw [componentProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨z, _, heq⟩ := hq
  have hsmooth : Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood) z = q :=
    (ComplexPoint.isOpenEmbedding_map_open
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)).injective heq
  rw [← hsmooth]
  change (Point.map (ComplexPoint.openInclusion
    (componentSmoothScheme V.over x) C.componentNeighborhood) z).underlying ∈
    C.componentNeighborhood.ι ''ᵁ (⊤ : C.componentNeighborhood.toScheme.Opens)
  rw [Point.underlying_map, Scheme.Opens.ι_image_top]
  exact z.underlying.property

/-- Evaluation of a regular section on the smooth locus is analytic along the inverse of an
exact component chart, provided the section is defined at the distinguished inverse-chart
point. -/
lemma analyticAt_componentProjectionChart_symm_smoothEvaluate
    {w : Fin n → ℂ} (hw : w ∈ C.componentProjectionChart.target)
    (W : (componentSmoothLocus V.over x).toScheme.Opens)
    (s : Γ((componentSmoothLocus V.over x).toScheme, W))
    (hW : Point.map (ComplexPoint.openInclusion
        (componentSmoothScheme V.over x) C.componentNeighborhood)
        (C.neighborhoodProjectionChart.symm w) ∈ Point.overOpen W) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate W s
      (Point.map (ComplexPoint.openInclusion
        (componentSmoothScheme V.over x) C.componentNeighborhood)
        (C.neighborhoodProjectionChart.symm v))) w := by
  have hw' : w ∈ C.neighborhoodProjectionChart.target := by
    simpa only [componentProjectionChart,
      OpenPartialHomeomorph.lift_openEmbedding_target] using hw
  have hW' : C.neighborhoodProjectionChart.symm w ∈
      Point.overOpen (C.componentNeighborhood.ι ⁻¹ᵁ W) :=
    (Point.mem_overOpen_map_iff (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood) _ W).mp hW
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_evaluate hw'
    (C.componentNeighborhood.ι ⁻¹ᵁ W)
    (C.componentNeighborhood.ι.app W s) hW'
  apply ha.congr
  filter_upwards with v
  exact (Point.evaluate_map (ComplexPoint.openInclusion
    (componentSmoothScheme V.over x) C.componentNeighborhood) W s
    (C.neighborhoodProjectionChart.symm v)).symm

/-- Each coordinate of a transition between two exact component charts is complex analytic. -/
lemma analyticAt_componentProjectionChart_transition_component
    (C' : CycleComponentSeparateLocalCoordinates V.over x d n)
    {w : Fin n → ℂ}
    (hw : w ∈ (C.componentProjectionChart.symm.trans
      C'.componentProjectionChart).source) (i : Fin n) :
    AnalyticAt ℂ (fun v ↦ C'.componentProjectionChart
      (C.componentProjectionChart.symm v) i) w := by
  rw [OpenPartialHomeomorph.trans_source] at hw
  let q : ComplexPoint (componentSmoothScheme V.over x) :=
    Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood)
      (C.neighborhoodProjectionChart.symm w)
  have hqmap : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) q =
      C.componentProjectionChart.symm w := rfl
  have hsource : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) q ∈
      C'.componentProjectionChart.source := hqmap ▸ hw.2
  have hW : q ∈ Point.overOpen C'.smoothCoordinateOpen :=
    C'.mem_smoothCoordinateOpen_of_mem_componentProjectionChart_source q hsource
  have ha := C.analyticAt_componentProjectionChart_symm_smoothEvaluate hw.1
    C'.smoothCoordinateOpen (C'.smoothCoordinateSection i) hW
  apply ha.congr
  have hcontinuous : ContinuousAt C.componentProjectionChart.symm w :=
    C.componentProjectionChart.continuousAt_symm hw.1
  have heventually : C.componentProjectionChart.symm ⁻¹'
      C'.componentProjectionChart.source ∈ nhds w :=
    hcontinuous (C'.componentProjectionChart.open_source.mem_nhds hw.2)
  filter_upwards [heventually] with v hv
  let qv : ComplexPoint (componentSmoothScheme V.over x) :=
    Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood)
      (C.neighborhoodProjectionChart.symm v)
  have hqvmap : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) qv =
      C.componentProjectionChart.symm v := rfl
  have hv' : Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)) qv ∈
      C'.componentProjectionChart.source := by
    rwa [hqvmap]
  rw [← hqvmap]
  exact (C'.componentProjectionChart_apply_component_eq_evaluate qv hv' i).symm

/-- A transition between two exact component charts is complex analytic on its overlap. -/
lemma analyticAt_componentProjectionChart_transition
    (C' : CycleComponentSeparateLocalCoordinates V.over x d n)
    {w : Fin n → ℂ}
    (hw : w ∈ (C.componentProjectionChart.symm.trans
      C'.componentProjectionChart).source) :
    AnalyticAt ℂ (fun v ↦ C'.componentProjectionChart
      (C.componentProjectionChart.symm v)) w :=
  AnalyticAt.pi fun i ↦
    C.analyticAt_componentProjectionChart_transition_component C' hw i

/-- Any two exact component charts transport the normalized complex local class to the same
class at every point in their common source. -/
theorem localClassOfChart_componentProjectionChart_eq
    (C' : CycleComponentSeparateLocalCoordinates V.over x d n)
    (q : ComplexPoint (Over.mk
      (cycleComponentι V.over.left x ≫ V.over.hom)))
    (hq : q ∈ C.componentProjectionChart.source)
    (hq' : q ∈ C'.componentProjectionChart.source) :
    localClassOfChart n C.componentProjectionChart q hq =
      localClassOfChart n C'.componentProjectionChart q hq' := by
  apply localClassOfChart_eq_of_analyticAt_transition n
  · apply C.analyticAt_componentProjectionChart_transition C'
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨C.componentProjectionChart.map_source hq, ?_⟩
    rw [Set.mem_preimage, C.componentProjectionChart.left_inv hq]
    exact hq'
  · apply C'.analyticAt_componentProjectionChart_transition C
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨C'.componentProjectionChart.map_source hq', ?_⟩
    rw [Set.mem_preimage, C'.componentProjectionChart.left_inv hq']
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
theorem componentLocalOrientationClass_eq_of_point_eq
    (C' : CycleComponentSeparateLocalCoordinates V.over x d n)
    (hpoint : C.point = C'.point) :
    hpoint ▸ C.componentLocalOrientationClass =
      C'.componentLocalOrientationClass := by
  have hq' : C.point ∈ C'.componentProjectionChart.source := by
    rw [hpoint]
    exact C'.point_mem_componentProjectionChart_source
  have hlocal := C.localClassOfChart_componentProjectionChart_eq C' C.point
    C.point_mem_componentProjectionChart_source
    hq'
  unfold componentLocalOrientationClass
  calc
    hpoint ▸ localClassOfChart n C.componentProjectionChart C.point
        C.point_mem_componentProjectionChart_source =
      hpoint ▸ localClassOfChart n C'.componentProjectionChart C.point hq' :=
        congrArg (fun c ↦ hpoint ▸ c) hlocal
    _ = localClassOfChart n C'.componentProjectionChart C'.point
        C'.point_mem_componentProjectionChart_source :=
      transport_localClassOfChart C'.componentProjectionChart C.point C'.point
        hq' C'.point_mem_componentProjectionChart_source hpoint

/-- The local class produced by any exact package centered at a prescribed smooth point agrees
with the canonical class defined using the internally chosen package. -/
theorem componentLocalOrientationClass_eq_cycleComponentComplexLocalOrientation
    (p : ℕ) (D : CycleComponentSeparateLocalCoordinates V.over x d (d - p))
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk
      (cycleComponentι V.over.left x ≫ V.over.hom)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x)
    (hpoint : D.point = z) :
    hpoint ▸ D.componentLocalOrientationClass =
      ComplexPoint.cycleComponentComplexLocalOrientation V x d p hx z hz := by
  let C' := cycleComponentLocalCoordinatesAt V x d p hx z hz
  have hchoice : C'.point = z :=
    cycleComponentLocalCoordinatesAt_point V x d p hx z hz
  let hDC' : D.point = C'.point := hpoint.trans hchoice.symm
  have hlocal : hDC' ▸ D.componentLocalOrientationClass =
      C'.componentLocalOrientationClass :=
    D.componentLocalOrientationClass_eq_of_point_eq C' hDC'
  have htransport := congrArg (fun c ↦ hchoice ▸ c) hlocal
  rw [transport_trans
    (fun q ↦ RelativeHomology ℚ (pointComplementPair q) (2 * (d - p)))
    hDC' hchoice D.componentLocalOrientationClass] at htransport
  have hproof : hDC'.trans hchoice = hpoint := Subsingleton.elim _ _
  rw [hproof] at htransport
  simpa only [ComplexPoint.cycleComponentComplexLocalOrientation, C'] using htransport

end CycleComponentSeparateLocalCoordinates
end AlgebraicGeometry
