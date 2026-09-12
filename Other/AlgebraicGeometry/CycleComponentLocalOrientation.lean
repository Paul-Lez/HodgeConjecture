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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
public import Other.AlgebraicGeometry.SmoothProjective
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-!
# Local complex orientation of a cycle component

Let `x` be a codimension-`p` point of a smooth complex `d`-fold. At every smooth complex point
of its reduced closure, this file constructs exact étale coordinates with `d - p` variables.
The resulting analytic chart is extended through the open immersions from the affine coordinate
neighborhood to the smooth locus and then to the whole component. Transporting the explicit
standard complex class gives an exactly normalized element of the component's top local
homology.

No local class, generator, sign, or rational multiple is an input to this construction. The only
choice is among the proved nonempty type of algebraic étale coordinate packages. Independence
of that choice follows once invariance of the explicit local class under positive chart
transitions is available.
-/

@[expose] public noncomputable section

open CategoryTheory Ideal MvPolynomial Topology TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] overSpecAlgebra

/-- Mapping a point lifted to an open subscheme back to the ambient scheme recovers the original
complex point. -/
@[simp]
lemma ComplexPoint.map_asOpenPoint {X : Over (Spec ↧ℂ)} (U : X.left.Opens)
    (z : ComplexPoint X)
    (hz : z ∈ Point.overOpen U) :
    Point.map (openInclusion X U) (asOpenPoint X U z hz) = z :=
  Over.OverMorphism.ext (liftToOpen_fac X U z hz)

variable {d p : ℕ}

/-- Transporting a generator along an equality of an indexed family preserves the property of
spanning the whole module. -/
private lemma span_singleton_transport_eq_top
    {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    {i j : ι} (h : i = j) (c : M i)
    (hc : Submodule.span ℚ {c} = ⊤) :
    Submodule.span ℚ {h ▸ c} = ⊤ := by
  subst j
  exact hc

/-- Transporting a nonzero vector along an equality of indices preserves nonvanishing. -/
private lemma transport_ne_zero
    {ι : Type*} (M : ι → Type*) [∀ i, Zero (M i)]
    {i j : ι} (h : i = j) (c : M i) (hc : c ≠ 0) :
    h ▸ c ≠ 0 := by
  subst j
  exact hc

/-- Exact component coordinates of dimension `d - p` can be constructed at any prescribed
smooth complex point of a codimension-`p` cycle component. -/
lemma nonempty_cycleComponentSeparateLocalCoordinates_at
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    ∃ C : CycleComponentSeparateLocalCoordinates V.over x d (d - p), C.point = z := by
  let c : cycleComponent V.scheme x ⟶ Spec ↧ℂ :=
    cycleComponentι V.scheme x ≫ V.structureMap
  let S : (cycleComponent V.scheme x).Opens := c.smoothLocus
  let g : S.toScheme ⟶ Spec ↧ℂ := S.ι ≫ c
  let : Smooth g := cycleComponent_smoothLocus_smooth V.over x
  let zs : S.toScheme := ⟨z.underlying, hz⟩
  obtain ⟨W, hW, hzsW, hstandard⟩ := Smooth.exists_affine_isStandardSmooth g zs
  have hstandardComplex := algebraMap_isStandardSmooth (Over.mk g) hstandard
  obtain ⟨m, hm⟩ := hstandardComplex.exists_isStandardSmoothOfRelativeDimension
  have hzclosed : IsClosed {z.underlying} :=
    cycleComponent_complexPoint_underlying_isClosed V.over x z
  have hzsClosed : IsClosed {zs} := by
    have hpreimage : S.ι ⁻¹' ({z.underlying} : Set (cycleComponent V.scheme x)) =
        ({zs} : Set S.toScheme) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    exact hpreimage ▸ hzclosed.preimage S.ι.continuous
  let zw : W.toScheme := ⟨zs, hzsW⟩
  let P : Ideal Γ(S, W) := (hW.primeIdealOf zw).asIdeal
  let : P.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed zw hzsClosed
  have hPm : P.height = m :=
    RingHom.IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal hm P
  have hPcoheight : P.height = Order.coheight zw :=
    hW.primeIdealOf_height_eq_coheight zw
  have hWcoheight : Order.coheight zs = Order.coheight zw :=
    coheight_eq_of_isOpenImmersion (x := zw) W.ι
  have hScoheight : Order.coheight z.underlying = Order.coheight zs :=
    coheight_eq_of_isOpenImmersion (x := zs) S.ι
  have hmEq : m = d - p := by
    exact_mod_cast calc
      (m : ℕ∞) = P.height := hPm.symm
      _ = Order.coheight zw := hPcoheight
      _ = Order.coheight zs := hWcoheight.symm
      _ = Order.coheight z.underlying := hScoheight.symm
      _ = d - p := cycleComponent_complexPoint_coheight_eq_sub V.over x z hx
  subst m
  obtain ⟨coordinateRingHom, hcomp, hetale⟩ := hm.exists_etale_mvPolynomial
  refine ⟨{
    point := z
    point_mem_smoothLocus := hz
    point_isClosed := hzclosed
    componentNeighborhood := W
    componentNeighborhood_isAffine := hW
    point_mem_componentNeighborhood := hzsW
    componentCoordinateAlgHom :=
      { toRingHom := coordinateRingHom
        commutes' := fun c ↦ DFunLike.congr_fun hcomp c }
    componentCoordinateAlgHom_etale := hetale
    ambientCoordinates := localEtaleCoordinates V.over d
      (cycleComponentι V.scheme x z.underlying) }, rfl⟩

/-- A fixed exact coordinate package at a prescribed smooth component point. Existence is the
preceding theorem; no coordinate package is supplied as data. -/
def cycleComponentLocalCoordinatesAt
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    CycleComponentSeparateLocalCoordinates V.over x d (d - p) :=
  Classical.choose (nonempty_cycleComponentSeparateLocalCoordinates_at V x d p hx z hz)

@[simp]
lemma cycleComponentLocalCoordinatesAt_point
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    (cycleComponentLocalCoordinatesAt V x d p hx z hz).point = z :=
  Classical.choose_spec (nonempty_cycleComponentSeparateLocalCoordinates_at V x d p hx z hz)

namespace CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

noncomputable local instance cycleComponentLocalOrientationTopology
    {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {V : SmoothProjectiveComplexVariety} {x : V.scheme} {d n : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  (C : CycleComponentSeparateLocalCoordinates V.over x d n)

/-- The composite open embedding from the affine component-coordinate neighborhood into the
whole reduced component, on complex points. -/
def neighborhoodToComponentPoint :
    ComplexPoint C.neighborhoodScheme →
      ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)) :=
  fun z ↦ Point.map (ComplexPoint.openInclusion
      (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))
      (componentSmoothLocus V.over x))
    (Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood) z)

/-- The neighborhood-to-component map is an open embedding. -/
lemma neighborhoodToComponentPoint_isOpenEmbedding :
    IsOpenEmbedding C.neighborhoodToComponentPoint :=
  (ComplexPoint.isOpenEmbedding_map_open
      (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))
      (componentSmoothLocus V.over x)).comp
    (ComplexPoint.isOpenEmbedding_map_open
      (componentSmoothScheme V.over x) C.componentNeighborhood)

/-- The selected neighborhood point maps to the selected component point. -/
@[simp]
lemma neighborhoodToComponentPoint_neighborhoodPoint :
    C.neighborhoodToComponentPoint C.neighborhoodPoint = C.point := by
  unfold neighborhoodToComponentPoint
  rw [show Point.map (ComplexPoint.openInclusion
      (componentSmoothScheme V.over x) C.componentNeighborhood) C.neighborhoodPoint =
      C.smoothPoint by
    simpa only [neighborhoodPoint] using
      (ComplexPoint.map_asOpenPoint C.componentNeighborhood C.smoothPoint _)]
  simpa only [smoothPoint] using
    (ComplexPoint.map_asOpenPoint
      (X := Over.mk (cycleComponentι V.over.left x ≫ V.over.hom))
      (componentSmoothLocus V.over x)
      C.point C.point_mem_smoothLocus)

/-- The exact component chart, extended along the open embedding into the whole reduced
component. -/
def componentProjectionChart :
    OpenPartialHomeomorph
      (ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
      (Fin n → ℂ) :=
  C.neighborhoodProjectionChart.lift_openEmbedding
    C.neighborhoodToComponentPoint_isOpenEmbedding

/-- The selected component point is in the source of the extended exact chart. -/
lemma point_mem_componentProjectionChart_source :
    C.point ∈ C.componentProjectionChart.source := by
  rw [componentProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨C.neighborhoodPoint, C.neighborhoodPoint_mem_projectionChart_source,
    C.neighborhoodToComponentPoint_neighborhoodPoint⟩

/-- The exactly normalized complex local class at the selected point of the whole component. -/
def componentLocalOrientationClass :
    RelativeHomology ℚ (pointComplementPair C.point) (2 * n) :=
  localClassOfChart n C.componentProjectionChart C.point
    C.point_mem_componentProjectionChart_source

/-- The constructed component-local class generates the full top local homology group. -/
theorem span_componentLocalOrientationClass_eq_top :
    Submodule.span ℚ {C.componentLocalOrientationClass} = ⊤ := by
  let : T2Space
      (ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))) :=
    ProjectiveSpace.Presentation.complexPoint_t2Space
      (Classical.choice (cycleComponent_projective V.over x).nonempty_presentation)
  exact span_localClassOfChart_eq_top n C.componentProjectionChart C.point
    C.point_mem_componentProjectionChart_source

/-- The exactly normalized component-local orientation class is nonzero. -/
theorem componentLocalOrientationClass_ne_zero :
    C.componentLocalOrientationClass ≠ 0 := by
  let : T2Space
      (ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))) :=
    ProjectiveSpace.Presentation.complexPoint_t2Space
      (Classical.choice (cycleComponent_projective V.over x).nonempty_presentation)
  exact localClassOfChart_ne_zero n C.componentProjectionChart C.point
    C.point_mem_componentProjectionChart_source

end CycleComponentSeparateLocalCoordinates

namespace ComplexPoint

open AlgebraicTopology.Singular

noncomputable local instance {V : SmoothProjectiveComplexVariety} {x : V.scheme} :
    TopologicalSpace
      (ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))) := Point.analyticTopology

/-- A family of rational top local homology classes on the smooth analytic locus of a reduced
cycle component. -/
abbrev CycleComponentComplexLocalClassFamily
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (n : ℕ) :=
  ∀ (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap))),
    z ∈ cycleComponentSmoothAnalyticLocus V.over x →
      RelativeHomology ℚ (pointComplementPair z) n

/-- The canonical local complex orientation on a codimension-`p` cycle component. At each smooth
point it is built from exact algebraic étale coordinates of dimension `d - p`. -/
def cycleComponentComplexLocalOrientation
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p) :
    CycleComponentComplexLocalClassFamily V x (2 * (d - p)) :=
  fun z hz ↦
    let C := cycleComponentLocalCoordinatesAt V x d p hx z hz
    (cycleComponentLocalCoordinatesAt_point V x d p hx z hz) ▸
      C.componentLocalOrientationClass

/-- Every value of the constructed component orientation is a generator of top local homology. -/
theorem span_cycleComponentComplexLocalOrientation_eq_top
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    Submodule.span ℚ {cycleComponentComplexLocalOrientation V x d p hx z hz} = ⊤ := by
  let C := cycleComponentLocalCoordinatesAt V x d p hx z hz
  unfold cycleComponentComplexLocalOrientation
  dsimp only
  exact span_singleton_transport_eq_top
    (fun w ↦ RelativeHomology ℚ (pointComplementPair w) (2 * (d - p)))
    (cycleComponentLocalCoordinatesAt_point V x d p hx z hz)
    C.componentLocalOrientationClass C.span_componentLocalOrientationClass_eq_top

/-- Every value of the constructed component orientation is nonzero. -/
theorem cycleComponentComplexLocalOrientation_ne_zero
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hx : Order.coheight x = p)
    (z : ComplexPoint (Over.mk (cycleComponentι V.scheme x ≫ V.structureMap)))
    (hz : z ∈ cycleComponentSmoothAnalyticLocus V.over x) :
    cycleComponentComplexLocalOrientation V x d p hx z hz ≠ 0 := by
  let C := cycleComponentLocalCoordinatesAt V x d p hx z hz
  unfold cycleComponentComplexLocalOrientation
  dsimp only
  exact transport_ne_zero
    (fun w ↦ RelativeHomology ℚ (pointComplementPair w) (2 * (d - p)))
    (cycleComponentLocalCoordinatesAt_point V x d p hx z hz)
    C.componentLocalOrientationClass C.componentLocalOrientationClass_ne_zero

end ComplexPoint
end AlgebraicGeometry
