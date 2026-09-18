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
public import Other.AlgebraicGeometry.SmoothProjectiveVariety
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
public import Other.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
public import Other.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
public import Other.AlgebraicGeometry.Cycle.Component.LocalGenerator
public import Other.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClass
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

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
lemma nonempty_closedEmbeddingSeparateLocalCoordinates_at
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint (Y))
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    ∃ C : ClosedEmbeddingSeparateLocalCoordinates i d (d - p), C.point = z := by
  let c : Y.left ⟶ Spec ↧ℂ :=
    i.left ≫ V.structureMap
  let S : (Y.left).Opens := c.smoothLocus
  let g : S.toScheme ⟶ Spec ↧ℂ := S.ι ≫ Y.hom
  let : Smooth g := by
    change Smooth (S.ι ≫ Y.hom)
    have h : Y.hom = c := (Over.w i).symm
    rw [h]
    exact c.smooth_restrict_smoothLocus
  let zs : S.toScheme := ⟨z.underlying, hz⟩
  obtain ⟨W, hW, hzsW, hstandard⟩ := Smooth.exists_affine_isStandardSmooth g zs
  have hstandardComplex := algebraMap_isStandardSmooth (Over.mk g) hstandard
  obtain ⟨m, hm⟩ := hstandardComplex.exists_isStandardSmoothOfRelativeDimension
  have hzclosed : IsClosed {z.underlying} :=
    closedEmbedding_complexPoint_underlying_isClosed i z
  have hzsClosed : IsClosed {zs} := by
    have hpreimage : S.ι ⁻¹' ({z.underlying} : Set (Y.left)) =
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
      _ = d - p := closedEmbedding_complexPoint_coheight_eq_sub i z hi
  subst m
  obtain ⟨coordinateRingHom, hcomp, hetale⟩ := hm.exists_etale_mvPolynomial
  refine ⟨{
    point := z
    point_mem_smoothLocus := hz
    point_isClosed := hzclosed
    sourceNeighborhood := W
    sourceNeighborhood_isAffine := hW
    point_mem_sourceNeighborhood := hzsW
    sourceCoordinateAlgHom :=
      { toRingHom := coordinateRingHom
        commutes' := fun c ↦ DFunLike.congr_fun hcomp c }
    sourceCoordinateAlgHom_etale := hetale
    ambientCoordinates := localEtaleCoordinates V.over d
      (i.left z.underlying) }, rfl⟩

/-- A fixed exact coordinate package at a prescribed smooth component point. Existence is the
preceding theorem; no coordinate package is supplied as data. -/
def closedEmbeddingLocalCoordinatesAt
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint (Y))
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    ClosedEmbeddingSeparateLocalCoordinates i d (d - p) :=
  Classical.choose (nonempty_closedEmbeddingSeparateLocalCoordinates_at V i d p hi z hz)

@[simp]
lemma closedEmbeddingLocalCoordinatesAt_point
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint (Y))
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    (closedEmbeddingLocalCoordinatesAt V i d p hi z hz).point = z :=
  Classical.choose_spec (nonempty_closedEmbeddingSeparateLocalCoordinates_at V i d p hi z hz)

namespace ClosedEmbeddingSeparateLocalCoordinates

open AlgebraicTopology.Singular

variable {V : SmoothProjectiveComplexVariety} {Y : Over (Spec ↧ℂ)} {i : Y ⟶ V.over}
  [IsIntegral Y.left] [IsClosedImmersion i.left] {d n : ℕ}
  [SmoothOfRelativeDimension d V.structureMap]
  (C : ClosedEmbeddingSeparateLocalCoordinates i d n)

/-- The composite open embedding from the affine source-coordinate neighborhood into the
whole source, on complex points. -/
def neighborhoodToSourcePoint :
    ComplexPoint C.neighborhoodScheme →
      ComplexPoint (Y) :=
  fun z ↦ Point.map (ComplexPoint.openInclusion
      (Y)
      (sourceSmoothLocus i))
    (Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood) z)

/-- The neighborhood-to-source map is an open embedding. -/
lemma neighborhoodToSourcePoint_isOpenEmbedding :
    IsOpenEmbedding C.neighborhoodToSourcePoint :=
  (ComplexPoint.isOpenEmbedding_map_open
      (Y)
      (sourceSmoothLocus i)).comp
    (ComplexPoint.isOpenEmbedding_map_open
      (sourceSmoothScheme i) C.sourceNeighborhood)

/-- The selected neighborhood point maps to the selected source point. -/
@[simp]
lemma neighborhoodToSourcePoint_neighborhoodPoint :
    C.neighborhoodToSourcePoint C.neighborhoodPoint = C.point := by
  unfold neighborhoodToSourcePoint
  rw [show Point.map (ComplexPoint.openInclusion
      (sourceSmoothScheme i) C.sourceNeighborhood) C.neighborhoodPoint =
      C.smoothPoint by
    simpa only [neighborhoodPoint] using
      (ComplexPoint.map_asOpenPoint C.sourceNeighborhood C.smoothPoint _)]
  simpa only [smoothPoint] using
    (ComplexPoint.map_asOpenPoint
      (X := Y)
      (sourceSmoothLocus i)
      C.point C.point_mem_smoothLocus)

/-- The exact source chart, extended along the open embedding into the whole source. -/
def sourceProjectionChart :
    OpenPartialHomeomorph
      (ComplexPoint (Y))
      (Fin n → ℂ) :=
  C.neighborhoodProjectionChart.lift_openEmbedding
    C.neighborhoodToSourcePoint_isOpenEmbedding

/-- The selected component point is in the source of the extended exact chart. -/
lemma point_mem_sourceProjectionChart_source :
    C.point ∈ C.sourceProjectionChart.source := by
  rw [sourceProjectionChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨C.neighborhoodPoint, C.neighborhoodPoint_mem_projectionChart_source,
    C.neighborhoodToSourcePoint_neighborhoodPoint⟩

/-- The exactly normalized complex local class at the selected point of the whole component. -/
def sourceLocalOrientationClass :
    RelativeHomology ℚ (pointComplementPair C.point) (2 * n) :=
  localClassOfChart n C.sourceProjectionChart C.point
    C.point_mem_sourceProjectionChart_source

/-- The constructed component-local class generates the full top local homology group. -/
theorem span_sourceLocalOrientationClass_eq_top :
    Submodule.span ℚ {C.sourceLocalOrientationClass} = ⊤ := by
  let : T2Space
      (ComplexPoint (Y)) :=
    ProjectiveSpace.Presentation.complexPoint_t2Space
      (Classical.choice (closedEmbedding_isProjective i).nonempty_presentation)
  exact span_localClassOfChart_eq_top n C.sourceProjectionChart C.point
    C.point_mem_sourceProjectionChart_source

/-- The exactly normalized source-local orientation class is nonzero. -/
theorem sourceLocalOrientationClass_ne_zero :
    C.sourceLocalOrientationClass ≠ 0 := by
  let : T2Space
      (ComplexPoint (Y)) :=
    ProjectiveSpace.Presentation.complexPoint_t2Space
      (Classical.choice (closedEmbedding_isProjective i).nonempty_presentation)
  exact localClassOfChart_ne_zero n C.sourceProjectionChart C.point
    C.point_mem_sourceProjectionChart_source

end ClosedEmbeddingSeparateLocalCoordinates

namespace ComplexPoint

open AlgebraicTopology.Singular

/-- A family of rational top local homology classes on the smooth analytic locus of a reduced
cycle component. -/
abbrev ClosedEmbeddingComplexLocalClassFamily
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (n : ℕ) :=
  ∀ (z : ComplexPoint (Y)),
    z ∈ closedEmbeddingSmoothAnalyticLocus i →
      RelativeHomology ℚ (pointComplementPair z) n

/-- The canonical local complex orientation on a codimension-`p` closed subvariety. At each
smooth point it is built from exact algebraic étale coordinates of dimension `d - p`. -/
def closedEmbeddingComplexLocalOrientation
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) :
    ClosedEmbeddingComplexLocalClassFamily V i (2 * (d - p)) :=
  fun z hz ↦
    let C := closedEmbeddingLocalCoordinatesAt V i d p hi z hz
    (closedEmbeddingLocalCoordinatesAt_point V i d p hi z hz) ▸
      C.sourceLocalOrientationClass

/-- Every value of the constructed source orientation is a generator of top local homology. -/
theorem span_closedEmbeddingComplexLocalOrientation_eq_top
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint (Y))
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    Submodule.span ℚ {closedEmbeddingComplexLocalOrientation V i d p hi z hz} = ⊤ := by
  let C := closedEmbeddingLocalCoordinatesAt V i d p hi z hz
  unfold closedEmbeddingComplexLocalOrientation
  dsimp only
  exact span_singleton_transport_eq_top
    (fun w ↦ RelativeHomology ℚ (pointComplementPair w) (2 * (d - p)))
    (closedEmbeddingLocalCoordinatesAt_point V i d p hi z hz)
    C.sourceLocalOrientationClass C.span_sourceLocalOrientationClass_eq_top

/-- Every value of the constructed source orientation is nonzero. -/
theorem closedEmbeddingComplexLocalOrientation_ne_zero
    (V : SmoothProjectiveComplexVariety) {Y : Over (Spec ↧ℂ)} (i : Y ⟶ V.over)
    [IsIntegral Y.left] [IsClosedImmersion i.left] (d p : ℕ)
    [SmoothOfRelativeDimension d V.structureMap]
    (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)
    (z : ComplexPoint (Y))
    (hz : z ∈ closedEmbeddingSmoothAnalyticLocus i) :
    closedEmbeddingComplexLocalOrientation V i d p hi z hz ≠ 0 := by
  let C := closedEmbeddingLocalCoordinatesAt V i d p hi z hz
  unfold closedEmbeddingComplexLocalOrientation
  dsimp only
  exact transport_ne_zero
    (fun w ↦ RelativeHomology ℚ (pointComplementPair w) (2 * (d - p)))
    (closedEmbeddingLocalCoordinatesAt_point V i d p hi z hz)
    C.sourceLocalOrientationClass C.sourceLocalOrientationClass_ne_zero

end ComplexPoint
end AlgebraicGeometry
