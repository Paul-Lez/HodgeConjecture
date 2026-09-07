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

public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentAnalyticEmbedding
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentPurity
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
public import FormalConjecturesForMathlib.AlgebraicGeometry.DimensionedSmoothProjective
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import FormalConjecturesForMathlib.AlgebraicGeometry.SingularCycleClass
public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassGenerator

/-!
# Purity for point supports

A complex manifold chart identifies local homology at a point with the punctured complex affine
model. The chart-local fundamental class therefore generates local homology, and its normalized
dual generates local cohomology.

For a codimension-`d` component of a smooth complex `d`-fold, the component has Krull dimension
zero. Its analytic support is consequently a singleton, so the chart-local coclass proves the
guarded singular purity proposition for that component. This is point-support purity only; it
does not assert the Thom--Gysin comparison needed for positive-dimensional supports.
-/

@[expose] public noncomputable section

open CategoryTheory Order Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

open AlgebraicTopology.Singular

/-- The ambient chart-local homology class at an analytic point. -/
def analyticPointLocalHomologyClass
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    RelativeHomology ℚ (pointComplementPair z) (2 * V.dimension) :=
  localClassOfChart V.dimension
    (ComplexPoint.localChart V.structureMap V.dimension z) z
    (ComplexPoint.mem_localChart_source V.structureMap V.dimension z)

/-- The ambient chart-local homology class is nonzero. -/
lemma analyticPointLocalHomologyClass_ne_zero
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    analyticPointLocalHomologyClass V z ≠ 0 := by
  let e := ComplexPoint.localChart V.structureMap V.dimension z
  let hz := ComplexPoint.mem_localChart_source V.structureMap V.dimension z
  let _ : T1Space V.analyticPoint := inferInstance
  have hinjective : Function.Injective
      (relativeHomologyMap ℚ (2 * V.dimension)
        (chartModelEmbeddingPair V.dimension e z hz)) :=
    (chartModelEmbedding_relativeHomologyMap_bijective V.dimension e z hz).1
  intro hzero
  apply standardComplexLocalClass_ne_zero V.dimension
  apply hinjective
  simpa only [analyticPointLocalHomologyClass, localClassOfChart, e, hz, map_zero] using hzero

/-- The ambient chart-local homology class generates local homology at the point. -/
lemma span_analyticPointLocalHomologyClass_eq_top
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    Submodule.span ℚ {analyticPointLocalHomologyClass V z} = ⊤ := by
  let _ : T1Space V.analyticPoint := inferInstance
  exact span_localClassOfChart_eq_top V.dimension
    (ComplexPoint.localChart V.structureMap V.dimension z) z
    (ComplexPoint.mem_localChart_source V.structureMap V.dimension z)

/-- The normalized local cohomology class dual to the chart-local fundamental class. -/
def analyticPointLocalCoclass
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    CohomologyWithSupport ℚ (TopCat.of V.analyticPoint) {z} (2 * V.dimension) :=
  normalizedDual (analyticPointLocalHomologyClass V z)
    (analyticPointLocalHomologyClass_ne_zero V z)

@[simp]
lemma analyticPointLocalCoclass_apply_localClass
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    analyticPointLocalCoclass V z (analyticPointLocalHomologyClass V z) = 1 := by
  exact normalizedDual_apply_self (analyticPointLocalHomologyClass V z)
    (analyticPointLocalHomologyClass_ne_zero V z)

/-- The normalized chart-local coclass generates rational cohomology supported at the point. -/
lemma span_analyticPointLocalCoclass_eq_top
    (V : DimensionedSmoothProjectiveComplexVariety) (z : V.analyticPoint) :
    Submodule.span ℚ {analyticPointLocalCoclass V z} = ⊤ := by
  exact span_normalizedDual_eq_top
    (analyticPointLocalHomologyClass_ne_zero V z)
    (span_analyticPointLocalHomologyClass_eq_top V z)

/-- A maximal-codimension component of a smooth complex variety has a singleton analytic
support. -/
lemma cycleComponentSupport_eq_singleton_of_coheight_eq_dimension
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : coheight x = V.dimension)
    (z : ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap)) :
    cycleComponentSupport V.toSmoothProjectiveComplexVariety x =
      {cycleComponentMap V.toSmoothProjectiveComplexVariety x z} := by
  have hdim : Order.krullDim (cycleComponent V.scheme x) = 0 := by
    simpa using orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
      (f := V.structureMap) (d := V.dimension) x hx
  let _ : Subsingleton (cycleComponent V.scheme x) := by
    constructor
    intro a b
    have hallMin : ∀ q : cycleComponent V.scheme x, IsMin q :=
      Order.krullDim_nonpos_iff_forall_isMin.mp hdim.le
    have htopLe (q : cycleComponent V.scheme x) : (⊤ : cycleComponent V.scheme x) ≤ q :=
      hallMin ⊤ le_top
    have hab : a ≤ b := le_top.trans (htopLe b)
    have hba : b ≤ a := le_top.trans (htopLe a)
    apply inseparable_iff_eq.mp
    rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
      ← Scheme.le_iff_specializes]
    exact ⟨hba, hab⟩
  have hpoints : Subsingleton
      (ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap)) := by
    constructor
    intro a b
    apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
    exact Subsingleton.elim a.underlying b.underlying
  rw [← range_cycleComponentMap]
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    rw [show w = z from hpoints.elim w z]
    exact Set.mem_singleton _
  · intro hy
    exact ⟨z, Set.mem_singleton_iff.mp hy.symm⟩

/-- Every maximal-codimension component has a generator of its singular cohomology with
support. -/
theorem exists_singularComponentSupportedGenerator_of_coheight_eq_dimension
    (V : DimensionedSmoothProjectiveComplexVariety) (x : V.scheme)
    (hx : coheight x = V.dimension) :
    ∃ β : RationalSingularComponentCohomologyWithSupport
        V.toSmoothProjectiveComplexVariety x (2 * V.dimension),
      IsSupportedCohomologyGenerator β := by
  obtain ⟨z, -⟩ := exists_cycleComponent_smooth_complexPoint
    V.toSmoothProjectiveComplexVariety x
  let y := cycleComponentMap V.toSmoothProjectiveComplexVariety x z
  have hsupport :
      cycleComponentSupport V.toSmoothProjectiveComplexVariety x = {y} :=
    cycleComponentSupport_eq_singleton_of_coheight_eq_dimension V x hx z
  change ∃ β : CohomologyWithSupport ℚ (TopCat.of V.analyticPoint)
      (cycleComponentSupport V.toSmoothProjectiveComplexVariety x) (2 * V.dimension),
    Submodule.span ℚ {β} = ⊤
  rw [hsupport]
  exact ⟨analyticPointLocalCoclass V y, span_analyticPointLocalCoclass_eq_top V y⟩

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
