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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentPurity
public import Other.AlgebraicGeometry.SingularCycleClass

import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.ChartLocalFundamentalClassGenerator

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

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsProjective X.hom] (d : ℕ)

/-- The ambient chart-local homology class at an analytic point. -/
def analyticPointLocalHomologyClass [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    RelativeHomology ℚ (pointComplementPair z) (2 * d) :=
  localClassOfChart d (ComplexPoint.localChart X d z) z
    (ComplexPoint.mem_localChart_source X d z)

/-- The ambient chart-local homology class is nonzero. -/
lemma analyticPointLocalHomologyClass_ne_zero [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    analyticPointLocalHomologyClass X d z ≠ 0 := by
  let e := ComplexPoint.localChart X d z
  let hz := ComplexPoint.mem_localChart_source X d z
  let : T1Space (ComplexPoint X) := inferInstance
  have hinjective : Function.Injective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e z hz)) :=
    (chartModelEmbedding_relativeHomologyMap_bijective d e z hz).1
  intro hzero
  apply standardComplexLocalClass_ne_zero d
  apply hinjective
  simpa only [analyticPointLocalHomologyClass, localClassOfChart, e, hz, map_zero] using hzero

/-- The ambient chart-local homology class generates local homology at the point. -/
lemma span_analyticPointLocalHomologyClass_eq_top [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    Submodule.span ℚ {analyticPointLocalHomologyClass X d z} = ⊤ := by
  let : T1Space (ComplexPoint X) := inferInstance
  exact span_localClassOfChart_eq_top d (ComplexPoint.localChart X d z) z
    (ComplexPoint.mem_localChart_source X d z)

/-- The normalized local cohomology class dual to the chart-local fundamental class. -/
def analyticPointLocalCoclass [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X)) {z} (2 * d) :=
  normalizedDual (analyticPointLocalHomologyClass X d z)
    (analyticPointLocalHomologyClass_ne_zero X d z)

@[simp]
lemma analyticPointLocalCoclass_apply_localClass [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    analyticPointLocalCoclass X d z
        (analyticPointLocalHomologyClass X d z) = 1 :=
  normalizedDual_apply_self (analyticPointLocalHomologyClass X d z)
    (analyticPointLocalHomologyClass_ne_zero X d z)

/-- The normalized chart-local coclass generates rational cohomology supported at the point. -/
lemma span_analyticPointLocalCoclass_eq_top [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    Submodule.span ℚ {analyticPointLocalCoclass X d z} = ⊤ :=
  span_normalizedDual_eq_top
    (analyticPointLocalHomologyClass_ne_zero X d z)
    (span_analyticPointLocalHomologyClass_eq_top X d z)

/-- A maximal-codimension component of a smooth complex variety has a singleton analytic
support. -/
lemma cycleComponentSupport_eq_singleton_of_coheight_eq_dimension [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (hx : coheight x = d)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :
    cycleComponentSupport X x = {cycleComponentMap X x z} := by
  have hdim : Order.krullDim (cycleComponent X.left x) = 0 := by
    simpa using orderKrullDim_cycleComponent_eq_zero_of_coheight_eq_dimension
      (f := X.hom) (d := d) x hx
  let : Subsingleton (cycleComponent X.left x) := by
    constructor
    intro a b
    have hallMin : ∀ q : cycleComponent X.left x, IsMin q :=
      Order.krullDim_nonpos_iff_forall_isMin.mp hdim.le
    have htopLe (q : cycleComponent X.left x) : (⊤ : cycleComponent X.left x) ≤ q :=
      hallMin ⊤ le_top
    have hab : a ≤ b := le_top.trans (htopLe b)
    have hba : b ≤ a := le_top.trans (htopLe a)
    apply inseparable_iff_eq.mp
    rw [inseparable_iff_specializes_and, ← Scheme.le_iff_specializes,
      ← Scheme.le_iff_specializes]
    exact ⟨hba, hab⟩
  have hpoints : Subsingleton
      (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) := by
    let : LocallyOfFiniteType (Over.mk (cycleComponentι X.left x ≫ X.hom)).hom :=
      inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left x ≫ X.hom))
    exact ⟨fun a b ↦ ComplexPoint.underlying_injective_of_locallyOfFiniteType
      (Subsingleton.elim (α := cycleComponent X.left x) a.underlying b.underlying)⟩
  rw [← range_cycleComponentMap]
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    rw [show w = z from hpoints.elim w z]
    exact Set.mem_singleton _
  · exact fun hy ↦ ⟨z, Set.mem_singleton_iff.mp hy.symm⟩

/-- Every maximal-codimension component has a generator of its singular cohomology with
support. -/
theorem exists_singularComponentSupportedGenerator_of_coheight_eq_dimension [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (hx : coheight x = d) :
    ∃ β : RationalSingularComponentCohomologyWithSupport X x (2 * d),
      IsSupportedCohomologyGenerator β := by
  obtain ⟨z, -⟩ := exists_cycleComponent_smooth_complexPoint X x
  let y := cycleComponentMap X x z
  have hsupport : cycleComponentSupport X x = {y} :=
    cycleComponentSupport_eq_singleton_of_coheight_eq_dimension X d x hx z
  change ∃ β : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d),
    Submodule.span ℚ {β} = ⊤
  rw [hsupport]
  exact ⟨analyticPointLocalCoclass X d y,
    span_analyticPointLocalCoclass_eq_top X d y⟩

end AlgebraicGeometry.ComplexPoint
