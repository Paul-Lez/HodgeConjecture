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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativePairExcision
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
public import Other.AlgebraicTopology.LocalHomology.ChartFundamentalClass

/-!
# ChartFundamentalClassGenerator, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicTopology.Singular
variable {M : Type} [TopologicalSpace M]
variable (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
  (hx : x ∈ e.source)
variable [T1Space M]

lemma chartModelEmbedding_mem_target : x ∈ (chartModelEmbedding d e x hx).target := by
  have hzero : chartModelEmbedding d e x hx 0 ∈ (chartModelEmbedding d e x hx).target :=
    (chartModelEmbedding d e x hx).map_source
      (by rw [chartModelEmbedding_source]; trivial)
  simpa only [chartModelEmbedding_zero] using hzero

/-- The target homeomorphism restricted away from the distinguished points. -/
def puncturedChartModelTargetHomeomorph :
    ({0}ᶜ : Set (Fin d → ℂ)) ≃ₜ
      {y : (chartModelEmbedding d e x hx).target | y.1 ≠ x} :=
  (chartModelTargetHomeomorph d e x hx).subtype fun y ↦ by
    change y ≠ 0 ↔ chartModelEmbedding d e x hx y ≠ x
    refine not_congr ⟨fun hzero ↦ ?_, fun hxy ↦ chartModelEmbedding_injective d e x hx ?_⟩
    · rw [hzero, chartModelEmbedding_zero d e x hx]
    · rw [chartModelEmbedding_zero d e x hx]
      exact hxy

/-- The pair isomorphism from the standard complex local model to the open chart target. -/
def standardComplexChartTargetPairIso :
    puncturedPair ℂ d ≅
      neighborhoodPointComplementPair (chartModelEmbedding d e x hx).target x where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨chartModelTargetHomeomorph d e x hx,
      (chartModelTargetHomeomorph d e x hx).continuous⟩)
    (TopCat.ofHom ⟨puncturedChartModelTargetHomeomorph d e x hx,
      (puncturedChartModelTargetHomeomorph d e x hx).continuous⟩)
    (by ext y; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(chartModelTargetHomeomorph d e x hx).symm,
      (chartModelTargetHomeomorph d e x hx).symm.continuous⟩)
    (TopCat.ofHom ⟨(puncturedChartModelTargetHomeomorph d e x hx).symm,
      (puncturedChartModelTargetHomeomorph d e x hx).symm.continuous⟩)
    (by ext y; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      exact (puncturedChartModelTargetHomeomorph d e x hx).left_inv y
    · ext y
      exact (chartModelTargetHomeomorph d e x hx).left_inv y
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      exact (puncturedChartModelTargetHomeomorph d e x hx).right_inv y
    · ext y
      exact (chartModelTargetHomeomorph d e x hx).right_inv y

/-- The original chart map factors through its open target and the neighborhood inclusion. -/
lemma standardComplexChartTargetPairIso_hom_comp_neighborhoodMap :
    (standardComplexChartTargetPairIso d e x hx).hom ≫
        neighborhoodPointComplementPairMap (chartModelEmbedding d e x hx).target x =
      chartModelEmbeddingPair d e x hx := rfl

/-- The compressed chart induces a bijection from standard complex local homology to ambient
local homology. -/
theorem chartModelEmbedding_relativeHomologyMap_bijective :
    Function.Bijective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) := by
  have htarget : Function.Bijective
      (relativeHomologyMap ℚ (2 * d)
        (standardComplexChartTargetPairIso d e x hx).hom) := by
    exact (ConcreteCategory.isIso_iff_bijective ((relativeHomologyFunctor ℚ (2 * d)).map
      (standardComplexChartTargetPairIso d e x hx).hom)).mp inferInstance
  have hexcision := neighborhoodPointComplement_relativeHomologyMap_bijective
    (chartModelEmbedding d e x hx).target x (chartModelEmbedding d e x hx).open_target
      (chartModelEmbedding_mem_target d e x hx) (2 * d)
  rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d e x hx,
    relativeHomologyMap_comp]
  exact hexcision.comp htarget

/-- The compressed chart is surjective on local homology. -/
theorem chartModelEmbedding_relativeHomologyMap_surjective :
    Function.Surjective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) :=
  (chartModelEmbedding_relativeHomologyMap_bijective d e x hx).2

/-- The class transported through a complex chart generates the full ambient rational local
homology group. -/
theorem span_localClassOfChart_eq_top :
    Submodule.span ℚ {localClassOfChart d e x hx} = ⊤ := by
  let f := relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)
  calc
    Submodule.span ℚ {localClassOfChart d e x hx} =
        (Submodule.span ℚ {standardComplexLocalClass ℚ d}).map f := by
      rw [Submodule.map_span]
      simp only [Set.image_singleton]
      rfl
    _ = (⊤ : Submodule ℚ _).map f := by
      rw [span_standardComplexLocalClass_eq_top_for_chart]
    _ = LinearMap.range f := Submodule.map_top f
    _ = ⊤ := LinearMap.range_eq_top.mpr
      (chartModelEmbedding_relativeHomologyMap_surjective d e x hx)

/-- The exactly normalized local class transported through a chart is nonzero. -/
theorem localClassOfChart_ne_zero :
    localClassOfChart d e x hx ≠ 0 := by
  have hinjective : Function.Injective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) :=
    (chartModelEmbedding_relativeHomologyMap_bijective d e x hx).1
  intro hzero
  apply standardComplexLocalClass_ne_zero_for_chart d
  apply hinjective
  simpa only [localClassOfChart, hzero, map_zero]

end AlgebraicTopology.Singular
end
