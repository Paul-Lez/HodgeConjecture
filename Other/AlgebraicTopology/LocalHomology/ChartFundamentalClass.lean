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

public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.ComplexClass
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass

/-!
# ChartFundamentalClass, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicTopology.Singular
variable {M : Type} [TopologicalSpace M] (d : ℕ)
variable (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

lemma chartModelEmbedding_injective : Function.Injective (chartModelEmbedding d e x hx) :=
  (chartModelEmbedding d e x hx).isOpenEmbedding
    (chartModelEmbedding_source d e x hx) |>.injective

/-- The compressed inverse chart on the complements of the two distinguished points. -/
def puncturedChartModelEmbedding :
    ({0}ᶜ : Set (Fin d → ℂ)) → ({x}ᶜ : Set M) := fun y =>
  ⟨chartModelEmbedding d e x hx y, by
    intro h
    apply y.2
    apply chartModelEmbedding_injective d e x hx
    rw [chartModelEmbedding_zero d e x hx]
    exact h⟩

lemma continuous_puncturedChartModelEmbedding :
    Continuous (puncturedChartModelEmbedding d e x hx) :=
  Continuous.subtype_mk (((chartModelEmbedding d e x hx).isOpenEmbedding
    (chartModelEmbedding_source d e x hx)).continuous.comp continuous_subtype_val) _

/-- The map from the standard punctured complex affine space to the local pair at `x`. -/
def chartModelEmbeddingPair : standardComplexPuncturedPair d ⟶ pointComplementPair x :=
  TopPair.ofHom
    (TopCat.ofHom ⟨chartModelEmbedding d e x hx,
      (chartModelEmbedding d e x hx).isOpenEmbedding
        (chartModelEmbedding_source d e x hx) |>.continuous⟩)
    (TopCat.ofHom ⟨puncturedChartModelEmbedding d e x hx,
      continuous_puncturedChartModelEmbedding d e x hx⟩)
    (by ext y; rfl)

/-- The local homology class at `x`, normalized by the complex ordering of the chart. -/
def localClassOfChart : RelativeHomology ℚ (pointComplementPair x) (2 * d) :=
  relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)
    (standardComplexLocalClass ℚ d)

end AlgebraicTopology.Singular
end
