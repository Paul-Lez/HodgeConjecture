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

/-!
# Generator properties of chart-local fundamental classes

A compressed complex chart is a homeomorphism from `ℂ^d` onto its open target.  On relative
homology, its map to the ambient point-complement pair factors as the isomorphism onto that target
followed by open-neighborhood excision.  Consequently the chart map is an isomorphism and the
transported standard complex local class generates the full ambient local homology group.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
variable (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
  (hx : x ∈ e.source)

lemma chartModelEmbedding_range_eq_target :
    Set.range (chartModelEmbedding d e x hx) = (chartModelEmbedding d e x hx).target := by
  rw [← Set.image_univ, ← chartModelEmbedding_source d e x hx]
  exact (chartModelEmbedding d e x hx).image_source_eq_target

/-- The compressed inverse chart as a homeomorphism onto its open target. -/
def chartModelTargetHomeomorph :
    (Fin d → ℂ) ≃ₜ (chartModelEmbedding d e x hx).target :=
  ((chartModelEmbedding d e x hx).isOpenEmbedding
      (chartModelEmbedding_source d e x hx)).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (chartModelEmbedding_range_eq_target d e x hx))

@[simp]
lemma chartModelTargetHomeomorph_apply_val (y : Fin d → ℂ) :
    (chartModelTargetHomeomorph d e x hx y).1 = chartModelEmbedding d e x hx y :=
  rfl

variable [T1Space M]

omit [T1Space M] in
/-- The oriented standard complex class generates its local homology in every complex
dimension. -/
lemma span_standardComplexLocalClass_eq_top_for_chart :
    Submodule.span ℚ {standardComplexLocalClass d} = ⊤ := by
  cases d with
  | zero => exact span_standardComplexLocalClass_zero_eq_top
  | succ n =>
      rw [span_standardComplexLocalClass_eq_top_iff]
      have hdeg : (n + 1) * 2 = n * 2 + 2 := by lia
      rw [hdeg]
      exact span_standardLocalClass_add_two_eq_top (n * 2)

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero_for_chart :
    standardComplexLocalClass d ≠ 0 := by
  rw [standardComplexLocalClass_ne_zero_iff]
  by_cases hd : d = 0
  · subst d
    exact standardLocalClass_zero_ne_zero
  · exact standardLocalClass_ne_zero_of_pos (d * 2)
      (Nat.mul_pos (Nat.pos_of_ne_zero hd) (by norm_num))

end AlgebraicTopology.Singular
