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

public import HodgeConjecture.Lemmas.AlgebraicTopology.ChartLocalFundamentalClass
public import HodgeConjecture.Other.AlgebraicTopology.RelativeHomotopyInvariance

/-!
# Homotopy invariance of chart-local fundamental classes

This file records the direct consequence of relative homotopy invariance needed when comparing
the local classes transported by two complex coordinate charts.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
variable (d : ℕ)
variable (e e' : OpenPartialHomeomorph M (Fin d → ℂ))
variable (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)

/-- Two chart-local classes agree whenever their compressed chart maps are homotopic as maps of
point-complement pairs. -/
theorem localClassOfChart_eq_of_pairHomotopy
    (H : TopPair.Homotopy (chartModelEmbeddingPair d e x hx)
      (chartModelEmbeddingPair d e' x hx')) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  exact H.relativeHomologyMap_apply_eq (R := ℚ) (2 * d) (standardComplexLocalClass d)

end AlgebraicTopology.Singular
