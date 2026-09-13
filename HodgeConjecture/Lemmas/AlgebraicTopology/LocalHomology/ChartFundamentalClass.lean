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

/-!
# Local fundamental classes from complex charts

This file transports the explicit standard class of `ℂ^d` to a point in a topological space with
a complex coordinate chart. An open ball around the coordinate of the point is chosen inside the
chart target. Mathlib's radial homeomorphism compresses all of `ℂ^d` into that ball, after which
the inverse chart gives an open embedding into the space. The induced map of punctured pairs sends
the standard complex local class to local homology at the point.

The construction fixes both the support and the complex orientation. It requires only a
chart and a proof that the point lies in its source; no fundamental or orientation class is passed
as data.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M] (d : ℕ)

/-- The pair `(M, M ∖ {x})` used for local homology at `x`. -/
abbrev pointComplementPair (x : M) : TopPair :=
  TopPair.ofSubset (X := TopCat.of M) ({x}ᶜ : Set M)

variable (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

/-- A positive radius whose coordinate ball is contained in the chart target. -/
def chartRadius : ℝ :=
  Classical.choose (Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx))

lemma chartRadius_pos : 0 < chartRadius d e x hx :=
  (Classical.choose_spec
    (Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx))).1

lemma ball_chartRadius_subset :
    Metric.ball (e x) (chartRadius d e x hx) ⊆ e.target :=
  (Classical.choose_spec
    (Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx))).2

/-- The open embedding that compresses `ℂ^d` into a coordinate ball and then applies the inverse
chart. -/
def chartModelEmbedding : OpenPartialHomeomorph (Fin d → ℂ) M :=
  (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).trans e.symm

lemma chartModelEmbedding_source :
    (chartModelEmbedding d e x hx).source = Set.univ := by
  ext y
  simp only [chartModelEmbedding, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.univBall_source, Set.mem_inter_iff, Set.mem_univ,
    true_and, Set.mem_preimage, OpenPartialHomeomorph.symm_source]
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  apply ball_chartRadius_subset d e x hx
  rw [← OpenPartialHomeomorph.univBall_target (e x) (chartRadius_pos d e x hx)]
  exact (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).map_source (by simp)

@[simp]
lemma chartModelEmbedding_zero : chartModelEmbedding d e x hx 0 = x := by
  rw [chartModelEmbedding, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.univBall_apply_zero]
  exact e.left_inv hx

end AlgebraicTopology.Singular
