/-
Copyright 2026 Rado Kirov and The Formal Conjectures Authors.

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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Homotopy.LocallyContractible

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothEquidimensional
import Mathlib.Analysis.Convex.Contractible

/-!
# Local contractibility of projective analytifications

Finite-dimensional complex vector spaces have bases of convex balls. Hence they are strongly
locally contractible, and this property transfers through manifold charts. Applying this to the
analytic charts of a smooth projective complex variety proves strong local contractibility of its
analytification.

The general charted-space argument is adapted from Rado Kirov's
[`sphere-six-complex` pull request #103](https://github.com/deancureton/sphere-six-complex/pull/103)
and its merged
[`SphereSixComplex/Topology/ManifoldLocallyContractible.lean`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/ManifoldLocallyContractible.lean),
used under that repository's Apache-2.0 license. The proof has been ported to this project's
Lean and Mathlib versions rather than importing the upstream repository.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Set Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

/-- A real normed space is strongly locally contractible: open balls form a neighbourhood basis
and are convex. -/
theorem normedSpace_stronglyLocallyContractibleSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E :=
  .of_bases (fun _ ↦ Metric.nhds_basis_ball)
    (fun x r hr ↦ Convex.contractibleSpace (_root_.convex_ball x r)
      ⟨x, Metric.mem_ball_self hr⟩)

/-- Strong local contractibility can be checked on open neighbourhoods. -/
theorem stronglyLocallyContractibleSpace_of_open_nhds
    {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace X := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hUopen, hxU, hU⟩ := h x
  have hemb : IsOpenEmbedding ((↑) : U → X) := hUopen.isOpenEmbedding_subtypeVal
  have hmap : 𝓝 x = Filter.map ((↑) : U → X) (𝓝 (⟨x, hxU⟩ : U)) :=
    (hemb.map_nhds_eq ⟨x, hxU⟩).symm
  have hbasis :=
    (StronglyLocallyContractibleSpace.contractible_basis (X := U) ⟨x, hxU⟩).map
      ((↑) : U → X)
  rw [← hmap] at hbasis
  refine hbasis.to_hasBasis' ?_ ?_
  · rintro s ⟨hs, hcontr⟩
    refine ⟨((↑) : U → X) '' s, ⟨?_, ?_⟩, le_rfl⟩
    · rw [hmap]
      exact Filter.image_mem_map hs
    · exact (hemb.toIsEmbedding.homeomorphImage s).contractibleSpace_iff.mp hcontr
  · rintro s ⟨hs, -⟩
    exact hs

/-- A charted space over a strongly locally contractible model is strongly locally
contractible. -/
theorem ChartedSpace.stronglyLocallyContractibleSpace
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] : StronglyLocallyContractibleSpace M := by
  refine stronglyLocallyContractibleSpace_of_open_nhds fun x ↦ ?_
  refine ⟨(chartAt H x).source, (chartAt H x).open_source, mem_chart_source H x, ?_⟩
  have htarget : StronglyLocallyContractibleSpace ((chartAt H x).target) :=
    (chartAt H x).open_target.stronglyLocallyContractibleSpace
  exact
    ((chartAt H x).toHomeomorphSourceTarget).isOpenEmbedding.stronglyLocallyContractibleSpace

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- The analytification of a smooth projective complex variety is strongly locally
contractible. -/
theorem stronglyLocallyContractibleSpace [IsIntegral X] [Smooth structureMap] :
    StronglyLocallyContractibleSpace (ComplexPoint (Over.mk structureMap)) := by
  let : StronglyLocallyContractibleSpace (Fin (dim X) → ℂ) :=
    normedSpace_stronglyLocallyContractibleSpace
  exact ChartedSpace.stronglyLocallyContractibleSpace
    (H := Fin (dim X) → ℂ) (M := ComplexPoint (Over.mk structureMap))

/-- The analytification of a smooth projective complex variety is locally contractible. -/
theorem locallyContractibleSpace [IsIntegral X] [Smooth structureMap] :
    LocallyContractibleSpace (ComplexPoint (Over.mk structureMap)) := by
  let : StronglyLocallyContractibleSpace (ComplexPoint (Over.mk structureMap)) :=
    stronglyLocallyContractibleSpace structureMap
  exact StronglyLocallyContractibleSpace.locallyContractible

end AlgebraicGeometry.ComplexPoint
