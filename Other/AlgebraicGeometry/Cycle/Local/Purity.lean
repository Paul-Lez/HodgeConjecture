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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Local.Purity
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity

/-!
# Purity, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicTopology.Singular
variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- The normalized dual of a homology generator generates the full dual space. -/
lemma span_normalizedDual_eq_top {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) :
    Submodule.span R {normalizedDual (R := R) z hz} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff R]
  intro φ
  refine ⟨φ z, ?_⟩
  ext y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp

end AlgebraicTopology.Singular
end

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicTopology.Singular
variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
section Coclass
variable {R : Type*} [Field R] {X : TopPair} {n : ℕ}

/-- The normalized coclass generates relative cohomology when its class generates relative
homology. -/
lemma span_normalizedRelativeCoclass_eq_top {z : RelativeHomology R X n} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) :
    Submodule.span R {normalizedRelativeCoclass z hz} = ⊤ := by
  have h := congrArg (Submodule.map (relativeCohomologyEquivDualHomology R X n).symm.toLinearMap)
    (span_normalizedDual_eq_top hz hzspan)
  rwa [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h

end Coclass
end AlgebraicTopology.Singular
end

@[expose] public noncomputable section
open CategoryTheory Topology
namespace AlgebraicTopology.Singular
variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- Sending the distinguished generator to the distinguished generator uniquely characterizes
the normalized equivalence. -/
lemma linearEquivOfNormalizedGenerators_unique
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤)
    (e : M ≃ₗ[R] N) (he : e x = y) :
    e = linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan := by
  ext z
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hxspan z
  simp [he]

end AlgebraicTopology.Singular
end
