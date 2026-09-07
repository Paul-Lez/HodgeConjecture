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

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClassImage
public import HodgeConjecture.Other.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Exact images of cohomology with support

For a closed support, the additive supported Betti comparison identifies supported sheaf
cohomology with a rational vector space. Composing its inverse with the support-forgetting map
therefore gives a rational linear map. Its range is exactly `rationalCohomologySupportedOn`:
taking the rational span does not enlarge the support-forgetting image under these hypotheses.

This construction uses the inverse supported comparison followed by sheaf-theoretic forgetting
of support. It does not assert compatibility with forgetting support in singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

private lemma span_range_eq_range_of_addEquiv
    {A V W : Type*} [AddCommGroup A] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : A ≃+ V) (f : A →+ W) :
    Submodule.span ℚ (Set.range f) =
      LinearMap.range ((f.comp e.symm.toAddMonoidHom).toRatLinearMap) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨a, rfl⟩
    exact ⟨e a, by simp⟩
  · rintro y ⟨v, rfl⟩
    exact Submodule.subset_span ⟨e.symm v, rfl⟩

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (d : ℕ) [SmoothOfRelativeDimension d structureMap]

local instance supportedCohomologyImageTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

variable [T2Space (ComplexPoint X structureMap)]
    [∀ U : Opens (ComplexPoint X structureMap), ParacompactSpace U]

/-- Forget support after the inverse additive supported Betti comparison. The resulting map is
rational-linear because every additive map between rational vector spaces is rational-linear. -/
def forgetSupportFromSingular (Z : Set (ComplexPoint X structureMap))
    (hZ : IsClosed Z) (n : ℕ) :
    AlgebraicTopology.Singular.CohomologyWithSupport ℚ
        (TopCat.of (ComplexPoint X structureMap)) Z n →ₗ[ℚ]
      RationalCohomology structureMap (n : ℤ) :=
  AddMonoidHom.toRatLinearMap
    ((forgetSupport structureMap Z (n : ℤ)).comp
      (rationalCohomologyWithSupportAddEquivSingular structureMap d Z hZ n).symm.toAddMonoidHom)

/-- The supported subspace is the exact range of the support-forgetting map transported from
rational singular cohomology with support. -/
lemma rationalCohomologySupportedOn_eq_range (Z : Set (ComplexPoint X structureMap))
    (hZ : IsClosed Z) (n : ℕ) :
    rationalCohomologySupportedOn structureMap Z (n : ℤ) =
      LinearMap.range (forgetSupportFromSingular structureMap d Z hZ n) := by
  exact span_range_eq_range_of_addEquiv
    (rationalCohomologyWithSupportAddEquivSingular structureMap d Z hZ n)
    (forgetSupport structureMap Z (n : ℤ))

include d in
/-- Every member of the supported rational subspace has a supported preimage. -/
lemma mem_rationalCohomologySupportedOn_iff (Z : Set (ComplexPoint X structureMap))
    (hZ : IsClosed Z) (n : ℕ) (α : RationalCohomology structureMap (n : ℤ)) :
    α ∈ rationalCohomologySupportedOn structureMap Z (n : ℤ) ↔
      ∃ β, forgetSupport structureMap Z (n : ℤ) β = α := by
  rw [rationalCohomologySupportedOn_eq_range structureMap d Z hZ n]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨(rationalCohomologyWithSupportAddEquivSingular structureMap d Z hZ n).symm β, hβ⟩
  · rintro ⟨β, rfl⟩
    refine ⟨rationalCohomologyWithSupportAddEquivSingular structureMap d Z hZ n β, ?_⟩
    simp [forgetSupportFromSingular]

end AlgebraicGeometry.ComplexPoint
