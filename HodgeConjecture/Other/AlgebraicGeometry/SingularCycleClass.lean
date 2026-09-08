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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Other.AlgebraicTopology.SingularCohomology
public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic

/-!
# Algebraic cycle-class lines in singular cohomology

Let `Z` be an irreducible algebraic subset of complex codimension `p`. Its fundamental class is
the image of a generator of `H^{2p}(X, X ∖ Z; ℚ)` in ordinary singular cohomology. Rather than
choosing a generator and thereby introducing an arbitrary sign or rational scalar, this file
takes the span of the images of all generators. This gives the cycle-class line intrinsically.

The assertion that the supported group is one-dimensional is cohomological purity. It is not an
assumption in these definitions: a class counts as a generator only when the displayed span is
the whole supported group. A later purity theorem can prove that every irreducible component has
such generators and identify them with locally normalized fundamental classes.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- The analytic complex-point space as an object of `TopCat`. -/
abbrev AnalyticPointTopCat
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] : TopCat :=
  TopCat.of (ComplexPoint X structureMap)

/-- Singular cohomology of the analytic complex-point space. -/
abbrev RationalSingularCohomology
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (n : ℕ) :=
  Cohomology ℚ (AnalyticPointTopCat structureMap) n

/-- Singular cohomology supported on an irreducible algebraic component. -/
abbrev RationalSingularComponentCohomologyWithSupport
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (x : X) (n : ℕ) :=
  CohomologyWithSupport ℚ (AnalyticPointTopCat structureMap)
    (cycleComponentSupport structureMap x) n

/-- A class generates its supported cohomology group over `ℚ`. This is a property, not an
assumed purity theorem. -/
def IsSupportedCohomologyGenerator {X : Scheme} {structureMap : X ⟶ Spec ↧ℂ}
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    {x : X} {n : ℕ}
    (β : RationalSingularComponentCohomologyWithSupport structureMap x n) : Prop :=
  Submodule.span ℚ {β} = ⊤

/-- The degree-`2p` singular cycle-class line of an irreducible codimension-`p` component.
It is the span of the images of all generators of the corresponding supported cohomology group.
This definition is independent of the choice and scaling of a fundamental class. -/
def singularComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ) (x : X) :
    Submodule ℚ (RationalSingularCohomology structureMap (2 * p)) :=
  Submodule.span ℚ {α | ∃ β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p),
    IsSupportedCohomologyGenerator β ∧
      forgetSupport ℚ (AnalyticPointTopCat structureMap)
          (cycleComponentSupport structureMap x) (2 * p) β = α}

/-- The rational span of the guarded singular component-class lines in codimension `p`.
Cohomological purity and local normalization are still required before this can be identified
with the usual topological cycle-class span in positive codimension. -/
def rationalSingularAlgebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (RationalSingularCohomology structureMap (2 * p)) :=
  ⨆ (x : X) (_ : coheight x = p), singularComponentCycleClassLine structureMap p x

/-- The forgotten class of a supported generator belongs to its component cycle-class line. -/
lemma forgetSupport_mem_singularComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) (x : X)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    forgetSupport ℚ (AnalyticPointTopCat structureMap)
        (cycleComponentSupport structureMap x) (2 * p) β ∈
      singularComponentCycleClassLine structureMap p x := by
  apply Submodule.subset_span
  exact ⟨β, hβ, rfl⟩

/-- Any supported generator computes the same intrinsic component line. -/
lemma singularComponentCycleClassLine_eq_span
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) (x : X)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    singularComponentCycleClassLine structureMap p x =
      Submodule.span ℚ
        {forgetSupport ℚ (AnalyticPointTopCat structureMap)
          (cycleComponentSupport structureMap x) (2 * p) β} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro α hα
    obtain ⟨γ, -, rfl⟩ := hα
    let f := forgetSupport ℚ (AnalyticPointTopCat structureMap)
      (cycleComponentSupport structureMap x) (2 * p)
    have hγ : γ ∈ Submodule.span ℚ {β} := by
      rw [hβ]
      exact Submodule.mem_top
    change f γ ∈ Submodule.span ℚ {f β}
    rw [← Set.image_singleton, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hγ
  · apply Submodule.span_mono
    intro α hα
    rw [Set.mem_singleton_iff] at hα
    subst α
    exact ⟨β, hβ, rfl⟩

/-- The forgotten class of a supported generator on a codimension-`p` component belongs to the
full algebraic cycle-class span. -/
lemma forgetSupport_mem_rationalSingularAlgebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) (x : X)
    (hx : coheight x = p)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    forgetSupport ℚ (AnalyticPointTopCat structureMap)
        (cycleComponentSupport structureMap x) (2 * p) β ∈
      rationalSingularAlgebraicCycleClassSpan structureMap p := by
  apply (le_iSup (fun y : X => ⨆ hy : coheight y = p,
    singularComponentCycleClassLine structureMap p y) x)
  apply (le_iSup (fun _ : coheight x = p => singularComponentCycleClassLine structureMap p x) hx)
  exact forgetSupport_mem_singularComponentCycleClassLine structureMap p x β hβ

end AlgebraicGeometry.ComplexPoint
