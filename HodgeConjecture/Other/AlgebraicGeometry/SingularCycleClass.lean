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

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSupport
public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCohomology
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Algebraic cycle-class lines in singular cohomology

For a closed support `Z`, this file takes the image of
`H^{2p}(X, X ∖ Z; ℚ) → H^{2p}(X; ℚ)`. The component cycle-class line is the span of the
classes that generate this image. This is the same image-generator condition used in the
constant-sheaf construction. It does not choose a generator or a normalization.

Cohomological purity identifies the supported image of an irreducible codimension-`p` component
with its usual fundamental-class line. A generator of the entire supported cohomology group
is sufficient to generate the image, and the lemmas below retain that useful special case.
The definitions themselves only test generators of the image.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

/-- The analytic complex-point space as an object of `TopCat`. -/
abbrev AnalyticPointTopCat
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] : TopCat :=
  TopCat.of (ComplexPoint X structureMap)

/-- Singular cohomology of the analytic complex-point space. -/
abbrev RationalSingularCohomology
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (n : ℕ) :=
  Cohomology ℚ (AnalyticPointTopCat structureMap) n

/-- Singular cohomology supported on an irreducible algebraic component. -/
abbrev RationalSingularComponentCohomologyWithSupport
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (x : X) (n : ℕ) :=
  CohomologyWithSupport ℚ (AnalyticPointTopCat structureMap)
    (cycleComponentSupport structureMap x) n

/-- A class generates its supported cohomology group over `ℚ`. This is a property, not an
assumed purity theorem. -/
def IsSupportedCohomologyGenerator {X : Scheme} {structureMap : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    {x : X} {n : ℕ}
    (β : RationalSingularComponentCohomologyWithSupport structureMap x n) : Prop :=
  Submodule.span ℚ {β} = ⊤

/-- The image in ordinary rational singular cohomology of classes supported on `Z`. -/
def rationalSingularCohomologySupportedOn
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (Z : Set (ComplexPoint X structureMap)) (n : ℕ) :
    Submodule ℚ (RationalSingularCohomology structureMap n) :=
  LinearMap.range (forgetSupport ℚ (AnalyticPointTopCat structureMap) Z n)

/-- A rational singular class generates the image supported on one component in degree `2p`. -/
def IsRationalSingularComponentCycleClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X) (α : RationalSingularCohomology structureMap (2 * p)) : Prop :=
  Submodule.span ℚ {α} =
    rationalSingularCohomologySupportedOn structureMap (cycleComponentSupport structureMap x) (2 * p)

/-- The degree-`2p` singular cycle-class line is the span of all generators of the component's
supported image. This definition is independent of the choice and scaling of a generator. -/
def singularComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X) :
    Submodule ℚ (RationalSingularCohomology structureMap (2 * p)) :=
  Submodule.span ℚ {α | IsRationalSingularComponentCycleClass structureMap p x α}

/-- The rational span of the component-class lines in codimension `p`. Cohomological purity
identifies each supported image with its usual fundamental-class line. -/
def rationalSingularAlgebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (RationalSingularCohomology structureMap (2 * p)) :=
  ⨆ (x : X) (_ : coheight x = p), singularComponentCycleClassLine structureMap p x

/-- A generator of the supported cohomology group maps to a generator of its image. -/
lemma isRationalSingularComponentCycleClass_forgetSupport
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    IsRationalSingularComponentCycleClass structureMap p x
      (forgetSupport ℚ (AnalyticPointTopCat structureMap)
        (cycleComponentSupport structureMap x) (2 * p) β) := by
  let f := forgetSupport ℚ (AnalyticPointTopCat structureMap)
    (cycleComponentSupport structureMap x) (2 * p)
  change Submodule.span ℚ {f β} = LinearMap.range f
  change Submodule.span ℚ {β} = ⊤ at hβ
  rw [← Set.image_singleton, ← Submodule.map_span, hβ, Submodule.map_top]

/-- Any generator of the supported image computes the same intrinsic component line. -/
lemma singularComponentCycleClassLine_eq_span_of_isRationalSingularComponentCycleClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (α : RationalSingularCohomology structureMap (2 * p))
    (hα : IsRationalSingularComponentCycleClass structureMap p x α) :
    singularComponentCycleClassLine structureMap p x = Submodule.span ℚ {α} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro γ hγ
    have hγmem : γ ∈ Submodule.span ℚ {γ} := Submodule.subset_span (Set.mem_singleton γ)
    change Submodule.span ℚ {γ} = _ at hγ
    change Submodule.span ℚ {α} = _ at hα
    rw [hγ, ← hα] at hγmem
    exact hγmem
  · apply Submodule.span_mono
    intro γ hγ
    rw [Set.mem_singleton_iff] at hγ
    subst γ
    exact hα

/-- The forgotten class of a supported generator belongs to its component cycle-class line. -/
lemma forgetSupport_mem_singularComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    forgetSupport ℚ (AnalyticPointTopCat structureMap)
        (cycleComponentSupport structureMap x) (2 * p) β ∈
      singularComponentCycleClassLine structureMap p x := by
  apply Submodule.subset_span
  exact isRationalSingularComponentCycleClass_forgetSupport structureMap p x β hβ

/-- Any generator of the entire supported group computes the intrinsic component line. -/
lemma singularComponentCycleClassLine_eq_span
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (β : RationalSingularComponentCohomologyWithSupport structureMap x (2 * p))
    (hβ : IsSupportedCohomologyGenerator β) :
    singularComponentCycleClassLine structureMap p x =
      Submodule.span ℚ
        {forgetSupport ℚ (AnalyticPointTopCat structureMap)
          (cycleComponentSupport structureMap x) (2 * p) β} := by
  apply singularComponentCycleClassLine_eq_span_of_isRationalSingularComponentCycleClass
  exact isRationalSingularComponentCycleClass_forgetSupport structureMap p x β hβ

/-- The forgotten class of a supported generator on a codimension-`p` component belongs to the
full algebraic cycle-class span. -/
lemma forgetSupport_mem_rationalSingularAlgebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
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
