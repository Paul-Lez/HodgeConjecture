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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.Purity

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

/-!
# Local dual classes on cycle components

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.Purity`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

@[simp]
lemma normalizedDual_apply_self (z : M) (hz : z ≠ 0) :
    (normalizedDual (R := R) z hz) z = (1 : R) :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one R hz)

@[simp]
lemma relativeCohomologyEquivDualHomology_normalizedRelativeCoclass {R : Type*} [Field R]
    {X : TopPair} {n : ℕ} (z : RelativeHomology R X n) (hz : z ≠ 0) :
    relativeCohomologyEquivDualHomology R X n (normalizedRelativeCoclass z hz) =
      normalizedDual z hz :=
  (relativeCohomologyEquivDualHomology R X n).apply_symm_apply _

@[simp]
lemma normalizedRelativeCoclass_pairing_self {R : Type*} [Field R] {X : TopPair} {n : ℕ}
    (z : RelativeHomology R X n) (hz : z ≠ 0) :
    relativeCohomologyEquivDualHomology R X n (normalizedRelativeCoclass z hz) z = (1 : R) := by
  rw [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass, normalizedDual_apply_self]

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero (n : ℕ) :
    standardComplexLocalClass n ≠ 0 := by
  rw [standardComplexLocalClass_ne_zero_iff]
  by_cases hn : n = 0
  · subst n
    exact standardLocalClass_zero_ne_zero
  · exact standardLocalClass_ne_zero_of_pos (n * 2) (Nat.mul_pos (Nat.pos_of_ne_zero hn) (by
      norm_num))

/-- Two one-dimensional vector spaces with specified normalized generators are canonically
linearly equivalent by sending the first generator to the second. -/
def linearEquivOfNormalizedGenerators
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    M ≃ₗ[R] N := by
  let f : M →ₗ[R] N :=
    (LinearMap.toSpanSingleton R N y).comp (normalizedDual x hx)
  let g : N →ₗ[R] M :=
    (LinearMap.toSpanSingleton R M x).comp (normalizedDual y hy)
  apply LinearEquiv.ofLinearMap f g
  · apply LinearMap.ext
    intro n
    obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R y).mp hyspan n
    simp [f, g, normalizedDual_apply_self]
  · apply LinearMap.ext
    intro m
    obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hxspan m
    simp [f, g, normalizedDual_apply_self]

end AlgebraicTopology.Singular

end

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- A normalized dual is unique when its distinguished vector generates the module. -/
lemma normalizedDual_unique {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤)
    (φ : Module.Dual R M) (hφ : φ z = 1) :
    φ = normalizedDual z hz := by
  ext y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp [hφ]

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

/-- The normalization condition characterizes the normalized coclass. -/
lemma normalizedRelativeCoclass_unique {z : RelativeHomology R X n} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) (β : RelativeCohomology R X n)
    (hβ : relativeCohomologyEquivDualHomology R X n β z = 1) :
    β = normalizedRelativeCoclass z hz :=
  (relativeCohomologyEquivDualHomology R X n).injective <| by
    rw [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass]
    exact normalizedDual_unique hz hzspan _ hβ

end Coclass

@[simp]
lemma linearEquivOfNormalizedGenerators_apply
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤)
    (z : M) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan z =
      (normalizedDual (R := R) x hx z : R) • y :=
  rfl

@[simp]
lemma linearEquivOfNormalizedGenerators_apply_generator
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan x = y := by
  change (normalizedDual (R := R) x hx x : R) • y = y
  rw [normalizedDual_apply_self, one_smul]

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

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

section

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

/-- The local homology class transported from the exact component chart is nonzero. -/
lemma neighborhoodLocalClass_ne_zero : C.neighborhoodLocalClass ≠ 0 := by
  let : IsAffine C.neighborhoodScheme.left :=
    C.componentNeighborhood_isAffine
  let : T2Space
      (ComplexPoint C.neighborhoodScheme) :=
    ComplexPoint.t2Space_of_isAffine C.neighborhoodScheme
  have hinjective : Function.Injective C.neighborhoodLocalHomologyMap :=
    (chartModelEmbedding_relativeHomologyMap_bijective
      n C.neighborhoodProjectionChart C.neighborhoodPoint
        C.neighborhoodPoint_mem_projectionChart_source).1
  intro hzero
  apply standardComplexLocalClass_ne_zero n
  apply hinjective
  simpa only [neighborhoodLocalClass, map_zero] using hzero

end

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
