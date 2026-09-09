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

public import Other.AlgebraicTopology.SingularCohomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Degree-zero singular cohomology of a path-connected space

The augmentation identifies degree-zero singular homology of a path-connected space with the
coefficient field.  Dualizing shows that the corresponding augmentation functional spans
degree-zero singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u}) [PathConnectedSpace X]

/-- The degree-zero singular-homology augmentation, regarded as a cohomology class. -/
def cohomologyUnitZero : Cohomology R X 0 :=
  (X.singularHomology₀ε (ModuleCat.of R R)).hom

/-- Every degree-zero singular cohomology class on a path-connected space is a scalar multiple
of the augmentation class. -/
lemma exists_smul_cohomologyUnitZero (φ : Cohomology R X 0) :
    ∃ r : R, r • cohomologyUnitZero R X = φ := by
  let e := (asIso (X.singularHomology₀ε (ModuleCat.of R R))).toLinearEquiv
  refine ⟨φ (e.symm 1), ?_⟩
  apply LinearMap.ext
  intro z
  have hz : (e z) • e.symm 1 = z := by
    apply e.injective
    simp
  change φ (e.symm 1) * e z = φ z
  rw [mul_comm]
  conv_rhs => rw [← hz]
  simp

/-- The degree-zero augmentation class spans singular cohomology of a path-connected space. -/
lemma span_cohomologyUnitZero_eq_top :
    Submodule.span R {cohomologyUnitZero R X} = ⊤ := by
  apply top_unique
  intro φ _
  rw [Submodule.mem_span_singleton]
  exact exists_smul_cohomologyUnitZero R X φ

/-- The degree-zero augmentation class of a path-connected space is nonzero. -/
lemma cohomologyUnitZero_ne_zero : cohomologyUnitZero R X ≠ 0 := by
  let e := (asIso (X.singularHomology₀ε (ModuleCat.of R R))).toLinearEquiv
  intro h
  have heval := LinearMap.congr_fun h (e.symm 1)
  change e (e.symm 1) = (0 : Module.Dual R (Homology R X 0)) (e.symm 1) at heval
  simp at heval

end AlgebraicTopology.Singular
