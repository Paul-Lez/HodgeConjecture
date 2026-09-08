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

public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Basic
public import HodgeConjecture.Other.AlgebraicTopology.SingularCohomologyZero
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Degree-zero singular cohomology detects path components

For a nonempty space, the augmentation class spans degree-zero singular cohomology exactly when
the space is path connected.  The reverse implication uses the standard description of zeroth
singular homology as the coproduct of one copy of the coefficient field for each path component.

For a locally path connected space this is also equivalent to connectedness.  These converses
isolate the remaining global connectedness input in applications to projective analytifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u}) [Nonempty X]

/-- If the augmentation class spans degree-zero singular cohomology, the space has only one path
component. -/
theorem pathConnectedSpace_of_span_cohomologyUnitZero_eq_top
    (hspan : Submodule.span R {cohomologyUnitZero R X} = ⊤) :
    PathConnectedSpace X := by
  classical
  rw [pathConnectedSpace_iff_zerothHomotopy]
  refine ⟨inferInstance, ⟨fun a b ↦ ?_⟩⟩
  by_contra hab
  let M : ModuleCat.{u} R := ModuleCat.of R R
  let e := X.singularHomology₀Iso M
  let χ : (∐ fun _ : ZerothHomotopy X ↦ M) ⟶ M :=
    Sigma.desc (fun i ↦ if i = a then 𝟙 M else 0)
  let φ : Cohomology R X 0 := (e.hom ≫ χ).hom
  have hφ : φ ∈ Submodule.span R {cohomologyUnitZero R X} := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hφ
  obtain ⟨r, hr⟩ := hφ
  let va : ↑(∐ fun _ : ZerothHomotopy X ↦ M) :=
    (Sigma.ι (fun _ : ZerothHomotopy X ↦ M) a).hom 1
  let vb : ↑(∐ fun _ : ZerothHomotopy X ↦ M) :=
    (Sigma.ι (fun _ : ZerothHomotopy X ↦ M) b).hom 1
  let za : Homology R X 0 := e.inv.hom va
  let zb : Homology R X 0 := e.inv.hom vb
  have hua : cohomologyUnitZero R X za = 1 := by
    change (X.singularHomology₀ε M).hom za = 1
    calc
      (X.singularHomology₀ε M).hom za =
          (e.hom ≫ Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 M)).hom za := by
            rw [X.singularHomology₀Iso_sigma_desc_id M]
      _ = 1 := by
        simp only [ConcreteCategory.comp_apply, za, Iso.inv_hom_id_apply, va]
        rw [← ConcreteCategory.comp_apply, Sigma.ι_desc]
        simp
  have hub : cohomologyUnitZero R X zb = 1 := by
    change (X.singularHomology₀ε M).hom zb = 1
    calc
      (X.singularHomology₀ε M).hom zb =
          (e.hom ≫ Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 M)).hom zb := by
            rw [X.singularHomology₀Iso_sigma_desc_id M]
      _ = 1 := by
        simp only [ConcreteCategory.comp_apply, zb, Iso.inv_hom_id_apply, vb]
        rw [← ConcreteCategory.comp_apply, Sigma.ι_desc]
        simp
  have hφa : φ za = 1 := by
    simp [φ, χ, za, va, e]
  have hφb : φ zb = 0 := by
    simp [φ, χ, zb, vb, e, Ne.symm hab]
  have hra := LinearMap.congr_fun hr za
  have hrb := LinearMap.congr_fun hr zb
  simp only [LinearMap.smul_apply, hua, hφa, smul_eq_mul, mul_one] at hra
  simp only [LinearMap.smul_apply, hub, hφb, smul_eq_mul, mul_one] at hrb
  exact one_ne_zero (hra.symm.trans hrb)

/-- On a nonempty space, the degree-zero augmentation class spans singular cohomology exactly
when the space is path connected. -/
theorem pathConnectedSpace_iff_span_cohomologyUnitZero_eq_top :
    PathConnectedSpace X ↔
      Submodule.span R {cohomologyUnitZero R X} = ⊤ := by
  constructor
  · intro h
    let _ : PathConnectedSpace X := h
    exact span_cohomologyUnitZero_eq_top R X
  · exact pathConnectedSpace_of_span_cohomologyUnitZero_eq_top R X

/-- On a nonempty locally path connected space, the augmentation class spans degree-zero
singular cohomology exactly when the space is connected. -/
theorem connectedSpace_iff_span_cohomologyUnitZero_eq_top
    [LocallyPathConnectedSpace X] :
    ConnectedSpace X ↔
      Submodule.span R {cohomologyUnitZero R X} = ⊤ := by
  rw [← pathConnectedSpace_iff_span_cohomologyUnitZero_eq_top R X,
    pathConnectedSpace_iff_connectedSpace]

end AlgebraicTopology.Singular
