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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationSecondCountable
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Clopen subsets of integral projective analytifications

A clopen subset of a complex manifold has a locally constant, hence holomorphic,
characteristic function.  For an integral projective complex variety, any such characteristic
function which is the analytification of a global regular function is constant.  This reduces
the remaining connectedness theorem to an analytic-to-algebraic comparison for holomorphic
idempotents.

The distinction is essential: the local path-connectedness argument in
[sphere-six-complex PR #192](https://github.com/deancureton/sphere-six-complex/pull/192) does not
prove global connectedness.  That pull request obtains global connectedness only from explicit
paths in its particular quotient space.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped Manifold

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

/-- The complex-valued characteristic function of a clopen subset of the analytification. -/
def clopenCharacteristic (V : DimensionedSmoothProjectiveComplexVariety)
    (S : Set V.analyticPoint) (hS : IsClopen S) : V.analyticPoint → ℂ :=
  LocallyConstant.charFn ℂ hS

/-- The characteristic function of a clopen subset is locally constant. -/
lemma clopenCharacteristic_isLocallyConstant
    (V : DimensionedSmoothProjectiveComplexVariety)
    (S : Set V.analyticPoint) (hS : IsClopen S) :
    IsLocallyConstant (clopenCharacteristic V S hS) :=
  (LocallyConstant.charFn ℂ hS).isLocallyConstant

/-- The characteristic function of a clopen subset of a complex manifold is holomorphic. -/
lemma clopenCharacteristic_mdifferentiable
    (V : DimensionedSmoothProjectiveComplexVariety)
    (S : Set V.analyticPoint) (hS : IsClopen S) :
    let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
      ComplexPoint.analyticChartedSpace V.structureMap V.dimension
    MDifferentiable
      (I := modelWithCornersSelf ℂ (Fin V.dimension → ℂ))
      (I' := modelWithCornersSelf ℂ ℂ)
      (clopenCharacteristic V S hS) := by
  dsimp only
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    ComplexPoint.analyticChartedSpace V.structureMap V.dimension
  intro x
  exact (mdifferentiableAt_const (c := clopenCharacteristic V S hS x)).congr_of_eventuallyEq
    ((clopenCharacteristic_isLocallyConstant V S hS).eventually_eq x)

/-- A clopen characteristic function which is represented by a global regular function is
constant.  The missing input for global connectedness is that every holomorphic idempotent on
the analytification has such an algebraic representative. -/
theorem clopen_eq_empty_or_univ_of_eq_evaluate
    (V : DimensionedSmoothProjectiveComplexVariety)
    (S : Set V.analyticPoint) (hS : IsClopen S)
    (s : Γ(V.scheme, ⊤))
    (hs : ∀ z, ComplexPoint.evaluate ⊤ s z = clopenCharacteristic V S hS z) :
    S = ∅ ∨ S = Set.univ := by
  by_cases hSne : S.Nonempty
  · right
    obtain ⟨x, hx⟩ := hSne
    let _ : Field Γ(V.scheme, ⊤) :=
      (isField_of_universallyClosed ℂ V.structureMap).toField
    let ev : Γ(V.scheme, ⊤) →+* ℂ :=
      (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp x.1.appTop.hom
    have hev_injective : Function.Injective ev := RingHom.injective ev
    have hs_one : s = 1 := by
      apply hev_injective
      have hx_one : clopenCharacteristic V S hS x = 1 :=
        (LocallyConstant.charFn_eq_one ℂ x hS).2 hx
      have hevs : ev s = 1 := by
        rw [show ev s = ComplexPoint.evaluate ⊤ s x by
          simp only [ev, RingHom.coe_comp, Function.comp_apply,
            ComplexPoint.evaluate_top_eq_appTop], hs x, hx_one]
      simpa only [map_one] using hevs
    apply Set.eq_univ_of_forall
    intro y
    apply (LocallyConstant.charFn_eq_one ℂ y hS).1
    change clopenCharacteristic V S hS y = 1
    rw [← hs y, hs_one, ComplexPoint.evaluate_top_eq_appTop, map_one, map_one]
  · left
    exact Set.not_nonempty_iff_eq_empty.mp hSne

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
