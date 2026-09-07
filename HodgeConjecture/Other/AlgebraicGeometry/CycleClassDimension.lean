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
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClass
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Dimension bounds for algebraic cycle classes

A smooth complex scheme of relative dimension `d` has no points of coheight greater than `d`.
Consequently the span indexed by codimension-`p` components is zero when `d < p`.
-/

@[expose] public noncomputable section

open Order

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- A smooth complex `d`-fold has no algebraic points of codimension greater than `d`. -/
lemma no_cycleComponent_of_lt
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (d p : ℕ)
    [SmoothOfRelativeDimension d structureMap] (h : d < p) :
    IsEmpty {x : X // coheight x = p} := by
  constructor
  intro x
  exact (SmoothOfRelativeDimension.coheight_ne_of_lt
    (f := structureMap) (d := d) x.1 h) x.2

/-- The algebraic cycle-class span is zero above the dimension of a smooth complex variety. -/
lemma algebraicCycleClassSpan_eq_bot_of_lt
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (d p : ℕ)
    [SmoothOfRelativeDimension d structureMap] (h : d < p) :
    algebraicCycleClassSpan structureMap p = ⊥ := by
  rw [algebraicCycleClassSpan_of_ne_zero structureMap p (by lia)]
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    exact (SmoothOfRelativeDimension.coheight_ne_of_lt
      (f := structureMap) (d := d) x h hx).elim
  · exact bot_le

end AlgebraicGeometry.ComplexPoint
