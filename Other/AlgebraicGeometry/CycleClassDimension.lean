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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Coniveau

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Dimension bounds for algebraic cycle classes

A smooth complex scheme of relative dimension `d` has no points of coheight greater than `d`.
Consequently the span indexed by codimension-`p` components is zero when `d < p`.
-/

@[expose] public noncomputable section

open CategoryTheory Order

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- A smooth complex `d`-fold has no algebraic points of codimension greater than `d`. -/
lemma no_cycleComponent_of_lt
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom] (h : d < p) :
    IsEmpty {x : X.left // coheight x = p} :=
  ⟨fun x ↦ SmoothOfRelativeDimension.coheight_ne_of_lt (f := X.hom) (d := d) x.1 h x.2⟩

/-- The algebraic cycle-class span is zero above the dimension of a smooth complex variety. -/
lemma algebraicCycleClassSpan_eq_bot_of_lt
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom] (h : d < p) :
    algebraicCycleClassSpan X p = ⊥ := by
  rw [algebraicCycleClassSpan_of_ne_zero X p (by lia)]
  refine le_antisymm (iSup_le fun x ↦ iSup_le fun hx ↦ ?_) bot_le
  exact (SmoothOfRelativeDimension.coheight_ne_of_lt (f := X.hom) (d := d) x h hx).elim

end AlgebraicGeometry.ComplexPoint
