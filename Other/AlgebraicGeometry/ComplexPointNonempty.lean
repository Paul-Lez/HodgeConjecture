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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Points

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Existence of a complex point

A scheme locally of finite type over `Spec ℂ` has a Jacobson underlying space, so a nonempty such
scheme carries a closed point. The Nullstellensatz identifies the residue field at a closed point
with `ℂ`, which turns that closed point into a `Spec ℂ`-point. An integral scheme is nonempty, so
`Nonempty (ComplexPoint X)` holds for every integral `X` locally of finite type over `Spec ℂ`, in
particular for every integral projective one.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint

open Point

/-- A closed point of a complex scheme locally of finite type carries a complex point above it. -/
lemma nonempty_of_isClosed_singleton (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {x : X.left} (hx : IsClosed {x}) : Nonempty (ComplexPoint X) :=
  let z := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
  ⟨Over.homMk z.1 z.2⟩

/-- A nonempty complex scheme locally of finite type has a complex point. -/
lemma nonempty_of_locallyOfFiniteType (X : Over (Spec ↧ℂ)) [Nonempty X.left]
    [LocallyOfFiniteType X.hom] : Nonempty (ComplexPoint X) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := X.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact nonempty_of_isClosed_singleton X hx

/-- An integral complex scheme locally of finite type has a complex point. This covers the
integral projective case, since a projective morphism is locally of finite type. -/
instance instNonemptyComplexPoint (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] : Nonempty (ComplexPoint X) :=
  nonempty_of_locallyOfFiniteType X

end AlgebraicGeometry.ComplexPoint
