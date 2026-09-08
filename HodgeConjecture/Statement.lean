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
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# The Hodge conjecture

The Hodge conjecture says that every rational Hodge class of degree `2p` on a nonsingular
complex projective variety is a rational linear combination of classes of algebraic subvarieties
of codimension `p`.

The proposition is stated intrinsically: rational Hodge classes must lie in the span of the
cycle-class lines of irreducible algebraic subvarieties. It does not choose a map out of the
rational Chow group. Construction of cycle-class maps, compatibility with rational equivalence,
and purity are useful independent results, but are not extra data in the conjecture itself.

This file names an open proposition. It does not assert or prove that proposition.

*Reference:*
- [P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open AlgebraicGeometry ComplexPoint

/-- The Hodge conjecture: on every nonsingular complex projective variety, every rational Hodge
class of degree `2p` is a rational linear combination of classes of codimension-`p` algebraic
subvarieties.

This definition is a proposition, not a proof. It is deliberately untagged because the current
problem metadata treats a sorry-free definition as a solved declaration. -/
@[expose] public def HodgeConjecture : Prop :=
  ∀ {X : Scheme} [IsIntegral X] (structureMap : X ⟶ Spec ↧ℂ) [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (d : ℕ)
    [SmoothOfRelativeDimension d structureMap] (p : ℕ),
    hodgeClasses ℚ structureMap d p ≤ algebraicCycleClassSpan structureMap p
