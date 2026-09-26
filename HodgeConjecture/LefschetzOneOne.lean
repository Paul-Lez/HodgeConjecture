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

public import HodgeConjecture.Statement

/-!
# Rational Lefschetz (1, 1): statement

This file is the auditable specification boundary for the result proved by the
Lefschetz `(1, 1)` development. It contains the proposition, not its proof.

The statement is the codimension-one rational Hodge conjecture for smooth projective integral
schemes over `ℂ`: every rational Hodge class of degree two lies in the rational span of
codimension-one algebraic cycle classes.

It deliberately does not assert the stronger integral identification with the image of the first
Chern class map from the Picard group, the reverse inclusion, or a result for compact Kähler
manifolds.

## Reference

* [P. Deligne, *The Hodge Conjecture*, §2(iii)]
  (https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- The rational Lefschetz `(1, 1)` statement proved in this repository.

For every smooth projective integral scheme `X` over `ℂ`, each rational degree-two Hodge class is
in the rational span of the classes of codimension-one algebraic subvarieties. -/
@[expose] public def LefschetzOneOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
    Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1
