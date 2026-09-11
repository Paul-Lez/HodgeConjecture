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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Coniveau
public import HodgeConjecture.Lemmas.AlgebraicGeometry.HodgeFiltration
/-!
# The Hodge conjecture

This file states (but does not prove!) the Hodge conjecture.

The Hodge conjecture says that, for every nonsingular complex projective variety `X` and natural
number `p`, every rational Hodge class of degree `2p` on `X` is a rational linear combination of
classes of algebraic subvarieties of `X` of codimension `p`.

## TODO

The conjecture is currently stated using the rational span of the constructed component classes,
which are the values of the constructed cycle-class map on individual components. Once that map
is proved to kill principal-divisor relations, it should be descended to the rational Chow group.
After separately proving that its values are Hodge classes, the conjecture can equivalently be
restated as surjectivity onto the rational Hodge classes.

## References

[P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- Statement of the **Hodge conjecture**.

For every nonsingular complex projective variety `X` and natural number `p`, every rational Hodge
class of degree `2p` on `X` is a rational linear combination of classes of algebraic subvarieties of
`X` of codimension `p`. The algebraic subspace is `algebraicCycleClassSpan`, the span of the
component classes of `CycleComponentSheafClass` indexed by the points of codimension `p`. -/
@[expose] public def HodgeConjecture : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ),
    Hdg^p(ℚ; X) ≤ algebraicCycleClassSpan X p
