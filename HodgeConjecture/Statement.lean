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

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClass

/-!
# The Hodge conjecture

This file states (but does not prove!) the Hodge conjecture.

The Hodge conjecture says that, for every nonsingular complex projective variety `X` and natural
number `p`, every rational Hodge class of degree `2p` on `X` is a rational linear combination of
classes of algebraic subvarieties of `X` of codimension `p`.

## TODO

Currently we state the Hodge conjecture as an inclusion of the Hodge classes inside the
algebraic classes. we should instead write the explicit map out of the Chow group, which is valued
into rational Hodge classes and whose image is the algebraic classes, and restate the conjecture
as the surjectivity of this map.

## References

[P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open AlgebraicGeometry ComplexPoint

/-- Statement of the **Hodge conjecture**.

For every nonsingular complex projective variety `X` and natural number `p`, every rational Hodge
class of degree `2p` on `X` is a rational linear combination of classes of algebraic subvarieties of
`X` of codimension `p`. -/
@[expose] public def HodgeConjecture : Prop :=
  ∀ {X : Scheme} [IsIntegral X] (structureMap : X ⟶ Spec ↧ℂ) [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ),
    Hdg^p(ℚ; structureMap) ≤ algebraicCycleClassSpan structureMap p
