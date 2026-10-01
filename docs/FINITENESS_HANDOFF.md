# Finite generation of `H₂(X^an, ℤ)`

## Status

Proved. For every smooth projective integral complex variety, the analytic space has finitely
generated integral singular homology in every degree. In particular,
`AlgebraicGeometry.ComplexPoint.hasFiniteSecondHomology` discharges the topological input used for
integral denominator clearing in the rational Lefschetz `(1, 1)` argument.

## Statement

The target predicate is defined in
[`Other/AlgebraicGeometry/IntegralDenominatorClearing.lean`](../Other/AlgebraicGeometry/IntegralDenominatorClearing.lean):

```lean
def HasFiniteSecondHomology (X : Over (Spec ↧ℂ)) : Prop :=
  Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
    (TopCat.of (ComplexPoint X))).homology 2)
```

The proved result is in
[`Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean`](../Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean):

```lean
theorem hasFiniteSecondHomology (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] : HasFiniteSecondHomology X
```

The same file proves finite generation in every degree and derives
`hasIntegralDenominatorClearing`.

## Proof route

1. The analytic space of a smooth projective variety is a compact Hausdorff real smooth manifold;
   see `Other/AlgebraicGeometry/ComplexPointRealManifold.lean` and the `ComplexPoint` projective
   compactness and Hausdorff modules.
2. `Other/Geometry/Manifold/TubularNeighbourhood.lean` realizes a compact smooth manifold as a
   retract of an open Euclidean neighbourhood.
3. `Other/AlgebraicTopology/RetractFiniteHomology.lean` proves finite generation of integral
   singular homology for such retracts.
4. `Other/Geometry/Manifold/CompactManifoldFiniteHomology.lean` packages those results for compact
   manifolds, and `ProjectiveFiniteHomology.lean` applies them to `ComplexPoint X`.

The proof introduces no project axiom. The build-enforced axiom check accepts only `propext`,
`Classical.choice`, and `Quot.sound`.

## Verification

```bash
lake build
lake build CheckLefschetzOneOneAxioms
python3 scripts/check_import_layers.py
git diff --check
```
