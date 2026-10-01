# Handoff: proper GAGA for line bundles

## Status

The projective GAGA input to rational Lefschetz `(1, 1)` is complete.
`Other/AlgebraicGeometry/GAGAProper.lean` proves
`analyticCoherentSheavesAlgebraize` and `analyticLineBundlesAlgebraize` for smooth projective
integral complex schemes. `Other/AlgebraicGeometry/LefschetzOneOne.lean` applies the latter to
prove the unconditional theorem `lefschetzOneOne`.

The completed route uses Oka's proper-GAGA development. Earlier experiments with a direct
Serre-presentation proof were not part of the final proof closure and have been removed.

## Exact line-bundle target

[`Other/AlgebraicGeometry/GAGAStatement.lean`](../Other/AlgebraicGeometry/GAGAStatement.lean)
defines:

```lean
def AnalyticLineBundlesAlgebraize : Prop :=
  ∀ M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)),
    TauCeti.SheafOfModules.IsInvertible M →
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ M)
```

The completed theorem is:

```lean
theorem analyticLineBundlesAlgebraize
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    AnalyticLineBundlesAlgebraize X
```

This is the existence statement required by the Lefschetz reduction: the algebraic model is
invertible, and its analytification is isomorphic to the given invertible analytic module sheaf.

## Proof route

All unqualified names below are in `AlgebraicGeometry.ComplexPoint`.

1. `HolomorphicAnalyticSpace.lean` packages the repository's holomorphic locally ringed space as
   Oka's `ComplexAnalytic.AnalyticSpace` and proves coherence of its structure sheaf.
2. `HolomorphicAnalytificationComparison.lean` constructs `holomorphicAnalytificationπ`, the
   comparison from this analytic space to the original scheme, and `comparisonToCanonical`, the
   map to Oka's canonical analytification.
3. `HolomorphicAnalytificationCharts.lean` proves compatibility with the local étale coordinate
   charts. `HolomorphicAnalytificationLocalIso.lean` uses those charts to prove
   `comparisonToCanonical_isLocalIso`.
4. `HolomorphicAnalytificationComparison.lean` combines that local-isomorphism result with the
   bijection on points to obtain `holomorphicAnalytificationπ_isAnalytification`. Oka's local GAGA
   theorem then gives `faithfullyFlat_stalkMap_holomorphicAnalytificationπ`.
5. `GAGAProper.lean` applies Oka's `gaga₃_proper` to the canonical analytification and transports
   the resulting coherent algebraic model across the comparison. This proves
   `analyticCoherentSheavesAlgebraize` for the repository's holomorphic model.
6. `GAGACoherentReduction.lean` observes that an invertible analytic sheaf is coherent, applies
   coherent algebraization, and reflects rank one through the faithfully flat stalk maps. This
   proves `analyticLineBundlesAlgebraize`.
7. `GAGAtoLefschetz.lean` converts line-bundle algebraization into `HasAlgebraicModel`.
8. `LefschetzOneOne.lean` supplies `analyticLineBundlesAlgebraize` to the fixed-variety reduction
   and maps the resulting cycle into `algebraicCycleClassSpan`.

The Oka theorems used at the decisive step are imported through
`Other/Oka/Analytification/GAGA/Proper/Equivalence.lean` and
`Other/Oka/Analytification/GAGA/SheafAnalytification.lean`.

## Boundaries

- `GAGAStatement.lean` states line-bundle algebraization without importing its proof.
- `GAGACoherentStatement.lean` separately states the coherent-sheaf existence property.
- `GAGAProper.lean` contains the proper-GAGA proof, but not the final Lefschetz declarations.
- `LefschetzOneOne.lean` contains one declaration: the direct statement and proof of the final
  theorem.
- The result proves rational codimension-one algebraicity. It does not assert the stronger
  integral Picard/Chern-class formulation of the classical Lefschetz `(1, 1)` theorem.

## PR provenance

[PR230](https://github.com/Paul-Lez/HodgeConjecture/pull/230) isolates the adapted Oka dependency
and enforces its upstream revision and import boundary.
[PR228](https://github.com/Paul-Lez/HodgeConjecture/pull/228) contains the project-specific
proper-GAGA comparison and final Lefschetz proof. It is stacked on PR230 and
[PR9](https://github.com/Paul-Lez/HodgeConjecture/pull/9), which supplies the Lefschetz reduction
and the divisor–Chern comparison.

## Verification

```bash
lake build Other.AlgebraicGeometry.GAGAProper
lake build Other.AlgebraicGeometry.LefschetzOneOne
lake build CheckLefschetzOneOneAxioms
lake build
lake exe lint-style HodgeConjecture Other HodgeGuide
python3 scripts/check_import_layers.py
git diff --check
```

The enforced axiom check covers the final theorem and its GAGA and divisor-comparison spines. It
accepts only `propext`, `Classical.choice`, and `Quot.sound`.
