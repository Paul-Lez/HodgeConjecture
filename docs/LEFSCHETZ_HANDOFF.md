# Rational Lefschetz (1, 1)

This development proves the unconditional theorem `lefschetzOneOne : LefschetzOneOne` in
`Other/AlgebraicGeometry/GAGAProper.lean`. Its stronger concrete helper
`rationalLefschetzOneOne : RationalLefschetzOneOne` produces an explicit rational divisor.
The proofs contain no `sorry` or added axiom.

## Goal

The repository's target is `LefschetzOneOne` in
[`HodgeConjecture/LefschetzOneOne.lean`](../HodgeConjecture/LefschetzOneOne.lean):

```lean
∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
  Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1
```

The proof first establishes the stronger concrete formulation `RationalLefschetzOneOne` in
[`Other/AlgebraicGeometry/LefschetzOneOneStatement.lean`](../Other/AlgebraicGeometry/LefschetzOneOneStatement.lean):

```lean
∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (α : H^2(X; ℚ)), α ∈ Hdg^1(X; ℚ) →
    ∃ D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left 1),
      rationalSheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 D = α
```

`RationalLefschetzOneOne.to_lefschetzOneOne` maps the explicit rational cycle into
`algebraicCycleClassSpan`. Thus the final theorem has the canonical target type without a
`HodgeConjecture` hypothesis or comparison axiom.

The canonical proposition has a statement-only module. The explicit-cycle proposition has a
separate proof-interface module. The import checks enforce both boundaries and restate both
contracts.

## PR split

[PR9](https://github.com/Paul-Lez/HodgeConjecture/pull/9) contains the analytic construction,
denominator clearing, and the divisor–Chern comparison. [PR41](https://github.com/Paul-Lez/HodgeConjecture/pull/41)
contains the earlier GAGA development and is stacked on PR9. The completed proper-GAGA comparison
and final theorem are in `GAGAProper.lean`.

The divisor–Chern comparison takes an algebraic line bundle and its analytic identification as
inputs. The uniform comparison is proved without GAGA by
`hasDivisorClassOfCartierData` in `ChernRelativeFinalAssembly.lean`; its proof route is in
[DIVISOR_HANDOFF.md](DIVISOR_HANDOFF.md).

The comparison audit is `scripts/lefschetz_axiom_audit.lean`; the GAGA audit is
`scripts/gaga_axiom_audit.lean` on PR41. Run `lake build` before either audit.

## What is proved

Names are in `AlgebraicGeometry.ComplexPoint` unless indicated.

| Files | Result |
| --- | --- |
| `HodgeConjecture/LefschetzOneOne.lean`, `Other/AlgebraicGeometry/LefschetzOneOneStatement.lean` | Canonical rational statement and stronger explicit-cycle statement. |
| `Other/AlgebraicGeometry/Cycle/SheafClass.lean`, `LefschetzOneOne.lean` | `rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan`; `HodgeConjecture.rationalLefschetzOneOne` and its `type_of%` copy. |
| `Other/Geometry/Manifold/HolomorphicLogarithm.lean` | Local holomorphic logarithms; local integer kernel of `exp(2πiz)`. |
| `Other/AlgebraicGeometry/HolomorphicExponential.lean`, `HolomorphicExponentialSequence.lean` | `holomorphicExponentialSequence_shortExact`: `0 → ℤ → 𝒪 → 𝒪ˣ → 0` on the analytic space. |
| `Other/AlgebraicGeometry/HolomorphicFirstChernClass.lean`, `HolomorphicFirstChernClassExactness.lean` | The connecting map `Ext¹(ℤ, 𝒪ˣ) → Ext²(ℤ, ℤ)` and `exists_holomorphicFirstChernClass_iff`. |
| `Other/AlgebraicGeometry/HolomorphicZeroForms.lean`, `HolomorphicHodgeProjection.lean` | The projection to `H²(𝒪)` kills `F¹`; `hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero`. |
| `Other/AlgebraicGeometry/AnalyticSheafCohomologyExt.lean` | `analyticSheafCohomologyEquivExt`, natural in coefficient maps. |
| `Other/AlgebraicGeometry/IntegralCohomology.lean`, `HolomorphicIntegralHodgeClass.lean` | `sheafCohomologyEquivExt`, `integralToRationalCohomology`, `exists_holomorphicFirstChernClass_of_integral_hodgeClass`. |
| `Other/CategoryTheory/Abelian/ExtOneRepresentative.lean` | `Abelian.Ext.exists_shortExact`. |
| `Other/AlgebraicTopology/SheafExtensionCocycle.lean`, `SheafExtensionLocalLifts.lean` | Local lifts through a sheaf epimorphism and their cocycles. |
| `Other/AlgebraicGeometry/HolomorphicUnitExtensionHodgeClass.lean` | `exists_holomorphicUnitExtension_of_integral_hodgeClass`: an extension `E` with `E.firstChernClass = α`. |
| `Other/AlgebraicGeometry/HolomorphicUnitTransition.lean`, `HolomorphicLineBundleOfExtension.lean` | Holomorphic unit transition functions and `E.lineBundleCore`. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleSections.lean`, `HolomorphicLineBundleModule.lean` | The sheaf of holomorphic sections and `E.sectionSheafOfModules`. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleCoordinates.lean`, `HolomorphicLineBundleInvertible.lean` | Local coordinate isomorphisms; `E.sectionSheafOfModules_isInvertible`. |
| `Other/AlgebraicGeometry/RegularFunctionsHolomorphic.lean` | `regularToHolomorphicSheaf`, the structure-sheaf map over `underlyingContinuousMap`. |
| `Other/AlgebraicGeometry/AnalytificationModules.lean` | `moduleAnalytification`, its adjunction and `moduleAnalytificationUnitIso`. |
| `Other/AlgebraicGeometry/HolomorphicAnalytificationLocalIso.lean`, `GAGAProper.lean` | Comparison with Oka's canonical analytification; coherent and line-bundle algebraization; unconditional `rationalLefschetzOneOne` and `lefschetzOneOne`. |
| `Other/LinearAlgebra/RationalDenominators.lean`, `Other/Algebra/Homology/RationalCochainDenominators.lean` | Denominator clearing for finitely generated abelian groups and for homology. |
| `Other/AlgebraicGeometry/ChernRelativeFinalAssembly.lean` | `hasDivisorClassOfCartierData`: the uniform divisor–Chern identity. |
| `Other/AlgebraicGeometry/LefschetzOneOneObligations.lean`, `LefschetzOneOneReduction.lean` | The remaining obligations as explicit propositions, and `RationalLefschetzOneOne.of_obligations`. |

## Discharged obligations

[`Other/AlgebraicGeometry/LefschetzOneOneObligations.lean`](../Other/AlgebraicGeometry/LefschetzOneOneObligations.lean)
states, for a single smooth projective integral complex variety `X`:

1. `HasIntegralDenominatorClearing X`: for every `α : H^2(X; ℚ)` there are `m ≠ 0`
   and `β : H^2(X; ℤ)` with `integralToRationalCohomology X 2 β = m • α`.
   **Reduced to geometry.** `Other/AlgebraicGeometry/IntegralDenominatorClearing.lean` proves
   `hasIntegralDenominatorClearing_of_hasFiniteGoodCover`: it suffices that the analytic space
   has a finite good cover (`HasFiniteGoodCover X`: finitely many opens whose nonempty finite
   intersections are contractible, `AlgebraicTopology.Singular.FiniteGoodCover`). The proof
   goes through
   - the integral Betti comparison `integralCohomologyEquivOrdinarySingularCohomology`
     (`BettiScalarComparison.lean`; the singular-cochain development is now generic over a
     commutative ring: `Other/Algebra/Homology/LinearDual.lean`,
     `Other/AlgebraicTopology/SimplicialCochainExtension.lean`, `SingularExcisionScalar.lean`,
     and the generalised `SingularCochain*`/`SingularSubdivisionCochainSheaf` files);
   - its naturality in the coefficient ring (`SimplicialCochainCoefficientChange.lean`,
     `SingularCochainCoefficientChange.lean`, `HypercohomologyFlasqueMapNaturality.lean`,
     `BettiScalarNaturality.lean`: `scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange`);
   - finite generation of integral singular homology from a finite good cover
     (`FiniteGoodCoverNerveHomology.lean`, transported to the `ModuleCat ℤ` chain model in
     `IntegralSingularHomologyFinite.lean`);
   - the elementary denominator-clearing theorem on simplicial cochains
     (`SimplicialCochainDenominators.lean`, `SSet.exists_integer_multiple_of_finite_homology`:
     a rational cocycle that is integer-valued on integral cycles is cohomologous to an integral
     cocycle, using divisibility of `ℚ/ℤ`; finite generation bounds the denominators).

   **Obligation (1) is discharged.** `Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean`
   proves `hasIntegralDenominatorClearing X` for every smooth projective integral complex
   variety: the analytic space is a compact Hausdorff real `C^∞` manifold
   (`ComplexPointRealManifold.lean`), a compact manifold embeds in a Euclidean space as a retract
   of an open neighbourhood (`Other/Geometry/Manifold/TubularNeighbourhood.lean`, proved through a
   uniform reach estimate for nearest points, with `ChartDifferential.lean` and
   `NormalReach.lean`), and compact neighbourhood retracts have finitely generated integral
   singular homology (`Other/AlgebraicTopology/RetractFiniteHomology.lean`, via a finite good cover
   of a union of balls). Hence `RationalLefschetzOneOne.of_divisor`: the theorem follows from
   `HasDivisorOfUnitExtension` alone.
2. `HasAlgebraicModel X`: for every `E : HolomorphicUnitExtension X (dim X.left)` there is an
   invertible `L : X.left.Modules` with `(moduleAnalytification X (dim X.left)).obj L ≅
   E.sectionSheafOfModules`. This is projective GAGA for line bundles. Its extension-free
   form `AnalyticLineBundlesAlgebraize X` (every invertible analytic sheaf is the
   analytification of an invertible algebraic one) implies it by
   `hasAlgebraicModel_of_analyticLineBundlesAlgebraize`.
   **Obligation (2) is discharged.** `GAGAProper.lean` proves
   `analyticLineBundlesAlgebraize` by identifying the repository's holomorphic space with Oka's
   analytification, applying proper GAGA to coherent sheaves, and reflecting rank one through
   faithfully flat stalk maps.
3. `HasDivisorOfAlgebraicModel X`: such an `L` is represented by `D : codimensionCycleSubgroup X.left 1`
   with `sheafCycleClassOnCycles (ofOver X) 1 D = integralToRationalCohomology X 2
   E.firstChernClass`. Since `D` is existential, sign and `2πi` normalisation conventions do not
   affect the statement. The algebraic half is proved: every invertible algebraic sheaf is
   represented by Cartier data (a cover with local equations) whose divisor is a
   `codimensionCycleSubgroup X.left 1` (`DivisorOfRationalSection.lean`,
   `InvertibleSheafRationalSection.lean`, `CartierDataOfTrivializingCover.lean`), and
   `hasDivisorOfAlgebraicModel_of_divisorClass` (`DivisorObligations.lean`) reduces the obligation
   to `HasDivisorClassOfSomeCartierData X`: the constructed class of the divisor of some Cartier
   datum representing `L` is the rational first Chern class of `E`.
   **Obligation (3) is discharged.** `hasDivisorClassOfCartierData` in
   `ChernRelativeFinalAssembly.lean` proves the stronger uniform comparison.
   Apply `hasDivisorClassOfSomeCartierData_of_cartierData`, then
   `hasDivisorOfAlgebraicModel_of_divisorClass`. See
   [DIVISOR_HANDOFF.md](DIVISOR_HANDOFF.md).

`RationalLefschetzOneOne.of_obligations` proves the target from (1) and
`HasDivisorOfUnitExtension`, which follows from (2) and (3) by
`hasDivisorOfUnitExtension_of_algebraicModel`. Since (1) is now a theorem,
`RationalLefschetzOneOne.of_divisor` (`LefschetzOneOneFiniteHomology.lean`) proves it from
`HasDivisorOfUnitExtension` alone, i.e. from (2) and (3). The bookkeeping proved there is: rational Hodge
classes are stable under integer scaling, integral Hodge classes lift to unit-sheaf extensions,
and the resulting integral divisor is divided by the denominator.

All three obligations are discharged. `GAGACoherentReduction.lean` reduces line-bundle GAGA to
coherent-sheaf algebraization and faithful flatness of analytification on stalks;
`GAGAProper.lean` supplies both through Oka's proper GAGA development and proves the final
`rationalLefschetzOneOne` and `lefschetzOneOne` theorems.

## Verification

```bash
lake build
python3 scripts/check_import_layers.py
lake env lean scripts/lefschetz_axiom_audit.lean
git diff --check
```

Practical Lean notes from this development:

- Use `type_of%`, not `typeof%`.
- Name local topology instances uniquely across files.
- Many sheaf, module and concrete-category aliases need explicit types or application lemmas;
  the local `backward.isDefEq.respectTransparency` settings are deliberate. In particular
  `codimensionCycleSubgroup X.left 1` and `CodimensionCycle (ofOver X).scheme 1` agree only after
  unfolding, so proofs manipulating both use that option.
- Distinguish `Scheme.Modules` from the generic `SheafOfModules` category, and specify the module
  universe (`.{0}`) where inferred right-adjoint instances otherwise generalise too far.
