# Unconditional Lefschetz (1, 1): status and remaining obligations

This is an incomplete proof development. The conditional statement
`HodgeConjecture → RationalLefschetzOneOne` is proved; the unconditional theorem is **not**.
A successful build of this branch does not establish the missing theorem.

## Goal

The target is `RationalLefschetzOneOne` in
[`Other/AlgebraicGeometry/LefschetzOneOne.lean`](../Other/AlgebraicGeometry/LefschetzOneOne.lean):

```lean
∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (α : H^2(X; ℚ)), α ∈ Hdg^1(X; ℚ) →
    ∃ D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left 1),
      rationalSheafCycleClassOnCycles { scheme := X.left, structureMap := X.hom } 1 D = α
```

Completion requires a theorem of this type without a `HodgeConjecture` hypothesis and without
comparison axioms, using the existing cohomology, Hodge-class, codimension-cycle and constructed
cycle-class definitions.

## PR split

Validation: `lake build`, the comparison axiom audit, and the import-layer check pass.

[PR9](https://github.com/Paul-Lez/HodgeConjecture/pull/9) contains the analytic construction,
denominator clearing, and the divisor–Chern comparison.
[PR230](https://github.com/Paul-Lez/HodgeConjecture/pull/230) isolates the adapted Oka dependency.
[PR228](https://github.com/Paul-Lez/HodgeConjecture/pull/228) is stacked on PR230 and adds the
project-specific proper-GAGA comparison and final theorem.

The divisor–Chern comparison takes an algebraic line bundle and its analytic identification as
inputs. The uniform comparison is proved without GAGA by
`hasDivisorClassOfCartierData` in `ChernRelativeFinalAssembly.lean`; its proof route is in
[DIVISOR_HANDOFF.md](DIVISOR_HANDOFF.md).

The comparison audit is `scripts/lefschetz_axiom_audit.lean`. PR228 also contains the GAGA audit
and a build-enforced axiom boundary for the final theorem.

## What is proved

Names are in `AlgebraicGeometry.ComplexPoint` unless indicated.

| Files | Result |
| --- | --- |
| `Other/AlgebraicGeometry/Cycle/SheafClass.lean`, `Other/AlgebraicGeometry/LefschetzOneOne.lean` | `algebraicCycleClassSpan_le_range_rationalSheafCycleClassOnCycles`; `HodgeConjecture.rationalLefschetzOneOne` and its `type_of%` copy. |
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
| [PR230 Oka port](https://github.com/Paul-Lez/HodgeConjecture/pull/230), [PR228 GAGA work](https://github.com/Paul-Lez/HodgeConjecture/pull/228) | Adapted Oka dependency; project-specific proper-GAGA comparison and final theorem. |
| `Other/LinearAlgebra/RationalDenominators.lean`, `Other/Algebra/Homology/RationalCochainDenominators.lean` | Denominator clearing for finitely generated abelian groups and for homology. |
| `Other/AlgebraicGeometry/ChernRelativeFinalAssembly.lean` | `hasDivisorClassOfCartierData`: the uniform divisor–Chern identity. |
| `Other/AlgebraicGeometry/LefschetzOneOneObligations.lean`, `Other/AlgebraicGeometry/LefschetzOneOneReduction.lean` | The reduction inputs as explicit propositions, and `RationalLefschetzOneOne.of_obligations`. |

## Reduction obligations and status

[`Other/AlgebraicGeometry/LefschetzOneOneObligations.lean`](../Other/AlgebraicGeometry/LefschetzOneOneObligations.lean)
states, for a single smooth projective integral complex variety `X`:

1. `HasIntegralDenominatorClearing X`: for every `α : H^2(X; ℚ)` there are `m ≠ 0`
   and `β : H^2(X; ℤ)` with `integralToRationalCohomology X 2 β = m • α`.
   **Discharged.** `Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean`
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
   `hasAlgebraicModel_of_analyticLineBundlesAlgebraize`. This obligation is scoped for
   downstream work in [PR228](https://github.com/Paul-Lez/HodgeConjecture/pull/228), using the
   isolated Oka port in [PR230](https://github.com/Paul-Lez/HodgeConjecture/pull/230).
3. `HasDivisorOfAlgebraicModel X`: such an `L` is represented by `D : codimensionCycleSubgroup X.left 1`
   with `sheafCycleClassOnCycles (ofOver X) 1 D = integralToRationalCohomology X 2
   E.firstChernClass`. The algebraic half is proved: every invertible algebraic sheaf is
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

Only obligation (2), algebraization by GAGA, remains on this branch. PR228 discharges it and proves
the final theorem.

## Verification

```bash
lake build
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
