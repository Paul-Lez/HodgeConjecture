# Unconditional Lefschetz (1, 1): status and remaining obligations

This is an incomplete proof development. The conditional statement
`HodgeConjecture → RationalLefschetzOneOne` is proved; the unconditional theorem is **not**.
A successful build of this branch does not establish the missing theorem.

## Goal

The target is `RationalLefschetzOneOne` in
[`Other/AlgebraicGeometry/LefschetzOneOne.lean`](../Other/AlgebraicGeometry/LefschetzOneOne.lean):

```lean
∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (α : FieldCohomology ℚ X 2), α ∈ Hdg^1(ℚ; X) →
    ∃ D : TensorProduct ℤ ℚ (CodimensionCycle X.left 1),
      rationalSheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D = α
```

Completion requires a theorem of this type without a `HodgeConjecture` hypothesis and without
comparison axioms, using the existing cohomology, Hodge-class, codimension-cycle and constructed
cycle-class definitions.

## Integration status

The development is now on the bundled `X : Over (Spec ↧ℂ)` interface of #4, with hypotheses on
`X.left` and `X.hom`. All modules are imported by `Other.lean`; `lake build` passes; and
`lake env lean scripts/lefschetz_axiom_audit.lean` reports only `propext`, `Classical.choice`
and `Quot.sound` for every audited declaration. No `sorry`, `admit` or `axiom` is used.

## What is proved

Names are in `AlgebraicGeometry.ComplexPoint` unless indicated.

| Files | Result |
| --- | --- |
| `Other/AlgebraicGeometry/SheafCycleClass.lean`, `LefschetzOneOne.lean` | `algebraicCycleClassSpan_le_range_rationalSheafCycleClassOnCycles`; `HodgeConjecture.rationalLefschetzOneOne` and its `type_of%` copy. |
| `Other/Geometry/Manifold/HolomorphicLogarithm.lean` | Local holomorphic logarithms; local integer kernel of `exp(2πiz)`. |
| `Other/AlgebraicGeometry/HolomorphicExponential.lean`, `HolomorphicExponentialSequence.lean` | `holomorphicExponentialSequence_shortExact`: `0 → ℤ → 𝒪 → 𝒪ˣ → 0` on the analytic space. |
| `Other/AlgebraicGeometry/HolomorphicFirstChernClass.lean` | The connecting map `Ext¹(ℤ, 𝒪ˣ) → Ext²(ℤ, ℤ)` and `exists_holomorphicFirstChernClass_iff`. |
| `Other/AlgebraicGeometry/HolomorphicZeroForms.lean`, `HolomorphicHodgeProjection.lean` | The projection to `H²(𝒪)` kills `F¹`; `hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero`. |
| `Other/AlgebraicGeometry/AnalyticSheafCohomologyExt.lean` | `analyticSheafCohomologyEquivExt`, natural in coefficient maps. |
| `Other/AlgebraicGeometry/HolomorphicIntegralHodgeClass.lean` | `IntegralCohomology`, `integralToRationalCohomology`, `exists_holomorphicFirstChernClass_of_integral_hodgeClass`. |
| `Other/CategoryTheory/Abelian/ExtOneRepresentative.lean` | `Abelian.Ext.exists_shortExact`. |
| `Other/AlgebraicTopology/SheafExtensionCocycle.lean`, `SheafExtensionLocalLifts.lean` | Local lifts through a sheaf epimorphism and their cocycles. |
| `Other/AlgebraicGeometry/HolomorphicUnitExtension.lean` | `exists_holomorphicUnitExtension_of_integral_hodgeClass`: an extension `E` with `E.firstChernClass = α`. |
| `Other/AlgebraicGeometry/HolomorphicUnitTransition.lean`, `HolomorphicLineBundleOfExtension.lean` | Holomorphic unit transition functions and `E.lineBundleCore`. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleSections.lean`, `HolomorphicLineBundleModule.lean` | The sheaf of holomorphic sections and `E.sectionSheafOfModules`. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleCoordinates.lean`, `HolomorphicLineBundleInvertible.lean` | Local coordinate isomorphisms; `E.sectionSheafOfModules_isInvertible`. |
| `Other/AlgebraicGeometry/RegularFunctionsHolomorphic.lean` | `regularToHolomorphicSheaf`, the structure-sheaf map over `underlyingContinuousMap`. |
| `Other/AlgebraicGeometry/AnalytificationModules.lean` | `moduleAnalytification`, its adjunction and `moduleAnalytificationUnitIso`. |
| `Other/AlgebraicGeometry/HolomorphicLocallyRingedSpace.lean` | Holomorphic stalks are local; `analytificationToAlgebraic`. |
| `Other/LinearAlgebra/RationalDenominators.lean`, `Other/Algebra/Homology/RationalCochainDenominators.lean` | Denominator clearing for finitely generated abelian groups and for homology. |
| `Other/AlgebraicGeometry/LefschetzOneOneReduction.lean` | The remaining obligations as explicit propositions, and `RationalLefschetzOneOne.of_obligations`. |

## Remaining obligations

[`Other/AlgebraicGeometry/LefschetzOneOneReduction.lean`](../Other/AlgebraicGeometry/LefschetzOneOneReduction.lean)
states, for a single smooth projective integral complex variety `X`:

1. `HasIntegralDenominatorClearing X`: for every `α : FieldCohomology ℚ X 2` there are `m ≠ 0`
   and `β : IntegralCohomology X 2` with `integralToRationalCohomology X 2 β = m • α`.
   Mathematically this is finite generation of `H²(X^an, ℤ)` together with the universal
   coefficient comparison. Neither is available: the finite-good-cover homology model in
   `Other/AlgebraicTopology/FiniteGoodCover*.lean` assumes a cover, whose existence for the
   analytification is unproved, and the sheaf/singular comparison in
   `Other/AlgebraicGeometry/BettiGlobalSectionsComparison.lean` is stated for field coefficients.
2. `HasAlgebraicModel X`: for every `E : HolomorphicUnitExtension X (dim X.left)` there is an
   invertible `L : X.left.Modules` with `(moduleAnalytification X (dim X.left)).obj L ≅
   E.sectionSheafOfModules`. This is projective GAGA for line bundles.
3. `HasDivisorOfAlgebraicModel X`: such an `L` is represented by `D : CodimensionCycle X.left 1`
   with `sheafCycleClassOnCycles (ofOver X) 1 D = integralToRationalCohomology X 2
   E.firstChernClass`. This combines the divisor/line-bundle dictionary on a smooth projective
   variety with the comparison between the constructed cycle class and the exponential connecting
   map. Since `D` is existential, sign and `2πi` normalisation conventions do not affect the
   statement.

`RationalLefschetzOneOne.of_obligations` proves the target from (1) and
`HasDivisorOfUnitExtension`, which follows from (2) and (3) by
`hasDivisorOfUnitExtension_of_algebraicModel`. The bookkeeping proved there is: rational Hodge
classes are stable under integer scaling, integral Hodge classes lift to unit-sheaf extensions,
and the resulting integral divisor is divided by the denominator.

Each of (1)–(3) is a substantial formalisation project in its own right; none is a matter of
elaboration or of connecting existing lemmas.

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
  `CodimensionCycle X.left 1` and `CodimensionCycle (ofOver X).scheme 1` agree only after
  unfolding, so proofs manipulating both use that option.
- Distinguish `Scheme.Modules` from the generic `SheafOfModules` category, and specify the module
  universe (`.{0}`) where inferred right-adjoint instances otherwise generalise too far.
