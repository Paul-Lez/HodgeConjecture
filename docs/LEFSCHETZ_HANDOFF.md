# Unconditional Lefschetz (1, 1): handoff

This is an incomplete proof development, handed off at the user's request. The conditional
statement is proved; the requested unconditional theorem is **not** proved. A successful build
of this branch does not establish the missing theorem.

## Goal and acceptance criteria

The original requests were to update to main, formalize Hodge implies Lefschetz (1, 1), and
then prove Lefschetz directly, including a copy made with the type elaborator. Tau Ceti was
explicitly allowed. The concrete target already defined in
[`Other/AlgebraicGeometry/LefschetzOneOne.lean`](../Other/AlgebraicGeometry/LefschetzOneOne.lean)
is `RationalLefschetzOneOne`:

```lean
∀ {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ) [Smooth s]
  [IsProjective s] (α : FieldCohomology ℚ s 2),
  α ∈ Hdg^1(ℚ; s) →
    ∃ D : TensorProduct ℤ ℚ (CodimensionCycle X 1),
      rationalSheafCycleClassOnCycles
        (DimensionedSmoothProjectiveComplexVariety.ofStructureMap s) 1 D = α
```

Completion requires a theorem of this type **without a `HodgeConjecture` hypothesis**, using the
existing cohomology, Hodge-class, codimension-cycle, and constructed cycle-class definitions.
It also requires the requested copied statement, using Lean's actual syntax `type_of%`.
Do not replace algebraic divisors with analytic bundles, add the missing mathematics as axioms,
or restrict the result to curves, integral-image rational classes, or varieties supplied with
extra comparison hypotheses. The rational divisor statement above is the explicit target;
the integral first-Chern-class statement is the intermediate route being developed.

The existing `HodgeConjecture.rationalLefschetzOneOne_direct` is a second proof of the
**conditional implication**. Its `type_of% HodgeConjecture.rationalLefschetzOneOne` type
still includes the Hodge hypothesis. It does not fulfill the unconditional request.

## What is proved

All paths below are relative to the repository. Names in the analytic rows are in
`AlgebraicGeometry.ComplexPoint` unless otherwise indicated.

| Files | Proven result / main entry point |
| --- | --- |
| `Other/AlgebraicGeometry/SheafCycleClass.lean`, `LefschetzOneOne.lean` | `algebraicCycleClassSpan_le_range_rationalSheafCycleClassOnCycles` realizes span membership by a rational cycle; `HodgeConjecture.rationalLefschetzOneOne` and its copied conditional proof specialize Hodge to codimension one. |
| `Other/Geometry/Manifold/HolomorphicLogarithm.lean` | Local holomorphic logarithms and the local integer kernel of the normalized exponential `exp(2πiz)`. |
| `Other/AlgebraicGeometry/HolomorphicExponential.lean`, `HolomorphicExponentialSequence.lean` | Actual sheaf maps and `holomorphicExponentialSequence_shortExact`: `0 → ℤ → 𝒪 → 𝒪ˣ → 0`. |
| `Other/AlgebraicGeometry/HolomorphicFirstChernClass.lean` | `holomorphicFirstChernClass` is the connecting map `Ext¹(ℤ,𝒪ˣ) → Ext²(ℤ,ℤ)`; `exists_holomorphicFirstChernClass_iff` identifies its image with the kernel of `H²(ℤ) → H²(𝒪)`. |
| `Other/AlgebraicGeometry/HolomorphicZeroForms.lean`, `HolomorphicHodgeProjection.lean` | Projection from holomorphic de Rham cohomology to `H²(𝒪)` kills the first Hodge filtration; `hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero` applies this to rational Hodge classes. |
| `Other/AlgebraicGeometry/AnalyticSheafCohomologyExt.lean` | `analyticSheafCohomologyEquivExt` compares the project's derived/hypercohomology presentation to `Ext`, naturally in coefficient maps. |
| `Other/AlgebraicGeometry/HolomorphicIntegralHodgeClass.lean` | `IntegralCohomology`, `integralToRationalCohomology`, and `exists_holomorphicFirstChernClass_of_integral_hodgeClass`: an integral class whose rational image is Hodge lifts to `Ext¹(ℤ,𝒪ˣ)` without assuming Hodge. |
| `Other/CategoryTheory/Abelian/ExtOneRepresentative.lean` | `Abelian.Ext.exists_shortExact` represents any degree-one Ext class by a short exact sequence, using enough injectives. |
| `Other/AlgebraicTopology/SheafExtensionCocycle.lean`, `SheafExtensionLocalLifts.lean` | Local lifts through a sheaf epimorphism; their differences give restriction-compatible cocycles. |
| `Other/AlgebraicGeometry/HolomorphicUnitExtension.lean` | `exists_holomorphicUnitExtension_of_integral_hodgeClass` produces an actual `HolomorphicUnitExtension` with `E.firstChernClass = α`. |
| `Other/AlgebraicGeometry/HolomorphicUnitTransition.lean`, `HolomorphicLineBundleOfExtension.lean` | `E.transitionUnit` and `E.lineBundleCore`: actual nonvanishing holomorphic transition functions, cocycle identities, and a holomorphic complex vector bundle with one-dimensional fibers. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleSections.lean`, `HolomorphicLineBundleModule.lean` | The sheaf of actual holomorphic sections, its structure-sheaf module action, and `E.sectionSheafOfModules`. |
| `Other/AlgebraicGeometry/HolomorphicLineBundleCoordinates.lean`, `HolomorphicLineBundleInvertible.lean` | Explicit coordinate linear equivalences and local sheaf isomorphisms; `E.sectionSheafOfModules_isInvertible` proves invertibility using Tau Ceti's rank-one predicate. |
| `Other/AlgebraicGeometry/RegularFunctionsHolomorphic.lean` | Regular-function evaluation is holomorphic; `regularToHolomorphicSheaf` is the structure-sheaf map over `underlyingContinuousMap`. |
| `Other/AlgebraicGeometry/AnalytificationModules.lean` | `moduleAnalytification`, its pushforward adjunction, and `moduleAnalytificationUnitIso`; this constructs the functor needed for algebraization, but proves no essential-surjectivity/GAGA theorem. |
| `Other/AlgebraicGeometry/HolomorphicLocallyRingedSpace.lean` | A holomorphic germ is invertible iff its value is nonzero; local stalk rings and `analytificationToAlgebraic`, with `analytification_stalkMap_comp_evaluation`. |

The strongest assembled unconditional existence statement currently starts with
`α : IntegralCohomology s 2` and the hypothesis that its rational image is Hodge. It produces
an extension `E` whose connecting class is `α`. The bundle and invertible section sheaf can
then be constructed from `E`.

**A distinction needed for the next proof:** `E.firstChernClass` is defined from the Ext class
of the extension. It is not yet an independently defined Chern-class function on arbitrary
line bundles or invertible sheaves, with a theorem identifying the class of
`E.sectionSheafOfModules` with `E.firstChernClass`. The construction of a bundle from the
extension's transitions alone does not supply that missing classification/comparison theorem.

## Exact stopping point

The analytic construction and the natural map of locally ringed spaces have been checked.
Work then moved to the independent rational-denominator step. The last two algebra files are:

- `Other/LinearAlgebra/RationalDenominators.lean`: clearing a common nonzero integer
  denominator for rational-valued linear maps on finitely generated abelian groups;
  `LinearMap.exists_integer_multiple_isInteger` and `LinearMap.exists_integer_multiple`.
- `Other/Algebra/Homology/RationalCochainDenominators.lean`:
  `ShortComplex.homologyMap_exists_integer_multiple` transports a middle-component
  denominator-lifting property to homology when the next component is injective.

These are algebraic lemmas. They have **not** been instantiated with integral/rational
cochain complexes of the variety, and do not prove denominator clearing for
`integralToRationalCohomology`. The next intended construction was a coefficient-dual short
complex for an integral chain model, its `ℤ → ℚ` map, and an application of these lemmas.
No proof search or background Lean process needs to be resumed from this handoff.

## Remaining proof obligations

Before extending the proof, migrate this checkpoint onto main's `2f3eb1a`
(`make use of CategoryTheory.Over`, PR #4). That change landed while the handoff was being
prepared and changes 114 existing files, including the Hodge statement and the analytic
interfaces used here. This branch preserves the checked proof against `fc97448`; the later
`Over` migration has **not** been applied or checked. Update the new modules from a scheme
and structure morphism to `X : Over (Spec ↧ℂ)`, with hypotheses on `X.left` and `X.hom`,
adapt the span-to-cycle lemma and both conditional theorems, then rebuild and rerun the audit.
The goal displayed above uses this checkpoint's pre-refactor syntax and should be transported
to the new interface without changing its mathematical content. Do not assume a clean textual
merge establishes compatibility.

1. **Rational denominator clearing in the actual cohomology.** For each degree-two rational
   class on a smooth projective integral complex variety, construct `m : ℤ`, `m ≠ 0`, and
   `β : IntegralCohomology s 2` with
   `integralToRationalCohomology s 2 β = m • α`. Connect the integer/rational cochain map to the
   existing hypercohomology coefficient map, including naturality. A finite chain model or an
   equivalent finiteness/coefficient-comparison theorem still has to be proved for the space.
   The Hodge condition for `β` then follows from closure of the Hodge submodule under scaling.
2. **Classify the constructed line bundle compatibly with Ext and Chern classes.** Establish
   the needed unit-torsor/line-bundle/`H¹(𝒪ˣ)` comparison, or an equivalent direct comparison
   sufficient for this construction. Track the transition orientation and the `2πi`
   normalization. Prove that the section sheaf constructed from `E` has connecting class
   `E.firstChernClass`, in the interface used for the later algebraic comparison.
3. **Algebraize the holomorphic invertible sheaf.** Prove the required projective GAGA
   essential-surjectivity statement, or a rank-one theorem sufficient here: construct an
   invertible `L : X.Modules` and an isomorphism from `(moduleAnalytification s (dim X)).obj L`
   to `E.sectionSheafOfModules`. Defining `moduleAnalytification` is not a proof of this.
4. **Represent algebraic line bundles by codimension-one cycles in arbitrary dimension.**
   Supply the needed rational section / Cartier divisor / Weil divisor dictionary for smooth
   integral projective schemes, and produce an actual `CodimensionCycle X 1`. Do not assume
   that the available curve-specific divisor results cover this step.
5. **Compare divisor cycle classes with Chern classes.** Prove compatibility with the
   repository's actual `rationalSheafCycleClassOnCycles`, built from fundamental/support
   classes. An abstract cycle-class map with assumed properties is insufficient. Check
   signs, the exponential normalization, integral-to-rational maps, and the presentation of
   cohomology. Existing principal-divisor reductions do not supply this theorem.
6. **Assemble the unconditional target and its copied statement.** Apply the previous steps
   to `m • α`, divide the resulting rational divisor by `m`, and prove
   `RationalLefschetzOneOne` without Hodge. Add the requested `type_of%` copy of the
   unconditional theorem (or use that theorem to prove the copied implication directly).
   Build and audit the final declarations for `sorryAx` and unexpected axioms.

These are substantial mathematical gaps, particularly algebraization and cycle-class
compatibility. They are not merely remaining elaboration errors or unconnected one-line lemmas.

## Existing material to reuse, and its limits

- `Other/AlgebraicTopology/FiniteGoodCoverHomology.lean` and
  `FiniteGoodCoverNerveHomology.lean` provide a finite nerve/homology model **given** a
  `FiniteGoodCover`. Existence of such a cover for the complex manifold was not found/proved.
- `Other/AlgebraicTopology/SingularCoefficientBaseChange.lean` constructs rational-to-complex
  coefficient comparison. Its cohomology base-change isomorphism needs finite-dimensional
  rational homology. `ProjectiveSingularCoefficientBaseChange.lean` currently supplies this
  only in degree zero; it does not solve the integer-to-rational degree-two problem.
- `Other/AlgebraicGeometry/PrincipalDivisorCycleClass.lean` and related reduction files
  separate geometric comparison/vanishing obligations; their interfaces are not proofs of
  those obligations.
- Only three Tau Ceti files are adapted into this branch, under `Other/TauCeti/SheafOfModules`.
  Their source, license, and pinned commit are in [the provenance note](../Other/TauCeti/README.md).
  They preserve the `TauCeti` namespaces and support invertibility and local trivializations.
  No Tau Ceti package dependency or toolchain upgrade was added.
- The inspected Tau Ceti commit is `b8d215394069a6c5713292fadcfa49746702a0eb` (Lean 4.34.0-rc2).
  Its Cartier-divisor files construct quotient sheaves/local equations, while the full
  Cartier-to-line-bundle dictionary remains unfinished there. Some Weil/Cartier results
  require dimension at most one. Searches did not find a usable GAGA proof there.

## Verification and development notes

The handoff uses Lean 4.33.1 and the repository's pinned Mathlib v4.33.1
(`0df444a360eaa60ab8c11dca51a86af692955474`). The checkpoint includes the
formalization-guide merge `fc97448`, but not the subsequent `Over` refactor `2f3eb1a` on main.
The checks below apply to the branch head, not to a merge with the newer main.

The final checkpoint passed `lake build` (4744 jobs), the 15-declaration axiom audit,
and `git diff fc97448 --check`. The import-layer output was byte-for-byte identical to
the saved base baseline. A source scan of the 29 changed Lean library files found no
`sorry`, `admit`, or added `axiom` declarations.

Reproduce the checks with:

```bash
lake build
lake env lean scripts/lefschetz_axiom_audit.lean
git diff --check
python3 scripts/check_import_layers.py
```

The import-layer checker already reports 189 violations on the base `fc97448`. The handoff is checked
against that baseline; a nonzero exit alone does not indicate a new violation. All new
library modules are imported by `Other.lean`. The axiom audit checks the conditional theorems,
analytic milestones, and the final denominator lemmas; expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Practical Lean details from this development:

- Use `type_of%`, not `typeof%`.
- Name local topology instances uniquely across files; anonymous instances previously caused
  collisions when the umbrella was built.
- Many sheaf, module, and concrete-category aliases need explicit types or application lemmas
  to make rewrites fire. Existing local `backward.isDefEq.respectTransparency` settings are
  deliberate; `erw` or an explicit `change` can be needed for bundled section types.
- Distinguish `Scheme.Modules` category instances from the definitionally related generic
  `SheafOfModules` category, and specify the module universe (`.{0}` here) where inferred
  right-adjoint instances otherwise generalize too far.
- The original development workspace reused dependency caches via a local `.lake/packages`
  symlink. It is not part of the PR or needed to reproduce the source; use the manifest.
