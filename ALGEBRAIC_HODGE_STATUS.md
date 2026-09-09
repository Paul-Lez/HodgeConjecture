# Algebraic and non-Hodge classes

## Current status

**Neither requested final result is proved:** the inclusion of all rational
algebraic cycle classes in Hodge classes, and a rational non-Hodge class in the
actual cohomology of an explicit smooth projective variety. All filtrations here
are the repository's actual analytic de Rham filtrations. The branch contains
proved prerequisites and reductions, without admitting the missing conclusions.

Current upstream `origin/main` at `023570e` has been merged in local commit
`4c93fdb`, including the `CategoryTheory.Over` refactor and the Verso guide.
The 21 PR modules requiring API changes now use `Over (Spec ℂ)`, with hypotheses
on `X.left` and `X.hom`. The original scheme definitions, cycle-class maps, and
theorem names are retained. `curveVariety` and `surfaceVariety` now package the
explicit schemes as objects of `Over`, with integrality, projectivity, and
smoothness instances. The branch is `codex/algebraic-and-non-hodge-classes`.

## Algebraic cycle classes

`AlgebraicHodgeClasses.lean` defines the unproved proposition
`AlgebraicGeometry.ComplexPoint.AlgebraicClassesAreHodge`:

```lean
∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ),
  algebraicCycleClassSpan X p ≤ Hdg^p(ℚ; X)
```

The file proves that the image of the actual rational cycle-class map is exactly
`algebraicCycleClassSpan`, including arbitrary rational combinations. The inclusion
holds in codimension zero and above the dimension, hence in every codimension
on a zero-dimensional variety. General inclusion is equivalent to filtered de
Rham lifts of the existing component classes; such lifts give a linear map into
the Hodge subspace whose underlying map is the existing cycle-class map.

The remaining geometric theorem must construct, for every codimension-`p`
component `x` with `hx : coheight x = p`, a class
`β : FilteredDeRhamHypercohomology X p (2 * (p : ℤ))` satisfying:

```lean
filteredToDeRhamCohomology X p (2 * (p : ℤ)) β =
  fieldToDeRhamCohomology ℚ X (2 * (p : ℤ))
    (cycleComponentSheafClass X x (d := dim X.left) hx)
```

The right-hand class uses normalized topological normal coclasses and extension
across the singular locus. Its identification with a filtered holomorphic de
Rham fundamental class remains missing. Products of divisor classes alone do
not cover all algebraic cycles.

### Completed exponential comparison

The logarithmic and exponential modules construct actual analytic classes:
closed logarithmic forms, their factorization through the first filtered de
Rham complex, local logarithms, and the short exact sequence
`0 → ℤ → O → Oˣ → 0` with integer map `n ↦ 2πi n`.
`HolomorphicExponentialResolution.lean` constructs its two-term resolution.
`ExponentialClassHodge.lean` proves the normalized logarithmic comparison and
degree-two Hodge membership for its rational classes.

The bounded comparison step identified in PR #8 is now completed:

1. `Other/Algebra/Homology/ShortExactComparisonExt.lean` cancels the actual cone
   quasi-isomorphism and proves `comparisonTriangle_derived`,
   `comparisonExt_hom`, and `comparisonExt`.
2. `ExponentialConnectingComparison.lean` specializes to the actual exponential
   sequence, proves `exponentialComparisonKernel_normalization`, and transports
   the connecting morphism through Ext/hypercohomology.
   `rationalExponentialConnectingClass_scaled_deRham` retains the `2πi` factor.
3. `ExponentialConnectingResolution.lean` proves
   `rationalExponentialConnectingClass_eq_neg` in every Ext degree: the rational
   connecting class is the negative of the **existing** resolution class after
   the established placement-degree equivalence. The mapping-cone convention
   forces the minus sign. `rationalExponentialConnectingClass_isHodge` proves
   degree-two Hodge membership.

These comparisons do **not** identify a divisor's existing topological component
class with its exponential class. That identification and the general filtered
fundamental-class comparison remain unproved.

### Existing obstruction and transition results

`HolomorphicTransitionClass.lean` constructs classes from actual two-open
transition units. `AnalyticTransitionCoboundary.lean` proves invariance under
changes of trivialization and characterizes vanishing by actual trivializing
units, without assuming an acyclic cover. `HolomorphicUnitObstruction.lean`
characterizes existence of a holomorphic logarithm by vanishing of an integral
cohomology class; an appropriate exponential-turn loop proves nonvanishing.
`HolomorphicLogarithmTransition.lean` identifies the integer transition cocycle
with this obstruction.

`HolomorphicZeroForms.lean` identifies the analytic degree-zero quotient with
holomorphic functions. `FirstHodgeObstruction.lean` constructs
`0 → F¹Ω• → Ω• → O[0] → 0` and proves `isHodgeClass_one_iff`: a rational
degree-two class is Hodge exactly when its actual `H²(O)` obstruction vanishes.
`ExponentialClassImage.lean` proves `integralClass_isHodge_iff_exponential`, using
the exactness established in `HypercohomologyExact.lean`.

## The explicit elliptic curve and surface

The actual schemes are `E: Y²Z = X³ − XZ²` and its scheme-theoretic self-product
`S = E ×ℂ E`. The cubic has discriminant `64`. The original chart, integrality,
smoothness, and Segre modules establish:

- The Y and Z affine opens cover E; their actual section rings are the
  dehomogenized polynomial quotients.
- E and S are integral and smooth of relative dimensions one and two.
- The actual Segre map embeds S as a closed subscheme of projective eight-space,
  providing `surface_isProjective`.
- `ExplicitEllipticDifferentials.lean` constructs nonzero Kähler differentials
  on both actual curve chart rings, using explicit Bézout coefficients and a
  descended Hamiltonian derivation.

### Completed regular and holomorphic form constructions

- `ExplicitEllipticDifferentialOverlap.lean` proves the actual coordinate
  restriction formulas and `curveDifferential_overlap_on` on every common open.
- `Other/Algebra/DeRham/Kaehler.lean` constructs the map from Kähler differentials
  to degree-one algebraic de Rham forms. `KaehlerWedge.lean` constructs a
  bilinear wedge into degree two from the two Kähler quotient presentations.
  Both maps have proved generator formulas and naturality.
- `RegularHolomorphicForms.lean` proves regular section evaluation holomorphic
  in the canonical analytic charts. Its algebra homomorphism and regular-form
  comparison commute with restrictions and de Rham differentials.
- `ExplicitEllipticHolomorphicDifferentials.lean` glues the evaluated curve forms
  **after sheafification**, constructing `curveGlobalHolomorphicDifferential`
  in the actual holomorphic de Rham sheaf with both chart formulas.
- `HolomorphicFormSheafification.lean` proves that the analytic relations equal
  the chart-evaluation kernel and that `holomorphicDeRham_toSheafify_injective`
  holds on every analytic open and in every degree.
- `ExplicitEllipticInfinityCoordinates.lean` proves the two actual Y-chart
  coordinate values at infinity are zero. `ExplicitEllipticAnalyticNonvanishing.lean`
  differentiates the actual cubic to get `dv = 0`; smoothness and generation of
  the affine section ring give `du ≠ 0`. Evaluating the form gives `−du`, proving
  `curveGlobalHolomorphicDifferential_ne_zero`.
- `RegularSectionPullback.lean` and `ExplicitEllipticSurfacePullback.lean`
  construct actual section and Kähler differential pullbacks over the complex
  base, with restriction and chart-overlap compatibility.
- `ExplicitEllipticSurfaceDifferential.lean` constructs the two pulled-back
  elliptic forms' wedge on all four product charts, proves compatibility, and
  glues `surfaceGlobalHolomorphicTwoForm` in the actual holomorphic two-form
  sheaf, with every product-chart formula proved.
- `ExplicitEllipticSurfaceCoordinateRing.lean` proves the Y product chart affine
  and its actual section ring generated by the four projection-pulled
  coordinates, using the affine pullback's pushout of section rings.
- `ExplicitEllipticSurfaceInfinity.lean` constructs the actual complex point
  `(∞,∞)` and proves all four coordinate values are zero there.
  `RegularDerivativeRank.lean` proves that derivatives of actual affine ring
  generators separate tangent vectors. `ExplicitEllipticSurfaceNonvanishing.lean`
  uses both cubic equations and the four-generator presentation to prove
  `du₁ ∧ du₂ ≠ 0` at this point.
- `RegularHolomorphicFormEvaluation.lean` compares actual quotient-form
  evaluation with the determinant of the regular functions' analytic
  derivatives. `ExplicitEllipticSurfaceFormEvaluation.lean` evaluates the actual
  local surface form as `du₁ ∧ du₂`, proves it remains nonzero after
  sheafification, and proves `surfaceGlobalHolomorphicTwoForm_ne_zero`.
- `TopHodgeFilteredClass.lean` identifies global top forms with the top-degree
  hypercohomology of the highest filtered complex, preserving zero and
  nonvanishing. `ExplicitEllipticSurfaceFilteredClass.lean` constructs
  `surfaceTopFilteredClass : FilteredDeRhamHypercohomology surfaceVariety 2 2`
  and proves `surfaceTopFilteredClass_ne_zero`. This is nonvanishing in the
  filtered source group; nonvanishing of its image in full de Rham cohomology
  is not proved.

### Remaining non-Hodge theorem

`NonHodgeClass.lean` proves:

```lean
(∃ α : FieldCohomology ℚ X (2 * (p : ℤ)), ¬ IsHodgeClass ℚ X p α) ↔
  complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ)) ≠ ⊤
```

Rational vectors span their complexification, proving this criterion without
assuming independent abstract Hodge data. Properness of the surface's actual
filtration has **not** been established.

The required continuation is a nonzero obstruction in actual cohomology and a
rational class detecting that obstruction. Nonzero local or global holomorphic
forms alone do not prove the cohomological assertion. The final step must apply `exists_not_isHodgeClass_iff`
to `surfaceVariety` at `p = 1`, or `isHodgeClass_one_iff` to an actual rational
class with nonzero `H²(O)` obstruction.

In particular, the repository does not yet connect a nonzero holomorphic
two-form with a nonzero `H²(O)` class by Dolbeault comparison, Hodge symmetry,
or Serre duality. Neither surjectivity of `firstHodgeObstruction` nor
surjectivity of `fieldToDeRhamComplexification` in degree two is proved.
`ProjectiveSingularCoefficientBaseChange.lean` supplies unconditional projective
coefficient base change only in degree zero; its higher-degree counterpart
still requires finite-dimensional singular homology. These are additional
mathematical steps, not consequences of local differential nonvanishing.

A concrete missing target, followed by rational detection, is:

```lean
∃ α : DeRhamHypercohomology surfaceVariety 2,
  firstHodgeObstruction surfaceVariety 2 α ≠ 0
```

The holomorphic two-form's own de Rham class lies in `F² ⊆ F¹`, so that class
cannot itself witness the degree-two non-Hodge obstruction.

## Verification

The integrated checkout has passed:

- `lake build`: both default libraries, `HodgeConjecture` and `Other`, with
  **4795 jobs**, including every new proof module.
- `lake build HodgeGuide`: **4723 jobs**. The guide and its dependencies are
  unchanged by the subsequent proof additions in `Other`.
- `lake env lean checks/AlgebraicHodgeHandoff.lean`: **81 declarations**, each
  depending only on `propext`, `Classical.choice`, and `Quot.sound`.
- A scan of all **65 changed Lean files** relative to current main found no
  `sorry`, `admit`, new axiom declarations, or unsafe declarations. The only
  keyword matches are explanatory comments and the audit's error message.
- `git diff --check` and `git diff --cached --check`.

Every new module also passed direct compilation without warnings. There are no
unfinished proof files in this checkpoint. The two final mathematical goals
remain unproved as described above.

Reproduce the checks with:

```text
lake build
lake build HodgeGuide
lake env lean checks/AlgebraicHodgeHandoff.lean
git diff --check
```

The audit now **fails** if a listed declaration transitively depends on an axiom
other than `propext`, `Classical.choice`, or `Quot.sound`; it no longer merely
prints dependencies. Its rejection of `sorryAx` was checked with a separate
untracked negative-control file. No admission of either final theorem is included.
