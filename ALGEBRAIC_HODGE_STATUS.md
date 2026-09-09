# Algebraic and non-Hodge classes

This worktree starts from freshly fetched `origin/main` at
`5c22fd9f08a3f19c9c44f23109dbaaea5c09057f`.

## Algebraic classes

`Other/AlgebraicGeometry/AlgebraicHodgeClasses.lean` records the general assertion as
`AlgebraicGeometry.ComplexPoint.AlgebraicClassesAreHodge`:

```lean
∀ {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ)
    [Smooth s] [IsProjective s] (p : ℕ),
  algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s)
```

This proposition is **not proved in arbitrary codimension**. The file proves:

- The image of the actual rational cycle-class map is exactly
  `algebraicCycleClassSpan`, including arbitrary rational combinations.
- The inclusion holds in codimension zero and above the dimension, hence in every
  codimension on a zero-dimensional variety.
- The general inclusion is equivalent to existence of filtered de Rham lifts for
  the actual constructed component classes. Those lifts give a rational linear
  map into the Hodge subspace whose underlying map is the existing cycle-class map.

The remaining geometric step is to construct, for each codimension-`p` component
`x`, an element `β : FilteredDeRhamHypercohomology s p (2 * (p : ℤ))` satisfying

```lean
filteredToDeRhamCohomology s p (2 * (p : ℤ)) β =
  fieldToDeRhamCohomology ℚ s (2 * (p : ℤ))
    (cycleComponentSheafClass s x (d := dim X) hx)
```

Upstream constructs the right-hand class using topological normal coclasses and
extension across the singular locus. It does not yet provide the filtered
holomorphic de Rham comparison needed for this equation. The classical argument
uses the integration current of a complex subvariety and its Hodge type `(p,p)`;
see [Deligne, *The Hodge Conjecture*, §§1 and 3](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf).
Implementing that route also requires comparing it with the existing normalized
class and with the repository's holomorphic de Rham hypercohomology.

The following analytic prerequisites are now proved and constructed, without
additional axioms or assumed comparison maps:

- `Other/Algebra/DeRham/Logarithmic.lean` constructs logarithmic forms in every
  degree, proves they are closed, and proves `dlog(uv) = dlog(u) + dlog(v)`.
- `HolomorphicLogarithmicForms.lean` constructs logarithmic forms on the actual
  analytic variety and the `dlog` morphism of sheaves and cochain complexes.
- `FilteredLogarithmicClass.lean` factors that morphism through the actual
  first filtered de Rham complex and constructs filtered logarithmic classes.
- `HolomorphicExponential.lean`, `HolomorphicLocalLogarithm.lean`, and
  `HolomorphicExponentialSequence.lean` construct the holomorphic exponential,
  prove `dlog(exp f) = df` using actual chart derivatives, construct local
  logarithm branches, and prove the actual sequence
  `0 → ℤ → O → Oˣ → 0` short exact, with integer map `n ↦ 2πi n`.
- `HolomorphicExponentialResolution.lean` constructs its two-term resolution,
  proves the augmentation a quasi-isomorphism, and constructs integral and
  rational exponential classes in actual analytic cohomology.
- `ExponentialClassHodge.lean` proves the precise comparison
  `2πi • fieldToDeRhamCohomology (rationalExponentialClass α) = logarithmicClass α`
  and consequently proves `rationalExponentialClass_isHodge` in degree two.

- `HolomorphicZeroForms.lean` identifies the actual analytic quotient in degree
  zero with holomorphic functions, including the sheaf isomorphism.
- `FirstHodgeObstruction.lean` constructs the short exact sequence
  `0 → F¹Ω• → Ω• → O[0] → 0` and proves that a rational degree-two class is
  Hodge exactly when its image in actual holomorphic-function cohomology vanishes.
- `ExponentialClassImage.lean` proves the converse for integral classes:
  `integralClass_isHodge_iff_exponential` identifies integral classes whose
  rational images are Hodge with the image of the actual exponential class map.
  The exactness needed here is proved for the repository's hypercohomology model
  in `HypercohomologyExact.lean`.

These results establish Hodge membership for the actual exponential classes.
They do **not yet identify an algebraic component class with an exponential
class**, and they do not prove the requested inclusion in arbitrary codimension.

## Non-Hodge classes on an explicit variety

`Other/AlgebraicGeometry/NonHodgeClass.lean` proves the following criterion using
the actual analytic cohomology and Hodge filtration of a scheme:

```lean
(∃ α : FieldCohomology ℚ s (2 * (p : ℤ)), ¬ IsHodgeClass ℚ s p α) ↔
  complexifiedFieldHodgeFiltration ℚ s p (2 * (p : ℤ)) ≠ ⊤
```

Its proof uses the fact that rational vectors span their complexification. It
does not assume a pure Hodge structure on the cohomology, and does not replace
the variety's filtration with independently chosen linear algebra data.

An explicit variety with a **proved proper filtration is still required**.
The criterion alone is not a counterexample to all classes being Hodge.

`Other/AlgebraicGeometry/ExplicitEllipticCandidate.lean` constructs the projective
cubic scheme with reduced closed locus `Y²Z = X³ − XZ²`, and its scheme-theoretic
self-product over `ℂ`. It proves the cubic's projectivity and properness and the
self-product's properness. The defining cubic is homogeneous of degree three
and, after changing coefficients to `ℂ`, is exactly the projective polynomial
of the displayed Weierstrass equation with discriminant `64`.

The subsequent `ExplicitEllipticCharts.lean`, `ExplicitProjectivePlaneChart.lean`,
`ExplicitEllipticChartRings.lean`, `ExplicitEllipticIntegrality.lean`, and
`ExplicitEllipticSmoothness.lean` prove actual scheme geometry:

- The `Y ≠ 0` and `Z ≠ 0` opens are affine and cover the cubic; actual complex
  points are constructed, including the point at infinity and a point in their
  intersection.
- Standard projective-plane chart rings are explicitly identified with
  two-variable polynomial rings; the actual curve charts are identified with
  the corresponding reduced dehomogenized cubic quotients.
- Both equations generate prime ideals, and the overlapping integral affine
  charts prove that the actual projective cubic is integral.
- A Jacobian argument on those identified charts, respecting their original
  complex structure maps, proves `SmoothOfRelativeDimension 1 curveToBase`.
- Base change and composition prove
  `SmoothOfRelativeDimension 2 surfaceToBase` for the actual self-product.

`ExplicitEllipticSurface.lean` further proves that the actual self-product is
integral: all four affine product charts have domain tensor-product coordinate
rings, and their shared explicit point proves irreducibility. Thus the displayed
curve is smooth, integral, projective, and nonempty, and its actual self-product
is smooth, integral, proper, and of relative dimension two.

The self-product's explicit projective presentation and the cohomology/filtration
computation needed for the non-Hodge example remain to be established. A non-Hodge
class has not yet been constructed.

## Verification

- `lake build` succeeds for both default library targets (4720 jobs).
- The new cohomological theorems were checked with `#print axioms`; they use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new axioms, or unsafe declarations were added.
