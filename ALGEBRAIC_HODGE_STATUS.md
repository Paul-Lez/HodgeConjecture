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

Scheme smoothness and integrality, the self-product's explicit projective
presentation, and its cohomology/filtration computation remain unproved.
The pointwise Weierstrass nonsingularity result
is not used as a substitute for a proof of scheme smoothness. Consequently this
construction is a concrete candidate, not a completed geometric non-Hodge example.

## Verification

- `lake build` succeeds for both default library targets (4681 jobs).
- The new cohomological theorems were checked with `#print axioms`; they use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new axioms, or unsafe declarations were added.
