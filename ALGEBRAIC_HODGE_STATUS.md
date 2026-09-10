# Algebraic and non-Hodge classes

This worktree starts from freshly fetched `origin/main` at
`5c22fd9f08a3f19c9c44f23109dbaaea5c09057f`.

## Handoff status

Work stopped at the user's request to open a handoff PR. **Neither requested
final result is proved:** the general inclusion of algebraic classes in Hodge
classes, and a rational non-Hodge class in the actual cohomology of an explicitly
constructed variety. The results below are completed prerequisites and reductions,
with no admitted proofs of the missing statements. The Hodge filtration used is
the repository's actual analytic de Rham filtration of a scheme, not an
independently supplied abstract Hodge structure.

The branch is `codex/algebraic-and-non-hodge-classes`, in the separate worktree
`/tmp/hodge-algebraic-and-non-hodge-classes`. Its original upstream base was current
when work began. At handoff, fetched `origin/main` is
`2f3eb1af5ace261df369f390ac55a216c5964329`; this includes the `CategoryTheory.Over`
refactor in PR #4 and the Verso guide in PR #6. This branch has **not** been rebased
or merged onto those changes. Its successful build applies to its own checkout
and original API, not to a merge with the newer main branch. Porting the new
modules from separate scheme/structure-map arguments to the current `Over (Spec ℂ)`
API is the first integration task.

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

- `HolomorphicTransitionClass.lean` constructs actual classes from a holomorphic
  transition unit on the intersection of a two-open analytic cover, using the
  actual Mayer–Vietoris extension and explicit sheaf/Ext/hypercohomology
  comparisons. Their rational images are proved Hodge; the trivial transition
  gives zero. No algebraic cycle comparison is assumed or asserted.
- `AnalyticTransitionCoboundary.lean` proves that changing local trivializations
  preserves the units, integral, and rational transition classes. It also proves
  that the units class vanishes exactly when actual units on the two opens
  trivialize the transition function, without assuming an acyclic cover.
- `HolomorphicUnitObstruction.lean` constructs the actual degree-one integral
  sheaf cohomology class of a holomorphic unit on any analytic open. It vanishes
  exactly when a holomorphic logarithm exists there. A closed analytic loop on
  which the unit makes one exponential turn proves that this class is nonzero.
  This is a local prerequisite, not the requested global non-Hodge class.
- `HolomorphicLogarithmTransition.lean` proves the exact comparison between the
  integer Mayer–Vietoris cocycle of actual logarithm branches and the actual
  exponential obstruction, retaining the displayed `2πi` period map.
- `ShortExactComparisonCochain.lean` supplies an explicit cochain and proves the
  sign of the connecting-map comparison in the homotopy and derived categories.
  The library's mapping-cone triangle uses `-fst`; the proof accounts for this
  convention rather than assuming a comparison identity.
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
is smooth, integral, proper, and of relative dimension two; its explicit projectivity
is established below.

`ExplicitProjectiveSpaceChart.lean` and `ExplicitSegreCharts.lean` construct
standard projective charts in arbitrary finite coordinate dimension and actual
Segre closed immersions on product charts. Their kernels are exactly the ideals
of matrix minors, and the overlap-open formula is proved. The global gluing
is now constructed in `ExplicitProjectiveCoordinates.lean`,
`ExplicitProjectiveRatioSections.lean`, and `ExplicitSegreMorphism.lean`, with
coordinate relabeling in `ExplicitProjectiveRelabeling.lean`.
`ExplicitEllipticSegre.lean` constructs the actual map
`surfaceSegre : surface ⟶ ProjectiveSpace (Fin 9) base`, proves it is over the
complex base, and proves its local coordinate formulas. The projection-recovery
and cancellation results in `ExplicitSegreProjections.lean` and
`ExplicitSegreCancellation.lean` prove this map is a monomorphism. Its properness
then proves `surfaceSegre_isClosedImmersion`, and `surface_isProjective` gives
the explicit projective presentation. `curveVariety` and `surfaceVariety` package
the actual integral projective complex varieties with proved smooth relative
dimensions one and two.

`ExplicitEllipticDifferentials.lean` constructs `curveZDifferential` and
`curveYDifferential` in the Kähler differential modules of the actual rings
`Γ(curve, chart 2)` and `Γ(curve, chart 1)`. For a hypersurface equation `F` and
Bézout identity `aF + bF_x + cF_y = 1`, it constructs `ω = c dx − b dy`, proves
`F_y ω = dx` and `F_x ω = −dy`, and proves that contraction with the descended
Hamiltonian derivation is one. Explicit coefficients on the cubic's two charts
therefore prove `curveZDifferential_ne_zero` and `curveYDifferential_ne_zero`.
These are local regular forms; their agreement on overlaps and their comparison
with holomorphic forms have not been proved.

The cohomology/filtration computation needed for the non-Hodge example remains
to be established. A non-Hodge class has not yet been constructed.

## Exact stopping points and continuation

### Algebraic-class comparison

The last completed general comparison is
`CategoryTheory.ShortComplex.comparisonCone_derived` in
`Other/Algebra/Homology/ShortExactComparisonCochain.lean`. It constructs an
explicit cochain and proves the derived connecting-map identity with the minus
sign imposed by the mapping-cone convention. It has **not** yet been transported
to an identity for the short exact sequence's `Ext` class, specialized to the
actual exponential sequence, or used to compare those classes with the existing
topological cycle classes. A proposed `ShortExactComparisonExt.lean` was not
created; there is no partial implementation to finish in that file.

The next bounded step is to cancel the quasi-isomorphism
`mappingCone.descShortComplex` in the derived identity and obtain the corresponding
`Ext` comparison, preserving the sign. Then specialize it to the exponential
sequence and transport through the actual Ext/hypercohomology equivalence,
tracking the `2πi` normalization. This supplies a comparison prerequisite; it
does not itself prove that a divisor's topological component class is its
exponential class. That geometric identification still needs a proof, and the
filtered fundamental-class comparison displayed above remains necessary for
arbitrary codimension. Products of divisor classes do not cover all algebraic
cycles.

### Explicit non-Hodge example

The last completed geometric step is the construction and nonvanishing of the
two local regular differentials. The curve and its self-product already have
proved smoothness, integrality, and explicit projectivity. Continue as follows:

1. Prove the two differentials agree under actual restriction to the chart
   overlap, using the coordinate relations `xv = u` and `yv = 1`.
2. Construct the regular-to-holomorphic comparison using
   `analyticAt_localChart_symm_evaluate` from
   `HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexManifold.lean` and the actual
   naturality of section evaluation. Prove that the resulting analytic form is
   nonzero; algebraic Kähler nonvanishing alone does not imply this comparison.
   The intended local calculation is at infinity, where the form is `−du` and
   the equation gives `dv = 0`; the derivative of the actual closed immersion
   should supply the required nonvanishing argument.
3. Glue in `holomorphicDeRhamSheaf` **after sheafification** and construct the
   surface's holomorphic two-form. The raw global `HolomorphicForm` presheaf is
   generated by global holomorphic functions and is insufficient for this step
   on the compact curve.
4. Establish a nonzero obstruction in the actual cohomology and show that a
   rational class detects it. A nonzero local or global holomorphic form alone
   is not a proof of this cohomological assertion. No such cohomology comparison,
   nonvanishing computation, or rational witness has been supplied in this work.
5. Apply `exists_not_isHodgeClass_iff` to `surfaceToBase` at `p = 1`, once its
   actual first filtration is proved proper. Alternatively use
   `isHodgeClass_one_iff` with a rational class whose actual `H²(O)` obstruction
   is nonzero.

## Verification

- `lake build` passed for both default library targets, `HodgeConjecture` and
  `Other` (4771 jobs), including the final differential module.
- `lake env lean checks/AlgebraicHodgeHandoff.lean` passed. This reproducible
  `#print axioms` audit covers 22 principal reductions, comparisons, constructions,
  projectivity, and nonvanishing results. Every audited declaration depends only
  on `propext`, `Classical.choice`, and `Quot.sound`.
- A keyword scan of all 43 added or modified Lean files found no `sorry`, `admit`,
  new axioms, or unsafe declarations (the only matches were explanatory uses of
  the word `axiom` in comments). `git diff --check` passed.
- These checks were run on this branch before integration with the newer
  upstream `CategoryTheory.Over` API; they must be rerun after that port.
