# Finite generation of `H₂(X^an, ℤ)` (`HasFiniteSecondHomology`) — completed

**Status: proved.** `AlgebraicGeometry.ComplexPoint.hasFiniteSecondHomology` in
`Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean`, following route 1 below
(`Other/Geometry/Manifold/TubularNeighbourhood.lean`, `Other/AlgebraicTopology/RetractFiniteHomology.lean`,
`Other/Geometry/Manifold/CompactManifoldFiniteHomology.lean`). The rest of this document is kept
as the original scoping note.

This scopes the remaining *topological* obligation for the unconditional rational Lefschetz
`(1, 1)` theorem (see [LEFSCHETZ_HANDOFF.md](LEFSCHETZ_HANDOFF.md)). It is independent of the
GAGA obligation ([GAGA_HANDOFF.md](GAGA_HANDOFF.md)) and of the divisor/cycle-class comparison.

## The exact target

In [`Other/AlgebraicGeometry/IntegralDenominatorClearing.lean`](../Other/AlgebraicGeometry/IntegralDenominatorClearing.lean):

```lean
def HasFiniteSecondHomology (X : Over (Spec ↧ℂ)) : Prop :=
  Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
    (TopCat.of (ComplexPoint X))).homology 2)
```

**Deliverable:** a theorem

```lean
theorem hasFiniteSecondHomology (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : HasFiniteSecondHomology X
```

with no `sorry` and no new axiom (`#print axioms` must show only `propext`, `Classical.choice`,
`Quot.sound`); add it to `scripts/lefschetz_axiom_audit.lean`. Here
`SingularChainComplex ℤ Y = (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)` is Mathlib's
singular chain complex with `ℤ` coefficients in `ModuleCat ℤ`, and `ComplexPoint X` carries
`Point.analyticTopology` (install it as a `local instance`, named uniquely, as every file does).
Proving finite generation in every degree is equally welcome, and a proof of the stronger
`HasFiniteGoodCover X` (below) is sufficient.

## What is available

- `HasFiniteGoodCover X` (same file): finitely many opens of `ComplexPoint X` whose nonempty
  finite intersections are contractible (`AlgebraicTopology.Singular.FiniteGoodCover`,
  `Other/AlgebraicTopology/FiniteGoodCoverHomology.lean`). It implies the target through
  `hasFiniteSecondHomology_of_hasFiniteGoodCover`, using the finite nerve model
  `integralSingularHomology_module_finite` (`FiniteGoodCoverNerveHomology.lean`) and the
  transport `singularChainComplex_homology_module_finite_of_finiteGoodCover`
  (`IntegralSingularHomologyFinite.lean`). Nonempty finite intersections of open *balls* (or of
  convex open sets) in a normed space are convex, hence contractible
  (`Convex.contractibleSpace` in Mathlib); so a finite cover by opens that are convex in a
  common chart is a finite good cover.
- Structure of `X^an`: compact (`complexPoint_compactSpace`,
  `Other/AlgebraicGeometry/ProjectiveAnalytification.lean`, via a closed embedding into
  `ℙ^N(ℂ)`), Hausdorff (`complexPoint_t2Space` instance,
  `ProjectiveAnalytificationHausdorff.lean`), hereditarily paracompact
  (`openParacompactSpace`), second countable; a complex manifold of dimension
  `d = dim X.left` with charts `localChart X d z` and the instance
  `isManifold_omega : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)`
  (`HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexManifold.lean`); a real `C¹` manifold
  instance `isRealManifold_one` (`Other/AlgebraicGeometry/ComplexManifoldOrientation.lean`),
  whose proof (`contDiffOn_localChart_transition` restricted to `ℝ` and `of_le`) gives the real
  `C^∞` instance with a one-line change. Every point has a basis of contractible open
  neighbourhoods (`exists_contractibleOpen_le`).
- Mathlib: the Whitney embedding for compact manifolds `exists_embedding_euclidean_of_compact`
  (a smooth closed embedding `M → EuclideanSpace ℝ (Fin n)` with injective differential), the
  inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`), smooth partitions of
  unity and bump coverings (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean`), thickenings of
  compact sets (`IsCompact.exists_cthickening_subset_open`), and functoriality/homotopy
  invariance of singular homology (`Mathlib/AlgebraicTopology/SingularHomology/`).
- The repository's Mayer–Vietoris and excision tools for singular chains
  (`SingularMayerVietoris.lean`, `RelativePairExcision.lean`, `SingularExcisionOpenCover.lean`),
  and `Module.Finite` is stable under direct summands and extensions
  (`Module.Finite.of_surjective`, `Module.Finite.of_injective` over the Noetherian ring `ℤ`).

## Routes

1. **Neighbourhood retract of a Whitney embedding (recommended).** Embed `M := X^an` as a
   compact smooth submanifold of `ℝ^N`. Prove a tubular-neighbourhood retraction: an open
   `W ⊇ M` and a continuous `r : W → M` with `r ∘ incl = id`. Then choose finitely many open
   balls covering `M` inside `W`; their union `W'` has a finite good cover (balls, convex
   intersections), so `H₂(W', ℤ)` is finitely generated, and `H₂(M, ℤ)` is a direct summand
   of it (`incl` has the left inverse `r|_{W'}`), hence finitely generated. The retraction is
   the only differential-geometric input: the map `(x, v) ↦ x + v` on the normal bundle is a
   local diffeomorphism along the zero section by the inverse function theorem and is injective
   on a uniform neighbourhood by compactness.
2. **Geodesically convex covers.** A Riemannian metric (from a partition of unity) has a positive
   convexity radius on a compact manifold; geodesic balls of smaller radius form a finite good
   cover. Mathlib has neither geodesics nor convexity radii; this route is longer.
3. **Algebraic covers.** Avoid the manifold structure by covering `X` by finitely many affine
   opens and using Mayer–Vietoris; this needs finite generation for smooth affine varieties
   (Andreotti–Frankel / Morse theory), which is not easier.

Do not weaken the statement (e.g. to rational coefficients, or to a hypothesis on `X`).

## Verification

```bash
lake build                                        # ~80 min from scratch; incremental afterwards
lake env lean Other/AlgebraicGeometry/<NewFile>.lean
lake env lean scripts/lefschetz_axiom_audit.lean
```

Add every new module to `Other.lean`.
