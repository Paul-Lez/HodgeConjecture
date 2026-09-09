# Statement of the Hodge Conjecture

This repo is work in progress towards stating the Hodge conjecture in Lean for the
[Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures).

The basis for this is a 50k lines of code autoformalisation due to Codex, of which 12k lines are
transitively used in the statement. The code is being cleaned up by
[Paul Lezeau](https://sites.google.com/view/paul-lezeau/home/),
[Yaël Dillies](https://www.su.se/english/profiles/y/yadi8568),
[Roktim Mascharak](https://roktimmascharak.github.io/) and
[Jack McCarthy](https://jackmccarthy.org/) during the Formal Conjectures workshop hosted
by Imperial College London 7-11 September 2026 thanks to a generous donation from Google DeepMind.

The short-term goal of this project is to be integrated to the Formal Conjectures repository.
The medium-term goal is for all the prerequisites to the conjecture to be upstreamed to
[Mathlib](https://github.com/leanprover-community/mathlib4).
The long-term goal is to have either a proof or a disproof of the Hodge conjecture in Mathlib.

The statement of the conjecture is in `HodgeConjecture/Statement.lean`.
The remaining content of the project is sorted into four folders:

- `HodgeConjecture/Mathlib`: Content that is on track to be upstreamed to Mathlib;
- `HodgeConjecture/Definitions`: Definitions used in the statement of the conjecture;
- `HodgeConjecture/Lemmas`: Supporting results needed by those definitions;
- `Other`: Results that aren't needed to state the conjecture but may be useful as sanity checks.

## Formalization guide

The repository includes a [Verso](https://github.com/leanprover/verso) guide that interleaves the
mathematics with elaborated Lean declarations. Once GitHub Pages is enabled, the deployed guide is
available at <https://paul-lez.github.io/HodgeConjecture/>. Build it locally with:

```bash
lake exe hodge-guide
python3 -m http.server 8000 -d _out/html-multi
```

Then open <http://localhost:8000>. The workflow in `.github/workflows/guide.yml` builds every pull
request and deploys pushes to `main` through GitHub Pages. In the repository settings, select
**GitHub Actions** as the Pages source once before the first deployment.

## Lefschetz (1, 1) development

`Other/AlgebraicGeometry/LefschetzOneOne.lean` states the rational Lefschetz `(1, 1)` theorem
and proves it assuming `HodgeConjecture`: every rational Hodge class of degree two is the class
of a rational divisor. This is the rational algebraicity statement, not the stronger integral
statement about first Chern classes of line bundles.

See [the Lefschetz handoff](docs/LEFSCHETZ_HANDOFF.md) for the exact goal, stopping point,
remaining proof obligations, and verification commands.

The unconditional proof is in progress. `Other/AlgebraicGeometry/HolomorphicExponentialSequence.lean`
constructs and proves the short exact sequence `0 → ℤ → 𝒪 → 𝒪ˣ → 0` on the analytic
complex-point space, using local holomorphic logarithms.
`Other/AlgebraicGeometry/HolomorphicFirstChernClass.lean` constructs its connecting map
`H¹(𝒪ˣ) → H²(ℤ)` and proves that its image is the kernel of `H²(ℤ) → H²(𝒪)`.
`Other/AlgebraicGeometry/HolomorphicHodgeProjection.lean` proves that degree-two rational
Hodge classes vanish under the de Rham projection to `H²(𝒪)`.
`Other/AlgebraicGeometry/AnalyticSheafCohomologyExt.lean` identifies the two cohomology
presentations and proves compatibility with coefficient maps.
`Other/AlgebraicGeometry/HolomorphicIntegralHodgeClass.lean` combines these results: an integral
degree-two class whose rational image is a Hodge class lifts through `H¹(𝒪ˣ) → H²(ℤ)`,
without assuming the Hodge conjecture.
`Other/AlgebraicGeometry/HolomorphicUnitExtension.lean` represents these lifts by sheaf extensions;
`Other/AlgebraicGeometry/HolomorphicLineBundleOfExtension.lean` constructs their holomorphic
line bundles from the resulting transition functions, with complex dimension one in each fiber.
`Other/AlgebraicGeometry/HolomorphicLineBundleModule.lean` constructs their sheaves of
holomorphic sections as modules over the holomorphic structure sheaf.
`Other/AlgebraicGeometry/HolomorphicLineBundleCoordinates.lean` constructs the local coordinate
isomorphisms, and `Other/AlgebraicGeometry/HolomorphicLineBundleInvertible.lean` proves that
these section sheaves are invertible. The rank-one sheaf interfaces are adapted from
[Tau Ceti](Other/TauCeti/README.md).
`Other/AlgebraicGeometry/RegularFunctionsHolomorphic.lean` proves that evaluation of regular
functions gives a morphism from the algebraic structure sheaf to the direct image of the
holomorphic structure sheaf. `Other/AlgebraicGeometry/AnalytificationModules.lean` uses this
map to construct analytification of algebraic sheaves of modules, with its adjunction and
its identification of the analytified structure sheaf with the holomorphic one.
`Other/AlgebraicGeometry/HolomorphicLocallyRingedSpace.lean` proves that holomorphic stalks
are local rings and constructs the natural morphism of locally ringed spaces to the
algebraic scheme, with the expected map on residue-field values.
Lifting rational classes to integral classes after scaling, algebraizing the line bundles,
and comparing their classes with the constructed algebraic divisor cycle-class map remain
unfinished.
