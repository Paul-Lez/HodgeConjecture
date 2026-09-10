# Handoff: projective GAGA for line bundles (`AnalyticLineBundlesAlgebraize`)

This document scopes one of the three remaining obligations for the unconditional rational
Lefschetz `(1, 1)` theorem (see [LEFSCHETZ_HANDOFF.md](LEFSCHETZ_HANDOFF.md)). It is written
so that the work can be done in isolation: nothing here requires the exponential sequence,
Hodge classes, or cycle classes.

## The exact target

In [`Other/AlgebraicGeometry/LefschetzOneOneReduction.lean`](../Other/AlgebraicGeometry/LefschetzOneOneReduction.lean):

```lean
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

def AnalyticLineBundlesAlgebraize : Prop :=
  ∀ M : SheafOfModules.{0} (holomorphicRingSheaf X (dim X.left)),
    TauCeti.SheafOfModules.IsInvertible M →
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ M)
```

**Deliverable:** a theorem

```lean
theorem analyticLineBundlesAlgebraize (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : AnalyticLineBundlesAlgebraize X
```

with no `sorry`, no new `axiom`, and `#print axioms` reporting only `propext`,
`Classical.choice`, `Quot.sound`. Add it to `scripts/lefschetz_axiom_audit.lean`.
`hasAlgebraicModel_of_analyticLineBundlesAlgebraize` already turns it into the form used by
`RationalLefschetzOneOne.of_obligations`. Do not weaken the statement (e.g. to curves, to
`L` merely locally free of unspecified rank, or to an isomorphism after pushforward): the
consumer needs an invertible algebraic `L` and an isomorphism of analytic sheaves of modules
with the analytification defined below.

If it is convenient, the isomorphism may be produced for the *general* invertible `M` as
stated; the consumer only ever applies it to `E.sectionSheafOfModules` for a
`HolomorphicUnitExtension E` (which is invertible by `sectionSheafOfModules_isInvertible`),
so a proof specialised to those sheaves via `HasAlgebraicModel X` is also acceptable, but the
general statement is cleaner and does not need the extension machinery.

## The objects involved, and where they are defined

All names are in namespace `AlgebraicGeometry.ComplexPoint` unless indicated. Throughout,
`d = dim X.left` (`TopologicalSpace.dim`), and `[SmoothOfRelativeDimension d X.hom]` is
available for smooth integral `X` (`DimensionedSmoothProjectiveComplexVariety.ofOver`).

### The analytic space

- `ComplexPoint X := Point ℂ X` (`HodgeConjecture/Definitions/AlgebraicGeometry/Points.lean`):
  the ℂ-points `Over.mk (𝟙 (Spec ℂ)) ⟶ X`, with `Point.analyticTopology`. Every file below
  installs `local instance : TopologicalSpace (ComplexPoint X) := Point.analyticTopology`
  (give each such instance a unique name).
- `Point.underlying : ComplexPoint X → X.left`, `Point.evaluate U a : ComplexPoint X → ℂ`
  (value of a regular function `a : Γ(X.left, U)`), `Point.overOpen U` (points over an
  algebraic open).
- Charts: `localChart X d z : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)` and the
  instances `ChartedSpace (Fin d → ℂ) (ComplexPoint X)` and
  `isManifold_omega : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoint X)`
  (`HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexManifold.lean`). Transition maps are
  holomorphic; regular functions are holomorphic (`contMDiffAt_evaluate`, in
  `Other/AlgebraicGeometry/RegularFunctionsHolomorphic.lean`).
- Topology for projective `X`: compactness `complexPoint_compactSpace`
  (`Other/AlgebraicGeometry/ProjectiveAnalytification.lean`, via a closed embedding into
  `ℙ^N(ℂ)` from a `ProjectiveSpace.Presentation`), paracompactness of every open
  `openParacompactSpace` (`ProjectiveAnalytificationParacompact.lean`), second countability
  (`ProjectiveAnalytificationSecondCountable.lean`).

### The holomorphic structure sheaf

- `holomorphicFunctionSheaf X d : TopCat.Sheaf CommRingCat (TopCat.of (ComplexPoint X))`
  (`HodgeConjecture/Definitions/AlgebraicGeometry/ComplexAnalyticSheaf.lean`): sections over
  `U` are `C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯` (Mathlib `ContMDiffMap`), i.e. functions analytic in
  the constructed charts. `OpenHolomorphicFunctions X d U` is the same ring
  (`AnalyticDifferentialForms.lean`).
- `holomorphicRingSheaf X d : Sheaf (Opens.grothendieckTopology _) RingCat`
  (`Other/AlgebraicGeometry/HolomorphicLineBundleModule.lean`): the same sheaf with values
  in `RingCat`. Sheaves of modules over it are `SheafOfModules.{0} (holomorphicRingSheaf X d)`.
- Stalks are local rings: `holomorphicStalk_isLocalRing`, with
  `holomorphicStalk_isUnit_iff` (a germ is a unit iff its value is nonzero) and the
  evaluation map `holomorphicStalkEvaluation`
  (`Other/AlgebraicGeometry/HolomorphicLocallyRingedSpace.lean`). The locally ringed space
  is `holomorphicLocallyRingedSpace X d`, and `analytificationToAlgebraic X d :
  holomorphicLocallyRingedSpace X d ⟶ X.left.toLocallyRingedSpace` is the natural morphism.

### Algebraic modules and the analytification functor

- `X.left.Modules` is Mathlib's `Scheme.Modules`, definitionally
  `SheafOfModules.{0} X.left.ringCatSheaf` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`).
  Instances for the generic `SheafOfModules` category sometimes need to be stated explicitly
  for `X.left.Modules`; the universe `.{0}` is deliberate.
- `underlyingContinuousMap X : TopCat.of (ComplexPoint X) ⟶ X.left.carrier`,
  `analyticOpen X U := (Opens.map (underlyingContinuousMap X)).obj U`,
  `regularToHolomorphicSheaf X d : X.left.sheaf ⟶ pushforward (holomorphicFunctionSheaf X d)`
  (evaluation of regular functions), and its `RingCat` form `regularToHolomorphicRingSheaf X d`
  (`RegularFunctionsHolomorphic.lean`, `AnalytificationModules.lean`).
- **`moduleAnalytification X d : X.left.Modules ⥤ SheafOfModules (holomorphicRingSheaf X d)`**
  is `SheafOfModules.pullback (regularToHolomorphicRingSheaf X d)` — Mathlib's inverse image
  of sheaves of modules along a morphism of ringed sites (inverse image followed by extension
  of scalars). Its right adjoint is `holomorphicModulePushforward X d`, the adjunction is
  `moduleAnalytificationAdjunction X d`, and
  `moduleAnalytificationUnitIso X d : (moduleAnalytification X d).obj (unit _) ≅ unit _`
  identifies the analytification of `𝒪_X` with `𝒪^an`
  (`Other/AlgebraicGeometry/AnalytificationModules.lean`). Mathlib's
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean` shows pullback sends free
  sheaves to free sheaves (`pullbackObjFreeIso`, `freeFunctorCompPullbackIso`).

### Invertible sheaves

- `TauCeti.SheafOfModules.IsInvertible M` (`Other/TauCeti/SheafOfModules/Invertible.lean`):
  there is Mathlib `LocalGeneratorsData` for `M` whose local free presentations are
  isomorphisms with exactly one generator each. It implies Mathlib's `M.IsLocallyFree`.
- `TauCeti.SheafOfModules.LocalTrivializations M` (`LocalTriviality.lean`): a covering family
  of opens with isomorphisms `free PUnit ≅ M.over U`; `LocalTrivializations.isInvertible`
  produces `IsInvertible`, and `freePUnitIsoUnit` identifies `free PUnit` with the structure
  sheaf. This is the easiest way to *prove* invertibility of a constructed sheaf; see
  `Other/AlgebraicGeometry/HolomorphicLineBundleInvertible.lean` for a worked example.
- The provenance of the Tau Ceti files is in `Other/TauCeti/README.md`.

## Implemented base cases

[`Other/AlgebraicGeometry/GAGALineBundles.lean`](../Other/AlgebraicGeometry/GAGALineBundles.lean)
now supplies the formal endpoint for globally trivial bundles and proves the complete statement
when the analytification is a one-point space. In particular:

- restriction of module sheaves to the top open is an equivalence;
- an invertible sheaf on a nonempty subsingleton space is globally trivial;
- `analyticLineBundlesAlgebraize_of_subsingleton` algebraizes all line bundles in that case; and
- `analyticLineBundlesAlgebraize_of_dimension_eq_zero` proves `AnalyticLineBundlesAlgebraize X`
  for smooth projective integral `X` with `dim X.left = 0`.
- the current Tau Ceti finite-presentation theorem has been ported, proving that both analytic
  and algebraic invertible module sheaves in the target are finitely presented; and
- Tau Ceti's restriction/refinement interface for local trivialization atlases has been ported as
  groundwork for local comparisons; and
- `Other/AlgebraicGeometry/AnalytificationRestriction.lean` now proves the full restriction
  comparison `moduleAnalytificationOverIso` and uses it to prove
  `moduleAnalytification_isInvertible`. Thus analytification of an algebraic line bundle is now
  formally known to be an analytic line bundle on the pulled-back trivializing cover.
- `Other/AlgebraicGeometry/ProjectiveSpectrumNegativeTwist.lean` constructs the negative twists
  `𝒪(-n)` on a general `ℕ`-graded projective spectrum as sheaves of modules made from local
  homogeneous fractions of degree `-n`. It proves closure under regular scalars and restriction,
  the sheaf condition, the canonical base case `𝒪(0) ≅ 𝒪`, and chartwise triviality on
  every basic open `D₊(q)` by the mutually inverse operations of multiplying and dividing by
  `q`. A family of degree-`n` basic opens covering `Proj` therefore makes `𝒪(-n)` invertible in
  Tau Ceti's sense, including after transport to Mathlib's `Scheme.Modules` presentation.
  This supplies the algebraic twist primitive needed for a Serre-presentation route; an
  intrinsic chartwise analytic description and the analytic Serre-presentation theorem remain.
- `Other/AlgebraicGeometry/ProjectiveSpaceNegativeTwist.lean` specializes the construction to
  the universal homogeneous coordinate ring used by the existing complex-projective-space
  model. The theorem `universalNegativeTwist_isInvertible` proves that every `𝒪(-n)` there is
  an actual invertible object of `Scheme.Modules`, using the standard coordinate basic-open
  cover (and positive powers of those coordinates for positive `n`).
- `Other/AlgebraicGeometry/InvertiblePullback.lean` proves that inverse image along an arbitrary
  morphism of (small) schemes preserves Tau Ceti invertibility. It pulls the trivializing cover
  back topologically and compares module restriction with pullback around each Cartesian square
  of open subschemes.
- Consequently `complexProjectiveNegativeTwist_isInvertible` supplies invertible algebraic
  `𝒪(-n)` on the actual base-changed scheme `ℙⁿ_ℂ`, not merely on the universal integral
  `Proj` model.
- `Other/AlgebraicGeometry/ProjectivePresentationTwist.lean` pulls these twists back along an
  explicit projective presentation of `X` and analytifies them. Thus both the algebraic
  presentation-induced `𝒪_X(-n)` and its analytic image are now concrete invertible module
  sheaves in the exact categories used by the target.
- `Other/TauCeti/SheafOfModules/FiniteLocalTriviality.lean` extracts a finite subatlas from any
  local trivialization atlas on a compact space, retaining the actual local isomorphisms.
  `Other/AlgebraicGeometry/AnalyticLineBundleFiniteAtlas.lean` applies this to arbitrary
  invertible holomorphic modules on projective `X`.
- `Other/TauCeti/SheafOfModules/CechTransition.lean` packages the change-of-frame
  automorphisms on common refinements and proves their identity, inverse, and cocycle laws.
- `Other/AlgebraicGeometry/AnalyticSerreGeneration.lean` packages finite algebraic and analytic
  twist sums, proves that analytification identifies them, and records the exact analytic Serre
  generation property for every finitely presented analytic module. Generation is proved stable
  under quotients; the general generation theorem itself remains the hard analytic input.
- `Other/AlgebraicGeometry/GAGATwistPresentation.lean` proves the categorical endpoint: an
  analytic module with a two-term twist presentation whose relation map is algebraic is
  canonically the analytification of the corresponding algebraic cokernel. Analytification
  preserves this cokernel because it is a left adjoint.
- `Other/AlgebraicGeometry/ProjectiveHolomorphicFunctions.lean` proves by maximum modulus that
  global holomorphic functions on a preconnected projective analytification are constant, and
  hence that evaluation from algebraic global functions is surjective in degree zero.
  `UnitEndomorphismComparison.lean` upgrades this to surjectivity on endomorphisms of the tensor
  unit using the analytification/pushforward adjunction.
- `Other/AlgebraicGeometry/FiniteFreeAnalytification.lean` extends that comparison entrywise:
  it builds coordinate projections and matrices directly for Mathlib's chosen free-sheaf
  coproducts, proves matrix extensionality, and proves that analytification is full on maps
  between arbitrary finite free module sheaves (under preconnectedness). Thus the complete
  degree-zero finite-matrix case of relation algebraization is now formalized.
- `Other/AlgebraicGeometry/ProjectiveAnalytification.lean` now also proves that complex
  projective space is path connected: the real unit sphere in its nonzero complex coordinate
  space is path connected, and the existing sphere-to-projectivization and homogeneous-coordinate
  maps are continuous surjections. Consequently the scalar, finite-free, and degree-zero
  comparison theorems need no separate preconnectedness premise on the ambient projective space
  itself. Passing connectedness to an arbitrary integral closed projective subvariety still
  needs a separate global argument.

The remaining decisive inputs are therefore analytic Serre generation (including finite
presentation of the first kernel), algebraization of relation morphisms between differently
twisted summands via the relevant nonzero-degree `H⁰` comparisons, connectedness (or a
componentwise replacement) for the degree-zero comparison, and descent/reflection of
invertibility for the resulting algebraic cokernel. None is present in Mathlib, this repository,
or Tau Ceti.

These declarations are included in `scripts/lefschetz_axiom_audit.lean` and use only `propext`,
`Classical.choice`, and `Quot.sound`. They do not address the positive-dimensional gluing step:
there an invertible analytic sheaf need not be globally trivial.

## Mathematical routes, and what is missing

The statement is Serre's GAGA (essential surjectivity of analytification) restricted to
invertible sheaves on a smooth projective variety. Nothing towards its analytic input exists
in Mathlib or in this repository: there are no coherent analytic sheaves, no Oka coherence, no
Cartan Theorems A/B, no finiteness of coherent cohomology on compact complex manifolds, and no
Kodaira embedding. Whichever route is chosen, that theory has to be built; the choice should
be made on the basis of what is smallest for line bundles.

1. **Classical GAGA.** Prove finiteness and the comparison `H^q(X, F) ≅ H^q(X^an, F^an)` for
   coherent `F` on `ℙ^N`, then essential surjectivity by the Serre/Chow induction. This is the
   most general and the largest.
2. **Line bundles through the exponential sequence on both sides.** Algebraic and analytic
   Picard groups both sit in exponential-type sequences; comparing them needs the algebraic
   `H^1(X, 𝒪_X) → H^1(X^an, 𝒪^an)` comparison (Hodge theory / Dolbeault plus finiteness) — not
   smaller in practice.
3. **Meromorphic sections plus Chow.** Show an invertible analytic sheaf on a projective
   manifold has a nonzero meromorphic section (Kodaira vanishing/Riemann–Roch-type input) and
   that its divisor is algebraic (Chow's theorem). Also heavy.

Whatever the route, the proof must end with an *isomorphism of sheaves of modules over
`holomorphicRingSheaf X d`* between `(moduleAnalytification X d).obj L` and `M`, so the
interface facts above (`moduleAnalytificationUnitIso`, `pullbackObjFreeIso`, local
trivialisations) will be needed at the end regardless.

## Tau Ceti status checked on 2026-09-10

Tau Ceti main at commit `6b10e2573adea2abab44b08630b9c69e73048090` has advanced the
algebraic line-bundle side beyond the older snapshot originally vendored here. In particular it
has restriction/refinement of local trivialization atlases, finite presentation of invertible
sheaves, tensor-product closure, scheme-level line-bundle packaging, Cartier local equations and
transition units, and a Weil-divisor sheaf whose locally principal divisors give invertible
sheaves (currently developed most fully in dimension at most one).

The current Tau Ceti tree and its open branches contain no GAGA, scheme analytification, Chow
theorem, coherent analytic sheaf, or meromorphic-function-sheaf development. Thus its divisor
machinery can supply the algebraic `𝒪_X(D)` endpoint of the meromorphic-section route, but it
does not supply either hard analytic premise: producing a meromorphic section of an arbitrary
analytic line bundle, or proving that its analytic divisor is algebraic. The generally useful
restriction and finite-presentation files have been adapted into `Other/TauCeti/SheafOfModules`;
porting the much larger divisor stack before one of those analytic premises exists would not by
itself advance the exact target.

## Completed interface lemmas and remaining warm-up

These are true, useful, and independent of the hard analysis; they also validate the
interface before the main construction is attempted.

- `moduleAnalytification` preserves invertibility: proved as
  `moduleAnalytification_isInvertible`, using the local regular-to-holomorphic pullback,
  `moduleAnalytificationOverIso`, and Tau Ceti `LocalTrivializations`.
- The analytification of `Γ(L, U)` for a free `L` on an algebraic open `U` is computed by the
  formula `𝒪^an ⊗ Γ(L, U)` on `analyticOpen X U`; `moduleAnalytificationUnitIso` is the rank-one
  case.
- For an algebraic open `U` with `L|_U` trivial, the analytification is trivial on
  `analyticOpen X U`.

## Verification

```bash
lake build                                        # ~80 min from scratch; incremental afterwards
lake env lean Other/AlgebraicGeometry/<NewFile>.lean
lake env lean scripts/lefschetz_axiom_audit.lean
```

Add every new module to `Other.lean`. Keep `set_option backward.isDefEq.respectTransparency
false in` local to the declarations that need it, following the existing files.
