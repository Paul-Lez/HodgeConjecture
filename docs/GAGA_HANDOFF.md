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
or Tau Ceti. **See the re-assessment below (2026-09-10) for a corrected weighting of these four
inputs and for two constructive prerequisites that must come first.**

These declarations are included in `scripts/lefschetz_axiom_audit.lean` and use only `propext`,
`Classical.choice`, and `Quot.sound`. They do not address the positive-dimensional gluing step:
there an invertible analytic sheaf need not be globally trivial.

## Added 2026-09-10: the several-variables polynomial-growth Liouville theorem

[`Other/AlgebraicGeometry/PolynomialGrowthLiouville.lean`](../Other/AlgebraicGeometry/PolynomialGrowthLiouville.lean)
proves, with no `sorry` and no new axiom (checked in `scripts/lefschetz_axiom_audit.lean`), the
analytic theorem at the bottom of the `H⁰` half of GAGA for twists. All names live in namespace
`Complex.PolynomialGrowth`.

- `exists_isHomogeneous_eval_eq_diag`: the diagonal restriction `z ↦ T (z, …, z)` of a continuous
  `k`-multilinear map on `ℂⁿ` is `MvPolynomial.eval z P` for a `P` that is *homogeneous* of
  degree `k` (expansion in the standard basis via `MultilinearMap.map_sum`).
- `iteratedDeriv_line_eq_zero`: Cauchy's estimates along complex lines. If `f` is entire on `ℂⁿ`
  with `‖f z‖ ≤ C · (1 + ‖z‖) ^ m`, then `iteratedDeriv k (fun t ↦ f (t • z)) 0 = 0` for `k > m`.
- `iteratedDeriv_line_eq_iteratedFDeriv`: those line derivatives are the diagonal values
  `iteratedFDeriv ℂ k f 0 (z, …, z)` of the iterated derivative of `f` at the origin (chain rule
  along `ContinuousLinearMap.smulRight`, so no several-variables power series are needed).
- `exists_isHomogeneous_sum_eq`: such an `f` is the sum of its first `m + 1` diagonal Taylor
  terms, each of which is a homogeneous polynomial function of its degree.
- **`exists_mvPolynomial_eq_of_growth`**: an entire `f : ℂⁿ → ℂ` with `‖f z‖ ≤ C · (1 + ‖z‖) ^ m`
  satisfies `f = MvPolynomial.eval · P` for some `P` with `P.totalDegree ≤ m`.
- `analyticOnNhd_eval`, `norm_eval_le_of_totalDegree`, `analyticOnNhd_and_growth_iff`: the
  converse and hence the exact characterisation — the entire functions of polynomial growth of
  order `m` on `ℂⁿ` are *exactly* the polynomial functions of total degree at most `m`.
- `exists_eq_const_of_bounded_of_analytic`: degree `0` recovers Liouville on `ℂⁿ`.
- `exists_mvPolynomial_eq_of_contMDiff_of_growth`: the same statement phrased with
  `ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω f`, i.e. with the exact smoothness predicate that
  `holomorphicFunctionSheaf` uses for its sections, so that a chart restriction of a holomorphic
  section can be fed in directly.
- `norm_cons_le_of_homogeneous_of_bounded_sphere` and
  `exists_mvPolynomial_eq_of_homogeneous_of_bounded_sphere`: the bridge from *compactness*. A
  function `F` on `ℂ^{N+1}` that is homogeneous of degree `m` (`F (t • x) = t ^ m * F x`) and
  bounded on the unit sphere satisfies `‖F (Fin.cons 1 z)‖ ≤ C · (1 + ‖z‖) ^ m`; if in addition
  its restriction to the chart `x₀ = 1` is entire, that restriction is a polynomial of total
  degree at most `m`.

This is not in Mathlib: Mathlib's Liouville theorems (`Differentiable.apply_eq_apply_of_bounded`,
`Complex.liouville_theorem_aux`) cover bounded functions only, and it has no polynomial-growth or
several-variables statement. The proof uses only Mathlib's one-variable Cauchy estimate
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `Complex.taylorSeries_eq_of_entire`
and `ContinuousLinearMap.iteratedFDeriv_comp_right`; the hypothesis is `AnalyticOnNhd ℂ f univ`
rather than `Differentiable ℂ f`, which is the honest hypothesis in several variables (Mathlib
has no Hartogs theorem) and is exactly what the repository's `C^ω` sections provide.

The last two items are the shape in which this enters `H⁰(ℙᴺ, 𝒪(m))`: a global holomorphic
section of `𝒪(m)^an`, read in homogeneous coordinates, is a degree-`m` homogeneous function on
the punctured cone, bounded on the unit sphere because `ℙᴺ(ℂ)` is compact; its restriction to an
affine chart is entire; the theorem makes that restriction a polynomial of total degree at most
`m`; homogenising back recovers a degree-`m` form. What is *not* yet bridged is the sheaf model:
see the re-assessment below.

## Critical re-assessment of the Serre-presentation reduction (2026-09-10)

`analyticLineBundlesAlgebraize_of_serreData` is a correct and honest theorem, and its categorical
content (`GAGATwistPresentation.lean`) is complete. But the four hypotheses it consumes are not
of comparable size, and one of them is much larger than the surrounding prose suggested. The
following corrections should be read together with the definitions in `GAGASerreReduction.lean`;
none of them requires changing the existing statements, only the plan for discharging them.

**(iii) `AnalyticTwistRelationsAlgebraize` is itself full `H⁰`-GAGA for all twists of `𝒪_X`.**
The proposition quantifies over morphisms `analyticSum X d P a r ⟶ analyticSum X d P b s` for
*arbitrary* `a, b, r, s : ℕ`. Since the presentation-induced twists are invertible
(`ProjectiveTwist.analytic_isInvertible`), such a morphism is an `r × s` matrix of global
sections of `𝒪_X(a - b)^an`, and its algebraic counterpart is an `r × s` matrix of global
sections of `𝒪_X(a - b)`. So (iii) is equivalent to:

> for every `k ∈ ℤ`, the comparison `H⁰(X, 𝒪_X(k)) → H⁰(X^an, 𝒪_X(k)^an)` is surjective,

with `k = a - b` ranging over all of `ℤ` (the negative `k` instances are the vanishing statement
`H⁰(X^an, 𝒪_X(k)^an) = 0`). This is not circular with respect to the target — the target is
essential surjectivity of analytification on invertible sheaves, which is strictly stronger — but
it is *not* a small or elementary input: it is the degree-zero half of Serre's comparison
theorem, for a subvariety `X ⊆ ℙᴺ` and for all twists at once, and on `X` it is of the same order
of difficulty as (i). The earlier description of it as "an `H⁰` comparison" that the
degree-zero finite-free case in `FiniteFreeAnalytification.lean` begins to discharge understates
it: that file settles only `k = 0`, where the analytic side is the constants.

**Consequence: the reduction should be reorganised to live on `ℙᴺ`, not on `X`.** On `ℙᴺ` both
sides of (iii) are explicit — `H⁰(ℙᴺ, 𝒪(m))` is the degree-`m` forms and, by the theorem added
above, so is `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an)` once the analytic twist has a chartwise model. On a
subvariety they are not. The classical organisation therefore is:

1. prove analytic Serre generation and the `H⁰` comparison **on `ℙᴺ`**;
2. transport the problem for `X ⊆ ℙᴺ` to `ℙᴺ` along the closed immersion `i` of
   `ProjectiveSpace.Presentation`, by applying (i)–(iv) to `i_*M` rather than to `M`, and
   recovering `M` from `i^* i_* M ≅ M`.

Step 2 needs two things that are absent from this repository and from Mathlib: exactness of
analytic pushforward along a closed immersion of analytic spaces, and its compatibility with
`moduleAnalytification` (`i^an_* (M^an) ≅ (i_* M)^an`). Those should be stated as explicit
`def … : Prop` obligations if the reorganised route is taken; deducing (iii) on `X` from (iii)
on `ℙᴺ` *without* them is not possible, because `H⁰(X, 𝒪_X(k))` is not a subquotient of
`H⁰(ℙᴺ, 𝒪(k))` in any way visible to the current interface.

**(i) `AnalyticSerreGeneration` presupposes coherence theory.** As stated it asks that every
finitely presented analytic module be a quotient of `𝒪(-n)^r`. That is Cartan's Theorem A for
the compact space `ℙᴺ(ℂ)` together with the ampleness of `𝒪(1)`; its usual proof needs Oka
coherence and Cartan's Theorem B. Nothing of that exists here.

**(ii) `AnalyticTwistPresentationKernelsFinite` is Oka coherence.** Finite presentation of the
kernel of a map of finitely presented analytic modules is exactly the coherence of `𝒪^an`; it
cannot be obtained from the categorical interface.

**(iv) `AlgebraicTwistCokernelsReflectInvertibility` needs a stalk comparison.** The intended
proof is faithful flatness of `𝒪^an_z` over `𝒪_{X, i(z)}`. Two separate ingredients are missing:
an identification of the stalk of `(moduleAnalytification X d).obj L` at `z` with
`𝒪^an_z ⊗_{𝒪_{X, i(z)}} L_{i(z)}` (the repository has `analytificationToAlgebraic` and
`analytification_stalkMap_comp_evaluation`, but no stalkwise base-change formula for modules),
and flatness itself.

**Missing prerequisites that are not any of (i)–(iv), and that block *any* analytic input.**
Two purely constructive things are absent, and until they exist no statement about
`H⁰(X^an, 𝒪(k)^an)` can even be *stated in computable form*, however much complex analysis is
available.

*(P1) No standard affine chart of `ℙᴺ(ℂ)^an`.* `ProjectiveAnalytification.lean` has the
homogeneous-coordinate machinery — `sphereToProjectivization`, `vectorToComplexPoint`,
`projectivizationToComplexPoint` (continuous, injective and surjective, but **never packaged as
a homeomorphism**), `nonzeroVectorChart i = {v | v i ≠ 0}` with `isOpen_nonzeroVectorChart` and
`iUnion_nonzeroVectorChart`, and `chartAffineComplexPointMap i` from
`ComplexPoint (𝔸^{Fin (N+1)}_ℂ)` (note: index type `Fin (N + 1)`, not `Fin N`), proved only
continuous. There is **no** homeomorphism between the open set `{x_i ≠ 0} ⊆ ComplexPoint ℙᴺ`
and `Fin N → ℂ`. The only genuine coordinate homeomorphism in the repository is for affine
space, `ComplexPoint.affineSpaceHomeomorph`
(`HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexAffineSpace.lean`). Note also that
`localChart X d z` (`HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexManifold.lean`) is built
from *étale* coordinates for a general smooth `X` and has nothing to do with homogeneous
coordinates, so it cannot serve as the chart here.

*(P2) No chartwise model of the analytic twist.* `ProjectiveTwist.analytic X d P n` is *defined*
as `(moduleAnalytification X d).obj` of the algebraic twist, i.e. as a sheafified pullback; the
only value of `moduleAnalytification` ever computed is on the unit
(`moduleAnalytificationUnitIso`), and `AnalytificationRestriction.moduleAnalytificationOverIso`
only compares restrictions. So the first two concrete tasks on the critical path are:

> **Task A.** Package `{x_i ≠ 0} ⊆ ComplexPoint ℙᴺ(ℂ)` as biholomorphic to `Fin N → ℂ`.
> *Step 1 is done*: `ComplexProjectiveSpace.projectivizationHomeomorph`
> ([`Other/AlgebraicGeometry/ProjectiveAnalytificationHomeomorph.lean`](../Other/AlgebraicGeometry/ProjectiveAnalytificationHomeomorph.lean))
> promotes `projectivizationToComplexPoint` to a homeomorphism
> `Projectivization ℂ (CoordinateSpace N) ≃ₜ ComplexPoint ℙᴺ`, using
> `Continuous.homeoOfEquivCompactToT2` with `instCompactSpace` and
> `instT2SpaceProjectiveSpaceComplexPoint`. Every topological question about `ℙᴺ(ℂ)^an` can now
> be transported to the concrete quotient model.
> *Step 2 is also done* (2026-09-11): see the progress section below —
> `ComplexProjectiveSpace.chartHomeomorph` and `complexPointChartHomeomorph` in
> [`ProjectiveAnalytificationCharts.lean`](../Other/AlgebraicGeometry/ProjectiveAnalytificationCharts.lean).
> What is *not* done is their holomorphic compatibility with the repository's `localChart` /
> `ChartedSpace` structure; that is gap (G1) below, and it is blocked by (G0).
>
> **Task B.** Construct the sheaf of holomorphic sections of `𝒪(-n)` on `ℙᴺ(ℂ)^an` directly — as
> degree `-n` homogeneous holomorphic functions on the punctured cone, or by gluing the charts of
> Task A with transition functions `(x_i / x_j)^n` — and produce an isomorphism with
> `(moduleAnalytification _ _).obj (ComplexProjectiveSpace.negativeTwist N n)`.

Task B mirrors, on the analytic side, what `ProjectiveSpectrumNegativeTwist.lean` already does
algebraically (`IsFractionOrZero`, `sectionModule n U`, `HomogeneousShift.basicOpenUnitIso`
trivialising on the basic opens `D₊(x_i)`), and it is purely constructive: no hard analysis, but
a substantial amount of sheaf bookkeeping. Once A and B exist,
`exists_mvPolynomial_eq_of_homogeneous_of_bounded_sphere` computes `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an)` for
`m ≥ 0`, with boundedness on the sphere supplied by `instCompactSpaceProjectiveSpaceComplexPoint`
and `surjective_sphereToProjectivization`.

**Corrected list of remaining inputs.** In dependency order, and stated for the ambient `ℙᴺ`
wherever possible:

0. *(topology: **done** 2026-09-11)* the standard charts `{x_i ≠ 0} ≅ ℂᴺ` of `ℙᴺ(ℂ)^an` as
   homeomorphisms — `ComplexProjectiveSpace.chartHomeomorph`, `complexPointChartHomeomorph`.
   Their *holomorphic* compatibility with the repository's atlas is gap (G1), blocked by (G0):
   `ℙᴺ_ℂ` carries no `SmoothOfRelativeDimension` instance in this repository, so its holomorphic
   structure sheaf does not yet exist;
1. *(constructive, no analysis)* gap (G2): a chartwise/holomorphic model of `𝒪(-n)^an` on
   `ℙᴺ(ℂ)` with transition units `(x_i/x_j)^n`, and its comparison with `moduleAnalytification`
   of the algebraic twist;
2. *(analysis **done** 2026-09-11 at function level; sheaf level is gap (G3))*
   `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an) = H⁰(ℙᴺ, 𝒪(m))` for `m ≥ 0` follows from
   `Complex.PolynomialGrowth.analyticOnNhd_homogeneous_iff`; the `m < 0` vanishing additionally
   needs a Hartogs/maximum-modulus argument and is false for `N = 0`;
3. *(hard analysis)* Oka coherence of `𝒪^an`, giving (ii);
4. *(hard analysis)* Cartan A/B on `ℙᴺ(ℂ)`, giving (i);
5. *(sheaf theory)* exactness and analytification-compatibility of pushforward along the closed
   immersion `X ↪ ℙᴺ`, to transport (i)–(iii) from `ℙᴺ` to `X`;
6. *(commutative algebra)* the stalkwise base-change formula for `moduleAnalytification` plus
   flatness of `𝒪_{X,x} → 𝒪^an_z`, giving (iv);
7. *(topology, only if the degree-zero comparison is used on `X` itself)* connectedness of
   `X^an` for integral `X`. This is a genuine theorem (irreducible ⇒ analytically connected) and
   should not be assumed; `ProjectiveTwistDegreeZeroRelations.analyticTwistRelationsAlgebraize_zero`
   still carries `[PreconnectedSpace (ComplexPoint X)]` for this reason. If the reorganisation
   onto `ℙᴺ` above is carried out it is not needed, since `ℙᴺ(ℂ)` is path connected
   (`ComplexProjectiveSpace.instPathConnectedSpace`).

## Progress 2026-09-11: affine charts on `ℙᴺ(ℂ)` and the cone-function comparison

Two further files, both `sorry`-free and axiom-clean (added to `scripts/lefschetz_axiom_audit.lean`).

### Item 0 — the standard affine charts (topological half: **done**)

[`Other/AlgebraicGeometry/ProjectiveAnalytificationCharts.lean`](../Other/AlgebraicGeometry/ProjectiveAnalytificationCharts.lean),
namespace `AlgebraicGeometry.ComplexProjectiveSpace`:

- `projMk : {v : CoordinateSpace N // v ≠ 0} → Projectivization ℂ (CoordinateSpace N)`, with
  `isQuotientMap_projMk`, `preimage_image_projMk`
  (`projMk ⁻¹' (projMk '' W) = ⋃ a : ℂˣ, (a • ·) ⁻¹' W`), `isOpenMap_projMk` and
  **`isOpenQuotientMap_projMk`**. This is the missing topological input the previous handoff
  asked for; Mathlib puts no topology on `Projectivization` at all.
- `chartRatio i v j = v (i.succAbove j) / v i` and `chartRatio_smul` — note the formula is
  scale-invariant *everywhere*, including off the chart, because `x / 0 = 0` in Lean, so it
  descends through `Projectivization.lift` to `chartMap i` with no side condition.
- `chartPoint i z = [i.insertNth 1 z]`, `chartSet i = Set.range (chartPoint i)`,
  `preimage_chartSet : projMk ⁻¹' chartSet i = nonzeroVectorChart i`, `isOpen_chartSet`,
  `iUnion_chartSet : ⋃ i, chartSet i = univ`, `chartMap_chartPoint`, `chartPoint_chartRatio`.
- `isOpenMap_chartPoint`: the cone over an open subset of the affine slice `x_i = 1` is open
  among the nonzero vectors, because `projMk ⁻¹' (chartPoint i '' W) =
  nonzeroVectorChart i ∩ (chartRatio i ·) ⁻¹' W` and `chartRatio i` is continuous there.
- **`chartHomeomorph i : (Fin N → ℂ) ≃ₜ chartSet i`** — the `i`-th standard affine chart.
- Transported to the scheme-theoretic analytification along `projectivizationHomeomorph`:
  `complexPointChartSet i`, `isOpen_complexPointChartSet`, `iUnion_complexPointChartSet`, and
  **`complexPointChartHomeomorph i : (Fin N → ℂ) ≃ₜ complexPointChartSet i`**.

### Item 2 — the cone-function comparison (**done** at the level of functions)

[`Other/AlgebraicGeometry/HomogeneousEntireFunctions.lean`](../Other/AlgebraicGeometry/HomogeneousEntireFunctions.lean),
namespace `Complex.PolynomialGrowth`:

- `iteratedDeriv_line_eq_zero_of_lt`: the *small-radius* Cauchy estimate.  If `F` is entire on
  `ℂⁿ` with `‖F w‖ ≤ C ‖w‖ᵐ`, then `iteratedDeriv k (fun t ↦ F (t • z)) 0 = 0` for `k < m`
  (letting `R → 0`).  Together with the large-radius estimate already proved, only the order-`m`
  coefficient can survive.
- `exists_bound_of_homogeneous`: a continuous degree-`m` homogeneous function on `ℂ^{N+1}`
  satisfies `‖F x‖ ≤ C ‖x‖ᵐ`, with `C` a bound on the unit sphere (compactness).
- **`exists_isHomogeneous_eq_of_homogeneous`**: an entire `F : ℂ^{N+1} → ℂ` with
  `F (t • x) = tᵐ · F x` equals `MvPolynomial.eval · Q` for a `Q` that is *homogeneous of degree
  `m`*.
- `eval_smul_of_isHomogeneous`: the converse scaling law for a homogeneous polynomial.
- **`analyticOnNhd_homogeneous_iff`**: hence the exact characterisation — on the coordinate cone
  `ℂ^{N+1}`, the entire functions homogeneous of degree `m` are *exactly* the degree-`m` forms.
  This is the whole mathematical content of `H⁰(ℙᴺ(ℂ)^an, 𝒪(m)^an) = H⁰(ℙᴺ, 𝒪(m))` for `m ≥ 0`;
  what remains between it and the sheaf statement is bookkeeping (G1)–(G3) below, not analysis.
- `eq_zero_of_homogeneous_neg`: an *entire* function on `ℂ^{N+1}` homogeneous of strictly
  negative degree is `0`.  **This is deliberately weaker than the sheaf-level vanishing**
  `H⁰(ℙᴺ(ℂ)^an, 𝒪(−k)^an) = 0`: a section of a negative twist is homogeneous on the *punctured*
  cone and need not extend over the origin.  The sheaf-level vanishing needs, in addition, either
  a Riemann/Hartogs extension theorem in `N + 1 ≥ 2` variables, or the elementary argument
  "multiply a degree-`(−k)` section by each degree-`k` form; the product is a degree-`0`
  homogeneous holomorphic function, hence constant by compactness + maximum modulus
  (`globalHolomorphic_eq_const`); comparing the constants obtained from `x_0^k` and `x_1^k`
  forces them to vanish".  Note that it is **false for `N = 0`**, where `ℙ⁰` is a point and every
  twist is trivial, so any statement of it must assume `N ≥ 1`.

### Newly discovered prerequisite: `ℙᴺ_ℂ` carries none of the repository's analytic structure

`holomorphicFunctionSheaf X d`, `holomorphicRingSheaf X d` and `moduleAnalytification X d` all
require `[SmoothOfRelativeDimension d X.hom]`.  For `X = Over.mk (ProjectiveSpace.toBase (Fin (N+1))
(Spec ℂ))` this instance is **not** available: `IsIntegral (ProjectiveSpace (Fin (N+1)) (Spec ℂ))`,
`Smooth (ProjectiveSpace.toBase (Fin (N+1)) (Spec ℂ))` and `dim = N` are all absent from this
repository and from Mathlib (checked directly: all three `infer_instance` calls fail).  Until they
exist, *no statement at all* about `H⁰(ℙᴺ(ℂ)^an, …)` can even be typed, which is why the
obligations below are stated in the handoff rather than as compiling `def … : Prop` declarations.
This is a genuine, self-contained, and quite large sub-project (smoothness of projective space
over a field, integrality of `Proj` of a polynomial ring, and the dimension computation), and it
sits *before* everything else in the reorganised plan.

### The remaining gaps, stated

**(G0) `ℙᴺ_ℂ` is a smooth integral complex variety of dimension `N`.**
```lean
instance : IsIntegral (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ))
instance : Smooth (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))
theorem dim_projectiveSpace : dim (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ)) = N
```
Only with these does `SmoothOfRelativeDimension N` — and hence `holomorphicRingSheaf`,
`moduleAnalytification` and the target statements — exist for `ℙᴺ`.

**(G1) The standard homogeneous charts are holomorphic charts.**  Writing `ℙᴺ` for the object of
(G0) and `d = N`:
```lean
def StandardChartsHolomorphic (N : ℕ) : Prop :=
  ∀ (i : Fin (N + 1)) (f : C^ω⟮𝓘(ℂ, Fin N → ℂ), ComplexPoint ℙᴺ; ℂ⟯),
    AnalyticOnNhd ℂ
      (fun z : Fin N → ℂ ↦ f (ComplexProjectiveSpace.complexPointChartHomeomorph i z))
      Set.univ
```
together with the converse (an entire function on `ℂᴺ` transported to the chart is a section of
`holomorphicFunctionSheaf` over `complexPointChartSet i`).  Equivalently: the homeomorphisms
`complexPointChartHomeomorph i` belong to the analytic atlas generated by `localChart`.  Since
`localChart` is built from *étale* coordinates, proving this means comparing the étale chart at a
point with the homogeneous chart — the natural route is that both are charts of the affine open
`D₊(x_i) ≅ 𝔸ᴺ`, using `ComplexPoint.affineSpaceHomeomorph` and `contMDiffAt_evaluate`.

**(G2) A chartwise holomorphic model of the analytified twist.**
```lean
def HasHolomorphicTwistFrames (N n : ℕ) : Prop :=
  ∃ e : ∀ i : Fin (N + 1),
      SheafOfModules.unit ((holomorphicRingSheaf ℙᴺ N).over (complexPointChartOpen i)) ≅
        (ProjectiveTwist.analytic ℙᴺ N P n).over (complexPointChartOpen i),
    ∀ i j, TauCeti.SheafOfModules.transitionUnit (e i) (e j) = (x_i / x_j) ^ n
```
i.e. `𝒪(−n)^an` is the line bundle glued from the standard charts with transition functions
`(x_i / x_j)^n`.  The algebraic side of this already exists
(`ProjectiveSpectrum.NegativeTwist.HomogeneousShift.basicOpenUnitIso`, trivialising `𝒪(−n)` on
`D₊(x_i)` by multiplication/division by `x_i^n`), and `analytificationGenerates`
(`Other/AlgebraicGeometry/AnalytificationGenerates.lean`) transports a generating algebraic
section to a generating analytic section; so (G2) should be obtainable by *transport*, once (G0)
and the identification of `analyticOpen (D₊(x_i))` with `complexPointChartSet i` are available.

**(G3) The section/cone-function dictionary.**
```lean
def TwistHomsAreConeFunctions (N a b : ℕ) : Prop :=
  Nonempty ((ProjectiveTwist.analytic ℙᴺ N P a ⟶ ProjectiveTwist.analytic ℙᴺ N P b) ≃
    {F : (Fin (N + 1) → ℂ) → ℂ //
       AnalyticOnNhd ℂ F Set.univ ∧ ∀ t x, F (t • x) = t ^ (a - b) * F x})
```
for `b ≤ a`, and the corresponding statement that the set is a singleton `{0}` when `a < b` and
`N ≥ 1`.  Given (G1) and (G2) this is gluing: a morphism of twists is a family of holomorphic
functions on the charts satisfying the `(x_i/x_j)^{a-b}` cocycle, which is the same as one
degree-`(a−b)` homogeneous holomorphic function on the cone.  Combining (G3) with
`analyticOnNhd_homogeneous_iff` and with the algebraic computation of
`Hom(𝒪(−a), 𝒪(−b)) = H⁰(ℙᴺ, 𝒪(a−b)) =` degree-`(a−b)` forms then gives
`AnalyticTwistRelationsAlgebraize` **on `ℙᴺ`**.

**(G4) Descent to a subvariety `X ⊆ ℙᴺ`** (unchanged from the previous re-assessment): exactness
of analytic pushforward along the closed immersion, and `i^an_*(M^an) ≅ (i_* M)^an`.

**(G5), (G6), (G7)**: Oka coherence, Cartan A/B, and the stalkwise base change plus flatness for
reflection of invertibility — unchanged, and still the three genuinely hard analytic/algebraic
inputs.

## Mathematical routes, and what is missing

The statement is Serre's GAGA (essential surjectivity of analytification) restricted to
invertible sheaves on a smooth projective variety. Apart from the several-variables
polynomial-growth Liouville theorem recorded above (which is the `q = 0` analysis for twists on
`ℙᴺ`), nothing towards its analytic input exists in Mathlib or in this repository: there are no
coherent analytic sheaves, no Oka coherence, no Cartan Theorems A/B, no finiteness of coherent
cohomology on compact complex manifolds, and no Kodaira embedding. Whichever route is chosen,
that theory has to be built; the choice should be made on the basis of what is smallest for line
bundles.

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
