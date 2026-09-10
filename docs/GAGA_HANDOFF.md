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

## Suggested warm-up lemmas

These are true, useful, and independent of the hard analysis; they also validate the
interface before the main construction is attempted.

- `moduleAnalytification` preserves invertibility: if `L : X.left.Modules` is
  `IsInvertible`, so is `(moduleAnalytification X d).obj L`. (Pullback of free is free plus
  restriction to opens; use `LocalTrivializations`.)
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
