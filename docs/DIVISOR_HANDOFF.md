# Handoff: the divisor of an algebraic model (`HasDivisorOfAlgebraicModel`)

This document scopes the third of the three remaining obligations for the unconditional
rational Lefschetz `(1, 1)` theorem (see [LEFSCHETZ_HANDOFF.md](LEFSCHETZ_HANDOFF.md); the
second is scoped in [GAGA_HANDOFF.md](GAGA_HANDOFF.md)). Nothing here depends on the other two
obligations.

The algebraic half is **proved**: every invertible sheaf of modules on `X.left` is represented by
Cartier data, whose Weil divisor is the divisor of a rational section (§2.1–§2.3). The transport
of that data to the analytic space is proved up to one isolated statement,
`AnalytificationGenerates` (§2.4, §4.2(b)). What is left is the comparison of the resulting cycle
class with the first Chern class, `HasDivisorClassOfSomeCartierData` (§3), whose route is planned
in §4.3 and whose first step, `SectionSheafDeterminesClass`, is stated in Lean.

## 1. The exact target

In [`Other/AlgebraicGeometry/LefschetzOneOneReduction.lean`](../Other/AlgebraicGeometry/LefschetzOneOneReduction.lean):

```lean
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

def HasDivisorOfAlgebraicModel : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ D : CodimensionCycle X.left 1,
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
        integralToRationalCohomology X 2 E.firstChernClass
```

`E` is a short exact sequence `0 → 𝒪ˣ → E.middle → ℤ → 0` of analytic sheaves obtained from an
integral Hodge class through the exponential sequence, `E.firstChernClass` is the image of its
`Ext` class under the connecting map, and `E.sectionSheafOfModules` is the sheaf of holomorphic
sections of the line bundle glued from the transition units `E.transitionUnit`. Because `D` is
existential, sign and `2πi` normalisation conventions are absorbed by replacing `D` with `-D`.

## 2. The decomposition, and what is proved

The cut is along the classical construction: *`L` has a nonzero rational section `s`; the
divisor of `s` is the cycle `D`.*

### 2.1 Divisors of local rational-function data — proved

[`Other/AlgebraicGeometry/DivisorOfRationalSection.lean`](../Other/AlgebraicGeometry/DivisorOfRationalSection.lean)

* `AlgebraicGeometry.Scheme.principalCodimensionOneDivisor (S) (f : S.functionField) :
  CodimensionCycle S 1` — the divisor of a rational function on an integral Noetherian scheme.
  Local finiteness is `Scheme.ord_locallyFiniteSupport`
  (`HodgeConjecture/Lemmas/AlgebraicGeometry/OrderOfVanishing.lean`); purity is free, since
  `Scheme.ord` is by definition zero at points whose coheight is not one.
* `AlgebraicGeometry.Scheme.CartierData S` — an open cover of `S` by nonempty opens `Uᵢ`
  (`opens`, `nonempty`, `covers`) together with nonzero rational functions `fᵢ`
  (`fn`, `fn_ne_zero`) whose orders of vanishing agree at every point of every overlap
  (`ord_eq`). This is exactly the input a Weil divisor needs; the comparison of the `fᵢ`
  themselves is not required.
* `Scheme.CartierData.divisor : CodimensionCycle S 1` — the glued divisor,
  `divisor_apply_of_mem : x ∈ c.opens i → c.divisor x = S.ord (c.fn i) x`. Local finiteness
  comes from the *global* finiteness of a single `Scheme.ord (c.fn i)` on a Noetherian integral
  scheme (`Scheme.ord_support_finite`), restricted to `Uᵢ`.
* `Scheme.CartierData.ofFunctionField` and `ofFunctionField_divisor` recover the principal
  case.

### 2.2 Generating sections and trivializing covers — proved

[`Other/AlgebraicGeometry/InvertibleSheafRationalSection.lean`](../Other/AlgebraicGeometry/InvertibleSheafRationalSection.lean)

* `Scheme.Modules.resSection L h s` — restriction of a section, with `resSection_rfl`,
  `resSection_resSection`, `resSection_smul`.
* `Scheme.Modules.Generates (s : Γ(L, U)) : Prop` — for every open `V ≤ U`, multiplication by
  the restriction of `s` is a bijection `Γ(X, V) → Γ(L, V)`.
* `Generates.restrict`, `Generates.exists_smul_eq`, `Generates.smul_left_injective`, and
  `Generates.exists_isUnit_smul_eq`: **two generating sections on the same open differ by a
  unit of the structure sheaf**. This is the transition-function statement; the unit is
  produced from surjectivity in both directions and its inverse from injectivity.
* `Scheme.Modules.TrivializingCover L` — a cover by nonempty opens with a generating section
  `gen i` on each member.
* `Scheme.Modules.unitIsoSection` and `generates_unitIsoSection`: the image of `1` under an
  isomorphism `unit (𝒪_S.over U) ≅ L.over U` generates on `U`. Bijectivity on each `V ≤ U` is
  `SheafOfModules.evaluation` applied to the isomorphism at the object `V ⟶ U` of the site
  `Over U`; that the map is multiplication by the restricted section is naturality
  (`PresheafOfModules.naturality_apply`, `PresheafOfModules.unit_map_one`) plus linearity.
* `Scheme.Modules.nonempty_trivializingCover_of_isInvertible (L) (hL : IsInvertible L) :
  Nonempty (TrivializingCover L)` — the section-level form of
  `TauCeti.SheafOfModules.IsInvertible`, via `LocalTrivializations.ofIsInvertible`,
  `TauCeti.SheafOfModules.freePUnitIsoUnit` and `Opens.coversTop_iff`. Members of the
  trivializing cover that are empty are discarded by indexing over
  `{i // Nonempty (t.X i)}`.

### 2.3 The divisor of a rational section — proved

[`Other/AlgebraicGeometry/CartierDataOfTrivializingCover.lean`](../Other/AlgebraicGeometry/CartierDataOfTrivializingCover.lean)

```lean
def Scheme.CartierData.Represents (c : S.CartierData) (L : S.Modules) : Prop :=
  ∃ g : ∀ i : c.ι, Γ(L, c.opens i),
    (∀ i, Generates (g i)) ∧
    ∀ (i j : c.ι) (u : Γ(S, c.opens i ⊓ c.opens j)), IsUnit u →
      u • resSection L inf_le_left (g i) = resSection L inf_le_right (g j) →
      S.germToFunctionField (c.opens i ⊓ c.opens j) u * c.fn j = c.fn i
```

`c` represents `L` when the local equations of `c` are the coordinates of one rational section
of `L`: the transition functions of `L` between two members of the cover are the ratios
`fᵢ/fⱼ`. Equivalently, the local sections `fᵢ • gᵢ` all define the same element of the generic
stalk, and `c.divisor` is its divisor. **This relation is what keeps the decomposition
faithful**: without it the obligation of §3 would be false, since an arbitrary divisor has no
reason to have the right class.

The construction, given `t : TrivializingCover L` on an integral Noetherian `S`:

* `t.base` — a reference member (it exists because `S` is irreducible, hence nonempty).
* `t.transitionUnit i` — the unit with `uᵢ • gᵢ = g_base` on `Uᵢ ⊓ U_base`, from
  `Generates.exists_isUnit_smul_eq`; the overlap is nonempty because `S` is irreducible
  (`Scheme.nonempty_inf`, via `Scheme.genericPoint_mem_of_nonempty`).
* `t.fn i := S.germToFunctionField _ (t.transitionUnit i)`, nonzero because it is a unit of a
  field (`isUnit_fn`, `fn_ne_zero`).
* `t.germToFunctionField_mul_fn`: for any `u` on `Uᵢ ⊓ Uⱼ` with `u • gᵢ = gⱼ`, one has
  `germ(u) · fⱼ = fᵢ`. This is proved on the triple overlap `Uᵢ ⊓ Uⱼ ⊓ U_base`, which is
  nonempty, by injectivity of `r ↦ r • gᵢ` there, and then transported to the function field —
  the germ at the generic point does not see which nonempty open a section lives on
  (`TopCat.Presheaf.germ_res_apply`).
* `t.ord_eq`: on `Uᵢ ⊓ Uⱼ` the ratio `fᵢ/fⱼ` is the germ of a unit, so
  `Scheme.ord_of_isUnit` and `Scheme.ord_mul` give equal orders at every point of the overlap.
* `t.cartierData` and `t.cartierData_represents`, hence
  `t.exists_cartierData_represents : ∃ c : S.CartierData, c.Represents L`.

Assembled in
[`Other/AlgebraicGeometry/DivisorObligations.lean`](../Other/AlgebraicGeometry/DivisorObligations.lean):

```lean
theorem exists_cartierData_represents (L : X.left.Modules)
    (hL : TauCeti.SheafOfModules.IsInvertible L) :
    ∃ c : Scheme.CartierData X.left, c.Represents L
```

with `#print axioms` reporting only `propext`, `Classical.choice`, `Quot.sound`.

### 2.4 Analytification of sections, and analytic frames — proved

[`Other/AlgebraicGeometry/HolomorphicSheafGenerators.lean`](../Other/AlgebraicGeometry/HolomorphicSheafGenerators.lean),
[`Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean`](../Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean)

The analytic counterpart of §2.2, and the transport of the algebraic local data to the analytic
space.

* `holRes`, `HolomorphicGenerates` — restriction and generation for sheaves of modules over
  `holomorphicRingSheaf X d`; the same definitions as §2.2, on the analytic space. Note that
  `RingCat` is not commutative, so `HolomorphicGenerates.exists_isUnit_smul_eq` proves both
  unit identities from the two generation hypotheses.
* `HolomorphicGenerates.map_iso`, `smul_holRes_map_iso` — generation and identities
  `u • a = b` between restrictions transport along an isomorphism of holomorphic sheaves of
  modules.
* `holomorphicUnitIsoSection`, `holomorphicGenerates_unitIsoSection`,
  `HolomorphicTrivializingCover` (with `ofLocalTrivializations`, `transport`) and
  `nonempty_holomorphicTrivializingCover_of_isInvertible` — an invertible holomorphic sheaf of
  modules has a cover by opens with a generating frame on each; in particular
  `E.sectionSheafOfModules` does, through `E.sectionLocalTrivializations`
  (`HolomorphicUnitExtension.frames`).
* `HolomorphicTrivializingCover.exists_isUnit_frameChange` — **frame change**: on an open
  contained in a member of each of two trivializing covers of the same sheaf, the two frames
  differ by a unit of the holomorphic structure sheaf, i.e. by a nowhere-vanishing holomorphic
  function.
* `analyticFunction X d U r` — a regular function on `U` as a section of the holomorphic
  structure sheaf on `U^an`, with `analyticFunction_one`, `analyticFunction_mul`,
  `analyticFunction_res` and `isUnit_analyticFunction` (the evaluation of a unit is a
  nowhere-vanishing holomorphic function).
* `analyticSection X d L U g` — the analytification of a section, defined as the image of `g`
  under the unit of `moduleAnalytificationAdjunction`, with
  `analyticSection_smul` (semilinearity over `analyticFunction`) and `analyticSection_res`
  (compatibility with restriction).
* **`analyticSection_smul_res`** — the transport of transition identities:
  `u • a|_W = b|_W` implies `u^an • a^an|_{W^an} = b^an|_{W^an}`. This is unconditional and is
  the fact the cocycle comparison rests on.
* Given the obligation `AnalytificationGenerates` of §4.2(b):
  `analyticTrivializingCover` (the analytified algebraic cover),
  `extensionFramesOfAlgebraic` (transported along an isomorphism with
  `E.sectionSheafOfModules`),
  **`analyticSection_transitionUnit`** and **`extensionFramesOfAlgebraic_transitionUnit`** (the
  transition functions of those frames are the evaluations `uᵢ^an` of the algebraic transition
  units, hence the analytifications of the local equations `fᵢ`), and
  **`exists_isUnit_frameChange_extension`** (on any open contained in `Uᵢ^an` and in one of the
  local-lift neighbourhoods of `E`, the analytified algebraic frame and `E`'s own frame differ
  by a nowhere-vanishing holomorphic function — so the two cocycles are cohomologous on the
  common refinement of the covers).

## 3. What remains

[`Other/AlgebraicGeometry/DivisorObligations.lean`](../Other/AlgebraicGeometry/DivisorObligations.lean):

```lean
def HasDivisorClassOfSomeCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ c : Scheme.CartierData X.left, c.Represents L ∧
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass

theorem hasDivisorOfAlgebraicModel_of_divisorClass
    (hclass : HasDivisorClassOfSomeCartierData X) : HasDivisorOfAlgebraicModel X
```

**Deliverable:** a theorem

```lean
theorem hasDivisorClassOfSomeCartierData (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] : HasDivisorClassOfSomeCartierData X
```

with no `sorry` and no new `axiom`, added to `scripts/lefschetz_axiom_audit.lean`.

A concrete `c` is available: `exists_cartierData_represents X L hL` produces one, built from
the trivializing cover of `L`. The existential form lets the prover pick a convenient one — for
instance one whose cover refines a cover on which the analytic comparison is easy to make.

The file also states the uniform variant

```lean
def HasDivisorClassOfCartierData : Prop :=
  ∀ E L hL iso, ∀ c : Scheme.CartierData X.left, c.Represents L →
    sheafCycleClassOnCycles (…) 1 c.divisor = integralToRationalCohomology X 2 E.firstChernClass
```

with `hasDivisorClassOfSomeCartierData_of_cartierData` deriving the former from it. The uniform
variant is the natural statement, but it is **strictly stronger**: two Cartier data representing
the same `L` are the local equations of two rational sections whose divisors differ by a
principal divisor, so proving it also proves that the constructed class of a principal divisor
vanishes — the codimension-one input to rational-equivalence descent
(`Other/AlgebraicGeometry/PrincipalDivisorCycleClass.lean`), which is *not* needed for the
Lefschetz reduction. Prove the existential form unless the uniform one comes for free.

Do not weaken further: the divisor must be one produced by `Represents` (any weakening that
drops `Represents` is either false or useless to `hasDivisorOfAlgebraicModel_of_divisorClass`).
Both sides may be replaced by anything provably equal to them; in particular the statement may
first be reduced to the *supported* form, which is where the mathematics actually happens (see
§4). The sign, however, must be settled rather than absorbed: `Represents` pins the divisor
down. If the repository's normalisations make the two classes differ by `-1`, the cheap fix is
to change the *definition* `Scheme.CartierData.Represents` — which belongs to this development,
not to the target — by exchanging `i` and `j` in its transition condition
(`germ(u) · fᵢ = fⱼ` instead of `germ(u) · fⱼ = fᵢ`). That inverts every `fᵢ`, negates
`c.divisor`, and leaves `exists_cartierData_represents` provable by the same argument with
`transitionUnit` taken in the other direction.

## 4. Mathematical route, and what is missing

Write `d = dim X.left`, `Uᵢ`, `fᵢ` for the Cartier data, `s` for the corresponding rational
section, `D = c.divisor = Σ n_x·[x]` its divisor, and `|D|` for the union of the closures of
the codimension-one points with `n_x ≠ 0` (a finite set: `Scheme.ord_support_finite`).

The two sides are built completely differently, so the comparison must be made at the one place
where both are described by explicit local data — a neighbourhood of a smooth point of one
component of `|D|` — and then propagated by a *uniqueness* statement.

### 4.1 The cycle-class side (exists)

`sheafCycleClassOnCycles V 1` (`Other/AlgebraicGeometry/SheafCycleClass.lean`) is
`cycleClassOnCyclesOfComponents (cycleComponentSheafClass X)`: the finite sum, with the exact
integer multiplicities `n_x`, of the classes `cycleComponentSheafClass X x hx`
(`Other/AlgebraicGeometry/CycleComponentSheafClass.lean`). Each of these is built as:

1. `cycleComponentSmoothSupportCoclassSection X x hx` — the normalised normal-chart coclass of
   the component on its smooth locus (`CycleComponentSmoothSupportCoclassSection.lean`,
   `CycleComponentNormalCoordinates.lean`);
2. `cycleComponentSupportedInjectiveClass X x hx` — its unique extension across the singular
   boundary, by purity (`CycleComponentSupportExtension.lean`,
   `CycleComponentSmoothSupportPurity.lean`), characterised by
   `cycleComponentSupportedInjectiveClass_normalization` and
   **`cycleComponentSupportedInjectiveClass_unique`**;
3. `cycleComponentSheafClass X x hx` — the image in ordinary rational cohomology after
   forgetting support, `cycleComponentSheafClass_eq_forgetSupport` (`forgetSupport`,
   `HodgeConjecture/Definitions/AlgebraicGeometry/CohomologyWithSupport.lean`).

Step 2 is the tool for the comparison: any supported class whose restriction to the smooth
locus is the normal-chart coclass *is* the constructed class.

### 4.2 The Chern-class side (partly exists)

`E.firstChernClass` (`HolomorphicUnitExtension.lean`) is
`(analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).symm
 (holomorphicFirstChernClass X d E.cohomologyClass)`, where `E.cohomologyClass` is
`E.shortExact.extClass` and `holomorphicFirstChernClass` is composition with the `Ext` class of
`holomorphicExponentialSequence_shortExact` (`HolomorphicFirstChernClass.lean`,
`HolomorphicExponentialSequence.lean`). The line bundle itself is reconstructed from `E` by
local lifts of the integer section `1`:

* `E.localLifts` (opens `E.localLifts.opens z` covering `X^an`),
* `E.transitionUnit z w V _ _ : (C^ω⟮…, V; ℂ⟯)ˣ` with the cocycle identity
  (`HolomorphicUnitTransition.lean`),
* `E.lineBundleCore`, `E.sectionSheafOfModules`, and the local trivializations
  `E.localSectionSheafIso`, `E.localFreeSheafIso` (`HolomorphicLineBundleOfExtension.lean`,
  `HolomorphicLineBundleModule.lean`, `HolomorphicLineBundleInvertible.lean`).

**Missing (a): a cocycle description of the connecting map.** What is available is the abstract
`Ext`-level connecting map. What the comparison needs is: *if the transition units of the line
bundle of `E` are `g_{ij}`, then `E.firstChernClass` is the Čech class
`[(1/2πi)(log g_{jk} − log g_{ik} + log g_{ij})]`* — or any statement of equivalent strength,
e.g. that `E.firstChernClass` is the image of the Čech `1`-cocycle `(g_{ij})` under a Čech
model of `H¹(𝒪ˣ) → H²(ℤ)`. The repository has the local lifts and their cocycles
(`Other/AlgebraicTopology/SheafExtensionCocycle.lean`,
`SheafExtensionLocalLifts.lean`) and the local logarithms
(`Other/Geometry/Manifold/HolomorphicLogarithm.lean`), so this is a matter of comparing the
`Ext`-representative with the Čech representative, not of new analysis. It is nevertheless a
substantial piece: there is no Čech-to-derived-functor comparison in the repository.

**Missing (b): `AnalytificationGenerates` — the analytification of a generating section
generates.** Stated in
[`Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean`](../Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean):

```lean
def AnalytificationGenerates : Prop :=
  ∀ (L : X.left.Modules) (U : X.left.Opens) (g : Γ(L, U)),
    Scheme.Modules.Generates g →
      HolomorphicGenerates (M := (moduleAnalytification X d).obj L) (analyticSection X d L U g)
```

Everything else on the analytic side of §2.4 is derived from it. Mathematically it is the base
change

  `((pullback φ).obj L).over U^an ≅ (pullback (φ.over U)).obj (L.over U)`

for `φ = regularToHolomorphicRingSheaf X d` and the induced functor
`Opens U ⥤ Opens U^an`, combined with Mathlib's `SheafOfModules.pullbackObjUnitToUnit` for that
restricted morphism of ringed sites (which is an isomorphism because `U ↦ U^an` is a final
functor — the proof of `underlyingContinuousMap_opensMap_final` in `AnalytificationModules.lean`
works verbatim over `U`). Concretely:

1. `Generates g` is the same as an isomorphism `unit (𝒪_X.over U) ≅ L.over U` carrying `1` to
   `g` — the two directions are `generates_unitIsoSection` and the fact that the morphism
   determined by `g` has bijective components.
2. Mathlib has no Beck–Chevalley statement for `SheafOfModules.pullback` and `overFunctor`.
   Both `overFunctor R U = pushforward (𝟙)` along `Over.forget U` and `pushforward φ` along `F`
   are pushforwards, and `pushforwardComp` identifies
   `pushforward φ ⋙ overFunctor R U ≅ overFunctor R' (F U) ⋙ pushforward (φ.over U)`
   because both are pushforward along `Over.forget U ⋙ F = F_U ⋙ Over.forget (F U)`. The mate
   of that isomorphism is the base change wanted; it is an isomorphism because `overFunctor` is
   *also* a left adjoint (`SheafOfModules.overPushforwardOverAdj`, and the instance
   `IsLeftAdjoint (pushforward (𝟙 (R.over x)))` in `Mathlib/Algebra/Category/ModuleCat/Sheaf/
   PushforwardContinuous.lean`), so open restriction satisfies base change on both sides.
3. An alternative, avoiding Beck–Chevalley: redo the Yoneda argument of
   `SheafOfModules.pullbackObjUnitToUnit` directly for the morphism
   `unit (𝒪^an.over U^an) ⟶ ((pullback φ).obj L).over U^an` determined by `g^an`, using that
   `overFunctor` is a left adjoint to express `Hom(N.over U^an, M)` as
   `Hom_{𝒪_X}(L, pushforward φ (pushforward (pushforwardOver U^an) M))` and the algebraic
   `overFunctor` adjunction to reduce to `Generates g`. This is the same content with less
   general machinery.
4. A third route is stalkwise: `((pullback φ).obj L)_z ≅ 𝒪^an_z ⊗_{𝒪_{X,x}} L_x`, and a
   generating section becomes a basis of a free rank-one module. Mathlib has module structures
   on stalks (`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) but no computation of the stalks
   of a pullback along a morphism of ringed sites, so this route needs the most new material.

Warm-up lemmas that are true, useful and independent of the choice: `moduleAnalytification`
preserves invertibility; the analytification of a free sheaf on an algebraic open is free on the
corresponding analytic open (`pullbackObjFreeIso`, `moduleAnalytificationUnitIso`).

**Missing (c): the local computation.** Near a smooth point `p` of one component `Z` of `|D|`,
choose an algebraic open `U ∋ p` on which `Z` is cut out by a regular function `h` with
`ord_Z(h) = 1` and the section `s` is `h^{n_Z} · (unit)`. In an analytic normal chart at `p`
the function `h` becomes a coordinate `z₁`, and the assertion is the local model of the
Lelong–Poincaré/first-Chern-class identity:

> the class in `H²_{|D|}` obtained from the transition functions `f_i/f_j` of `𝒪(D)` restricts,
> on the smooth locus of `Z`, to `n_Z` times the normalised normal-chart coclass of `Z`.

Concretely, on `{z : |z₁| < ε}` the cocycle `(1/2πi) d log z₁` on the punctured disc generates
`H¹` of the punctured disc, and the Čech class of the transition function `z₁` between the two
half-planes where `log z₁` has a branch is the generator of `H²` of the disc supported at
`{z₁ = 0}`. This is the only genuinely analytic input; it is a one-variable computation, but
formalising it against the repository's normal-chart normalisation
(`cycleComponentSmoothSupportCoclassSection`, `CycleComponentNormalCoordinates.lean`,
`ComplexLocalOrientation*.lean`) is where the effort will go, and it fixes the sign.

**Missing (d): a supported exponential sequence.** To use
`cycleComponentSupportedInjectiveClass_unique` the Chern class must first be *lifted to a class
supported on `|D|`*. Mathematically: `s` trivialises `L` on `X \ |D|`, so the analytic line
bundle is canonically trivial there and its Chern class comes from
`H²_{|D|}(X^an, ℤ) → H²(X^an, ℤ)` (`forgetSupport`). Formally this needs a version of the
exponential-sequence connecting map for cohomology with support in a closed set, or, more
economically, the statement that the Čech class of §4.4(a) built from a cocycle that is a
coboundary on `X \ |D|` lifts through `forgetSupport`. Cohomology with support and
`forgetSupport` exist (`CohomologyWithSupport.lean`, `CycleComponentSupportExtension.lean`);
the supported exponential sequence does not.

### 4.3 Plan and order of work

**Step 1 — the algebraic data on the analytic space.** Done except for
`AnalytificationGenerates` (missing (b)); see §2.4. Its output is: frames `γᵢ` of
`E.sectionSheafOfModules` on the analytic opens `Uᵢ^an`, with transition functions the
evaluations `uᵢ^an` of the algebraic transition units — equivalently the analytifications of the
local equations `fᵢ` of the rational section whose divisor is `c.divisor` — and a unit frame
change to `E`'s own frames on any common open.

**Step 2 — from the line bundle back to the extension class.** Two pieces.

*2a. `SectionSheafDeterminesClass`* (stated in
[`Other/AlgebraicGeometry/UnitExtensionClassObligations.lean`](../Other/AlgebraicGeometry/UnitExtensionClassObligations.lean)):
two unit-sheaf extensions with isomorphic sheaves of sections have the same class in
`Ext¹(ℤ, 𝒪ˣ)`. This is injectivity of `H¹(X^an, 𝒪ˣ) → Pic(X^an)`, and it is what allows
`E.firstChernClass` to be computed from the algebraic data at all
(`firstChernClass_eq_of_sectionSheafOfModules_iso`). Route: pass to a common refinement of the
two trivializing covers; `HolomorphicTrivializingCover.exists_isUnit_frameChange` gives unit
frame changes `c_z`; correcting the local lifts of the integer section `1` by `c_z` makes the two
cocycles of `Other/AlgebraicTopology/SheafExtensionCocycle.lean` agree, the resulting local
isomorphisms `E.middle|_W ≅ E'.middle|_W` agree on overlaps and glue, and
`ShortComplex.ShortExact.extClass` is invariant under an isomorphism of short exact sequences.
No comparison of cohomology theories is involved.

*2b. Realization of a cocycle.* For a `1`-cocycle of holomorphic units on an open cover, an
extension whose local lifts have that cocycle. The repository builds the bundle from the
extension (`HolomorphicUnitTransition.lean`, `HolomorphicLineBundleOfExtension.lean`); the
converse glues `𝒪ˣ ⊕ ℤ` along the cocycle. Together with 2a this makes the assignment
"cocycle ↦ extension class" well defined, which is the practical substitute for a Čech-to-derived
comparison.

**Do not build general Čech cohomology of sheaves.** The repository's Čech development
(`Other/AlgebraicTopology/OpenCoverOrderedCechBicomplex.lean`, `OrderedCechRealization.lean`,
`OrderedCechNormalization.lean`, `CechNerveEvaluation.lean`, `IntegralCechTotalAugmentation.lean`)
is about the singular chains of a cover, built for the Betti comparison; it is not a Čech complex
of an abstract sheaf, and there is no Čech-to-derived-functor comparison anywhere in the
repository or in Mathlib. Building one — plus the comparison with
`Abelian.Ext` and with `Hypercohomology` — is a project of the size of the whole present
obligation. The route below is designed to avoid it: the only handle needed on `H²(X^an, ℤ)` is
`hypercohomologyAddEquivGlobalSectionsKInjective` (`HypercohomologyGlobalSectionsNaturality.lean`)
together with the supported/relative comparisons that already exist.

**Step 3 — localize the class on the divisor** (missing (d)). The rational section `s` frames
the bundle on `Ω := X^an \ |D|^an`, so `E|_Ω` splits: a global frame over `Ω` gives, through 2a/2b,
a global lift over `Ω` of the constant integer section `1`, i.e. a splitting of the restricted
extension, i.e. the vanishing of `E.cohomologyClass|_Ω`. Hence `E.firstChernClass` is in the
image of `forgetSupport X (cycleComponentSupport …) 2` — a class in cohomology with support in
`|D|^an`. Formally, what is needed is the connecting/exact sequence
`H²_{|D|}(X, ℤ) → H²(X, ℤ) → H²(Ω, ℤ)` and the vanishing of the restriction; both the supported
groups (`HodgeConjecture/Definitions/AlgebraicGeometry/CohomologyWithSupport.lean`) and the
restriction maps exist, but the exactness statement in this presentation does not yet.

**Step 4 — the local model** (missing (c)) **and conclusion.** On the smooth locus of a component
`Z` with multiplicity `n_Z`, in a normal chart the divisor is `{z₁ = 0}` and the transition
cocycle is that of `z₁^{n_Z}`; the supported class is `n_Z` times the normalised normal-chart
coclass `cycleComponentSmoothSupportCoclassSection`. Then
`cycleComponentSupportedInjectiveClass_unique` identifies the supported lift of `E.firstChernClass`
with `∑ n_Z · cycleComponentSupportedInjectiveClass`, and forgetting support
(`cycleComponentSheafClass_eq_forgetSupport`) together with additivity
(`sheafCycleClassOnCycles_sum_single`) gives exactly the equation of §3. This step fixes the sign.

Summary of the named obligations, in dependency order:

| Name | File | Content |
| --- | --- | --- |
| `AnalytificationGenerates` | `AnalyticSectionOfAlgebraic.lean` | analytification of a generating section generates |
| `SectionSheafDeterminesClass` | `UnitExtensionClassObligations.lean` | `H¹(𝒪ˣ) → Pic` is injective |
| — (not yet stated) | — | realization of a cocycle by an extension; supported exactness; the local model |
| `HasDivisorClassOfSomeCartierData` | `DivisorObligations.lean` | the target of §3 |

## 5. Interface reference

* Cycles: `CodimensionCycle X p := codimensionCycleSubgroup X p`,
  `CodimensionCycle.single`, `PrincipalDivisor`, `rationalEquivalenceSubgroup`, `ChowGroup`
  (`HodgeConjecture/Definitions/AlgebraicGeometry/ChowGroup.lean`); the descent lemmas for
  rational equivalence, which this obligation does **not** need, are in
  `Other/AlgebraicGeometry/PrincipalDivisorCycleClass.lean`.
* Orders of vanishing: Mathlib `AlgebraicGeometry.Scheme.ord` / `ordHom` / `ord_mul` /
  `ord_of_isUnit` (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`), plus
  `Scheme.ord_support_finite` and `Scheme.ord_locallyFiniteSupport`
  (`HodgeConjecture/Lemmas/AlgebraicGeometry/OrderOfVanishing.lean`).
* Noetherianness of `X.left` is `isNoetherian_of_isProjective`
  (`HodgeConjecture/Definitions/AlgebraicGeometry/Points.lean`), a theorem, not an instance:
  `attribute [local instance] isNoetherian_of_isProjective`.
* Sheaves of modules on a scheme: `Scheme.Modules`, `Γ(M, U)`, `Scheme.Modules.presheaf`,
  `Hom.app` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`); the `Over U` site presentation
  used by `TauCeti.SheafOfModules.IsInvertible` is `SheafOfModules.over`,
  `SheafOfModules.evaluation`, and `(M.over U).val.obj (op W) = M.val.obj (op W.left)` holds by
  `rfl`.
* Analytic side: see [GAGA_HANDOFF.md](GAGA_HANDOFF.md) §"The objects involved" for
  `ComplexPoint`, `holomorphicFunctionSheaf`, `moduleAnalytification` and the charts.

## 6. Verification

```bash
lake env lean Other/AlgebraicGeometry/DivisorOfRationalSection.lean
lake env lean Other/AlgebraicGeometry/InvertibleSheafRationalSection.lean
lake env lean Other/AlgebraicGeometry/CartierDataOfTrivializingCover.lean
lake env lean Other/AlgebraicGeometry/DivisorObligations.lean
lake env lean Other/AlgebraicGeometry/HolomorphicSheafGenerators.lean
lake env lean Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean
lake env lean Other/AlgebraicGeometry/UnitExtensionClassObligations.lean
lake build Other.AlgebraicGeometry.DivisorObligations
lake build Other.AlgebraicGeometry.UnitExtensionClassObligations
```

All seven modules are imported by `Other.lean`. Repository conventions: files start with
`module`, use `public import`, `@[expose] public noncomputable section`; local topology
instances need unique names; `set_option backward.isDefEq.respectTransparency false in` is often
needed to `change`/`rw` through bundled categories, and `omit [...] in` before the docstring
(not after) when a section variable is unused.
