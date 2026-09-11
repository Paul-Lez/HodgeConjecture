# Handoff: the divisor of an algebraic model (`HasDivisorOfAlgebraicModel`)

This document scopes the third of the three remaining obligations for the unconditional
rational Lefschetz `(1, 1)` theorem (see [LEFSCHETZ_HANDOFF.md](LEFSCHETZ_HANDOFF.md); the
second is scoped in [GAGA_HANDOFF.md](GAGA_HANDOFF.md)). Nothing here depends on the other two
obligations.

The algebraic half is **proved**: every invertible sheaf of modules on `X.left` is represented by
Cartier data, whose Weil divisor is the divisor of a rational section (§2.1–§2.3). The transport
of that data to the analytic space is also **proved**: `AnalytificationGenerates` is now the
theorem `analytificationGenerates` (§2.4, §4.2(b)). What is left is the comparison of the resulting cycle
class with the first Chern class, `HasDivisorClassOfSomeCartierData` (§3), whose route is planned
in §4.3. Of that route, step 2a (`SectionSheafDeterminesClass`) is **proved**
(`sectionSheafDeterminesClass`), and **the whole of step 3 is now proved**: the support sequence
is exact (`exact_forgetSupport_restrictToComplement`), an extension that splits over an open set
`Ω` has vanishing restricted extension class (`cohomologyClass_comp_restrictionUnit_eq_zero`),
and the compatibility of the exponential connecting map with restriction to `Ω` is
`hasRestrictedChernFactorization` / `restrictedChernClassVanishes` (§4.3 step 3c); only the
splitting datum `ℓ` (a frame of the line bundle on `X^an ∖ |D|^an`) is still to be produced. Step 4 has been restated correctly and its
**assembly is proved** (`hasDivisorClassOfSomeCartierData_of_localModel`, §4.3 step 4); its
codimension-one excision statement `HasComponentSupportDecomposition` is now **proved**
unconditionally (`hasComponentSupportDecomposition_unconditional`, §4.3 step 4), together with
its codimension-two vanishing input (`hasCodimensionTwoSupportedVanishing`), so what is left of
step 4 is the local model `HasChernLocalModel` alone.

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
* Given `AnalytificationGenerates` of §4.2(b) (now the theorem `analytificationGenerates`):
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

**Proved (b): `AnalytificationGenerates` — the analytification of a generating section
generates.** Stated in
[`Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean`](../Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean):

```lean
def AnalytificationGenerates : Prop :=
  ∀ (L : X.left.Modules) (U : X.left.Opens) (g : Γ(L, U)),
    Scheme.Modules.Generates g →
      HolomorphicGenerates (M := (moduleAnalytification X d).obj L) (analyticSection X d L U g)
```

and **proved** in
[`Other/AlgebraicGeometry/AnalytificationGenerates.lean`](../Other/AlgebraicGeometry/AnalytificationGenerates.lean)
as

```lean
theorem analytificationGenerates (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : AnalytificationGenerates X d
```

The proof follows **none** of the three routes listed below: it needs no base-change theorem at
all. Writing `φ := regularToHolomorphicRingSheaf X d`, `M := (pullback φ).obj L` and `A := U^an`,
it uses the two sheaves of `𝒪^an`-modules `starUnitSheaf X d A : V ↦ 𝒪^an(A ⨯ V)` and
`starModuleSheaf X d A M : V ↦ M(A ⨯ V)`, obtained as pushforwards along `Over.star A` of
`unit (𝒪^an.over A)` and of `M.over A` (so the sheaf condition is free), together with:

* `Scheme.Modules.Generates.coeff`
  ([`GeneratingSectionCoefficient.lean`](../Other/AlgebraicGeometry/GeneratingSectionCoefficient.lean)):
  the unique `c : Γ(𝒪_X, W ⊓ U)` with `c • g|_{W ⊓ U} = t|_{W ⊓ U}`, and its four structural
  identities (`coeff_res`, `coeff_smul`, `coeff_add`, `coeff_self`);
* `coeffHom : L ⟶ (pushforward φ).obj (starUnitSheaf X d A)`, `t ↦ (hg.coeff W t)^an`, an
  *explicit* morphism of algebraic sheaves of modules, and its adjoint
  `analyticCoeffHom : M ⟶ starUnitSheaf X d A`, which satisfies
  `analyticCoeffHom (t^an) = coeffHom t` (`analyticCoeffHom_analyticSection`, the triangle
  identity);
* `smulSectionHom : unit (𝒪^an.over A) ⟶ M.over A`, multiplication by
  `s := analyticSection X d L U g`, whose components are bijective exactly when
  `HolomorphicGenerates s` holds;
* `analyticCoeffHom_comp_smulSectionHom :
  analyticCoeffHom ≫ (starPushforward A).map smulSectionHom = toStarModuleSheaf`, where
  `toStarModuleSheaf : M ⟶ starModuleSheaf X d A M` is `m ↦ m|_{A ⨯ V}`. Because morphisms out
  of a pullback are determined by their adjoints, this identity reduces to the algebraic
  `hg.coeff W t • g|_{W ⊓ U} = t|_{W ⊓ U}` transported by the already-proved
  `analyticSection_smul_res`.

Evaluating `analyticCoeffHom_comp_smulSectionHom` on an analytic open `V ≤ A` produces a
two-sided inverse to multiplication by `s|_V`, which is
`holomorphicGenerates_analyticSection`.

For the record, the routes originally suggested were the following. Mathematically the statement
is the base change

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

**Step 1 — the algebraic data on the analytic space.** Done, including
`AnalytificationGenerates` (§4.2(b), `analytificationGenerates`); see §2.4. Its output is: frames `γᵢ` of
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
(`firstChernClass_eq_of_sectionSheafOfModules_iso`).

**Done**, as the theorem `AlgebraicGeometry.ComplexPoint.sectionSheafDeterminesClass` in
[`Other/AlgebraicGeometry/UnitExtensionClassOfSectionSheaf.lean`](../Other/AlgebraicGeometry/UnitExtensionClassOfSectionSheaf.lean).
No comparison of cohomology theories is involved. The pieces, in dependency order, are:

* [`HolomorphicLineBundleFrame.lean`](../Other/AlgebraicGeometry/HolomorphicLineBundleFrame.lean) —
  the canonical frame `E.frame i U hU` of the line bundle over an open subset of the `i`-th
  lifting neighbourhood, with fibre coordinates `x ↦ E.transitionValue i x x`; it generates
  (`holomorphicGenerates_frame`) and two such frames differ by the transition unit of the
  extension (`smul_frame`).
* [`UnitExtensionCorrectedLifts.lean`](../Other/AlgebraicGeometry/UnitExtensionCorrectedLifts.lean) —
  the datum `CorrectedLifts E E'`: opens `W z ∋ z` inside `E.localLifts.opens z`, lifts of the
  integer section `1` in `E'` over `W z` whose differences are *`E`'s* transition sections. Plus
  the local models `sourceModel`/`targetModel` (`i(a) + n • lift`) and their calculus.
* [`SheafHomOfLocalStalkMaps.lean`](../Other/AlgebraicGeometry/SheafHomOfLocalStalkMaps.lean) and
  [`UnitExtensionIntegerStalk.lean`](../Other/AlgebraicGeometry/UnitExtensionIntegerStalk.lean) —
  gluing a morphism of sheaves of abelian groups from a family of stalk maps that is locally
  represented by sections, and the local constancy of sections of the constant integer sheaf.
* [`UnitExtensionMiddleHom.lean`](../Other/AlgebraicGeometry/UnitExtensionMiddleHom.lean) — from
  `CorrectedLifts E E'`, the morphism `E.middle ⟶ E'.middle` under `𝒪ˣ` and over `ℤ`
  (`CorrectedLifts.middleHom`), hence `CorrectedLifts.cohomologyClass_eq`.
* [`UnitExtensionClassOfMiddleHom.lean`](../Other/AlgebraicGeometry/UnitExtensionClassOfMiddleHom.lean) —
  `ShortComplex.ShortExact.extClass_eq_of_middleHom`: a *morphism* (invertibility is not needed)
  of the middle terms commuting with the inclusions and the projections already equates the two
  `extClass`es, via `extClass_naturality`.
* [`UnitExtensionCorrectedLiftsOfIso.lean`](../Other/AlgebraicGeometry/UnitExtensionCorrectedLiftsOfIso.lean) —
  the frame changes `c_z` on `W z = E.localLifts.opens z ⊓ E'.localLifts.opens z` obtained from
  the isomorphism of section sheaves, the cocycle identity they satisfy
  (`frameChange_cocycle`), and the resulting `CorrectedLifts` datum
  (`CorrectedLifts.nonempty_correctedLifts`, via `CorrectedLifts.ofUnitCochain`).

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
image of `forgetSupport X |D|^an 2` — a class in cohomology with support in `|D|^an`.

*3a. Exactness of the support sequence.* **Done**, in
[`Other/AlgebraicGeometry/CohomologyWithSupportExact.lean`](../Other/AlgebraicGeometry/CohomologyWithSupportExact.lean):
`restrictToComplement X Z n := hypercohomologyMap X (rationalRestrictionComplexInt X Z) n` and
`exact_forgetSupport_restrictToComplement : Function.Exact (forgetSupport X Z n)
(restrictToComplement X Z n)`, from the mapping-cone triangle of `rationalRestrictionComplexInt`
and `Hom_D(ℤ_X, −)`.

*3b. The splitting kills the restricted extension class.* **Done**, in
[`Other/AlgebraicGeometry/UnitExtensionOpenRestriction.lean`](../Other/AlgebraicGeometry/UnitExtensionOpenRestriction.lean)
and its support file
[`Other/AlgebraicTopology/ConstantSheafGlobalSection.lean`](../Other/AlgebraicTopology/ConstantSheafGlobalSection.lean).
Write `T := j_* j^*` for `openRestrictionFunctor Ω` (the composite
`openRestrictionPushforward`, restriction to `Ω` followed by direct image, from
`Other/AlgebraicTopology/DerivedSheafSupport.lean`) and `η` for `restrictionUnit Ω`, its
canonical map `F ⟶ T F` (`toOpenRestrictionPushforward`). The theorem is

```lean
theorem HolomorphicUnitExtension.cohomologyClass_comp_restrictionUnit_eq_zero
    (E : HolomorphicUnitExtension X d) (Ω : Opens (TopCat.of (ComplexPoint X)))
    (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection) :
    E.cohomologyClass.comp
      (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1) = 0
```

The hypothesis `hℓ` is exactly "`E` splits over `Ω`": a global lift over `Ω` of the constant
integer section `1`, equivalently (`HolomorphicLineBundleFrame.lean`) a frame of
`E.sectionSheafOfModules` over `Ω`. No short exactness of `T` applied to the sequence is used.
The proof instead produces a *factorisation of `η` through the inclusion* and appeals to
`ShortComplex.ShortExact.extClass_comp`: an extension class dies against any morphism out of
`X₁` that factors through `X₂`. The factorisation is built as follows.

* `TopCat.Sheaf.constHomOfSection F t` — the morphism `ℤ_Y ⟶ F` determined by a global section
  `t` of `F`, sending the constant `n` to `n · t|_V`; `constHomOfSection_comp` (naturality in
  `F`) and `constHomOfSection_integerOne` (the section `1` gives `𝟙`). This is the only
  ingredient about constant sheaves that is needed; there is no need for the abstract
  `constantSheaf ⊣ Γ` adjunction.
* `HolomorphicUnitExtension.liftHom E Ω ℓ : ℤ_X ⟶ T E.middle` — `constHomOfSection` applied to
  `ℓ`, transported along `openRestrictionPushforwardTopEvaluationIso`
  (`Other/AlgebraicTopology/NestedSheafSupportOnOpen.lean`), which identifies `Γ(X, T F)` with
  `F(Ω)`. `liftHom_comp_projection` says `liftHom ≫ T(E.projection) = η_{ℤ}`; this is exactly
  `hℓ` read through that identification (`projection_liftSection`).
* `restrictedSection` — the adjoint of `liftHom` under `openSheafRestrictionAdjunction`
  (`Other/AlgebraicTopology/OpenSheafRestriction.lean`), a section of `j^*E.projection` over
  `Ω`; `restrictedSection_comp_projection` is the triangle identity.
* `shortExact_map_restrictToOpen` — `j^*` is exact (`openSheafRestriction_preservesFiniteLimits`
  and `…_preservesFiniteColimits`), so `j^*E` is short exact, and
  `ShortComplex.Splitting.ofExactOfSection` turns the section into a full splitting
  `restrictedSplitting`, whose retraction `r` satisfies `j^*(E.inclusion) ≫ r = 𝟙`.
* `restrictionFactorisation` — the adjoint of `r`, a morphism `E.middle ⟶ T 𝒪ˣ` with
  `inclusion_comp_restrictionFactorisation : E.inclusion ≫ restrictionFactorisation = η_{𝒪ˣ}`.

*3c. The restricted Chern class factors through the restricted extension class — proved.* In
[`Other/AlgebraicGeometry/ChernClassRestrictionVanishing.lean`](../Other/AlgebraicGeometry/ChernClassRestrictionVanishing.lean),
where `restrictedRationalChernClass X d Ω e` abbreviates
`restrictToComplement X (↑Ω)ᶜ 2 (integralToRationalCohomology X 2 ((analyticSheafCohomologyEquivExt
X (constantIntegerSheaf X) 2).symm (holomorphicFirstChernClass X d e)))`:

```lean
def HasRestrictedChernFactorization : Prop :=
  ∃ Φ : Abelian.Ext.{1} (constantIntegerSheaf X)
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) 1 →+
      Hypercohomology X
        (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 2,
    ∀ e, restrictedRationalChernClass X d Ω e =
      Φ (e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1))

def RestrictedChernClassVanishes : Prop :=
  ∀ e, e.comp (Abelian.Ext.mk₀ (restrictionUnit Ω (holomorphicUnitSheaf X d))) (add_zero 1) = 0 →
    restrictedRationalChernClass X d Ω e = 0
```

with `restrictedChernClassVanishes_of_factorization` deriving the second from the first. **Both
are now theorems**, `hasRestrictedChernFactorization` and `restrictedChernClassVanishes`, with
`#print axioms` reporting only `propext`, `Classical.choice`, `Quot.sound`. So the hypothesis
`hvan` of the two theorems of 3d (and of `exists_supportedChernLift_of_splitting`) is
dischargeable and only the splitting datum `ℓ` remains between step 3 and
`HasSupportedChernLift`.

The proof does **not** restrict the exponential sequence to `Ω` — that would need `Rj_*` of a
short exact sequence, which is the difficulty. It works entirely on `X`, as follows.

* Everything after the connecting map is postcomposition with a *morphism of complexes*
  `w : ℤ_X^• ⟶ j_*I^•` (`chernRestrictionTargetMap`, the rationalisation followed by
  `rationalRestrictionComplexInt`), so by associativity of `Localization.SmallShiftedHom.comp`
  and `analyticSheafCohomologyEquivExt_apply`,
  `restrictedRationalChernClass X d Ω e` is, up to the fixed isomorphism identifying the two
  presentations of the source `ℤ_X` (`analyticSheafComplexIntIsoSingle`), the composite of `e`
  with the *single* class
  `ζ' := ε.comp (mk₀ (isoℤ.inv ≫ w)) ∈ Hom_{D(X)}(𝒪ˣ, (j_*I^•)[1])`,
  where `ε` is the exponential extension class. This is
  `restrictedRationalChernClass_eq` and `analyticSheafCohomologyEquivExt_comp`.
* `ζ'` factors through `η : 𝒪ˣ ⟶ j_*(𝒪ˣ|_Ω)`. This is the new input, proved in
  [`Other/AlgebraicGeometry/OpenRestrictionDerivedFactorization.lean`](../Other/AlgebraicGeometry/OpenRestrictionDerivedFactorization.lean)
  as `exists_comp_restrictionUnit_eq`, from two facts:
  * `derivedPushforwardComplementConstantRationalComplexInt X Z` is K-injective
    (`CochainComplex.isKInjective_of_injective`, using the already proved termwise injectivity
    `derivedPushforwardComplementConstantRationalComplexInt_injective`), so a derived morphism
    from `single₀ 𝒪ˣ` into it is the class of an honest cocycle
    (`CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective`), and a cocycle from a
    single complex is just a morphism `𝒪ˣ ⟶ (j_*I^•)^n` killed by the differential
    (`Cocycle.fromSingleMk_surjective`);
  * each term `j_* I^n` is *local on `Ω`*: precomposition with `η` is a **bijection**
    `Hom(j_*j^*F, j_*S) ≅ Hom(F, j_*S)`. This is `TopCat.Sheaf.isOpenRestrictionLocal_pushforward`
    in [`Other/AlgebraicGeometry/OpenRestrictionLocalSheaf.lean`](../Other/AlgebraicGeometry/OpenRestrictionLocalSheaf.lean),
    proved from the adjunction `j^* ⊣ j_*` (`openSheafRestrictionAdjunction`, whose unit *is*
    `restrictionUnit`) together with `IsIso (j^* η)`, which follows from the counit of that
    adjunction being an isomorphism (`isIso_openSheafRestrictionCounit_app`; on an open `V ⊆ Ω`
    the counit is restriction of sections along `j^{-1}(j(V)) = V`). The terms of the complex in
    degrees outside `ℕ` are zero, hence trivially local; the terms in degree `n` are direct
    images along `Ω.inclusion'` because the inclusion of `Zᶜ` factors through `Ω` whenever
    `↑Ω = Zᶜ` (`complementToOpen`, `analyticComplementInclusion_eq`, both `rfl`-level).
  Surjectivity of the precomposition produces the cocycle on `j_*(𝒪ˣ|_Ω)`; injectivity in the
  next degree gives its cocycle condition.
* Then `Φ` is composition with the resulting class `ζ`, read through
  `analyticSheafCohomologyAddEquivExt` (the additive form of `analyticSheafCohomologyEquivExt`,
  `analyticSheafCohomologyEquivExt_add`) and `hypercohomologyCompHom`; the required identity is
  associativity of `SmallShiftedHom.comp` three times.

> **Warning (still relevant).** Do *not* reduce the problem to the underived group
> `Ext²_X(ℤ_X, j_*ℚ_Ω)`. The map `restrictToComplement ∘ integralToRationalCohomology` does factor
> through it — because `rationalRestrictionComplexInt X Z` factors as `analyticSheafComplexIntMap
> X (rationalRestrictionSheaf X Z)` followed by the resolution map — but vanishing in
> `Ext²_X(ℤ_X, j_*ℚ_Ω)` is *strictly stronger* than vanishing in `H²(Ω, ℚ)` and there is no
> reason for it to hold: the kernel of `Ext²_X(ℤ_X, j_*ℚ_Ω) → Ext²_X(ℤ_X, Rj_*ℚ_Ω)` is not zero.
> The correspondingly-shaped factorisation of the exponential connecting class through
> `𝒪ˣ_X → j_*(𝒪ˣ|_Ω)` at the *underived* level would need `j_*` of the exponential sequence on
> `Ω` to be right exact, which fails (`R¹j_*ℤ ≠ 0`). The proof above avoids it by working with
> the K-injective model `j_*I^•` throughout.

*3d. The conclusion of step 3.* Also in `ChernClassRestrictionVanishing.lean`, from 3a, 3b, 3c:

```lean
theorem restrictToComplement_integralToRational_firstChernClass_eq_zero
    (hvan : RestrictedChernClassVanishes X d Ω) (E : HolomorphicUnitExtension X d)
    (ℓ : E.middle.obj.obj (op Ω)) (hℓ : …) :
    restrictToComplement X ((Ω : Set (ComplexPoint X))ᶜ) 2
      (integralToRationalCohomology X 2 E.firstChernClass) = 0

theorem exists_forgetSupport_eq_integralToRational_firstChernClass
    (hvan : RestrictedChernClassVanishes X d Ω) (E : HolomorphicUnitExtension X d)
    (ℓ : E.middle.obj.obj (op Ω)) (hℓ : …) :
    ∃ β : RationalCohomologyWithSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2,
      forgetSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2 β =
        integralToRationalCohomology X 2 E.firstChernClass
```

In the application `Ω` is the analytic complement of `|D|^an`, so `Z = (↑Ω)ᶜ = |D|^an`.

**Step 4 — the local model** (missing (c)) **and conclusion.** On the smooth locus of a component
`Z` with multiplicity `n_Z`, in a normal chart the divisor is `{z₁ = 0}` and the transition
cocycle is that of `z₁^{n_Z}`; the supported class is `n_Z` times the normalised normal-chart
coclass `cycleComponentSmoothSupportCoclassSection`. Then
`cycleComponentSupportedInjectiveClass_unique` identifies the component contributions of the
supported lift of `E.firstChernClass` with `n_Z · cycleComponentSupportedInjectiveClass`, and
forgetting support together with additivity gives exactly the equation of §3. This step fixes the
sign.

Step 4 is now carried out in two files:

* [`Other/AlgebraicGeometry/DivisorClassComparisonSupport.lean`](../Other/AlgebraicGeometry/DivisorClassComparisonSupport.lean)
  — the support bookkeeping, **entirely proved**;
* [`Other/AlgebraicGeometry/ChernLocalModel.lean`](../Other/AlgebraicGeometry/ChernLocalModel.lean)
  — the two remaining propositions and the **proved** assembly
  `hasDivisorClassOfSomeCartierData_of_localModel`;
* [`Other/AlgebraicGeometry/SupportEnlargementCodimTwo.lean`](../Other/AlgebraicGeometry/SupportEnlargementCodimTwo.lean)
  — **proved**: for Zariski-closed `Z ≤ Z'` such that every point of `Z' ∖ Z` has coheight at
  least two, the support-enlargement map
  `enlargeSupportedInjectiveHomology X _ 2 : H²_{Z^an} → H²_{Z'^an}` is bijective
  (`enlargeSupportedInjectiveHomology_bijective_of_codimTwo`), so every degree-two class
  supported on `Z'^an` descends to a class supported on `Z^an` with the same ordinary class
  (`exists_enlarge_eq_of_codimTwo`). The proof splits `Z'` as `Z ∪ W` with `W` the union of the
  irreducible components of `Z'` not contained in `Z` (all of codimension at least two), and
  reads the bijectivity off the two splitting short exact sequences of
  `SupportUnionSplitting.lean` together with the vanishing of `H^{<4}` along `W^an` and
  `(W ∩ Z)^an` from `ClosedSupportCoheightDimension.lean`.

*A correction to the statement drafted here previously.* The earlier draft of `HasChernLocalModel`
quantified over a class `β : RationalCohomologyWithSupport X (cycleComponentSupport X x) 2`
supported on a **single** component with `forgetSupport β = c₁`. That is wrong: when `D` has more
than one component no such `β` exists — `c₁` restricted to the complement of one component need
not vanish — so the drafted proposition was vacuous, and useless. What step 3 delivers is a class
supported on the analytic support `|D|^an` of the **whole** divisor, and the comparison target is
the finite sum `∑_x n_x · cycleComponentSheafClass X x`. The statement is therefore split into a
*decomposition* obligation and a *local model* obligation. The route taken is variant (ii) of the
three considered — a Mayer–Vietoris/excision decomposition — because variants (i) and (iii) need
the same codimension-two vanishing anyway: `cycleComponentSmoothSupportAmbientOpen X x` is
`X^an ∖ Sing(Z_x)`, which still meets every other component of `D`, so neither the restriction of
`β` to it nor the uniqueness theorem `cycleComponentSupportedInjectiveClass_unique` sees a single
component until the other components have been removed, and removing them is exactly the
codimension-two excision.

*The support bookkeeping (proved).* All of it is stated inside the concrete "supported injective
sections" model, which is where both `cycleComponentSupportedInjectiveClass` and
`rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport` already live, so no further
comparison of models is needed:

```lean
abbrev SupportedInjectiveHomology (S : Closeds (ComplexPoint X)) (n : ℤ) :=
  ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj (complexSupportInjectiveComplex X S)).homology n)

def enlargeSupportedInjectiveHomology {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ) :
    SupportedInjectiveHomology X S n ⟶ SupportedInjectiveHomology X T n

def supportedInjectiveToAmbient (S : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedInjectiveHomology X S n ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
        S.compl ⊤ (ambientRationalInjectiveComplex X)).X₂.homology n

theorem supportedInjectiveToAmbient_enlarge {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ)
    (a : SupportedInjectiveHomology X S n) :
    supportedInjectiveToAmbient X T n (enlargeSupportedInjectiveHomology X h n a) =
      supportedInjectiveToAmbient X S n a
```

The enlargement map is the coefficient-level `TopCat.Sheaf.sheafSectionsWithClosedSupportMap`
(support-enlargement is the inclusion of kernels of restriction maps), and
`supportedInjectiveToAmbient_enlarge` is `sheafSectionsSupportedOutsideMap_inclusion` transported
through `mapHomologicalComplex` and `homologyMap`. Two identifications make the two sides of §3
computable in this model, and both hold by `rfl`:

* `cycleComponentSheafClass X x hx =
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
    (supportedInjectiveToAmbient X (cycleComponentAnalyticClosedSupport X x) (2 * (p : ℤ))
      (cycleComponentSupportedInjectiveClass X x hx))` — this *is* the definition of
  `cycleComponentSheafClass`;
* `rationalCohomologyAddEquivAmbientInjectiveHomology X n (forgetSupport X ↑S n β) =
  supportedInjectiveToAmbient X S n (rationalSupportAddEquivSupportedInjectiveHomology X ↑S S.isClosed n β)`
  — this is `rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport`.

Also proved there: the analytic support of a finite family of components,
`componentsAnalyticClosedSupport X s := s.sup (fun x ↦ cycleComponentAnalyticClosedSupport X x)`,
its one-component enlargements `componentContribution X s x n a` (zero off `s`), the finite
component set `cycleComponents D := (compactCycleToFinsupp D.1).support` of a codimension-one
cycle with `coheight_of_mem_cycleComponents`, and the explicit finite-sum formula

```lean
theorem sheafCycleClassOnCycles_eq_sum (D : CodimensionCycle X.left 1) :
    sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
      ∑ x ∈ cycleComponents X D, D.1 x •
        (if hx : coheight x = ((1 : ℕ) : ℕ∞) then
            cycleComponentSheafClass X x (d := dim X.left) hx else 0)
```

*The corrected propositions.* In
[`ChernLocalModel.lean`](../Other/AlgebraicGeometry/ChernLocalModel.lean), writing
`cycleAnalyticClosedSupport X D := componentsAnalyticClosedSupport X (cycleComponents X D)` for
`|D|^an`:

```lean
/-- **Step 3 output (no longer a hypothesis of the assembly).** *Some* supported lift exists. This
is exactly the conclusion of `exists_forgetSupport_eq_integralToRational_firstChernClass` for
`Ω := (cycleAnalyticClosedSupport X c.divisor).compl`. It is strictly weaker than
`HasChernLocalModel`, which asks for the *normalised* lift; see the warning below. -/
def HasSupportedChernLift : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : RationalCohomologyWithSupport X
          ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
            Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)),
        forgetSupport X _ (2 * ((1 : ℕ) : ℤ)) β =
          integralToRationalCohomology X 2 E.firstChernClass

/-- **Excision in codimension one** (no longer an obligation: proved unconditionally in
`Other/AlgebraicGeometry/ComponentSupportDecomposition.lean` and
`Other/AlgebraicGeometry/ClosedSupportCoheightDimension.lean`, see below). A degree-two class
supported on a finite union
of codimension-one component supports is a sum of classes supported on the individual
components. -/
def HasComponentSupportDecomposition : Prop :=
  ∀ (s : Finset X.left), (∀ x ∈ s, coheight x = ((1 : ℕ) : ℕ∞)) →
    ∀ β : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s)
        (2 * ((1 : ℕ) : ℤ)),
      ∃ γ : ∀ x : X.left,
          SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
            (2 * ((1 : ℕ) : ℤ)),
        β = ∑ x ∈ s, componentContribution X s x (2 * ((1 : ℕ) : ℤ)) (γ x)

/-- **Obligation: the local model.** There *exists* a supported lift of the first Chern class —
the relative first Chern class cut out by the frame of the bundle off `|D|^an` — such that in any
decomposition of it, the piece supported on the component of `x` normalises, on the smooth locus
of that component, to `c.divisor x` times the normal-chart coclass. -/
def HasChernLocalModel : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor)
          (2 * ((1 : ℕ) : ℤ)),
        supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor)
            (2 * ((1 : ℕ) : ℤ)) β =
          rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
            (integralToRationalCohomology X 2 E.firstChernClass) ∧
        ∀ γ : ∀ x : X.left,
            SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
              (2 * ((1 : ℕ) : ℤ)),
          β = ∑ x ∈ cycleComponents X c.divisor,
              componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
          ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
            (cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x) =
              (c.divisor x) • cycleComponentSmoothSupportCoclassSection X x (d := dim X.left) hx
```

> **A second correction (important).** An earlier form of `HasChernLocalModel` quantified
> **universally** over every `β` lifting the first Chern class. *That statement is false*, and the
> assembly therefore rested on an unprovable hypothesis. The supported lift is not unique: by the
> exactness of the support sequence (§4.3 step 3a) two lifts differ by an element of the image of
> `H¹(X^an ∖ |D|^an, ℚ)` under the connecting map, and such a difference *does* change the local
> multiplicities.
>
> *Counterexample.* `X = ℙ¹`, `L = 𝒪`, rational section `s = z`. Then `D = [0] − [∞]` and
> `c₁(L) = 0`. Supported cohomology `H²_{\{0,∞\}}(ℙ¹, ℚ) ≅ ℚ²`, with coordinates the two local
> coclasses, and `forgetSupport : ℚ² → ℚ` is the sum map (`H²(ℙ¹, ℚ) ≅ ℚ`). Both `β = (1, −1)` and
> `β = (2, −2)` satisfy `forgetSupport β = 0 = c₁`; only the first has the local multiplicities
> `(1, −1)` of `D`. Their difference `(1, −1)` is exactly the image of the generator of
> `H¹(ℙ¹ ∖ \{0, ∞\}, ℚ) ≅ ℚ` (the winding class of `z` on `ℂ^×`).
>
> So the statement must be existential in `β`, and the witness must be *constructed*. The
> decomposition `γ` may still be quantified universally: it is unique, because the codimension-two
> vanishing makes the enlargement maps jointly **bijective**, not merely surjective.
>
> As a consequence `HasSupportedChernLift` is **no longer a hypothesis of the assembly**: it is the
> bare existence of *some* lift, which is strictly weaker than what is needed and is implied by
> `HasChernLocalModel`. It is kept in the file because it records the conclusion of step 3 and
> because its bridge `exists_supportedChernLift_of_splitting` is where the splitting datum enters.

*What the canonical lift is — Route A, now carried out.* The right witness is the **relative
first Chern class** `c₁(L, s) ∈ H²_{|D|^an}(X^an, ℚ)` of the pair (line bundle, rational section).
The frame of `L^an` on `Ω := X^an ∖ |D|^an` supplied by `s` gives a *splitting* of the restricted
extension `j^* E`, not merely the vanishing of the restricted class; step 3 built that splitting
(`restrictedSplitting`, `restrictionFactorisation` in `UnitExtensionOpenRestriction.lean`) and then
threw it away, keeping only the vanishing. Route A keeps it, and is **now formalised**, in

* [`Other/AlgebraicGeometry/ChernRelativeClass.lean`](../Other/AlgebraicGeometry/ChernRelativeClass.lean)
  — the construction of the canonical relative class and the proof that it lifts `c₁`;
* [`Other/AlgebraicGeometry/ChernRelativeClassNaturality.lean`](../Other/AlgebraicGeometry/ChernRelativeClassNaturality.lean)
  — its transport into the supported injective model, and the resulting reduction of
  `HasChernWindingNaturality` to a statement about *one explicitly constructed class*.

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for everything below.

**(i) The canonical relative class, with no choice at all.** The key observation is that the
mapping cone of a morphism of *complexes* is functorial for honest commutative squares, so the
splitting produces a canonical derived morphism, not merely an existence statement. Write
`Sgl` for `CochainComplex.singleFunctor _ 0`, `η := restrictionUnit Ω 𝒪ˣ` and
`R := E.restrictionFactorisation Ω ℓ hℓ`, so that `E.inclusion ≫ R = η` (step 3b). Then:

```lean
abbrev relativeUnitCone (Ω) : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone (Sgl.map (restrictionUnit Ω (holomorphicUnitSheaf X d)))

abbrev relativeUnitConeδ (Ω) :                         -- forget the trivialisation on `Ω`
    ShiftedHom (relativeUnitCone X d Ω) (Sgl.obj (holomorphicUnitSheaf X d)) 1 :=
  (CochainComplex.mappingCone.triangle (Sgl.map (restrictionUnit Ω _))).mor₃

def HolomorphicUnitExtension.relativeConeMap (E Ω ℓ hℓ) :          -- `cone(i) ⟶ cone(η)`
    E.inclusionCone ⟶ relativeUnitCone X d Ω :=
  CochainComplex.mappingCone.map _ _ (𝟙 _) (Sgl.map (E.restrictionFactorisation Ω ℓ hℓ)) _

def HolomorphicUnitExtension.relativeCohomologyClass (E Ω ℓ hℓ) :
    SmallShiftedHom (analyticQuasiIsomorphisms X) (Sgl.obj (constantIntegerSheaf X))
      (relativeUnitCone X d Ω) 0 :=
  (SmallShiftedHom.precompEquiv E.coneToInteger _).symm (SmallShiftedHom.mk₀ _ 0 rfl
    (E.relativeConeMap Ω ℓ hℓ))
```

Here `E.coneToInteger := CochainComplex.mappingCone.descShortComplex (Sgl E.shortComplex)` is the
canonical **quasi-isomorphism** `cone(Sgl E.inclusion) ⟶ Sgl ℤ` of a short exact sequence
(`CochainComplex.mappingCone.quasiIso_descShortComplex`), so `precompEquiv` inverts it. The two
theorems that make this the right object are

```lean
theorem HolomorphicUnitExtension.mk₀_coneToInteger_comp_cohomologyClass :
    (mk₀ W 0 rfl E.coneToInteger).comp E.cohomologyClass (add_zero 1) =
      SmallShiftedHom.mk W (CochainComplex.mappingCone.triangle E.singleShortComplex.f).mor₃

theorem HolomorphicUnitExtension.relativeCohomologyClass_comp_relativeUnitConeδ :
    (E.relativeCohomologyClass Ω ℓ hℓ).comp (mk W (relativeUnitConeδ X d Ω)) (add_zero 1) =
      E.cohomologyClass
```

The first identifies `ShortComplex.ShortExact.extClass` with the connecting morphism of the
mapping-cone triangle after precomposition with the quasi-isomorphism (it is `extClass_hom`,
`DerivedCategory.descShortComplex_triangleOfSESδ` and the fact that the components of
`singleFunctorsPostcompQIso` are identities). The second is then the third square of
`CochainComplex.mappingCone.triangleMap` for the square `(𝟙, Sgl R)`, whose `hom₁` is the
identity — this is exactly "the relative class lifts the extension class".

**(ii) From the relative unit cone to supported rational cohomology.** What remains is a
comparison `cone(η) ⟶ Cone(ℚ_X → Rj_*ℚ_Ω)[1]`, packaged as

```lean
structure RelativeChernComparison (Y) (e) (V) where
  hom : SmallShiftedHom W (relativeUnitCone Y e V)
    (rationalCohomologyWithSupportComplex Y (↑V)ᶜ) 1
  comm : hom.comp (forgetSupportShiftedHom Y (↑V)ᶜ) _ =
    (SmallShiftedHom.mk W (relativeUnitConeδ Y e V)).comp (rationalChernShiftedHom Y e) _
```

where `rationalChernShiftedHom X d : SmallShiftedHom W (Sgl 𝒪ˣ) (ℚ_X^•) 1` is the exponential
connecting class followed by the rationalisation. **Its existence is proved**:

```lean
theorem nonempty_relativeChernComparison (Ω) : Nonempty (RelativeChernComparison X d Ω)
```

by the axiom TR3 applied to the square `η ≫ ζ = ζ₀ ≫ m₁`, which is precisely the factorisation
`exists_comp_restrictionUnit_eq` of step 3c (the target triangle is the restriction triangle
shifted by `1`, whence the signs `Int.negOnePow 1 = -1` and `shiftFunctorComm_eq_refl`).

Given the datum, the relative first Chern class is a *definition*, and lifts `c₁`:

```lean
def HolomorphicUnitExtension.relativeChernClass (E Ω ℓ hℓ) (cmp : RelativeChernComparison X d Ω) :
    RationalCohomologyWithSupport X (↑Ω)ᶜ 2 :=
  (E.relativeCohomologyClass' Ω ℓ hℓ).comp cmp.hom _

theorem HolomorphicUnitExtension.forgetSupport_relativeChernClass :
    forgetSupport X (↑Ω)ᶜ 2 (E.relativeChernClass Ω ℓ hℓ cmp) =
      integralToRationalCohomology X 2 E.firstChernClass
```

(`relativeCohomologyClass'` is `relativeCohomologyClass` precomposed with
`analyticSheafComplexIntIsoSingle`, so that its source is the integral constant *complex* used by
`Hypercohomology`; `cohomologyClass_comp_rationalChernShiftedHom` is the computation
`c₁ = e ∘ ζ₀` in that presentation.) Combining, `exists_relativeChernClass` re-proves step 3's
conclusion **with a canonical witness** rather than by bare exactness.

**(iii) The consequence for step 4.** In
`Other/AlgebraicGeometry/ChernRelativeClassNaturality.lean` the relative class is transported into
the supported injective model along `rationalSupportAddEquivSupportedInjectiveHomology` (the only
bookkeeping is `compl_compl`, packaged as `supportedClassTransport`), giving

```lean
def relativeChernSupportedClass (c E ℓ hℓ cmp) :
    SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor) (2 * (1 : ℤ))

theorem supportedInjectiveToAmbient_relativeChernSupportedClass :
    supportedInjectiveToAmbient X _ _ (relativeChernSupportedClass c E ℓ hℓ cmp) =
      rationalCohomologyAddEquivAmbientInjectiveHomology X _
        (integralToRationalCohomology X 2 E.firstChernClass)
```

— i.e. **the first clause of `HasChernLocalModel` / `HasChernWindingNaturality` is now a theorem
for the canonical witness.** The existential quantifier over the lift, which was the delicate
point of step 4 (see the `ℙ¹` warning above), is therefore discharged, and what is left of
obligation (a) is a statement about *one explicitly constructed class*:

```lean
/-- the frame off `|D|^an` supplied by the rational section (the step-3 splitting datum) -/
def HasComplementFrame : Prop :=
  ∀ E L hL iso, ∀ c : Scheme.CartierData X.left, c.Represents L →
    ∃ ℓ : E.middle.obj.obj (op (divisorComplementOpen c)),
      E.projection.hom.app _ ℓ = (constantIntegerSheaf X).obj.map (homOfLE le_top).op
        HolomorphicUnitExtension.integerOneSection

/-- the chart formula for the canonical relative class -/
def HasRelativeChernChartFormula : Prop :=
  ∀ c E ℓ hℓ cmp γ, relativeChernSupportedClass c E ℓ hℓ cmp =
      ∑ x ∈ cycleComponents X c.divisor, componentContribution X _ x _ (γ x) →
    ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = 1,
    ∀ q (ch : ChernWindingChart X c x (dim X.left) 1 q),
      ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
      ch.ComputesClass (c.divisor x)
        ((cycleComponentSupportedClassNormalizationIso X x hx).hom (γ x))

theorem hasChernWindingNaturality_of_relativeChernChartFormula
    (hframe : HasComplementFrame X) (hchart : HasRelativeChernChartFormula X) :
    HasChernWindingNaturality X

theorem hasDivisorClassOfSomeCartierData_of_relativeChernChartFormula
    (hframe : HasComplementFrame X) (hcharts : HasNormalizedWindingCharts X)
    (hchart : HasRelativeChernChartFormula X) :
    HasDivisorClassOfSomeCartierData X
```

Note that `HasRelativeChernChartFormula` already *is* the "naturality under restriction to opens"
statement asked for by Route A: `cycleComponentSupportedClassNormalizationIso` sends a class
supported on one component to a **section over the smooth-support open of the
relative-cohomology sheaf** `supportRelativeCohomologySheaf`, and `ChernWindingChart.ComputesClass`
compares its restriction to the chart `V` with the winding class there. So the restriction maps
needed are the sheaf restrictions of `supportRelativeCohomologySheaf`, which already exist; no
separate theory of restriction of supported cohomology to opens is required.

*Route B (characterisation), for reference.* One could instead characterise the canonical lift as
the unique class whose restriction near each smooth point of each component is the winding class
of the transition function, and prove existence by gluing the local winding classes over a cover
of `|D|^an` (uniqueness being the codimension-two vanishing again). Route A above makes this
unnecessary for the *existence* of the witness; the gluing statement is exactly what
`HasRelativeChernChartFormula` now asserts for the already-constructed class.

So **what is left of §4.3 step 4 is: `HasNormalizedWindingCharts` and
`HasRelativeChernChartFormulaGeneric`** (see the codimension-two subsection below: the frame
input `HasComplementFrame` has been replaced by the unconditional
`hasComplementFrameOffCodimTwo`, and the resulting change of support is absorbed by the proved
excision `enlargeSurjectiveCodimTwo`). The first is the pure one-variable analysis, scoped in
`ChernLocalModelWinding.lean` and `ChernWinding*.lean`. The second is the Chern-class half, now
stated about a single explicit class rather than about an existentially quantified lift.

In the `|D|^an`-supported form stated just above, the three inputs were `HasComplementFrame`,
`HasNormalizedWindingCharts` and `HasRelativeChernChartFormula`; that form is kept because it is
the cleanest statement, and because `HasComplementFrame` is proved from the algebraic Hartogs
statement `HasStalkUnitOfOrdEqZero` (next subsection). The unconditional route runs through the
codimension-two enlargement instead.

*`HasComplementFrame`, reduced to algebraic Hartogs.* In
[`Other/AlgebraicGeometry/ComplementFrame.lean`](../Other/AlgebraicGeometry/ComplementFrame.lean)
the frame off the divisor is **proved from a single algebraic statement**:

```lean
/-- the local equations are units off the divisor -/
def HasUnitOffDivisor : Prop :=
  ∀ (c : Scheme.CartierData X.left) (i : c.ι) (p : X.left), p ∈ c.opens i →
    (∀ y, c.divisor y ≠ 0 → p ∉ closure {y}) →
    ∃ (V : X.left.Opens) (hp : p ∈ V), V ≤ c.opens i ∧
      ∃ v : Γ(X.left, V), IsUnit v ∧ X.left.germToFunctionField V v = c.fn i

/-- its stalk-level form: algebraic Hartogs at `𝒪_{X,p}` -/
def HasStalkUnitOfOrdEqZero : Prop :=
  ∀ (p : X.left) (f : X.left.functionField), f ≠ 0 →
    (∀ y, coheight y = 1 → y ⤳ p → X.left.ord f y = 0) →
    ∃ u : (X.left.presheaf.stalk p)ˣ, algebraMap _ X.left.functionField u = f

theorem hasUnitOffDivisor_of_stalkUnit : HasStalkUnitOfOrdEqZero X → HasUnitOffDivisor X
theorem hasComplementFrame_of_unitOffDivisor : HasUnitOffDivisor X → HasComplementFrame X
theorem hasComplementFrame_of_stalkUnit : HasStalkUnitOfOrdEqZero X → HasComplementFrame X
theorem hasChernWindingNaturality_of_unitOffDivisor (hunit : HasUnitOffDivisor X)
    (hchart : HasRelativeChernChartFormula X) : HasChernWindingNaturality X
theorem hasDivisorClassOfSomeCartierData_of_unitOffDivisor (hunit : HasUnitOffDivisor X)
    (hcharts : HasNormalizedWindingCharts X) (hchart : HasRelativeChernChartFormula X) :
    HasDivisorClassOfSomeCartierData X
```

Everything analytic is done there: the local sections `v • gᵢ|_V` of `L` are restrictions of one
rational section (`UnitDatum.localSection_agree`, from `Represents` and the injectivity of the
germ map on nonempty opens), they analytify to generating frames of `E.sectionSheafOfModules`
(`analytificationGenerates`) agreeing on overlaps, each differs from `E.frame z` by a
nowhere-vanishing holomorphic function (`frameUnit`), the corrected local lifts
`lift_z − ι(frameUnit)` of `1` agree on overlaps (`frameUnit_cocycle`, `localLift_compatible`),
and they glue in the sheaf `E.middle` (`existsUnique_gluing'`). **What is missing is exactly
`HasStalkUnitOfOrdEqZero`**: for the regular local ring `𝒪_{X,p}`, a rational function which is a
unit at every height-one prime is a unit. This is `𝒪_{X,p} = ⋂_{ht 𝔮 = 1} (𝒪_{X,p})_𝔮`, i.e. the
normality of regular local rings (Auslander–Buchsbaum, or Serre's `R₁ + S₂`) together with the
intersection description of a Noetherian normal domain; neither is in Mathlib. Note that the
"unit off the support" statement cannot be obtained from `CartierLocalForm.lean`: the local form
`c.fn i = u · h^{c.divisor x}` exists only on a neighbourhood of a *codimension-one* point `x`, and
a closed point off `|D|` need not lie in any such neighbourhood; the unit statement at a closed
point of a variety of dimension `≥ 2` genuinely needs normality.

*Avoiding Hartogs: enlarge the closed set.* In
[`Other/AlgebraicGeometry/ComplementFrameGeneric.lean`](../Other/AlgebraicGeometry/ComplementFrameGeneric.lean)
the frame is obtained **unconditionally** off a larger closed set. The *good locus*
`goodLocus c` (points carrying unit data) is Zariski open; its complement `badLocus c` contains
every component of the divisor (`closure_subset_badLocus`) and, off those components, consists of
points of coheight `≥ 2` (`two_le_coheight_of_mem_badLocus`: the generic point is good, and a
codimension-one point off the divisor is good because its stalk is a DVR in which a rational
function of order zero is a unit, which spreads to a basic open). The gluing of
`ComplementFrame.lean` then applies on the analytic complement (`exists_lift_of_goodLocus`):

```lean
def HasComplementFrameOffCodimTwo : Prop :=
  ∀ E L, IsInvertible L → (L^an ≅ E.sectionSheafOfModules) → ∀ c, c.Represents L →
    ∃ Z' : Closeds X.left,
      (∀ y, c.divisor y ≠ 0 → closure {y} ⊆ Z') ∧
      (∀ z ∈ Z', (∀ y, c.divisor y ≠ 0 → z ∉ closure {y}) → (2 : ℕ∞) ≤ coheight z) ∧
      ∃ ℓ : E.middle.obj.obj (op (analyticClosedSupport X Z').compl),
        E.projection.hom.app _ ℓ = (constantIntegerSheaf X).obj.map (homOfLE le_top).op integerOneSection

theorem hasComplementFrameOffCodimTwo : HasComplementFrameOffCodimTwo X   -- proved
theorem cycleAnalyticClosedSupport_le_analyticClosedSupport (c) (Z')
    (h : ∀ y, c.divisor y ≠ 0 → closure {y} ⊆ Z') :
    cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z'
```

*The relative Chern class for the enlarged support, and the restatement — done.* In
[`Other/AlgebraicGeometry/ChernRelativeClassGeneric.lean`](../Other/AlgebraicGeometry/ChernRelativeClassGeneric.lean).
Nothing in `ChernRelativeClass.lean` refers to the divisor: the canonical relative class is built
from a frame over the complement of an *arbitrary* open set, so it applies verbatim to
`Ω' := (analyticClosedSupport X Z').compl`. The generic forms are

```lean
def relativeChernClassOnClosed (S : Closeds (ComplexPoint X)) (E ℓ hℓ)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    RationalCohomologyWithSupport X (S : Set (ComplexPoint X)) 2 :=
  supportedClassTransport X (compl_compl _) 2 (E.relativeChernClass S.compl ℓ hℓ cmp)

def relativeChernSupportedClassOnClosed (S E ℓ hℓ cmp) :
    SupportedInjectiveHomology X S (2 * (1 : ℤ)) :=
  rationalSupportAddEquivSupportedInjectiveHomology X ↑S S.isClosed _
    (relativeChernClassOnClosed S E ℓ hℓ cmp)

theorem supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed :
    supportedInjectiveToAmbient X S (2 * (1 : ℤ)) (relativeChernSupportedClassOnClosed S E ℓ hℓ cmp)
      = rationalCohomologyAddEquivAmbientInjectiveHomology X _
          (integralToRationalCohomology X 2 E.firstChernClass)
```

(`supportedClassTransport` is the transport of `RationalCohomologyWithSupport` along an equality
of supports, proved by `subst`; the whole generalisation is that bookkeeping plus `compl_compl`.)

The class supported on `|D|^an` is then recovered from the class supported on `(Z')^an` by
*excision in codimension two*, which is the only extra input the enlargement costs:

```lean
def EnlargeSurjectiveCodimTwo : Prop :=
  ∀ (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z'),
    (∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z) →
    ∀ β' : SupportedInjectiveHomology X (analyticClosedSupport X Z') (2 * (1 : ℤ)),
      ∃ β : SupportedInjectiveHomology X (analyticClosedSupport X Z) (2 * (1 : ℤ)),
        enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ') _ β = β'

theorem enlargeSurjectiveCodimTwo : EnlargeSurjectiveCodimTwo X   -- proved
```

the last being `exists_enlarge_eq_of_codimTwo` of
[`SupportEnlargementCodimTwo.lean`](../Other/AlgebraicGeometry/SupportEnlargementCodimTwo.lean).
(`exists_enlarge_of_analyticClosedSupport_eq` restates it with the two analytic supports supplied
as closed analytic sets together with equalities, so that no transport is needed at the point of
use; the equality used is `analyticClosedSupport_componentsZariskiSupport`, which identifies the
analytic support of the Zariski support of the divisor with `cycleAnalyticClosedSupport`.)

The chart formula is restated for this situation — same shape as
`HasRelativeChernChartFormula`, with the extra `Z'`, the class `β` supported on `|D|^an`, and the
equation pinning `β` by its enlargement:

```lean
def HasRelativeChernChartFormulaGeneric : Prop :=
  ∀ (c) (E) (Z' : Closeds X.left)
    (hle : cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z')
    (ℓ : E.middle.obj.obj (op (analyticClosedSupport X Z').compl)) (hℓ)
    (cmp : RelativeChernComparison X (dim X.left) (analyticClosedSupport X Z').compl)
    (β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor) (2 * (1 : ℤ))),
    enlargeSupportedInjectiveHomology X hle (2 * (1 : ℤ)) β =
        relativeChernSupportedClassOnClosed (analyticClosedSupport X Z') E ℓ hℓ cmp →
      ∀ γ, β = ∑ x ∈ cycleComponents X c.divisor, componentContribution X _ x _ (γ x) →
      ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = 1,
      ∀ q (ch : ChernWindingChart X c x (dim X.left) 1 q),
        ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
        ch.ComputesClass (c.divisor x)
          ((cycleComponentSupportedClassNormalizationIso X x hx).hom (γ x))
```

and the reductions are proved, **with both the frame and the excision inputs discharged**:

```lean
theorem hasChernWindingNaturality_of_generic
    (hframe : HasComplementFrameOffCodimTwo X) (henl : EnlargeSurjectiveCodimTwo X)
    (hchart : HasRelativeChernChartFormulaGeneric X) : HasChernWindingNaturality X

theorem hasDivisorClassOfSomeCartierData_of_generic
    (hframe) (henl) (hcharts : HasNormalizedWindingCharts X) (hchart) :
    HasDivisorClassOfSomeCartierData X

theorem hasChernWindingNaturality_of_relativeChernChartFormulaGeneric
    (hchart : HasRelativeChernChartFormulaGeneric X) : HasChernWindingNaturality X

theorem hasDivisorClassOfSomeCartierData_of_relativeChernChartFormulaGeneric
    (hcharts : HasNormalizedWindingCharts X) (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasDivisorClassOfSomeCartierData X
```

The witness `β` is the pullback along the enlargement map of the relative first Chern class of the
frame; the first clause of `HasChernWindingNaturality` is `supportedInjectiveToAmbient_enlarge`
together with `supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed`. `#print axioms`
reports only `propext`, `Classical.choice`, `Quot.sound` for all of these.

**So step 4 no longer needs `HasComplementFrame` (hence no algebraic Hartogs): what is left of it
is `HasNormalizedWindingCharts` and `HasRelativeChernChartFormulaGeneric`.**


*Non-vacuity.* The previous draft of this step was vacuous, so the new statements come with a
check: `exists_componentContribution_sum_singleton` proves
`HasComponentSupportDecomposition`'s conclusion for a one-element family, from
`componentsAnalyticClosedSupport_singleton` and `enlargeSupportedInjectiveHomology_refl`
(enlargement along the identity is the identity). In particular the obligation is satisfiable, and
it is exactly the multi-component content that is missing.

Note that `HasChernLocalModel` quantifies over *every* decomposition `γ` of its `β`. That is the
honest statement: mathematically the decomposition is unique (the enlargement maps are jointly
*bijective*, not merely surjective, again by the codimension-two vanishing), so nothing is lost,
and phrasing it this way avoids having to state and prove injectivity separately. The lift `β`
itself, by contrast, is **existential**, and must be — see the warning above.

*The assembly, proved.*

```lean
theorem hasDivisorClassOfSomeCartierData_of_localModel
    (hdec : HasComponentSupportDecomposition X)
    (hloc : HasChernLocalModel X) :
    HasDivisorClassOfSomeCartierData X
```

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. The proof: pick the
Cartier data from `exists_cartierData_represents`; take the normalised lift `β` from `hloc`;
decompose it with `hdec`; use the normalisation clause of `hloc` and the injectivity of
`cycleComponentSupportedClassNormalizationIso` (packaged as
`eq_zsmul_cycleComponentSupportedInjectiveClass`, the additive form of
`cycleComponentSupportedInjectiveClass_unique`) to identify each piece with
`c.divisor x • cycleComponentSupportedInjectiveClass X x hx`; and finish with
`supportedInjectiveToAmbient_enlarge` and `sheafCycleClassOnCycles_eq_sum`. Combined with
`hasDivisorOfAlgebraicModel_of_divisorClass` this reduces `HasDivisorOfAlgebraicModel X` to
`HasComponentSupportDecomposition` (now proved unconditionally) and `HasChernLocalModel`. Step 3
still supplies the weaker `HasSupportedChernLift`, through the proved bridge

```lean
theorem exists_supportedChernLift_of_splitting
    (E : HolomorphicUnitExtension X (dim X.left)) (c : Scheme.CartierData X.left)
    (hvan : RestrictedChernClassVanishes X (dim X.left)
      (cycleAnalyticClosedSupport X c.divisor).compl)
    (ℓ : E.middle.obj.obj (op ((cycleAnalyticClosedSupport X c.divisor).compl)))
    (hℓ : …) :
    ∃ β : RationalCohomologyWithSupport X
        ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
          Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)), forgetSupport X _ _ β = …
```

so that only the splitting datum `ℓ` over `X^an ∖ |D|^an` — a frame of the line bundle there,
which the rational section provides but which has not been formalised — stands between step 3 and
`HasSupportedChernLift`: its other hypothesis `hvan` is now the theorem
`restrictedChernClassVanishes` (§4.3 step 3c). That same datum `ℓ` is what should produce the
*canonical* lift required by `HasChernLocalModel`, by route A above.

*`HasComponentSupportDecomposition` is proved*, in
[`Other/AlgebraicGeometry/ComponentSupportDecomposition.lean`](../Other/AlgebraicGeometry/ComponentSupportDecomposition.lean),
from a single vanishing statement:

```lean
/-- **Vanishing of supported cohomology in complex codimension two** (proved below). -/
def HasCodimensionTwoSupportedVanishing : Prop :=
  ∀ W : Closeds X.left, (∀ z ∈ W, (2 : ℕ∞) ≤ coheight z) →
    IsZero (SupportedInjectiveHomology X (analyticClosedSupport X W) (2 * ((1 : ℕ) : ℤ) + 1))

theorem hasComponentSupportDecomposition (hvan : HasCodimensionTwoSupportedVanishing X) :
    HasComponentSupportDecomposition X

theorem hasDivisorClassOfSomeCartierData_of_localModel_of_vanishing
    (hvan : HasCodimensionTwoSupportedVanishing X) (hloc : HasChernLocalModel X) :
    HasDivisorClassOfSomeCartierData X
```

Here `analyticClosedSupport X W := Point.underlying ⁻¹' W` is the analytic support of a
Zariski-closed subset, and the hypothesis `∀ z ∈ W, 2 ≤ coheight z` is exactly "`W` has
codimension at least two" (`coheight` is antitone, so it suffices to check it at the generic
points of the components of `W`). Only degree `2·1 + 1 = 3` is needed; mathematically the
vanishing holds in all degrees `< 4`, by the stratification argument described below. `#print
axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for both theorems.

The proof has two halves.

*(i) Mayer–Vietoris for two closed supports*, proved in full generality (any topological space,
any termwise flasque coefficient complex) in
[`Other/AlgebraicGeometry/SupportUnionSplitting.lean`](../Other/AlgebraicGeometry/SupportUnionSplitting.lean).
The engine is the splitting short exact sequence of section complexes

`0 → Γ(X, Γ̲_{X∖W} K) → Γ(X, Γ̲_{X∖U} K) → Γ(U', Γ̲_{X∖U} K) → 0`  for `U, U' ≤ W ≤ U ⊔ U'`,

whose surjectivity is `sheafSectionsSupportedOutside_restriction_surjective` (flasqueness of the
supported-sections sheaf, `FlasqueSupportedSections.lean`) and whose exactness in the middle is
the two-open gluing `eq_of_locally_eq₂` plus
`exists_supportedOutsideSection_of_restrict_eq_zero`. Applying it twice — once with
`(U, U') = (X∖Z₁, X∖Z₂)` and once with `(U, U') = (X∖(Z₁ ∪ Z₂), X∖Z₂)`, the two third terms
being identified by `supportedOutsideMap_app_bijective` (over `X ∖ Z₂` the supports `Z₁` and
`Z₁ ∪ Z₂` have the same trace) — gives

```lean
theorem exists_supportedSectionsEnlarge_add_eq … (hvan : IsZero (supportedSectionsHomology X K Ui m))
    (β : supportedSectionsHomology X K Uu n) :
    ∃ a b, β = supportedSectionsEnlarge X K h₁ n a + supportedSectionsEnlarge X K h₂ n b
```

i.e. `H^n_{Z₁} ⊕ H^n_{Z₂} → H^n_{Z₁ ∪ Z₂}` is onto as soon as `H^{n+1}_{Z₁ ∩ Z₂} = 0`. The four
opens are taken as separate variables with inequality hypotheses, so that no transport along
equalities of supports is needed at the point of use; instantiated at `Z.compl` the statement is
*definitionally* about `SupportedInjectiveHomology` and `enlargeSupportedInjectiveHomology`. No
Mayer–Vietoris sequence for sheaf-theoretic supports existed in the repository before; the
singular one in `RelativeMayerVietoris.lean` is about singular chains.

*(ii) The codimension estimate.* Two distinct prime divisors meet in codimension at least two:
`two_le_coheight_of_mem_closure_inter` proves that a point `z` of `closure {x} ∩ closure {y}`
with `x ≠ y` of coheight one has `coheight z ≥ 2`. Either `z < x` (and then
`coheight x + 1 ≤ coheight z` by `Order.coheight_add_one_le`), or `z < y`, or else `x ≤ z ≤ y`
and `y ≤ z ≤ x`, whence `x = y` by `Specializes.antisymm` and the `T0Space` instance of a
scheme. The induction on the finite set of components then only needs that the intersection
`Z_a ∩ ⋃_{y ∈ t} Z_y` is the analytic support of a Zariski-closed set all of whose points have
coheight at least two (`analyticClosedSupport_componentsZariskiSupport`,
`mem_componentsZariskiSupport`), and the empty case, which is the vanishing
`isZero_supportedInjectiveHomology_bot` (proved, from `supportedSections_top_homology_isZero`).

*`HasCodimensionTwoSupportedVanishing` is proved as well*, so the codimension-one excision
statement is now **unconditional**:

```lean
theorem hasCodimensionTwoSupportedVanishing : HasCodimensionTwoSupportedVanishing X

theorem hasComponentSupportDecomposition_unconditional : HasComponentSupportDecomposition X

theorem hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel
    (hloc : HasChernLocalModel X) : HasDivisorClassOfSomeCartierData X
```

(`Other/AlgebraicGeometry/ClosedSupportCoheightDimension.lean`; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`). So **step 4 now rests on `HasChernLocalModel`
only.** The proof is the general-codimension form of the vanishing that
was already available for the singular boundary of one cycle component, in three files.

* [`ClosedSupportSmoothFiltration.lean`](../Other/AlgebraicGeometry/ClosedSupportSmoothFiltration.lean)
  — the canonical finite smooth filtration `closedSupportFiltration X W k :=
  reducedSmoothClosedFiltration X.hom W k` of an **arbitrary** `W : Closeds X.left`, with its
  strata `closedSupportStratum X W k := reducedClosedSmoothPiece X.hom (…)`, their locally
  closed immersions, the closed lifts `closedSupportStratumClosedLift` into the complement of
  the next remainder (`IsClosedImmersion`), the analytic supports
  `closedSupportAnalyticFiltration X W k` and the layer identity
  `closedSupportAnalyticFiltration_layer`. This is
  `CycleComponentSingularClosedFiltration.lean` with the singular boundary of one component
  replaced by `W`; it is shorter, because the filtration already lives in `X.left` and needs no
  transport along the closed immersion of a component.
* [`ClosedSupportCodimensionVanishing.lean`](../Other/AlgebraicGeometry/ClosedSupportCodimensionVanishing.lean)
  — the cohomological half, for a `q` supplied as the local dimension datum

  ```lean
  def ClosedSupportStrataNormalCodimension : Prop :=
    ∀ (k : ℕ) (z : closedSupportStratum X W k),
      ∃ A : (closedSupportStratum X W k).Opens, z ∈ A ∧ ∃ m : ℕ, m + q ≤ d ∧
        SmoothOfRelativeDimension m (A.ι ≫ closedSupportStratumι X W k ≫ X.hom)

  theorem closedSupportFiltrationSectionCohomology_isZero_of_lt
      (hstr : ClosedSupportStrataNormalCodimension X W d q)
      (k : ℕ) (hk : k ≤ closedSupportFiltrationLength X W) (n : ℤ) (hn : n < 2 * (q : ℤ)) :
      IsZero (… (complexSupportInjectiveComplex X (closedSupportAnalyticFiltration X W k)) …)
  ```

  proved exactly as `SingularFiltrationLocalSupportVanishing.lean` +
  `CycleComponentSupportExtension.lean`: normal-neighbourhood purity
  (`exists_smoothClosedSourceOpenImageNeighborhood`, vanishing away from degree `2(d - m)`) gives
  cofinal local vanishing below `2q ≤ 2(d - m)`; `sectionCohomology_isZero_of_cofinal_lower_vanishing`
  turns it into vanishing on the complement of the next remainder; and
  `TopCat.Sheaf.finiteNestedSupport_homology_isZero` propagates it along the filtration.
* [`ClosedSupportCoheightDimension.lean`](../Other/AlgebraicGeometry/ClosedSupportCoheightDimension.lean)
  — the dimension input, which is where the codimension hypothesis enters:

  ```lean
  theorem topologicalKrullDim_lt_of_forall_le_coheight
      {d q : ℕ} [SmoothOfRelativeDimension d X.hom] (W : Closeds X.left)
      (hW : ∀ z ∈ W, (q : ℕ∞) ≤ coheight z) :
      topologicalKrullDim W < ((d - q + 1 : ℕ) : WithBot ℕ∞)
  ```

  A chain of irreducible closed subsets of `W` of length `n` maps (`IrreducibleCloseds.map`,
  `map_strictMono_of_isInducing`) to one in `X.left`, and `irreducibleSetEquivPoints` turns it
  into a chain of points whose last member `y` is the generic point of a closed irreducible
  subset of `W`, hence lies in `W`; then `n ≤ height y` (`Order.length_le_height_last`),
  `q ≤ coheight y` (hypothesis) and `height y + coheight y ≤ d`
  (`SmoothOfRelativeDimension.height_add_coheight_le_complex`), so `n + q ≤ d`. Each stratum is
  contained in `W`, so `Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt`
  bounds its local relative dimension `m` by `m + q ≤ d`
  (`closedSupportStrataNormalCodimension_of_forall_le_coheight`; `q ≤ d` comes from
  `SmoothOfRelativeDimension.coheight_le_complex` applied to the image of a stratum point).
  For `q = 2` the vanishing holds in all degrees `< 4`, in particular in degree three.

*What `HasChernLocalModel` needs.* This is missing (c) of §4.2 and it still rests on missing (a)
of §4.2: there is no description of `E.firstChernClass` by the Čech cocycle of the transition
units, so the analytic transition data provided by step 1
(`extensionFramesOfAlgebraic_transitionUnit`, `exists_isUnit_frameChange_extension`) cannot yet be
fed into the cohomology class at all. In dependency order the sub-obligations are:

1. *Cocycle description of the connecting map* (§4.2(a)). A statement of the form
   "`E.firstChernClass` is the image of the `1`-cocycle `(g_{ij})` of `E.transitionUnit` under a
   Čech model of `H¹(𝒪ˣ) → H²(ℤ)`", or any statement of equal strength, e.g. that the *supported*
   class attached to a cocycle which is a coboundary off `|D|^an` is computed by
   `(1/2πi)(log g_{jk} − log g_{ik} + log g_{ij})` on a cover refining both the `U_i^an` and the
   lifting neighbourhoods of `E`. The local logarithms are
   `Other/Geometry/Manifold/HolomorphicLogarithm.lean`.
2. ~~*The algebraic local form of the local equation.*~~ **Done**, in
   [`Other/AlgebraicGeometry/DiscreteValuationLocalRing.lean`](../Other/AlgebraicGeometry/DiscreteValuationLocalRing.lean)
   and [`Other/AlgebraicGeometry/CartierLocalForm.lean`](../Other/AlgebraicGeometry/CartierLocalForm.lean),
   as `Scheme.CartierData.exists_localForm`: for `x` of coheight one in `c.opens i` there is a
   `Scheme.CartierData.LocalForm c i x`, i.e. an affine open `V ∋ x` with `V ≤ c.opens i`, a
   regular `h : Γ(X.left, V)` and a unit `u : Γ(X.left, V)ˣ` with

   * `Scheme.ord (germToFunctionField V h) x = 1` (`ord_equation`),
   * `c.fn i = u · h ^ (c.divisor x)` in `X.left.functionField` (`fn_eq`),
   * `(V : Set X.left) \ X.left.basicOpen h = closure {x} ∩ V` (`zeroLocus_eq`, from the two
     fields `notMem_basicOpen` and `mem_closure_of_notMem_basicOpen`): `h` cuts out `Z_x` on `V`
     exactly.

   The ingredients, all proved: `isDiscreteValuationRing_stalk_of_coheight_eq_one` (the stalk is
   regular by `Smooth.isRegularLocalRing_stalk_complex` and of dimension one by
   `ringKrullDim_stalk_eq_coheight`, hence a DVR by the cotangent-space characterisation
   `IsLocalRing.finrank_CotangentSpace_eq_one_iff`); `Scheme.exists_unit_mul_zpow_eq`, the
   factorisation `c.fn i = u · π^n` in the function field, from `Ring.ordFrac_irreducible` and
   `Ring.associated_of_ordFrac_eq` with `Scheme.ordHom = Ring.ordFrac` of the stalk;
   `exists_coheight_eq_one_of_not_isUnit_germ`, Krull's principal ideal theorem in geometric form
   (a minimal prime over `(h)` in `Γ(X.left, V)` has height one, and heights of primes are
   coheights of points by `idealHeight_eq_coheight`); and `Scheme.ord_support_finite`, used to
   shrink `V` until the only codimension-one zero of `h` left is `x` itself. No analytic input.
   Unused for the moment by anything else: it is the algebraic half of what step 3 below consumes.
3. *The one-variable Lelong–Poincaré computation.* In a normal chart the function `h` becomes the
   coordinate `z₁`, the divisor is `{z₁ = 0}`, and the supported class of the cocycle of `z₁^n` on
   the chart is `n` times the normalised normal-chart coclass
   `cycleComponentSmoothSupportCoclassSection`. The repository's normalisation is fixed by
   `ComplexLocalOrientation*.lean`, `Other/AlgebraicTopology/NormalProjectionCoclass.lean`,
   `ChartLocalFundamentalClass*.lean`, and this is where the sign is determined: if it comes out
   inverted, negate `Scheme.CartierData.Represents` by exchanging `i` and `j` in its transition
   condition, as explained in §3. Only steps 1 and 3 are analytic; step 3 is one variable.

   **This item is now reduced**, in
   [`Other/AlgebraicGeometry/ChernLocalModelWinding.lean`](../Other/AlgebraicGeometry/ChernLocalModelWinding.lean),
   to two named obligations, by making the *winding homomorphism of a chart* explicit. The chart
   datum is

   ```lean
   structure ChernWindingChart (q : ComplexPoint X) where
     index : c.ι
     localForm : c.LocalForm index x          -- the algebraic local form `c.fn i = u · h ^ n`
     carrier : Opens (ComplexPoint X)         -- the analytic chart `V ∋ q`
     mem : q ∈ carrier
     le : carrier ≤ cycleComponentSmoothSupportAmbientOpen X x
     le_analytic : carrier ≤ analyticOpen X localForm.opens
     coord : (holomorphicUnitSheaf X d).obj.obj (op (carrier ⊓ (…).compl))
     coord_eq : …                             -- `coord` is the analytification `h^an` of `h`
     winding : (holomorphicUnitSheaf X d).obj.obj (op (carrier ⊓ (…).compl)) →+
       (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
         (2 * p)).obj.obj (op carrier)
     exists_log : …                           -- every unit on `V` is an exponential (`V` a polydisc)
   ```

   `winding` is the composite `∂ ∘ δ` of the exponential connecting map on the punctured chart (the
   winding number `(1/2πi) ∮ d log`) with the connecting map `H¹(V ∖ Z) → H²_Z(V)` of the pair.
   It is *data* in the structure for historical reasons; **both maps are now constructed**, see
   "the winding homomorphism, constructed" below, and a chart can be built from geometric data
   alone (`WindingChartData`). Note that `localForm` is required to live on an affine open
   containing the *given* point of `Z_x`, so a version of `Scheme.CartierData.exists_localForm`
   starting from an arbitrary affine open meeting `Z_x` is needed (harmless: any open meeting
   `Z_x` contains its generic point).

   The three facts of the computation are the per-chart predicates

   * `ChernWindingChart.ComputesClass n a` — **(a) naturality**:
     `a|_V = winding (u^an + n • coord)` for some unit `u` on `V` (the group of the unit sheaf is
     written additively, so `n • coord` is `h^n`);
   * `ChernWindingChart.HasTrivialUnitWinding` — **(b) winding**: `winding` kills the restriction of
     every unit defined on all of `V`, because such a unit has a holomorphic logarithm. For the
     *constructed* winding homomorphism this is now the **theorem**
     `WindingChartData.hasTrivialUnitWinding` (see below), so (b) has disappeared as an
     obligation;
   * `ChernWindingChart.NormalizesCoclass hx` — **(c) normalisation**:
     `winding coord = cycleComponentSmoothSupportCoclassSection|_V`, the sign-fixing statement.

   `ChernWindingChart.restrict_eq_zsmul_coclass` **proves** that (a) + (b) + (c) give
   `a|_V = (n • coclass)|_V`. The two remaining obligations are

   ```lean
   /-- (b) + (c): normalised winding charts exist at every point of the component inside its
   smooth-support open, off a Zariski-closed `B ⊆ Z_x` with `x ∉ B` chosen by the obligation.
   No line bundle and no Chern class occur; this is the pure analysis. -/
   def HasNormalizedWindingCharts : Prop :=
     ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
       ∃ B : Closeds X.left, (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
         ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
           Point.underlying q ∉ B →
           ∃ ch : ChernWindingChart X c x (dim X.left) 1 q,
             ch.HasTrivialUnitWinding ∧ ch.NormalizesCoclass hx

   /-- (a): there *exists* a supported lift `β` of the first Chern class — the relative first
   Chern class cut out by the frame of the bundle off `|D|^an` — for which every normalised winding
   chart computes the corresponding component piece. The lift must be existential (see the `ℙ¹`
   counterexample above); the decomposition `γ` may stay universal. This is where §4.2(a) — a
   cocycle description of the connecting map `H¹(𝒪ˣ) → H²(ℤ)` — is needed. -/
   def HasChernWindingNaturality : Prop :=
     ∀ E L hL iso c hc, ∃ β, supportedInjectiveToAmbient … β = c₁(E)_ℚ ∧
       ∀ γ (hγ : β = ∑ …), ∀ x ∈ cycleComponents X c.divisor, ∀ hx, ∀ q ch,
         ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
         ch.ComputesClass (c.divisor x) (… (γ x))
   ```

   Obligation (a) therefore contains the construction of the canonical relative class; route B
   above is exactly the plan of building it by gluing the local winding classes.

   and

   ```lean
   theorem hasChernLocalModel_of_winding (h₁ : HasNormalizedWindingCharts X)
       (h₂ : HasChernWindingNaturality X) : HasChernLocalModel X
   ```

   is **proved** (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`). The equality of
   sections over the smooth-support open `U` is first reduced to one over `U ∖ B^an` by the
   **gluing lemma** `cycleComponentSmoothSupport_restriction_injective`
   (`Other/AlgebraicGeometry/CycleComponentRestrictionInjective.lean`, proved): for a
   Zariski-closed `B ⊆ Z_x` with `x ∉ B`, restriction of `supportRelativeCohomologySheaf … (2p)`
   from `U` to `U ∖ B^an` is injective — every point of `B` is a proper specialisation of `x`,
   so has coheight `≥ p + 1`, the supported cohomology along `(singular boundary of Z_x) ⊔ B` vanishes
   below `2(p+1)` (`closedSupportSectionCohomology_isZero_of_lt`), the nested-support localisation
   sequence makes restriction from `Γ_Z(X, I•)` to `Γ_Z(U ∖ B^an, I•)` injective on `H^{2p}`,
   and the section comparison `sectionCohomologyToSheafSection` is an isomorphism on both opens.
   The gluing from charts to `U ∖ B^an` is then sheaf separatedness for
   `supportRelativeCohomologySheaf`; off the component the comparison is trivial, because
   `AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero` — also **proved**
   here — says that every section of that sheaf over an open set disjoint from the (closed) support
   vanishes, via `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` and the repository's
   `supportRelativeCohomologyGerm_eq_zero_of_not_mem`.

   The reduction is faithful: `hasChernWindingNaturality_of_localModel` proves the converse
   implication for (a), so that, granted `HasNormalizedWindingCharts X`, obligation (a) is
   *equivalent* to `HasChernLocalModel X`. `computesClass_of_restrict_eq` is the corresponding
   non-vacuity check for the per-chart predicate `ComputesClass`.

   Verification: `lake build Other.AlgebraicGeometry.ChernLocalModelWinding` (the module is
   registered in `Other.lean`).

   ### The winding homomorphism, constructed

   The two connecting maps that `ChernWindingChart.winding` assumed are now **built**, in four
   new modules (all registered in `Other.lean`, all `#print axioms`-clean: `propext`,
   `Classical.choice`, `Quot.sound`). The construction is elementary and uses no sheaf theory:
   it produces the winding *cocycle* directly on singular chains.

   * [`Other/AlgebraicGeometry/ChernWindingLift.lean`](../Other/AlgebraicGeometry/ChernWindingLift.lean)
     — logarithmic increments. On a simply connected, locally path connected space `A`, every
     continuous nowhere vanishing `g : A → ℂ` is `exp ∘ L` (Mathlib's
     `Complex.isCoveringMapOn_exp` and `IsCoveringMapOn.existsUnique_continuousMap_lifts`), and
     `ChernWinding.logIncrement g hg a b := L b - L a` is independent of the lift
     (`sub_eq_sub_of_exp_eq`). It is additive in the endpoints
     (`logIncrement_add_logIncrement`), additive in `g` under multiplication
     (`logIncrement_mul`), natural in `A` (`logIncrement_comp`), and equal to `f b - f a` when
     `g = exp ∘ f` (`logIncrement_of_exp`). The file also supplies the missing instance
     `ChernWinding.Convex.locallyPathConnectedSpace`: a convex subset of a real normed space is
     locally path connected.

   * [`Other/AlgebraicGeometry/ChernWindingCochain.lean`](../Other/AlgebraicGeometry/ChernWindingCochain.lean)
     — the winding cocycle. A singular `n`-simplex of `Y` is a continuous map out of
     `stdSimplex ℝ (Fin (n+1))`, which is convex, hence contractible, hence simply connected, and
     locally path connected; so `logIncrement` applies to it. `ChernWinding.simplexIncrement g hg σ`
     is the increment of `g` along a singular `1`-simplex, and
     `simplexIncrement_boundary` — the cocycle identity — is the telescoping of the increments of
     *one* logarithm of `g ∘ τ` between the three vertices of `stdSimplex ℝ (Fin 3)`. Dividing by
     `2πi` and descending along `CokernelCofork.IsColimit.desc'` gives

     ```lean
     def ChernWinding.windingPeriod (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
         AlgebraicTopology.Singular.Homology ℚ Y 1 →ₗ[ℚ] ℂ
     ```

     the honest winding number `(1/2πi) ∮ d log g`, with `windingPeriod_mul` (additivity in `g`),
     `windingPeriod_eq_zero_of_exp` (vanishing when `g` has a global continuous logarithm — the
     `0`-cochain of the logarithm is a primitive of the cocycle) and `windingPeriod_map`
     (naturality in `Y`). This is `δ`; it is the degree-`0 → 1` connecting map of the exponential
     sequence, obtained without any comparison of cohomology theories.

   * [`Other/AlgebraicGeometry/ChernWindingBoundary.lean`](../Other/AlgebraicGeometry/ChernWindingBoundary.lean)
     — `∂`, and the supported class. The key observation is that the repository's relative
     cohomology *is* the linear dual of relative homology, and the homology connecting map of a
     pair already exists (`AlgebraicTopology.Singular.relativeSingularBoundary`, in
     `Other/AlgebraicTopology/EuclideanLocalHomology.lean`); so `∂` is simply precomposition,
     and no long exact sequence in cohomology has to be built. Writing `P := (W, W ∖ S)`,

     ```lean
     def ChernWinding.relativeWindingPeriod (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
         ComplexPeriodSpace (RelativeHomology ℚ (supportPair W S) 2) :=
       (windingPeriod g hg).comp (relativeSingularBoundary (supportPair W S) 1).hom
     ```

     with `relativeWindingPeriod_mul` and `relativeWindingPeriod_eq_zero_of_exp`. This is the full
     composite `∂ ∘ δ` — at the level of **complex** periods.

   * The one remaining input is the **rationality (integrality) of the periods**, isolated as

     ```lean
     def ChernWinding.HasRationalWindingPeriod (g) (hg) : Prop :=
       ∃ a : RelativeCohomology ℚ (supportPair W S) 2,
         rationalPeriod _ a = relativeWindingPeriod W S g hg
     ```

     Mathematically this is the statement that the winding number of `g` along an integral cycle
     is an integer; on the normal chart it should follow from the fact that
     `H₂(V, V ∖ Z; ℚ)` is spanned by `flattenedSupportNormalClass`, whose boundary is the class of
     an explicit *loop*, together with the fact that the increment of a logarithm along a loop lies
     in `2πi ℤ` — the latter is proved, as `ChernWinding.exists_int_logIncrement`. Granted it,
     `ChernWinding.windingRelativeClass` is the honest rational class, with
     `windingRelativeClass_mul` and `windingRelativeClass_eq_zero_of_exp`.

   * **The normalisation obligation (c) is reduced to one number.** By
     `AlgebraicTopology.Singular.chartNormalProjectionCoclass_unique`, a class on a flattening
     chart is the normalised normal-chart coclass exactly when it pairs to `1` with
     `flattenedSupportNormalClass`. Hence
     `ChernWinding.windingRelativeClass_eq_chartNormalProjectionCoclass`: in codimension one the
     winding class of `g` **is** the coclass as soon as

     ```lean
     windingPeriod g hg ((relativeSingularBoundary (supportPair …) 1).hom
       (flattenedSupportNormalClass E 1 e x hx S hS h0)) = 1
     ```

     i.e. as soon as the winding number of `g` around the normal circle of the support is `1`.
     That single equation is the whole of the Lelong–Poincaré computation, and it is where the
     sign is fixed.

   * [`Other/AlgebraicGeometry/ChernWindingUnitClass.lean`](../Other/AlgebraicGeometry/ChernWindingUnitClass.lean)
     — from units to sheaf sections. A section of `holomorphicUnitSheaf X d` over `V ⊓ Sᶜ` is an
     invertible element of the ring of holomorphic functions there, hence has an underlying
     continuous nowhere vanishing function (`windingUnitFunction`, `windingUnitFunction_ne_zero`,
     `windingUnitFunction_add`). Under `HasWindingPeriods X d V S` (the rationality above, for
     every unit on the punctured chart) this gives

     ```lean
     def windingSheafHom (h : HasWindingPeriods X d V S) :
         (holomorphicUnitSheaf X d).obj.obj (op (windingPuncturedOpen X V S)) →+
           (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) ↑S 2).obj.obj (op V)
     ```

     — exactly the shape of the `winding` field — together with
     `windingSheafHom_restrict_eq_zero`: a unit on all of `V` which is `exp(2πi f)` there
     restricts to a unit with a global continuous logarithm on `V ∖ S`, so its winding class
     vanishes.

   * [`Other/AlgebraicGeometry/ChernWindingNormalizedCharts.lean`](../Other/AlgebraicGeometry/ChernWindingNormalizedCharts.lean)
     — the resulting reduction. `WindingChartData X c x d q` is `ChernWindingChart` with the
     `winding` field deleted and `HasWindingPeriods` added; `WindingChartData.toChart` fills in
     `windingSheafHom`, and

     ```lean
     theorem WindingChartData.hasTrivialUnitWinding : D.toChart.HasTrivialUnitWinding
     theorem hasNormalizedWindingCharts_of_windingChartData
         (h : HasWindingChartData (X := X)) : HasNormalizedWindingCharts X
     ```

     are proved, where

     ```lean
     def HasWindingChartData : Prop :=
       ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
         ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
           ∃ D : WindingChartData X c x (dim X.left) q, D.toChart.NormalizesCoclass hx
     ```

   So `HasNormalizedWindingCharts` has been reduced to `HasWindingChartData`, i.e. to four
   statements about a normal chart `V` at a smooth point of `Z_x`, with obligation (b) removed.
   Three of the four are now settled; here is their status.

   ### (1) The local form at a prescribed point: **an obstruction, and a needed correction**

   This one is **impossible as stated**, and `HasNormalizedWindingCharts` is therefore
   **false** in general.  In
   [`Other/AlgebraicGeometry/ChernWindingLocalFormObstruction.lean`](../Other/AlgebraicGeometry/ChernWindingLocalFormObstruction.lean):

   ```lean
   theorem Scheme.CartierData.LocalForm.divisor_eq_zero_of_notMem_closure
       (f : c.LocalForm i x) {y : S} (hy : y ∈ f.opens) (hyx : y ∉ closure ({x} : Set S)) :
       c.divisor y = 0

   theorem AlgebraicGeometry.ComplexPoint.exists_chernWindingChart_imp_divisor_eq_zero
       (ch : ChernWindingChart X c x d p q) (hx : coheight x = 1)
       {y : X.left} (hy1 : coheight y = 1) (hyx : y ≠ x)
       (hq : Point.underlying q ∈ closure ({y} : Set X.left)) :
       c.divisor y = 0
   ```

   The reason is forced by the shape of `LocalForm`: on its affine open `V₀` the local equation
   factors as `u · h ^ n` with `u` a **unit on `V₀`** and `h` invertible off `Z_x`, so every
   codimension-one point of `V₀` off `Z_x` has order of vanishing zero.  Hence `V₀ ∩ |D| ⊆ Z_x`,
   and since the chart is required to satisfy `carrier ≤ analyticOpen X localForm.opens`, a
   winding chart can exist at `q` only if `q` lies on no component of `|D|` other than `Z_x`.

   But `HasNormalizedWindingCharts` quantifies over **every**
   `q ∈ cycleComponentSmoothSupportAmbientOpen X x ∩ cycleComponentSupport X x`, and that set
   *does* meet the other components: for a pair of lines in `ℙ²`, the node lies on the smooth
   locus of each line.  So the proposition is unprovable as written, and no strengthening of
   `Scheme.CartierData.exists_localForm` can repair it.

   **The correction (done).** `HasNormalizedWindingCharts` (and likewise
   `HasGeometricWindingCharts`) now has the *generic* form displayed above: for each `c`, `x`
   the obligation chooses a Zariski-closed `B ⊆ Z_x` with `x ∉ B` and only has to produce charts
   at the points of `cycleComponentSmoothSupportAmbientOpen X x ∩ Z_x` whose underlying scheme
   point is not in `B`. The intended choice is `B = Z_x ∖ V₀` for the affine open `V₀` of a
   single local form (`Scheme.CartierData.exists_localForm`), which is dense open in `Z_x`; this
   excludes the other components automatically and needs **no** local form at points other than
   the generic point (in particular no algebraic Hartogs). The reduction
   `hasChernLocalModel_of_winding` is re-proved with the gluing lemma
   `cycleComponentSmoothSupport_restriction_injective`
   (`CycleComponentRestrictionInjective.lean`): restriction of the local relative-cohomology
   sheaf from `U` to `U ∖ B^an` is injective, because every point of `B` has codimension `≥ 2`
   in `X`. The old pointwise form still implies the new one (`hasNormalizedWindingCharts_of_forall`,
   with `B = ∅`), so nothing proved before is lost.

   With `q` off `B` the remaining existence problem is the standard one: `q` lies in the
   analytification of the affine open of the chosen local form, and a polydisc chart around `q`
   inside it is required.

   ### (2) `exists_log` on a simply connected chart: **proved**

   [`Other/AlgebraicGeometry/ChernWindingHolomorphicLog.lean`](../Other/AlgebraicGeometry/ChernWindingHolomorphicLog.lean):

   ```lean
   theorem AlgebraicGeometry.ComplexPoint.exists_holomorphicExponential_of_simplyConnected
       (V : Opens (TopCat.of (ComplexPoint X)))
       [SimplyConnectedSpace (V : Set (ComplexPoint X))]
       [LocallyPathConnectedSpace (V : Set (ComplexPoint X))]
       (u : (holomorphicUnitSheaf X d).obj.obj (op V)) :
       ∃ f : (holomorphicAdditiveSheaf X d).obj.obj (op V),
         (holomorphicExponential X d).hom.app (op V) f = u
   ```

   This is exactly the `exists_log` field.  The continuous logarithm comes from
   `ChernWinding.exists_expLift`; it is holomorphic because near each point it agrees, up to a
   constant in `2πi ℤ`, with the germ-local holomorphic branch of
   `ContMDiffAt.exists_local_log` — the constancy being
   `ContinuousAt.exists_local_exp_period`, already in the repository.  The two topological
   hypotheses hold for an open homeomorphic to a nonempty convex set, e.g. a ball of a
   holomorphic chart: `ChernWinding.simplyConnectedSpace_of_homeomorphConvex`,
   `ChernWinding.locallyPathConnectedSpace_of_homeomorphConvex`.

   ### (3) Rationality of the winding periods: **proved, unconditionally**

   [`Other/AlgebraicGeometry/ChernWindingRational.lean`](../Other/AlgebraicGeometry/ChernWindingRational.lean)
   and
   [`Other/AlgebraicGeometry/ChernWindingChartPeriods.lean`](../Other/AlgebraicGeometry/ChernWindingChartPeriods.lean):

   ```lean
   theorem ChernWinding.hasRationalWindingPeriod (g : C(puncturedSpace W S, ℂ))
       (hg : ∀ y, g y ≠ 0) : HasRationalWindingPeriod W S g hg
   theorem AlgebraicGeometry.ComplexPoint.hasWindingPeriods (X d V S) : HasWindingPeriods X d V S
   ```

   The proof needs no comparison of coefficients.  Take the *pointwise* principal branch
   `λ y := Complex.log (g y)` — no continuity is required of a `0`-cochain.  For a singular
   `1`-simplex `σ`, both `exp` of the logarithmic increment of `g` along `σ` and `exp` of
   `λ(σ v₁) − λ(σ v₀)` equal `g(σ v₁)/g(σ v₀)`, so they differ by an element of `2πi ℤ`:

   ```lean
   theorem ChernWinding.simplexIncrement_eq_pointLog_add_windingIndex (σ) :
       simplexIncrement g hg σ =
         (pointLog g (simplexMap σ (stdSimplex.vertex 1)) -
           pointLog g (simplexMap σ (stdSimplex.vertex 0))) + (windingIndex g hg σ : ℂ) * twoPiI
   ```

   So `windingCochain = δ(λ/2πi) + windingIndex` with `windingIndex` **integer valued**
   (`windingCochain_eq_coboundary_add_integer`); the integer cochain is automatically a cocycle
   (`d_comp_windingIntegerCochain`), hence descends to `ChernWinding.windingRationalPeriod`, a
   class in `Cohomology ℚ Y 1`, whose complexification is the complex winding period
   (`rationalPeriod_windingRationalPeriod`) because the two cochains differ by a coboundary.

   As a consequence `WindingChartData` may be replaced by `GeometricWindingChartData`, which
   contains only geometric data, and

   ```lean
   theorem AlgebraicGeometry.ComplexPoint.hasNormalizedWindingCharts_of_geometricWindingCharts
       (h : HasGeometricWindingCharts (X := X)) : HasNormalizedWindingCharts X
   ```

   ### (4) `NormalizesCoclass`: the sign is **`+1`**

   The topological half of the remaining equation is computed in
   [`Other/AlgebraicGeometry/ChernWindingStandardTriangle.lean`](../Other/AlgebraicGeometry/ChernWindingStandardTriangle.lean):

   ```lean
   theorem ChernWinding.windingPeriod_standardPuncturedBoundaryClass :
       windingPeriod complexCoordinate complexCoordinate_ne_zero
         (standardPuncturedBoundaryClass 1) = 1
   ```

   Here `complexCoordinate` is the identification `v ↦ v 0 + v 1 · I` of `ℝ² ∖ {0}` with
   `ℂ ∖ {0}`, and `standardPuncturedBoundaryClass 1` is the repository's generator of
   `H₁(ℝ² ∖ {0}; ℚ)` — the oriented boundary `∑ᵢ (-1)ⁱ dᵢ` of the standard affine `2`-simplex,
   whose vertices are `1`, `I` and `-1 - I` and whose barycentre is the origin.  Since
   `relativeSingularBoundary_standardLocalClass` already identifies `∂ (standardLocalClass 2)`
   with that class, **the repository's orientation and the winding number `(1/2πi) ∮ d log z`
   agree: the sign is `+1`, not `−1`.**  No change to `Scheme.CartierData.Represents` is
   indicated by this computation.

   The computation is explicit: each face is an affine segment, on which a suitable rotation of
   the principal branch of `Complex.log` is a continuous logarithm
   (`ChernWinding.logIncrement_of_slitPlane`), so the increments are
   `Log (-1 + I)`, `Log (-1 - I)` and `Log I`, and

   `Log (-1 + I) − Log (-1 - I) + Log I = (3π/2) I + (π/2) I = 2πi`.

   What remains of obligation (4) is the *geometry*, not the sign: transporting this number
   through `standardComplexRealPairIso`, `normalSliceSection`, `flattenedSupportPairIso` and
   `chartNormalProjectionCoclass`, and identifying the analytified local equation `h` with the
   normal coordinate of the chart (which needs `dh ≠ 0` along `Z_x`, i.e. that `h` is part of a
   holomorphic coordinate system — the analytic content of `ord_x h = 1` at a smooth point).

   ### (4) continued: `NormalizesCoclass` is now **proved** for a normal winding chart

   The geometric transport promised above is carried out in five further modules.

   * [`ChernWindingNormalChartBoundary.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartBoundary.lean)
     supplies the missing **naturality of the connecting map of a pair**, which the repository did
     not have, by building the morphism of short exact sequences of chains and invoking Mathlib's
     `HomologicalComplex.HomologySequence.δ_naturality`:

     ```lean
     def AlgebraicTopology.Singular.relativeSingularChainShortComplexMap {P Q : TopPair} (f : P ⟶ Q) :
         relativeSingularChainShortComplex P ⟶ relativeSingularChainShortComplex Q

     theorem AlgebraicTopology.Singular.relativeSingularBoundary_naturality
         {P Q : TopPair} (f : P ⟶ Q) (n : ℕ) :
         relativeSingularBoundary P n ≫
             HomologicalComplex.homologyMap ((chainPairFunctor ℚ).map f).left n =
           HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) (n + 1) ≫
             relativeSingularBoundary Q n
     ```

     and deduces `relativeSingularBoundary_standardComplexLocalClass`, that
     `∂ (standardComplexLocalClass 1)` is the image of the explicit oriented boundary
     `standardPuncturedBoundaryClass 1` under the real-to-complex coordinate map.

   * [`ChernWindingNormalChartValue.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartValue.lean)
     computes the number:

     ```lean
     theorem ChernWinding.windingPeriod_flattenedNormalClass
         (g : C((neighborhoodSupportComplementPair ↑(flattenedSupportNeighborhood E 1 e x hx) S).snd, ℂ))
         (hg : ∀ y, g y ≠ 0)
         (hcoord : ∀ w, g w =
           complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
         windingPeriod g hg ((relativeSingularBoundary _ 1).hom
           (flattenedNormalClass E e S hS x hx h0)) = 1
     ```

     — *the winding number of the normal coordinate around the normal sphere of the support is
     `+1`.*  The radial compression built into `flattenedSupportEmbedding` costs nothing, because
     the repository's own `centeredComplexUnivBall_preserves_standardComplexLocalClass` says the
     recentred compression fixes `standardComplexLocalClass 1`; the chain is
     `flattenedSupportNormalClass_eq_normalFiber` → δ-naturality →
     `normalFiber_comp_chartNormalProjection` → the compression invariance →
     `relativeSingularBoundary_standardComplexLocalClass` →
     `windingPeriod_standardPuncturedBoundaryClass`.

     *Elaboration note.* The degrees `2 * 1` (used by `flattenedSupportNormalClass`) and `1 + 1`
     (used by `relativeSingularBoundary … 1`) are definitionally equal but their unification over
     the expensive `flattenedSupportNeighborhood` is very slow; `ChernWinding.flattenedNormalClass`
     pays that cost once, in a `def` with the expected type given, and everything downstream is
     fast.

   * [`ChernWindingNormalChartClass.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartClass.lean)
     combines it with the unconditional rationality of the periods:

     ```lean
     theorem ChernWinding.windingClass_eq_chartNormalProjectionCoclass
         (g) (hg) (hcoord) :
         windingClass ↑(flattenedSupportNeighborhood E 1 e x hx) S g hg =
           chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx) _
     ```

   * [`ChernWindingNormalChartData.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartData.lean)
     packages the geometry.  `NormalWindingChartData X c x d q` is `GeometricWindingChartData` with
     the chart pinned to a **flattening chart** of the component at `q`:

     ```lean
     structure NormalWindingChartData (q : ComplexPoint X) where
       index : c.ι
       localForm : c.LocalForm index x
       chart : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d - 1) → ℂ) × (Fin 1 → ℂ))
       mem_source : q ∈ chart.source
       flattens : ∀ y ∈ chart.source, y ∈ cycleComponentSupport X x ↔ (chart y).2 = 0
       center : (chart q).2 = 0
       le : flattenedSupportNeighborhood (Fin (d-1) → ℂ) 1 chart q mem_source ≤
         cycleComponentSmoothSupportAmbientOpen X x
       le_analytic : flattenedSupportNeighborhood … ≤ analyticOpen X localForm.opens
       coord : (holomorphicUnitSheaf X d).obj.obj (op (flattenedSupportNeighborhood … ⊓ (…).compl))
       coord_eq : …                    -- `coord` is the analytification of `localForm.equation`
       exists_log : …                  -- automatic, see `exists_log_of_flattening`
       normal_coordinate : ∀ w, windingUnitFunction X d … coord w =
         ChernWinding.complexLineCoordinate ((ChernWinding.flattenedNormalProjection …).left w)
       coclass_restrict : ∀ hx, (supportRelativeCohomologySheaf … (2*1)).obj.map (homOfLE le).op
           (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
         (supportRelativeCohomologyToSheaf … (2*1)).app (op (flattenedSupportNeighborhood …))
           (chartNormalProjectionCoclass (Fin (d-1) → ℂ) 1 chart … )
     ```

     with `toGeometric`, `toChart`, and

     ```lean
     theorem NormalWindingChartData.normalizesCoclass (hx : coheight x = ((1 : ℕ) : ℕ∞)) :
         G.toChart.NormalizesCoclass hx
     ```

     **This is obligation (c), proved.**  Its two inputs are the winding computation above and the
     field `coclass_restrict`.

   * [`ChernWindingNormalChartLog.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartLog.lean)
     removes the `exists_log` field: a flattened-support neighbourhood is homeomorphic to the whole
     model vector space (`flattenedSupportHomeomorph`), hence contractible and locally path
     connected, so

     ```lean
     theorem AlgebraicGeometry.ComplexPoint.exists_holomorphicExponential_flattenedSupportNeighborhood
         (E) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
         (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
         (z : ComplexPoint X) (hz : z ∈ e.source)
         (u : (holomorphicUnitSheaf X d).obj.obj (op (flattenedSupportNeighborhood E c e z hz))) :
         ∃ f, (holomorphicExponential X d).hom.app _ f = u
     ```

   * [`ChernWindingNormalChartExistence.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartExistence.lean)
     states what is left, in the `∃ B` shape forced by the obstruction of item (1):

     ```lean
     def HasNormalFlatteningCharts : Prop :=
       ∀ (c : Scheme.CartierData X.left) (x : X.left), coheight x = ((1 : ℕ) : ℕ∞) →
         ∃ B : Set X.left, IsClosed B ∧ B ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
           ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
             Point.underlying q ∉ B →
             Nonempty (NormalWindingChartData X c x (dim X.left) q)

     theorem exists_closed_normalizedWindingCharts (h : HasNormalFlatteningCharts (X := X))
         (c) (x) (hx : coheight x = ((1 : ℕ) : ℕ∞)) :
         ∃ B : Set X.left, IsClosed B ∧ B ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
           ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
             Point.underlying q ∉ B →
             ∃ ch : ChernWindingChart X c x (dim X.left) 1 q,
               ch.HasTrivialUnitWinding ∧ ch.NormalizesCoclass hx
     ```

   ### (4) concluded: the residual obligation, and two simplifications of it

   Two further reductions cut the residual obligation down.

   **The normal coordinate only matters up to a unit**
   ([`ChernWindingNormalChartUnit.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartUnit.lean)).
   A flattened-support neighbourhood is simply connected, so a nowhere vanishing continuous
   function on *all* of it has a continuous logarithm there and therefore zero winding class.
   Hence

   ```lean
   theorem ChernWinding.windingClass_eq_chartNormalProjectionCoclass_of_unit
       (g) (hg) (u : C(↥(flattenedSupportNeighborhood E 1 e x hx), ℂ)) (hu : ∀ y, u y ≠ 0)
       (hmul : ∀ w, g w = u (flattenedPuncturedInclusion E e x hx w) *
         complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
       windingClass ↑(flattenedSupportNeighborhood E 1 e x hx) S g hg =
         chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx) _
   ```

   **This removes the holomorphic implicit function theorem from the remaining work.**  One no
   longer has to build a chart whose normal coordinate *is* `h^an`; it suffices that `h^an`
   differs from the normal coordinate of *some* flattening chart (for instance the repository's
   own `closedImmersionHolomorphicFlatteningChart`) by a nowhere vanishing factor — i.e. that `h`
   generates the ideal of `Z_x` near `q`.

   Accordingly
   [`ChernWindingGenericChartData.lean`](../Other/AlgebraicGeometry/ChernWindingGenericChartData.lean)
   replaces `NormalWindingChartData` by `GenericWindingChartData`, whose `normal_coordinate` field
   is the `u ·` version (with the unit `normalUnit` and `normalUnit_ne_zero` as extra fields), and
   proves `GenericWindingChartData.normalizesCoclass` from it.
   [`ChernWindingGenericChartExistence.lean`](../Other/AlgebraicGeometry/ChernWindingGenericChartExistence.lean)
   then gives the whole chain in the current `∃ B` form:

   ```lean
   def HasGenericFlatteningCharts : Prop :=
     ∀ (c : Scheme.CartierData X.left) (x : X.left), coheight x = ((1 : ℕ) : ℕ∞) →
       ∃ B : Closeds X.left, (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
         ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
           Point.underlying q ∉ B → Nonempty (GenericWindingChartData X c x (dim X.left) q)

   theorem hasGeometricWindingCharts_of_genericFlatteningCharts
       (h : HasGenericFlatteningCharts (X := X)) : HasGeometricWindingCharts (X := X)
   theorem hasNormalizedWindingCharts_of_genericFlatteningCharts
       (h : HasGenericFlatteningCharts (X := X)) : HasNormalizedWindingCharts X
   ```

   **`coclass_restrict` only has to be checked on the component**
   ([`ChernWindingNormalChartTransport.lean`](../Other/AlgebraicGeometry/ChernWindingNormalChartTransport.lean)).
   The local relative-cohomology sheaf has subsingleton stalks off its support, so

   ```lean
   theorem AlgebraicTopology.Singular.supportRelativeCohomologySheaf_eq_toSheaf_of_germ
       (M : TopCat.{0}) (S : Set M) (hS : IsClosed S) (n : ℕ) (W : Opens M)
       (s : (supportRelativeCohomologySheaf M S n).obj.obj (op W))
       (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (W : Set M) S) n)
       (h : ∀ y, ∀ hy : y ∈ W, y ∈ S →
         (supportRelativeCohomologySheaf M S n).presheaf.germ W y hy s =
           supportRelativeCohomologyGerm M S n W y hy a) :
       s = (supportRelativeCohomologyToSheaf M S n).app (op W) a

   theorem AlgebraicGeometry.ComplexPoint.coclass_restrict_of_germ …
   ```

   ### What is left

   **So both obligations (b) and (c) are now theorems**, and `HasGenericFlatteningCharts` is all
   that remains of §4.3 step 4 item 3 apart from the Chern-class half (a).  It needs exactly three
   things, none of which involves cohomology or the Chern class:

   1. **The exceptional set.**  Take one local form `f` of `c` at `x`
      (`Scheme.CartierData.exists_localForm`) and put `B :=` the closure of `{x}` minus `f.opens`,
      united with the locus on `closure {x}` where `f.equation` fails to generate the ideal of
      `Z_x`.  Both pieces are Zariski-closed in `closure {x}` and miss `x`: the first because
      `f.opens` is open and contains `x`; the second because `ord_x f.equation = 1` says exactly
      that `f.equation` generates the ideal at the generic point, and "`h = a · g` with `a(q) ≠ 0`
      for a local generator `g`" fails on the Zariski-closed locus `{a = 0} ∩ Z_x`.  The `B`
      is *forced*: by `exists_chernWindingChart_imp_divisor_eq_zero` no winding chart at all
      exists at a point lying on a second component of `|D|`.
   2. **The chart and the unit.**  At `q` off `B`, take the repository's own flattening chart
      `closedImmersionHolomorphicFlatteningChart` of the smooth-locus closed immersion, and
      produce `normalUnit`: the continuous nowhere vanishing function on the chart neighbourhood
      with `h^an = normalUnit · (normal coordinate)`.  This is the analytic form of "the local
      equation generates the ideal at `q`"; *no implicit function theorem is needed any more*.
      The remaining fields (`le`, `le_analytic`) are shrinking, and `exists_log` is automatic
      (`exists_log_of_flattening`).
   3. **`coclass_restrict`.**  By `coclass_restrict_of_germ` this is now a statement about germs
      at points of `Z_x` only.  Upstairs along the open embedding
      `cycleComponentSmoothClosedLiftAmbientMap` the repository already computes those germs
      (`smoothClosedSupportCoclassSection_germ_eq_normalCoclass`,
      `smoothClosedSupportNormalCoclass_restrict_eq_chart`,
      `smoothClosedSupportCoclassSection_restrict_chart`); what is missing is only the
      stalk/section transport through `supportRelativeCohomologySheafOpenIso` (see
      `supportRelativeCohomologySectionOnOpen_restrict` and
      `supportRelativeCohomologySheafOpenIso_unit_apply`) together with the degree rewrite
      `d - (d - 1) = 1` inside `cycleComponentSmoothClosedLiftCoclassSection`.

   Verification: `lake build Other.AlgebraicGeometry.ChernWindingNormalizedCharts`,
   `… ChernWindingChartPeriods`, `… ChernWindingHolomorphicLog`,
   `… ChernWindingStandardTriangle`, `… ChernWindingLocalFormObstruction`,
   `… ChernWindingNormalChartExistence`; `lake env lean scripts/lefschetz_axiom_audit.lean`.

Summary of the named obligations, in dependency order:

| Name | File | Content |
| --- | --- | --- |
| ~~`AnalytificationGenerates`~~ | `AnalytificationGenerates.lean` | **proved**: `analytificationGenerates` |
| ~~`SectionSheafDeterminesClass`~~ | `UnitExtensionClassOfSectionSheaf.lean` | **proved**: `sectionSheafDeterminesClass` |
| ~~supported exactness~~ | `CohomologyWithSupportExact.lean` | **proved**: `exact_forgetSupport_restrictToComplement` |
| ~~vanishing of the restricted extension class~~ | `UnitExtensionOpenRestriction.lean` | **proved**: `cohomologyClass_comp_restrictionUnit_eq_zero` |
| ~~`HasRestrictedChernFactorization`, `RestrictedChernClassVanishes`~~ | `ChernClassRestrictionVanishing.lean` | **proved**: `hasRestrictedChernFactorization`, `restrictedChernClassVanishes` (§4.3 step 3c), via `OpenRestrictionLocalSheaf.lean` and `OpenRestrictionDerivedFactorization.lean` |
| `HasSupportedChernLift` | `ChernLocalModel.lean` | §4.3 step 4: the step-3 conclusion, packaged for `|D|^an`; **not** a hypothesis of the assembly any more — only *some* lift, which is too weak |
| ~~`HasComponentSupportDecomposition`~~ | `ComponentSupportDecomposition.lean` | **proved**: `hasComponentSupportDecomposition_unconditional` |
| ~~`HasCodimensionTwoSupportedVanishing`~~ | `ClosedSupportCoheightDimension.lean` | **proved**: `hasCodimensionTwoSupportedVanishing`, via the generic smooth filtration of any `Closeds X.left` |
| ~~Mayer–Vietoris for two closed supports~~ | `SupportUnionSplitting.lean` | **proved**: `exists_supportedSectionsEnlarge_add_eq` |
| `HasChernLocalModel` | `ChernLocalModel.lean` | §4.3 step 4: the local model, **existential in the lift** (an arbitrary lift has the wrong multiplicities — `ℙ¹` counterexample in §4.3 step 4); needs §4.2(a) and the canonical relative class |
| `HasNormalizedWindingCharts` | `ChernLocalModelWinding.lean` | §4.3 step 4 item 3: (b) + (c), existence of normalised winding charts **off a Zariski-closed `B ⊆ Z_x`, `x ∉ B`, chosen by the obligation** (generic form; gluing by `cycleComponentSmoothSupport_restriction_injective`, `CycleComponentRestrictionInjective.lean`); **reduced** to `HasGeometricWindingCharts` — (b) is now a theorem |
| ~~the winding homomorphism `∂ ∘ δ`~~ | `ChernWindingLift.lean`, `ChernWindingCochain.lean`, `ChernWindingBoundary.lean`, `ChernWindingUnitClass.lean` | **constructed**: `ChernWinding.windingPeriod`, `ChernWinding.relativeWindingPeriod`, `windingSheafHom`; plus `windingSheafHom_restrict_eq_zero` (obligation (b)) and the normalisation criterion `windingRelativeClass_eq_chartNormalProjectionCoclass` |
| `HasWindingChartData` | `ChernWindingNormalizedCharts.lean` | §4.3 step 4 item 3: what is left of (b) + (c) — a normal chart with a local form, a holomorphic logarithm on the chart, rational winding periods, and the single winding-number equation |
| `HasGeometricWindingCharts` | `ChernWindingChartPeriods.lean` | §4.3 step 4 item 3: `HasWindingChartData` with the rationality of the periods removed (now a theorem), in the same generic `∃ B` form; reduces to `HasNormalizedWindingCharts` by `hasNormalizedWindingCharts_of_geometricWindingCharts` |
| ~~rationality of the winding periods~~ | `ChernWindingRational.lean`, `ChernWindingChartPeriods.lean` | **proved**: `hasRationalWindingPeriod`, `hasWindingPeriods` |
| ~~`exists_log` on a chart~~ | `ChernWindingHolomorphicLog.lean` | **proved**: `exists_holomorphicExponential_of_simplyConnected` (simply connected, locally path connected chart) |
| ~~the sign of the normalisation~~ | `ChernWindingStandardTriangle.lean` | **proved**: `windingPeriod_standardPuncturedBoundaryClass = 1` — the repository's orientation gives `+1` |
| ~~naturality of the connecting map of a pair~~ | `ChernWindingNormalChartBoundary.lean` | **proved**: `relativeSingularBoundary_naturality`, `relativeSingularBoundary_standardComplexLocalClass` |
| ~~`NormalizesCoclass` for a normal chart~~ | `ChernWindingNormalChartValue.lean`, `…Class.lean`, `…Data.lean` | **proved**: `windingPeriod_flattenedNormalClass`, `windingClass_eq_chartNormalProjectionCoclass`, `NormalWindingChartData.normalizesCoclass` |
| ~~`exists_log` on a flattening chart~~ | `ChernWindingNormalChartLog.lean` | **proved**: `exists_holomorphicExponential_flattenedSupportNeighborhood` |
| ~~`HasNormalFlatteningCharts`~~ | `ChernWindingNormalChartExistence.lean` | superseded by `HasGenericFlatteningCharts`, which needs only the normal coordinate *up to a unit* |
| ~~the normal coordinate up to a unit~~ | `ChernWindingNormalChartUnit.lean`, `ChernWindingGenericChartData.lean` | **proved**: `windingClass_eq_chartNormalProjectionCoclass_of_unit`, `GenericWindingChartData.normalizesCoclass` — this removes the implicit function theorem from the remaining work |
| ~~`coclass_restrict` reduced to germs~~ | `ChernWindingNormalChartTransport.lean` | **proved**: `supportRelativeCohomologySheaf_eq_toSheaf_of_germ`, `coclass_restrict_of_germ` |
| `HasGenericFlatteningCharts` | `ChernWindingGenericChartExistence.lean` | §4.3 step 4 item 3: **all that is left of (b) + (c)** — a flattening chart at `q` off a Zariski-closed `B ⊆ Z_x` with `x ∉ B`, a unit comparing `h^an` with the chart's normal coordinate, and the germ-level coclass transport; reduces to the two obligations by `hasGeometricWindingCharts_of_genericFlatteningCharts` and `hasNormalizedWindingCharts_of_genericFlatteningCharts` |
| ~~correction needed~~ | `ChernLocalModelWinding.lean`, `CycleComponentRestrictionInjective.lean` | **done**: the pointwise form was **false** at points where two components of `D` meet (`ChernWindingLocalFormObstruction.lean`); the obligation now quantifies only over `q` off a Zariski-closed `B ⊆ Z_x` with `x ∉ B`, and the reduction is re-proved via the injectivity of restriction away from `B^an` |
| ~~`HasComplementFrame` off `\|D\|^an`~~ | `ComplementFrameGeneric.lean` | **proved** off a codimension-two enlargement: `hasComplementFrameOffCodimTwo` |
| ~~excision in codimension two~~ | `SupportEnlargementCodimTwo.lean` | **proved**: `exists_enlarge_eq_of_codimTwo`; packaged as `enlargeSurjectiveCodimTwo` in `ChernRelativeClassGeneric.lean` |
| `HasRelativeChernChartFormulaGeneric` | `ChernRelativeClassGeneric.lean` | §4.3 step 4 item 3: (a) for the **canonical** relative first Chern class of a frame defined off a codimension-two enlargement of `\|D\|`; the frame and the excision inputs are discharged, so `hasDivisorClassOfSomeCartierData_of_relativeChernChartFormulaGeneric` needs only this and `HasNormalizedWindingCharts` |
| `HasStalkUnitOfOrdEqZero`, `HasUnitOffDivisor` | `ComplementFrame.lean` | §4.3 step 3/4: algebraic Hartogs at the stalks (`𝒪_{X,p}` normal); **`HasComplementFrame` reduces to it**: `hasComplementFrame_of_stalkUnit` |
| `HasChernWindingNaturality` | `ChernLocalModelWinding.lean` | §4.3 step 4 item 3: (a), the canonical relative class and its computation by winding numbers; **reduces to it**: `hasChernLocalModel_of_winding` |
| ~~winding reduction~~ | `ChernLocalModelWinding.lean` | **proved**: `hasChernLocalModel_of_winding`, `hasChernWindingNaturality_of_localModel`, `supportRelativeCohomologySheaf_section_eq_zero` |
| — (not yet stated) | — | realization of a cocycle by an extension; the Čech description of the connecting map, §4.2(a) |
| ~~step 4 assembly~~ | `ChernLocalModel.lean` | **proved**: `hasDivisorClassOfSomeCartierData_of_localModel` |
| ~~step 4 support bookkeeping~~ | `DivisorClassComparisonSupport.lean` | **proved**: `supportedInjectiveToAmbient_enlarge`, `sheafCycleClassOnCycles_eq_sum` |
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
lake env lean Other/AlgebraicTopology/ConstantSheafGlobalSection.lean
lake env lean Other/AlgebraicGeometry/UnitExtensionOpenRestriction.lean
lake env lean Other/AlgebraicGeometry/ChernClassRestrictionVanishing.lean
lake build Other.AlgebraicGeometry.DivisorObligations
lake build Other.AlgebraicGeometry.UnitExtensionClassObligations
lake env lean Other/AlgebraicGeometry/DivisorClassComparisonSupport.lean
lake env lean Other/AlgebraicGeometry/ChernLocalModel.lean
lake build Other.AlgebraicGeometry.ChernLocalModelWinding
lake build Other.AlgebraicGeometry.ComponentSupportDecomposition
lake build Other.AlgebraicGeometry.ClosedSupportCoheightDimension
lake build Other.AlgebraicGeometry.ChernClassRestrictionVanishing
lake build Other.AlgebraicGeometry.ChernLocalModel
lake env lean Other/AlgebraicGeometry/DiscreteValuationLocalRing.lean
lake env lean Other/AlgebraicGeometry/CartierLocalForm.lean
```

All of these modules are imported by `Other.lean`. Repository conventions: files start with
`module`, use `public import`, `@[expose] public noncomputable section`; local topology
instances need unique names; `set_option backward.isDefEq.respectTransparency false in` is often
needed to `change`/`rw` through bundled categories, and `omit [...] in` before the docstring
(not after) when a section variable is unused.
