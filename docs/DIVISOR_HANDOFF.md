# Handoff: the divisor of an algebraic model (`HasDivisorOfAlgebraicModel`)

This document scopes the third of the three remaining obligations for the unconditional
rational Lefschetz `(1, 1)` theorem (see [LEFSCHETZ_HANDOFF.md](LEFSCHETZ_HANDOFF.md); the
second is scoped in [GAGA_HANDOFF.md](GAGA_HANDOFF.md)). Half of it is now **proved**; what is
left is one precisely stated comparison theorem, `HasDivisorClassOfCartierData`, described in
§3 below. Nothing here depends on the other two obligations.

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

**Missing (b): the analytic transition functions of an algebraic model.** The hypothesis of the
obligation is an isomorphism `(moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules`.
From `c.Represents L` one gets algebraic generators `gᵢ` of `L` on `Uᵢ` and their transition
units `u_{ij} ∈ Γ(Uᵢ ⊓ Uⱼ, 𝒪ˣ)` with `germ(u_{ij}) = fᵢ/fⱼ`. What is needed is: the
analytification of `gᵢ` generates `(moduleAnalytification X d).obj L` on `analyticOpen X Uᵢ`,
so that the analytic transition units of `E.sectionSheafOfModules` are — after the given
isomorphism and a refinement of the two covers — the evaluations of `u_{ij}` (holomorphic by
`contMDiffAt_evaluate`, `RegularFunctionsHolomorphic.lean`). The ingredients are
`moduleAnalytification`, `moduleAnalytificationUnitIso` and Mathlib's `pullbackObjFreeIso`
(`AnalytificationModules.lean`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`);
the statement "analytification of a generating section generates" is not yet proved and is a
good self-contained warm-up.

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

### 4.3 Suggested order of work

1. *Warm-up, no analysis:* analytification of a generating section generates; the analytic
   trivializing cover of `(moduleAnalytification X d).obj L` indexed by the algebraic one.
2. Čech model of `H¹(𝒪ˣ)` and of the connecting map to `H²(ℤ)`, compared with
   `holomorphicFirstChernClass` — missing (a).
3. The supported refinement — missing (d).
4. The one-variable local computation — missing (c) — and the conclusion by
   `cycleComponentSupportedInjectiveClass_unique` plus additivity of
   `sheafCycleClassOnCycles` over the components of `c.divisor`
   (`sheafCycleClassOnCycles_sum_single`).

An alternative that avoids (a) and (d) is to compare *both* sides with the topological
intersection-theoretic description through `cycleComponentSheafBorelMooreFundamentalClass`
(`CycleComponentSheafClass.lean`) and the Poincaré dual of the divisor as a `2d−2` cycle. That
route needs a Borel–Moore statement for the analytic divisor of a holomorphic section, which the
repository does not have either; the estimate is not obviously smaller.

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
lake build Other.AlgebraicGeometry.DivisorObligations
```

All four modules are imported by `Other.lean`. Repository conventions: files start with
`module`, use `public import`, `@[expose] public noncomputable section`; local topology
instances need unique names; `set_option backward.isDefEq.respectTransparency false in` is often
needed to `change`/`rw` through bundled categories, and `omit [...] in` before the docstring
(not after) when a section variable is unused.
