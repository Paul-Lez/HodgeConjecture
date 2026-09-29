/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Basic
public import Other.Oka.AnalyticSpace.ProjectionStalk
public import Other.Oka.Regular

/-!
# A hypersurface with a simple zero projects isomorphically on stalks

Let `i : X ⟶ ℂ^(n+1)` cut out `X` by a single holomorphic function `F`
(`ComplexAnalytic.IsCutOutBy`), and let `p : ℂ^(n+1) ⟶ ℂ^n` forget the last coordinate. At a
point `x` of `X` at which the germ of `F` has a **simple zero along the last axis**, the stalk
map of `i ≫ p` is an isomorphism: the germ ring of the hypersurface is the germ ring one
dimension down, and the isomorphism is the one the projection induces.

This is the stalk half of *the analytification of a standard étale morphism is a local
isomorphism*. It is the algebra of `Other/Oka/Regular.lean` read as a statement about a morphism of
spaces, and everything it needs was already here **in substance** ; the file is the assembly and
one general lemma about kernels. Not literally: the two pointwise forms of the projection's stalk
map that the assembly consumes,
`ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply` and
`ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply`, are added to
`Other/Oka/AnalyticSpace/ProjectionStalk.lean` by the same change as this file.

## The four inputs

* the stalk of a cut-out is the ambient stalk modulo the germs of the cutting sections ;
  `ComplexAnalytic.IsCutOutBy`'s `surjective_stalkMap` and `ker_stalkMap` fields;
* the stalk of `𝒪_{ℂ^ι}` at any point is `LocalOkaRing ι` ; `okaStalkEquiv`, which is in the
  **root** namespace, in `Other/Oka/StalkEquiv.lean`;
* the stalk map of the projection is `LocalOkaRing.incl` ;
  `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords`;
* `LocalOkaRing (Fin n)` is `LocalOkaRing (Fin (n+1)) ⧸ (f)` at a germ with a simple zero ;
  `LocalOkaRing.quotientSimpleZeroEquiv`.

The last of those is the mathematics ; Weierstrass division at degree one ; and the three before
it are what turns it into a statement about `i ≫ p`. What makes the assembly go through in one
step is that `LocalOkaRing.quotientSimpleZeroEquiv`'s underlying map **is**
`Ideal.Quotient.mk ∘ LocalOkaRing.incl`, on the nose: it is built by `RingEquiv.ofBijective` on
that composite in `LocalOkaRing.quotientDegreeOneEquiv`, so no computation is needed to recognise
it in the composite stalk map.

## The shape: one abstract step, two indexings

`ComplexAnalytic.bijective_stalkMap_comp_of_incl` takes the two identifications as arguments ;
a ring isomorphism of each stalk with a `LocalOkaRing`, and the statement that the projection is
`LocalOkaRing.incl` between them ; and is the whole proof. It is stated that way because this
development indexes the coordinates of `ℂ^n` in **two** ways, `Fin n` and `ULift (Fin n)`, and
the two instances differ only in which pair of isomorphisms is supplied:

* `ComplexAnalytic.bijective_stalkMap_comp_projCoords`, for `complexSpace (Fin (n+1))` and
  `ComplexAnalytic.projCoords`, where the identification is `okaStalkEquiv` alone;
* `ComplexAnalytic.bijective_stalkMap_comp_uliftProj`, for `complexAffineSpace (n+1)` ; which is
  `complexSpace (ULift (Fin (n+1)))`, both in the root namespace ; and
  `ComplexAnalytic.uliftCastSuccEmb`, where it is
  `okaStalkEquiv` followed by `LocalOkaRing.uliftEquiv`.

The second is the one the Riemann-existence line consumes, since
`ComplexAnalytic.AnalyticSpace` is indexed by `ULift (Fin n)`; the first is the one to read,
since nothing in it is bookkeeping. Neither is a corollary of the other: there is no morphism of
spaces between the two spellings of `ℂ^n` above `Type 0`, for the reason
`Other/Oka/AnalyticSpace/ProjectionStalk.lean`'s module docstring gives.

## Why the hypothesis is a coefficient condition

The primitive form is `PowerSeries.order (MvPowerSeries.partialEval (Fin.last n) f) = 1`, because
that is what `LocalOkaRing.quotientSimpleZeroEquiv` asks for and what
`localweierstrass_preparation` computes internally. Its own docstring gives the reason it is not
stated as a derivative: **this repository has no partial-derivative operator on `LocalOkaRing`**,
so *"`∂F/∂X_n` is a unit at the point"* is not expressible.

**That is still true, and it is no longer a reason to leave the hypothesis in the order
spelling.** `MvPowerSeries.order_partialEval_eq_one_iff` says the order condition **is** two
coefficient conditions ; no constant term, and a nonzero coefficient at
`Finsupp.single (Fin.last n) 1`. Neither mentions a derivative, and no derivative operator is
needed to supply them: a consumer that has one may use it, and a consumer that computes a Taylor
coefficient directly need not acquire one. What that leaves open is the *identification* of that
coefficient with `∂F/∂X_n` at the point, which is a statement about one named coefficient rather
than about the order of a power series.

**For a cutting section that comes from a polynomial, that identification now exists**, and it is
`Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean`: when `F` is `OkaRing.ofMvPolynomial ⊤ P` the
coefficient is `MvPolynomial.pderiv` of `P` in the last variable, evaluated at the point
(`LocalOkaRing.coeff_single_one_ofMvPolynomial`). **It is still not here and it is still not a
derivative on `LocalOkaRing`**: the derivative there is Mathlib's, on polynomials, and it reaches
the germ by translating the polynomial to the point rather than by differentiating a germ.

**For a general holomorphic `F` there is now something to identify the coefficient with too, and
this paragraph used to say there was not.** `OkaRing.coeff_single_one_germ`
(`Other/Oka/GermDerivative.lean`) says the coefficient is `fderiv ℂ (F.toGlobalFun ⊤) y (Pi.single j 1)`
; the derivative of the *function*, at the point, in the direction of the last axis. **It is
still not a derivative on `LocalOkaRing`**, for the reason the previous paragraph gives and which
`Other/Oka/Regular.lean` states in full: the value is a complex number and not a germ, so *"`∂F/∂X_n`
is a unit at the point"* remains unstatable. What changes is that the hypothesis of the four
`…_of_coeff` results below can be read as a derivative by a caller who has `F` as a holomorphic
function rather than as a polynomial.

**And only one of the two is a hypothesis, because the other is free.** The first says through
`OkaRing.constantCoeff_germ` that `F` vanishes at the point, and
`ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` derives exactly that from `hcut`: a point of the
subspace is one where every cutting section vanishes, which is what `range_base` says. So the four
`…_of_coeff` results below ask for the **linear coefficient alone**. The same argument reads
backwards on the four results above: given their `hcut`, their order hypothesis is *equivalent* to
that one coefficient being nonzero, so nothing was lost in the trade.

At the `ULift (Fin _)` indexing the surviving hypothesis is read off the germ on the space one
actually has, with no `LocalOkaRing.uliftEquiv` in the statement.

Note that the germ is taken **at the point**, so the condition is on the Taylor expansion of `F`
centred at `i.base x` and not at the origin; `okaStalkEquiv` absorbs the translation.

## Main results

- `ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff`: for a cut-out by a **single** section, the
  kernel of the stalk map is the principal ideal on the germ, read through any ring isomorphism
  of the ambient stalk.
- `ComplexAnalytic.bijective_stalkMap_comp_of_incl`: **the abstract step** ; if the projection is
  the inclusion of the germs not involving the last variable and the immersion is the quotient by
  a germ with a simple zero, the composite is bijective on stalks.
- `ComplexAnalytic.bijective_stalkMap_comp_projCoords` and
  `ComplexAnalytic.isIso_stalkMap_comp_projCoords`: **the projection of a hypersurface with a
  simple zero is an isomorphism on stalks**, for the `Fin`-indexed `ℂ^(n+1)`.
- `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj`: the same for the `ULift (Fin _)`-indexed
  affine space named in §*The shape* above.
- `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero`: **every cutting section vanishes at every point
  of the subspace it cuts out**, which is what makes the vanishing half of the hypothesis below
  free rather than asked for.
- `ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff` and
  `ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_coeff`: **the same hypothesis as one
  coefficient** ; the coefficient of the last variable in the Taylor expansion of `F` at the point
  is nonzero ; with `ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff` and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` the `ULift (Fin _)`-indexed forms,
  **stated with no relabelling in sight**.

## What is not here

**Nothing the results above are stated *in terms of* is named in that list** ; not
`LocalOkaRing.incl`, not `okaStalkEquiv`, not `complexAffineSpace`, though all three are named in
the paragraphs before it: none of those is a result of this file.

**No finiteness, and so no `IsFiniteEtale`. And no `IsLocalIso` ; but that is now an absence
from this *file* and not from the tree.** Nothing below says anything about the underlying map of
`i ≫ p`, not even that it is open, and that has not changed. What has changed is that the other
field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` is supplied elsewhere:
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff` in
`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`, which imports this file, proves the projection a
local homeomorphism from the *same* coefficient hypothesis quantified over every point, and
`ComplexAnalytic.isLocalIso_comp_proj_of_coeff` there is the two halves together. Finiteness is
untouched by all of it ; that the projection of a monic hypersurface to its base is closed is a
separate and much larger piece of work, and it is what `IsFiniteEtale` still waits on.

**No hypersurface inside an open subset ; this is no longer absent, and it is not in this
file.** `Y` is the whole of `ℂ^(n+1)` below, so `F` is entire, and that has not changed. A
standard étale algebra inverts a polynomial as well as cutting one out, and its analytification
lives in an open subspace; `ComplexAnalytic.IsLocalModel` is stated for
`(complexAffineSpace n).restrict U` for exactly that reason. The transport is
`ComplexAnalytic.bijective_stalkMap_comp_projRestrict` and
`ComplexAnalytic.isIso_stalkMap_comp_projRestrict` in
`Other/Oka/AnalyticSpace/OpenBaseProjection.lean`, which imports this file.

**That transport is of the *base* and the open subspace a standard étale algebra lives in is of
the *source*, which the sentence above runs together.** The source one needs nothing new on the
stalk side and that is a property of the statements below: they are quantified one point at a
time, so a point of an open subspace supplies the hypothesis at itself and the open immersion
contributes an isomorphism by
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`. The composition is inside
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_coeff`
(`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`); the topological half of that statement is the one
that needed statements of its own, though none of them needed mathematics the tree did not
already have.

**And it does not go through `AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso`**, which is
what the paragraph that used to stand here predicted it would need. That `Iso` is never
constructed there. `ComplexAnalytic.cylinderStalkEquiv` inverts the stalk map of the inclusion of
the open subspace using the instance `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict` ;
the same isomorphism, at the spelling a caller of `ofRestrict` already holds ; and
`ComplexAnalytic.baseStalkEquiv` goes through `ComplexAnalytic.restrictStalkEquiv`, which
`Other/Oka/AnalyticSpace/Restrict.lean` had already built for exactly this factorisation. Recorded
because a reader who took the old sentence at face value would go and build a Mathlib bridge that
the working proof does not use.

**No derivative hypothesis, and none for a general `F` anywhere** ; see §*Why the hypothesis is
a coefficient condition* for what replaced the need for one, and for the polynomial case, which
is `Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean` and not this file ; and **no packaged
`LocalOkaRing (Fin n) ≃+* X.presheaf.stalk x`**:
the isomorphism is available from the results below ; `CategoryTheory.asIso` turns one of them
into an isomorphism in `CommRingCat`, and `okaStalkEquiv` identifies its source with
`LocalOkaRing (Fin n)` ; and naming that composite would fix a direction this file has no consumer
for yet. The two are an isomorphism of `CommRingCat` and a `RingEquiv`, so "composite" is what a
reader would have to build and not something a coercion supplies.

**No statement about more than one cutting section.** `ComplexAnalytic.IsCutOutBy` allows a family
of any length; `ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff` and everything after it are for
`![F]`, because `LocalOkaRing.quotientSimpleZeroEquiv` quotients by a principal ideal. A complete
intersection of higher codimension would be an induction and is not attempted.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Function

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### A cutting section vanishes on the subspace it cuts out -/

/-- **Every section cutting out `X` evaluates to zero at every point of `X`.**

`ComplexAnalytic.IsCutOutBy`'s `range_base` field states the image as the set where every germ of
every `f j` is a non-unit, and on `ℂ^ι` a germ is a non-unit exactly when the function vanishes,
which is `germ_mem_maximalIdeal_iff`. Applied at `i.base x`, which is in the image by
construction.

**It makes the vanishing hypothesis of the `…_of_coeff` results below unstatable rather than
optional**: a caller who has a point of the hypersurface already has this, so asking for it would
be asking for something the other hypothesis carries. The set form of the same fact, at one
section and for `ComplexAnalytic.AnalyticSpace`, is
`ComplexAnalytic.range_base_eq_of_isCutOutBy` in `Other/Oka/AnalyticSpace/MonicProjection.lean`; this is
the pointwise form, at a family of any length, and it is stated here because the results below are
where it is consumed. -/
theorem IsCutOutBy.evalHom_eq_zero {ι : Type u} [Fintype ι] {X : LocallyRingedSpace.{u}}
    {i : X ⟶ complexSpace ι} {k : ℕ} {f : Fin k → OkaRing (⊤ : Opens (ι → ℂ))}
    (hcut : IsCutOutBy i f) (x : X) (j : Fin k) :
    OkaRing.evalHom (show i.base x ∈ (⊤ : Opens (ι → ℂ)) from trivial) (f j) = 0 := by
  have hmem : i.base x ∈ Set.range i.base := ⟨x, rfl⟩
  rw [hcut.range_base] at hmem
  exact (germ_mem_maximalIdeal_iff
    (show i.base x ∈ (⊤ : Opens (ι → ℂ)) from trivial) (f j)).1 (hmem j)

/-! ### The kernel of the stalk map of a cut-out by one section -/

/-- **For a cut-out by a single section, the kernel of the stalk map is the principal ideal on
its germ**, transported along any ring isomorphism of the ambient stalk.

`ComplexAnalytic.IsCutOutBy`'s `ker_stalkMap` field gives the ideal generated by the *range* of
the family, which at a one-element family is a singleton; the transport is there because every
consumer of this holds the ambient stalk as a `LocalOkaRing` and not as a colimit.

The generator is an argument together with the equation that produces it, rather than being
written out as `β (Y.presheaf.Γgerm (i.base x) F)`. That is not cosmetic: the two spellings of
the ambient point ; through `X.toTopCat` and through `X.toPresheafedSpace` ; make the written-out
form a term `rw` will not match against the one a caller builds, and passing the equation lets
elaboration do the identification instead. -/
theorem IsCutOutBy.mem_ker_stalkMap_iff {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y}
    {F : Y.presheaf.obj (op ⊤)} (hcut : IsCutOutBy i ![F]) (x : X)
    {R : Type*} [CommRing R] (β : Y.presheaf.stalk (i.base x) ≃+* R) {a : R}
    (ha : β (Y.presheaf.Γgerm (i.base x) F) = a) (s : Y.presheaf.stalk (i.base x)) :
    s ∈ RingHom.ker (i.stalkMap x).hom ↔ β s ∈ Ideal.span {a} := by
  subst ha
  have hker : RingHom.ker (i.stalkMap x).hom =
      Ideal.span {Y.presheaf.Γgerm (i.base x) F} := by
    rw [hcut.ker_stalkMap x]
    congr 1
    rw [Set.range_unique]
    rfl
  rw [hker, Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff β]

/-! ### The abstract step -/

/-- **The composite of a one-section cut-out and a projection which is `LocalOkaRing.incl` on
stalks is bijective on stalks, at a germ with a simple zero.**

The two identifications are arguments: `β` reads the ambient stalk as `LocalOkaRing (Fin (n+1))`,
`α` reads the stalk of the base as `LocalOkaRing (Fin n)`, `hP` says the projection is
`LocalOkaRing.incl` between them, and `hker` says the immersion is the quotient by `(f)`. What is
proved is that `LocalOkaRing.quotientSimpleZeroEquiv` is exactly the induced map.

Both halves are the same two facts read in opposite directions. **Injectivity**: a germ killed by
the composite lands in `(f)`, so its class is `0`, so it is `0` because
`LocalOkaRing.quotientSimpleZeroEquiv` is injective. **Surjectivity**: lift the target to the
ambient stalk, take the preimage of its class, and the difference lands in `(f)` ; which is the
kernel ; so the two have the same image. -/
theorem bijective_stalkMap_comp_of_incl {X Y W : LocallyRingedSpace.{u}}
    (i : X ⟶ Y) (p : Y ⟶ W) (x : X)
    (α : W.presheaf.stalk (p.base (i.base x)) ≃+* LocalOkaRing (Fin n))
    (β : Y.presheaf.stalk (i.base x) ≃+* LocalOkaRing (Fin (n + 1)))
    {f : LocalOkaRing (Fin (n + 1))}
    (hP : ∀ t, β ((p.stalkMap (i.base x)).hom t) = LocalOkaRing.incl (α t))
    (hQ : Function.Surjective (i.stalkMap x).hom)
    (hker : ∀ s, s ∈ RingHom.ker (i.stalkMap x).hom ↔ β s ∈ Ideal.span {f})
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      (f : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective ((i ≫ p).stalkMap x).hom := by
  -- `LocalOkaRing.quotientSimpleZeroEquiv` is `Ideal.Quotient.mk ∘ LocalOkaRing.incl` on the
  -- nose, which is why this `have` needs no proof beyond the equivalence itself.
  have hE : Function.Bijective
      (fun c : LocalOkaRing (Fin n) ↦ Ideal.Quotient.mk (Ideal.span {f}) (LocalOkaRing.incl c)) :=
    (LocalOkaRing.quotientSimpleZeroEquiv hf).bijective
  have hcomp : ((i ≫ p).stalkMap x).hom =
      (i.stalkMap x).hom.comp ((p.stalkMap (i.base x)).hom) := by
    rw [LocallyRingedSpace.stalkMap_comp]
    rfl
  rw [hcomp]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h1 : ((p.stalkMap (i.base x)).hom t) ∈ RingHom.ker (i.stalkMap x).hom := ht
    rw [hker, hP t] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {f}) (LocalOkaRing.incl (α t)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 h1
    exact (map_eq_zero_iff α α.injective).1 (hE.1 (by simpa using h2))
  · intro c
    obtain ⟨s, hs⟩ := hQ c
    obtain ⟨t₀, ht₀⟩ := hE.2 (Ideal.Quotient.mk (Ideal.span {f}) (β s))
    refine ⟨α.symm t₀, ?_⟩
    have hdiff : (p.stalkMap (i.base x)).hom (α.symm t₀) - s ∈
        RingHom.ker (i.stalkMap x).hom := by
      have hsub : β ((p.stalkMap (i.base x)).hom (α.symm t₀) - s) =
          β ((p.stalkMap (i.base x)).hom (α.symm t₀)) - β s := map_sub β _ _
      rw [hker, hsub, hP, RingEquiv.apply_symm_apply]
      exact Ideal.Quotient.eq.1 ht₀
    have h4 : (i.stalkMap x).hom ((p.stalkMap (i.base x)).hom (α.symm t₀)) -
        (i.stalkMap x).hom s = 0 := by
      rw [← map_sub]
      exact hdiff
    have h5 : (i.stalkMap x).hom ((p.stalkMap (i.base x)).hom (α.symm t₀)) = c := by
      rw [← hs, ← sub_eq_zero]
      exact h4
    exact h5

/-! ### The two indexings

`ComplexAnalytic.projCoords` for `Fin`, `ComplexAnalytic.uliftCastSuccEmb` for `ULift (Fin _)`.
The only difference between the two proofs is the pair of identifications handed to
`ComplexAnalytic.bijective_stalkMap_comp_of_incl`. -/

section Fin

variable {X : LocallyRingedSpace.{0}} {i : X ⟶ complexSpace (Fin (n + 1))}
  {F : OkaRing (⊤ : Opens (Fin (n + 1) → ℂ))}

/-- **The projection of a hypersurface with a simple zero is bijective on stalks.**

`F` is an entire function on `ℂ^(n+1)`, `i` cuts out `X` by it, and the hypothesis says that the
Taylor expansion of `F` at `i.base x`, restricted to the last axis, has a simple zero. -/
theorem bijective_stalkMap_comp_projCoords (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective ((i ≫ okaMapHom (projCoords n)).stalkMap x).hom := by
  refine bijective_stalkMap_comp_of_incl i _ x _ (okaStalkEquiv (i.base x))
    (fun t ↦ okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply t)
    (hcut.surjective_stalkMap x) (fun s ↦ ?_) hf
  exact hcut.mem_ker_stalkMap_iff x (okaStalkEquiv (i.base x)) (okaStalkEquiv_germ _ _) s

/-- **The projection of a hypersurface with a simple zero is an isomorphism on stalks.** -/
theorem isIso_stalkMap_comp_projCoords (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    IsIso ((i ≫ okaMapHom (projCoords n)).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkMap_comp_projCoords hcut x hf)

/-- **The same, from one coefficient rather than from the order**: the coefficient of the last
variable in the Taylor expansion of `F` at the point is nonzero.

`MvPowerSeries.order_partialEval_eq_one_iff` splits the order hypothesis into two coefficient
conditions, and **the first of them is free**: it says through `OkaRing.constantCoeff_germ` that
`F` vanishes at the point, and `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` derives that from
`hcut` alone. So what is left is one coefficient, and it is a single Taylor coefficient and
**not** a derivative; see this file's `## Why the hypothesis is a coefficient condition`. -/
theorem bijective_stalkMap_comp_projCoords_of_coeff (hcut : IsCutOutBy i ![F]) (x : X)
    (hlin : MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) ≠ 0) :
    Function.Bijective ((i ≫ okaMapHom (projCoords n)).stalkMap x).hom := by
  refine bijective_stalkMap_comp_projCoords hcut x ?_
  rw [MvPowerSeries.order_partialEval_eq_one_iff]
  refine ⟨?_, hlin⟩
  rw [← LocalOkaRing.constantCoeff_apply, OkaRing.constantCoeff_germ]
  simpa using hcut.evalHom_eq_zero x 0

/-- **The same as an isomorphism**, from the one coefficient. -/
theorem isIso_stalkMap_comp_projCoords_of_coeff (hcut : IsCutOutBy i ![F]) (x : X)
    (hlin : MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) ≠ 0) :
    IsIso ((i ≫ okaMapHom (projCoords n)).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_projCoords_of_coeff hcut x hlin)

end Fin

section ULift

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}

/-- **The same for `complexAffineSpace`** ; the root-namespace one, `Other/Oka/ComplexSpace.lean`,
whose coordinates are indexed by `ULift (Fin (n+1))`.

The germ ring is relabelled by `LocalOkaRing.uliftEquiv` at both ends, which is why the
hypothesis is about `LocalOkaRing.uliftEquiv` of the germ rather than about the germ. That
relabelling is a ring isomorphism and not an isomorphism of spaces, and it cannot be one; see
`Other/Oka/AnalyticSpace/ProjectionStalk.lean`. -/
theorem bijective_stalkMap_comp_uliftProj (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F) :
          LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective
      ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x).hom := by
  refine bijective_stalkMap_comp_of_incl i _ x
    ((okaStalkEquiv (okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) (i.base x))).trans
      (LocalOkaRing.uliftEquiv (Fin n)))
    ((okaStalkEquiv (i.base x)).trans (LocalOkaRing.uliftEquiv (Fin (n + 1))))
    (fun t ↦ by exact AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply t)
    (hcut.surjective_stalkMap x) (fun s ↦ ?_) hf
  exact hcut.mem_ker_stalkMap_iff x _
    (congrArg (LocalOkaRing.uliftEquiv (Fin (n + 1))) (okaStalkEquiv_germ _ _)) s

/-- **The same as an isomorphism.** The morphism is
`ComplexAnalytic.AnalyticSpace.proj`'s underlying morphism of locally ringed spaces, by
`ComplexAnalytic.AnalyticSpace.toLRSHom_proj`. -/
theorem isIso_stalkMap_comp_uliftProj (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F) :
          LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    IsIso ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkMap_comp_uliftProj hcut x hf)

/-- **The same, from one coefficient rather than from the order** ; and, unlike the hypothesis it
replaces, **stated entirely at the `ULift (Fin _)` indexing**, so a caller who holds `F` on
`ComplexAnalytic.complexAffineSpace (n + 1)` never meets `LocalOkaRing.uliftEquiv` at all.

That is what `LocalOkaRing.coeff_uliftEquiv` buys: the relabelling moves the coefficient at
`Finsupp.single (ULift.up (Fin.last n)) 1` to the one at `Finsupp.single (Fin.last n) 1` and does
nothing else, so the condition may be read off the germ on the space one actually has. The
vanishing half of the order hypothesis is discharged from `hcut` by
`ComplexAnalytic.IsCutOutBy.evalHom_eq_zero`, through
`LocalOkaRing.constantCoeff_uliftEquiv` and `OkaRing.constantCoeff_germ`. -/
theorem bijective_stalkMap_comp_uliftProj_of_coeff (hcut : IsCutOutBy i ![F]) (x : X)
    (hlin : MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    Function.Bijective
      ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x).hom := by
  refine bijective_stalkMap_comp_uliftProj hcut x ?_
  rw [MvPowerSeries.order_partialEval_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [← LocalOkaRing.constantCoeff_apply, LocalOkaRing.constantCoeff_uliftEquiv,
      OkaRing.constantCoeff_germ]
    simpa using hcut.evalHom_eq_zero x 0
  · rw [show (Finsupp.single (Fin.last n) 1 : Fin (n + 1) →₀ ℕ) =
        Finsupp.embDomain (Equiv.ulift (α := Fin (n + 1))).toEmbedding
          (Finsupp.single (ULift.up.{u} (Fin.last n)) 1) by
      rw [Finsupp.embDomain_single]; rfl,
    LocalOkaRing.coeff_uliftEquiv]
    exact hlin

/-- **The same as an isomorphism**, from the one coefficient. This is the form the
Riemann-existence line consumes, since `ComplexAnalytic.AnalyticSpace` indexes its coordinates by
`ULift (Fin _)`. -/
theorem isIso_stalkMap_comp_uliftProj_of_coeff (hcut : IsCutOutBy i ![F]) (x : X)
    (hlin : MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    IsIso ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_uliftProj_of_coeff hcut x hlin)

end ULift

end ComplexAnalytic

end

end
