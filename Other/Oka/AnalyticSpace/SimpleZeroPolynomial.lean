/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.SimpleZeroStalk
public import Other.Oka.Polynomial.Germ

/-!
# A polynomial hypersurface with a nonvanishing derivative projects isomorphically on stalks

`Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` states the simple-zero hypothesis as one Taylor
coefficient of the germ of the cutting section:
`MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)` of it is nonzero. That is the right form for
a general holomorphic `F`, and it is the wrong form for a caller who has a **polynomial**, because
such a caller has a derivative and not a Taylor coefficient. This file closes that gap: when the
cutting section is `OkaRing.ofMvPolynomial ⊤ P`, the hypothesis is

```
MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0
```

; *"the partial derivative of `P` in the last variable does not vanish at the point"*, with no
germ, no power series and no relabelling anywhere in it.

## What supplies it, and what it is not

The whole content is `LocalOkaRing.coeff_single_one_ofMvPolynomial`
(`Other/Oka/Polynomial/Germ.lean`): the coefficient of `xᵢ` in the germ at `y` of a polynomial is
`∂p/∂xᵢ` evaluated at `y`. Each theorem below is that rewrite and the corresponding theorem of
`Other/Oka/AnalyticSpace/SimpleZeroStalk.lean`, in two lines; the step from the cutting section to the
germ is `LocalOkaRing.ofMvPolynomial_eq`, which is `rfl`.

**No derivative operator on `LocalOkaRing` is constructed here or anywhere**, and
`Other/Oka/Regular.lean` still records correctly that there is none and that no bridge from one has
been built. The derivative below is Mathlib's `MvPolynomial.pderiv`, on polynomials, and the
route reaches the germ's coefficient without ever differentiating a germ ; by translating the
polynomial to the point and reading a *polynomial* coefficient off the shift.

## Main results

- `ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_pderiv` and
  `ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv`: **the projection of a polynomial
  hypersurface with a nonvanishing last partial derivative is an isomorphism on stalks**, for the
  `Fin`-indexed `ℂ^(n+1)`.
- `ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv` and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`: the same at the
  `ULift (Fin _)` indexing, which is the one the Riemann-existence line consumes.

## What is not here

**No `IsLocalIso` and no `IsFiniteEtale` below, and the first of the two is no longer as far
away as this bullet used to say.** Nothing below says anything about the underlying map of
`i ≫ p` ; the four results are the four `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` states, at a
hypothesis a polynomial supplies ; but they are now the *stalk input* of one:
`ComplexAnalytic.isLocalIso_comp_proj_of_pderiv`, in
`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`, is
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv` below together with the implicit
function theorem, at the same polynomial hypothesis quantified over every point. **And of a
second one, for a reason that is a property of the statements below rather than of that file**:
they are quantified one point at a time, so
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` ; the projection of an *open
subspace* of the hypersurface ; consumes the last of them at a point of that subspace with the
hypothesis asked only there, and needs no restricted stalk statement of its own.
`IsFiniteEtale` is untouched: its finiteness field is not on this line at all.

**Nothing here reads `StandardEtalePair.cond`, and the step that does is now elsewhere.** From
`derivative f * p₁ + f * p₂ = g ^ n` in `R[X]`, at a point where `f` vanishes and `g` does not, to
the derivative being nonzero there is `ComplexAnalytic.eval_pderiv_ne_zero`
(`Other/Oka/Analytification/StandardEtale.lean`). **It reaches the last two results below and not the
first two, and what separates them is the indexing rather than the mathematics.** It concludes
about `MvPolynomial (ULift (Fin (n+1))) ℂ`, where `ComplexAnalytic.localisationVar n` is
`ULift.up (Fin.last n)` by definition and so nothing has to be relabelled; the first two are about
`MvPolynomial (Fin (n+1)) ℂ`, which is a different type and is reachable only through a
`MvPolynomial.rename` along `ULift.up` that nothing on this line asks for. **And what it supplies
is the shape of that hypothesis and not an instance of it**: those last two take it at `i.base x`
for a cut-out immersion `i`, while the theorem there delivers it at a tuple already known to
satisfy the relations and `F`. Between the two sits the `ComplexAnalytic.IsCutOutBy` datum ; one
cutting section, which is what all four results below take, against a presentation's `k + 1`
relations. **This sentence ended *"and `Other/Oka/Analytification/StandardEtaleAnalytification.lean`
records it as absent"*, and that file no longer records it as absent**: it says the count was
right and the reading of it was wrong, because those four results conclude about the projection
to `ℂ^n`, so `k + 1` against one is the signature of a statement whose base is the whole of
`ℂ^n`. At `k = 0` the datum is
`ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
(`Other/Oka/Analytification/StandardEtaleLocalIso.lean`), one rewrite off
`ComplexAnalytic.isCutOutBy_analytificationInclHom`
(`Other/Oka/Analytification/UniversalProperty.lean`), which holds for every `k`. What is untouched at
`k ≥ 1` is the **projection** statement, which is a different theorem over a general base and is
false there; the statement about the structure map to `X^an` alone is
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`) and needs no implicit function theorem
relative to `X^an`.
`ComplexAnalytic.eval_pderiv_ne_zero` stands on
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv` in the same file, which says
`MvPolynomial.pderiv` of a lift is a lift of the `Polynomial.derivative` ; a lift, because that is
how `ComplexAnalytic.exists_lift_polyPresentedAlgebraEquiv` produces the polynomial the étale
presentation cuts with. **It is stated there and not here for the reason this file exists**: those
statements mention a presentation and a `StandardEtalePair`, and nothing below does.
`Other/Oka/Analytification/StandardEtaleAnalytification.lean` records what is left. **The restriction to
`D(G)` was the largest of it and is no longer part of it**: the projection statement now exists
for an arbitrary open subspace of the source. **This sentence went on to say that what stands
between that theorem and the étale presentation is *"the `ComplexAnalytic.IsCutOutBy` datum named
in the sentence above and nothing else on this line"*, and at `k = 0` nothing stands between them
at all**: the datum is built, and
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`
(`Other/Oka/Analytification/StandardEtaleLocalIso.lean`) is the end-to-end statement, taking
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` as its derivative input. **The reading taken here is
that this line is closed rather than one datum short**, and that what remains at `k ≥ 1` is not
on it: it is a statement over a general base, which is a different theorem ;
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`) for the structure map, and a false one for
the projection.

**No hypersurface inside an open subset, and the transport is no longer stated only for the germ
hypothesis.** As in the file this one builds on, `F` is entire and the ambient space here is the
whole of `ℂ^(n+1)`. The transport to an open base is `Other/Oka/AnalyticSpace/OpenBaseProjection.lean`,
which now carries the coefficient form as well as the order one, and the derivative form of it ;
this file's four statements over an open `V` ; is
`Other/Oka/AnalyticSpace/OpenBaseProjectionPolynomial.lean`. **That open subset is of the base**: it is
a cylinder `V × ℂ`, and the `D(G)` a standard étale algebra inverts is cut out of the *source* by
a polynomial in the fibre variable, so the two restrictions are not the same one and neither file
claims they are. **The source one is stated and it is not in either of those files**: it is
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
(`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`), which takes an open subspace and not a cylinder,
and shares no lemma with the open-base pair.

**No non-polynomial gain.** Every statement here is an instance of one in the imported file, so a
consumer holding a general holomorphic `F` should use that file directly; this one is not more
general and does not try to be.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Function

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

section Fin

variable {X : LocallyRingedSpace.{0}} {i : X ⟶ complexSpace (Fin (n + 1))}
  {P : MvPolynomial (Fin (n + 1)) ℂ}

/-- **The projection of a polynomial hypersurface to its base is bijective on stalks at a point
where the last partial derivative does not vanish.**

This is `ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff` with its Taylor coefficient
read as a derivative by `LocalOkaRing.coeff_single_one_ofMvPolynomial`. The vanishing of `P` at
the point is not a hypothesis here either: it follows from `hcut`, by
`ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` inside the theorem this one calls. -/
theorem bijective_stalkMap_comp_projCoords_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0) :
    Function.Bijective ((i ≫ okaMapHom (projCoords n)).stalkMap x).hom := by
  refine bijective_stalkMap_comp_projCoords_of_coeff hcut x ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin

/-- **The same as an isomorphism.** -/
theorem isIso_stalkMap_comp_projCoords_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0) :
    IsIso ((i ≫ okaMapHom (projCoords n)).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_projCoords_of_pderiv hcut x hlin)

end Fin

section ULift

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}

/-- **The same for `complexAffineSpace`**, whose coordinates are indexed by `ULift (Fin _)`.

The relabelling that `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` carries in its hypothesis
does not appear here for the same reason it does not appear in
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff`: the coefficient ; and now the
derivative ; is read at the index type the space actually has, `ULift.up (Fin.last n)`. -/
theorem bijective_stalkMap_comp_uliftProj_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    Function.Bijective
      ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x).hom := by
  refine bijective_stalkMap_comp_uliftProj_of_coeff hcut x ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin

/-- **The same as an isomorphism.** This is the form the Riemann-existence line consumes, since
`ComplexAnalytic.AnalyticSpace` indexes its coordinates by `ULift (Fin _)` and a standard étale
presentation is given by polynomials. -/
theorem isIso_stalkMap_comp_uliftProj_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsIso ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_uliftProj_of_pderiv hcut x hlin)

end ULift

end ComplexAnalytic

end

end
