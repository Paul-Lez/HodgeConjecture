/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.GammaSpecAdjunction
public import Other.Oka.AnalyticSpace.Evaluation
public import Other.Oka.Analytification.AffineSpace

/-!
# The analytification of a presented affine `ℂ`-algebra

Fix polynomials `g₁, …, g_k ∈ ℂ[x₁, …, x_n]` and write `I = (g₁, …, g_k)`. This file builds the
complex analytic space

```
X^an = { z ∈ ℂ^n | g₁ z = ⋯ = g_k z = 0 }
```

and the comparison morphism of locally ringed spaces `X^an ⟶ Spec (ℂ[x]/I)`.

The space is nothing new: it is `ComplexAnalytic.AnalyticSpace.zeroLocus` applied to the
polynomials read as holomorphic functions by `OkaRing.ofMvPolynomial`, and its structure sheaf
is coherent by Oka's theorem. What this file adds is the *comparison with algebraic geometry*:
the ring map that sends a polynomial to the holomorphic function it defines, restricted to
`X^an`, kills `I` ; that is `ComplexAnalytic.IsCutOutBy.c_app_eq_zero`, the statement that the
sections cutting a subspace out pull back to zero ; so it factors through `ℂ[x]/I`, and the
`Γ`-`Spec` adjunction turns the factorisation into a morphism `X^an ⟶ Spec (ℂ[x]/I)`.

The content is then the identification of that morphism's map on points
(`ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff`): the prime of `Spec (ℂ[x]/I)`
underneath `z ∈ X^an` is the ideal of functions vanishing at `z`. Without it the morphism would
be a formal composite; with it, it is the classical comparison map, it lands in the closed
points, and it is injective.

## What this is *not*, and the sentence to read before citing it

**`analytification g` depends on the tuple `g`, not on the algebra `ℂ[x]/I`, and nothing *in
this file* says otherwise.** There is no presentation-independence, no functoriality and no
universal property here; this file does not use `Hom(Z, ℂ^n) ≃ Γ(Z, 𝒪_Z)^n` and does not provide
it. The name `analytification` is used because that is what the object is, but every statement
below is a statement about a *chosen* presentation.

**Two of those three now exist next door, and a reader who needs them should go there rather
than conclude they are missing.** `Other/Oka/Analytification/UniversalProperty.lean` proves the
mapping property ; morphisms `Z ⟶ X^an` correspond to tuples of global sections of `𝒪_Z`
satisfying the equations ; and deduces from it that the analytification depends only on the
**ideal** `(g₁, …, g_k)`, so that two tuples spanning the same ideal, of possibly different
lengths, give canonically isomorphic spaces. It also proves that
`ComplexAnalytic.polyToGlobal` below *is* substitution of the coordinates of `X^an`.

**Both of the things that were still missing after that now exist as well.** A change of
*variables* ; two presentations of the same algebra in different numbers of variables ; is
`Other/Oka/Analytification/ChangeOfVariables.lean`; functoriality is `Other/Oka/Analytification/Functor.lean`,
where the analytification becomes a functor of the finitely generated `ℂ`-algebra with no
presentation in its statement; and `ComplexAnalytic.analytificationToSpec` below is natural in
the presentation, in `Other/Oka/Analytification/Comparison.lean`. So the sentence to carry away is that
**every statement in this file is about a chosen presentation, and none of them has to be**.

Also absent: the comparison of *structure sheaves*. `analytificationToSpec` is a morphism of
locally ringed spaces, so it carries a map `𝒪_{Spec} ⟶ π_* 𝒪_{X^an}`, but nothing here
identifies that map, and the flatness which would make analytification exact on coherent
sheaves is a separate and later question (a GAGA input, not needed for the construction). Its
map on **stalks** is identified next door, in `Other/Oka/Analytification/PresentationStalk.lean`; the
flatness is still open.

## Main definitions

- `ComplexAnalytic.polySection`: a tuple of polynomials read as holomorphic functions on `ℂ^n`.
- `ComplexAnalytic.AnalyticSpace.analytification`: **the analytic space cut out by a tuple of
  polynomials.**
- `ComplexAnalytic.presentationIdeal`: the ideal `(g₁, …, g_k)` they generate.
- `ComplexAnalytic.PresentedAlgebra`: the `ℂ`-algebra `ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)`, and
  `ComplexAnalytic.presentedAlgebraMap`, its structure map.
- `ComplexAnalytic.analytificationι` and `ComplexAnalytic.analytificationIncl`: the closed
  immersion of `X^an` into `ℂ^n` presented as an open subspace of itself, and into `ℂ^n`
  itself. Which of the two a statement wants is not a matter of taste; see
  `ComplexAnalytic.analytificationIncl`.
- `ComplexAnalytic.analytificationToSpec`: **the comparison morphism
  `X^an ⟶ Spec (ℂ[x]/I)`.**
- `ComplexAnalytic.quotientEval`: evaluation of an element of `ℂ[x]/I` at a point of `X^an`,
  which is well defined precisely because the points of `X^an` are the common zeros.

## Main results

- `ComplexAnalytic.mem_zeroLocus_polySection_iff`: **the points of `X^an` are the common zeros
  of the `gⱼ`.** This is `ComplexAnalytic.mem_zeroLocus_nodeSection_iff` for an arbitrary tuple.
- `ComplexAnalytic.range_base_analytificationIncl`: **the image of `X^an` in `ℂ^n` is that same
  common zero locus** ; the previous statement read through the inclusion whose target is `ℂ^n`
  rather than through the one whose target is `ℂ^n` presented as an open subspace of itself ;
  and `ComplexAnalytic.isClosedEmbedding_base_analytificationIncl`, that that inclusion is a
  closed embedding.
- `ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff`: for **any** complex analytic
  space `Z`, the prime of `Spec Γ(Z, 𝒪_Z)` underneath `z` is the ideal of global sections
  vanishing at `z`. This mentions no polynomials and belongs beside the evaluation API of
  `Other/Oka/AnalyticSpace/Evaluation.lean`; it is here only because that file does not import the
  `Γ`-`Spec` adjunction and should not acquire it for one lemma.
- `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff` and
  `ComplexAnalytic.analytificationToSpec_base_asIdeal`: **the point of `Spec (ℂ[x]/I)`
  underneath `z` is the ideal of functions vanishing at `z`**, i.e. the kernel of
  `ComplexAnalytic.quotientEval`.
- `ComplexAnalytic.quotientEval_mk`: **evaluating the class of a polynomial is evaluating the
  polynomial**, which is `rfl` and is stated because Mathlib's rewrite for a quotient lift does
  not fire through the definition ; named at the declaration, since a backticked name under this
  heading is read as a result of this file.
- `ComplexAnalytic.isMaximal_analytificationToSpec_base_asIdeal` and
  `ComplexAnalytic.analytificationToSpec_base_injective`: the comparison morphism lands in the
  closed points and is injective on points.
- `ComplexAnalytic.analytificationToSpec_comp_specMk`: **the comparison morphism is the
  restriction of `ℂ^n ⟶ Spec ℂ[x]`**, i.e. the evident square commutes.

## A note on namespaces, for whoever writes the next file in this directory

Everything here is in `ComplexAnalytic`, which is the convention across `Other/Oka/AnalyticSpace/`.
**`Other/Oka/Analytification/AffineSpace.lean`, next door, is not**: `complexSpaceToSpec`,
`okaGlobalOfMvPolynomial`, `mem_complexSpaceToSpec_base_asIdeal_iff` and their neighbours are
in the *root* namespace. So a
docstring here that reaches for one of them must write it unqualified. That is not a hypothetical
; this file shipped with two `ComplexAnalytic.`-prefixed references to those names, both
dangling, and they were found by `#check`ing every backticked name in the file rather than by
reading.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### The space -/

/-- A tuple of polynomials, read as a tuple of holomorphic functions on `ℂ^n` by
`OkaRing.ofMvPolynomial`. `ComplexAnalytic.nodeSection` is this at `g = fun _ ↦ X₀ * X₁`. -/
def polySection (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Fin k → (complexAffineSpaceTop.{u} n).presheaf.obj (op ⊤) :=
  fun j ↦ OkaRing.ofMvPolynomial _ (g j)

/-- **The analytic space cut out by a tuple of polynomials**: the common zero locus of the `gⱼ`
in `ℂ^n`, with the structure sheaf `𝒪_{ℂ^n} ⧸ (g₁, …, g_k)`.

Its structure sheaf is coherent, by `AnalyticSpace.isCoherentStructureSheaf`; see
`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus`. Read the module docstring
before citing this as *the* analytification: it depends on `g` and not only on the algebra
`ℂ[x]/(g)`. -/
def AnalyticSpace.analytification (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    AnalyticSpace.{u} :=
  AnalyticSpace.zeroLocus ⊤ (polySection g)

/-- **The points of the analytification are the common zeros of the `gⱼ`.**

Without this the construction is a formal composite; this is what makes it the zero locus. The
proof is `ComplexAnalytic.mem_zeroLocus_nodeSection_iff`'s, for an arbitrary tuple: a germ of a
holomorphic function on `ℂ^n` is a non-unit exactly when the function vanishes, and the value
of `OkaRing.ofMvPolynomial p` is `MvPolynomial.eval`. -/
theorem mem_zeroLocus_polySection_iff (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (y : complexAffineSpaceTop.{u} n) :
    y ∈ (complexAffineSpaceTop.{u} n).zeroLocus (polySection g) ↔
      ∀ j, MvPolynomial.eval (y.1 : ULift.{u} (Fin n) → ℂ) (g j) = 0 := by
  rw [mem_zeroLocus_restrict_complexSpace_iff]
  exact forall_congr' fun j ↦
    Iff.of_eq (congrArg (· = (0 : ℂ)) (OkaRing.evalHom_ofMvPolynomial _ _ (g j)))

/-! ### The prime underneath a point, for an arbitrary analytic space

The one general fact needed below. It belongs with the evaluation API of
`Other/Oka/AnalyticSpace/Evaluation.lean` and is here only because that file does not import the
`Γ`-`Spec` adjunction; see the module docstring. -/

/-- **The prime of `Spec Γ(Z, 𝒪_Z)` underneath `z` is the ideal of global sections vanishing at
`z`**, for an arbitrary complex analytic space `Z`.

Both halves are already available and this only joins them: Mathlib's
`AlgebraicGeometry.LocallyRingedSpace.notMem_prime_iff_unit_in_stalk` says the complement of the
prime consists of the sections with unit germ, and
`ComplexAnalytic.AnalyticSpace.evalStalk_ne_zero_iff_isUnit` says a germ is a unit exactly when
its value is nonzero ; which is the content of the residue field of `Z` being `ℂ`. -/
theorem AnalyticSpace.mem_toΓSpec_base_asIdeal_iff (Z : AnalyticSpace.{u}) (z : Z)
    (a : Z.presheaf.obj (op ⊤)) :
    a ∈ (Z.toLocallyRingedSpace.toΓSpec.base z).asIdeal ↔ Z.eval (U := ⊤) z trivial a = 0 := by
  rw [← not_iff_not, ← ne_eq, AnalyticSpace.eval_apply,
    AnalyticSpace.evalStalk_ne_zero_iff_isUnit]
  exact LocallyRingedSpace.notMem_prime_iff_unit_in_stalk (X := Z.toLocallyRingedSpace) a z

/-! ### The comparison morphism -/

section Comparison

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The ideal generated by the tuple `g`, so that the algebra being analytified is
`MvPolynomial (ULift (Fin n)) ℂ ⧸ presentationIdeal g`. -/
abbrev presentationIdeal : Ideal (MvPolynomial (ULift.{u} (Fin n)) ℂ) := Ideal.span (Set.range g)

/-- **The `ℂ`-algebra `ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` presented by a tuple.**

Stated here rather than with the `ℂ`-algebra maps between such algebras
(`Other/Oka/Analytification/ChangeOfVariables.lean`, which is where it used to live) because every
statement in this file about `ComplexAnalytic.analytificationToSpec` is a statement about it, and
because `Other/Oka/Analytification/PresentationStalk.lean` needs the name without needing any of the
`ComplexAnalytic.PresHom` machinery. -/
abbrev PresentedAlgebra (n k : ℕ) (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) : Type u :=
  MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g

/-- The structure map `ℂ → ℂ[x] ⧸ I`. -/
abbrev presentedAlgebraMap (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    ℂ →+* PresentedAlgebra.{u} n k g :=
  (Ideal.Quotient.mk (presentationIdeal.{u} g)).comp MvPolynomial.C

/-- The closed immersion of the analytification into `ℂ^n`, presented as an open subspace of
itself. -/
abbrev analytificationι :
    (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ⟶ complexAffineSpaceTop.{u} n :=
  (complexAffineSpaceTop.{u} n).zeroLocusSubspaceι (polySection g)

/-- **The inclusion of the analytification into `ℂ^n` itself**, as opposed to into `ℂ^n`
presented as an open subspace of itself: `ComplexAnalytic.analytificationι` followed by
`ofRestrict`.

Both spellings are needed and they are not interchangeable. `analytificationι` is the one the
construction runs through, because `OkaRing.ofMvPolynomial _ (g j)` at the open
`ComplexAnalytic.complexAffineSpaceTop` elaborates to *is* the cutting section, definitionally,
which is what makes `IsCutOutBy.c_app_eq_zero` apply on the nose. `analytificationIncl` is the
one a statement about `ℂ^n` ; such as `ComplexAnalytic.analytificationToSpec_comp_specMk` ;
has to be phrased in. -/
abbrev analytificationIncl :
    (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ⟶
      complexSpace (ULift.{u} (Fin n)) :=
  analytificationι g ≫ (complexAffineSpace.{u} n).ofRestrict
    (⊤ : Opens (complexAffineSpace.{u} n)).isOpenEmbedding

/-- **The inclusion of `X^an` into `ℂ^n` is a closed embedding.**

`ComplexAnalytic.analytificationι` is one by
`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, and
`ComplexAnalytic.analytificationIncl` composes it with
`AlgebraicGeometry.LocallyRingedSpace.restrictTopIso`, whose underlying map is a
homeomorphism. -/
theorem isClosedEmbedding_base_analytificationIncl :
    IsClosedEmbedding ⇑(analytificationIncl.{u} g).base :=
  (LocallyRingedSpace.homeoOfIso
      (complexAffineSpace.{u} n).restrictTopIso).isClosedEmbedding.comp
    ((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι
      (polySection.{u} g)).isClosedEmbedding

/-- **The image of `X^an` in `ℂ^n` is the common zero locus of the `gⱼ`.**

`ComplexAnalytic.mem_zeroLocus_polySection_iff` says this for
`ComplexAnalytic.analytificationι`, whose target is `ℂ^n` presented as an open subspace of
itself; this is the same statement for `ComplexAnalytic.analytificationIncl`, whose target is
`ℂ^n`, and it is the form a statement about a set of points of `ℂ^n` needs.

The proof is `Subtype.property` in one direction and the pair `⟨⟨z, trivial⟩, _⟩` in the other:
`AnalyticSpace.analytification g` is a subtype of the points of `ℂ^n` presented as an open
subspace of itself, so both directions are the membership of that subtype and no image of a
range has to be computed. -/
theorem range_base_analytificationIncl :
    Set.range ⇑(analytificationIncl.{u} g).base =
      {z : complexAffineSpace.{u} n |
        ∀ j, MvPolynomial.eval (z : ULift.{u} (Fin n) → ℂ) (g j) = 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (mem_zeroLocus_polySection_iff.{u} g _).1 y.2
  · intro hz
    exact ⟨⟨⟨z, trivial⟩, (mem_zeroLocus_polySection_iff.{u} g _).2 hz⟩, rfl⟩

/-- A polynomial, read as a global section of `𝒪_{X^an}`: the holomorphic function it defines
on `ℂ^n`, restricted to the analytification. -/
def polyToGlobal : MvPolynomial (ULift.{u} (Fin n)) ℂ →+*
    (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map (analytificationι g).op).hom.comp
    (OkaRing.ofMvPolynomial _).toRingHom

/-- **Each `gⱼ` restricts to the zero section of `𝒪_{X^an}`.**

This is the whole reason the comparison morphism exists, and it is
`ComplexAnalytic.IsCutOutBy.c_app_eq_zero` on the nose: the sections cutting a subspace out pull
back to zero on it. No compatibility lemma is needed because `polySection g j` *is*
`OkaRing.ofMvPolynomial _ (g j)` by definition. -/
theorem polyToGlobal_apply_eq_zero (j : Fin k) : polyToGlobal g (g j) = 0 :=
  ((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι (polySection g)).c_app_eq_zero j

/-- Reading polynomials as global sections of `𝒪_{X^an}` kills the ideal they generate. -/
theorem presentationIdeal_le_ker : presentationIdeal g ≤ RingHom.ker (polyToGlobal g) :=
  Ideal.span_le.2 (Set.range_subset_iff.2 fun j ↦ polyToGlobal_apply_eq_zero g j)

/-- **`ℂ[x]/I` acts on the analytification by holomorphic functions**: the factorisation of
`ComplexAnalytic.polyToGlobal` through the quotient, which exists by
`ComplexAnalytic.presentationIdeal_le_ker`. -/
def quotientToGlobal :
    MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal g →+*
      (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤) :=
  Ideal.Quotient.lift _ (polyToGlobal g) fun _ ha ↦ presentationIdeal_le_ker g ha

/-- **The comparison morphism `X^an ⟶ Spec (ℂ[x]/I)`.**

The canonical map to the spectrum of the global sections
(`AlgebraicGeometry.LocallyRingedSpace.toΓSpec`) composed with `Spec` of
`ComplexAnalytic.quotientToGlobal`. This is `complexSpaceToSpec`'s construction
with the quotient inserted, and `ComplexAnalytic.analytificationToSpec_comp_specMk` says the
two agree over `Spec ℂ[x]`. -/
def analytificationToSpec :
    (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ⟶
      Spec.locallyRingedSpaceObj
        (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal g)) :=
  (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.toΓSpec ≫
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (quotientToGlobal g))

/-! ### The map on points -/

/-- The value at a point of `X^an` of the section attached to a polynomial is the value of the
polynomial there: `ComplexAnalytic.eval_ofCutOut` at the closed immersion cutting `X^an` out. -/
theorem eval_polyToGlobal (y : AnalyticSpace.analytification.{u} g)
    (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (AnalyticSpace.analytification.{u} g).eval (U := ⊤) y trivial (polyToGlobal g p) =
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p :=
  eval_ofCutOut
    ((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι (polySection g)) y
    (OkaRing.ofMvPolynomial _ p)

/-- **The point of `Spec (ℂ[x]/I)` underneath `y` is the ideal of functions vanishing at `y`.**

This is what makes `ComplexAnalytic.analytificationToSpec` recognisable as the classical
comparison map rather than a formal composite, and it is the analogue for `X^an` of
`mem_complexSpaceToSpec_base_asIdeal_iff` for `ℂ^n`. -/
theorem mem_analytificationToSpec_base_asIdeal_iff (y : AnalyticSpace.analytification.{u} g)
    (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Ideal.Quotient.mk (presentationIdeal g) p ∈ ((analytificationToSpec g).base y).asIdeal ↔
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p = 0 := by
  refine Iff.trans ?_ (Iff.of_eq (congrArg (· = (0 : ℂ)) (eval_polyToGlobal g y p)))
  exact AnalyticSpace.mem_toΓSpec_base_asIdeal_iff _ y (polyToGlobal g p)

/-- Every `gⱼ` vanishes at every point of the analytification ; the half of
`ComplexAnalytic.mem_zeroLocus_polySection_iff` that a point of `X^an` carries with it. -/
theorem eval_eq_zero_of_mem (y : AnalyticSpace.analytification.{u} g) (j : Fin k) :
    MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) (g j) = 0 :=
  (mem_zeroLocus_polySection_iff g y.1).1 y.2 j

/-- **Evaluation of an element of `ℂ[x]/I` at a point of `X^an`.** Well defined exactly because
the points of `X^an` are the common zeros of the `gⱼ`. -/
def quotientEval (y : AnalyticSpace.analytification.{u} g) :
    MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal g →+* ℂ :=
  Ideal.Quotient.lift _ (MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ))
    fun _ ha ↦ Ideal.span_le.2
      (Set.range_subset_iff.2 fun j ↦ RingHom.mem_ker.2 (eval_eq_zero_of_mem g y j)) ha

/-- **Evaluating the class of a polynomial is evaluating the polynomial**, by `rfl` and by
construction: `ComplexAnalytic.quotientEval` is `Ideal.Quotient.lift` of `MvPolynomial.eval`.

Stated because `Ideal.Quotient.lift_mk` will not fire through the definition ; a `rw` looks for
the head symbol `Ideal.Quotient.lift` and finds `ComplexAnalytic.quotientEval` ; so a caller
holding an equation between *classes* and wanting one between *values* has nothing to rewrite
with. It is the bridge `ComplexAnalytic.localisationOpen_eq_of_isUnit_mul`
(`Other/Oka/Analytification/DistinguishedOpen.lean`) crosses. -/
theorem quotientEval_mk (y : AnalyticSpace.analytification.{u} g)
    (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    quotientEval.{u} g y (Ideal.Quotient.mk (presentationIdeal.{u} g) p) =
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p :=
  rfl

/-- `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff` as an equality of ideals: the
point underneath `y` is the kernel of evaluation at `y`. -/
theorem analytificationToSpec_base_asIdeal (y : AnalyticSpace.analytification.{u} g) :
    ((analytificationToSpec g).base y).asIdeal = RingHom.ker (quotientEval g y) := by
  refine Ideal.ext fun q ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (mem_analytificationToSpec_base_asIdeal_iff g y p).trans RingHom.mem_ker.symm

/-- **The comparison morphism lands in the closed points of `Spec (ℂ[x]/I)`**: evaluation at a
point of `X^an` is a surjection onto the field `ℂ`, so its kernel is maximal. -/
theorem isMaximal_analytificationToSpec_base_asIdeal (y : AnalyticSpace.analytification.{u} g) :
    ((analytificationToSpec g).base y).asIdeal.IsMaximal := by
  rw [analytificationToSpec_base_asIdeal]
  exact RingHom.ker_isMaximal_of_surjective (quotientEval g y)
    fun c ↦ ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), MvPolynomial.eval_C c⟩

/-- **The comparison morphism is injective on points**, by the same argument as for `ℂ^n`: the
polynomial `xᵢ - wᵢ` vanishes at `w` and hence at any point with the same image. -/
theorem analytificationToSpec_base_injective :
    Function.Injective
      fun y : AnalyticSpace.analytification.{u} g ↦ (analytificationToSpec g).base y := by
  intro y w h
  -- As in `complexSpaceToSpec_base_injective`, the equality of points is fed to `congrArg`
  -- rather than to `rw`: the carriers involved are definitionally equal but not at `instances`
  -- transparency, and a `rw` across that seam is rejected outright.
  have key (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p = 0 ↔
        MvPolynomial.eval (w.1.1 : ULift.{u} (Fin n) → ℂ) p = 0 :=
    (mem_analytificationToSpec_base_asIdeal_iff g y p).symm.trans
      ((Iff.of_eq (congrArg (fun q : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸
          presentationIdeal g) ↦ Ideal.Quotient.mk _ p ∈ q.asIdeal) h)).trans
        (mem_analytificationToSpec_base_asIdeal_iff g w p))
  refine Subtype.ext (Subtype.ext (funext fun i ↦ ?_))
  have hz :=
    (key (MvPolynomial.X i - MvPolynomial.C ((w.1.1 : ULift.{u} (Fin n) → ℂ) i))).2 (by simp)
  simpa [sub_eq_zero] using hz

/-! ### Compatibility with the comparison morphism of `ℂ^n` -/

/-- Reading a polynomial as a section of `𝒪_{X^an}` is the same whether one restricts it from
`ℂ^n` or reads it directly on the open subspace `ℂ^n|⊤`.

**This is a `rfl`, and the reason is worth recording**, because taxis #702 established that
`functor.obj ⊤` and `⊤` are *not* definitionally equal even at `⊤` and even over `ℂ^n`, so an
arbitrary section would need a transport here. A polynomial does not, because
`Γ.map (ofRestrict U).op` is definitionally the restriction map of the presheaf, the restriction
map of `okaCommPresheaf` is definitionally `OkaRing.restrict`, and
`OkaRing.restrict_ofMvPolynomial` is itself a `rfl`: the *presentation* of the section does not
mention its open. -/
theorem mk_comp_quotientToGlobal :
    CommRingCat.ofHom (Ideal.Quotient.mk (presentationIdeal g)) ≫
        CommRingCat.ofHom (quotientToGlobal g) =
      okaGlobalOfMvPolynomial (ULift.{u} (Fin n)) ≫
        LocallyRingedSpace.Γ.map (analytificationIncl g).op :=
  rfl

/-- **The comparison morphism of `X^an` is the restriction of the comparison morphism of
`ℂ^n`**: the square

```
X^an  ⟶  Spec (ℂ[x]/I)
 ↓              ↓
ℂ^n   ⟶  Spec ℂ[x]
```

commutes. Together with `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff` this pins
`analytificationToSpec` down as the classical map.

The proof is formal ; naturality of `toΓSpec`, functoriality of `Spec`, and
`ComplexAnalytic.mk_comp_quotientToGlobal` ; and uses nothing analytic. -/
theorem analytificationToSpec_comp_specMk :
    analytificationToSpec g ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom (Ideal.Quotient.mk (presentationIdeal g))) =
      analytificationIncl g ≫ complexSpaceToSpec (ULift.{u} (Fin n)) := by
  rw [analytificationToSpec, complexSpaceToSpec, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp, ← Category.assoc,
    LocallyRingedSpace.toΓSpec_naturality, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp]
  exact congrArg _ (congrArg Spec.locallyRingedSpaceMap (mk_comp_quotientToGlobal g))

end Comparison

end

end ComplexAnalytic

end
