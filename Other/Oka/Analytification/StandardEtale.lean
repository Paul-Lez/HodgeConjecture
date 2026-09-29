/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.ChangeOfVariables
public import Other.Oka.Analytification.DistinguishedOpen
public import Mathlib.RingTheory.Etale.StandardEtale

/-!
# A standard étale algebra over a presented `ℂ`-algebra is presented

Mathlib's `StandardEtalePair R` is a pair `f g : R[X]` with `f` monic and `f'` invertible in
`R[X][1/g] ⧸ (f)`, and `StandardEtalePair.Ring` is the algebra `R[X][Y] ⧸ (f, Y·g - 1)` it names.
**The `⧸ (f)` is not decoration.** The field is `cond : ∃ p₁ p₂ n, f' * p₁ + f * p₂ = g ^ n`, and
over `ℤ` the pair `f = X² - 1`, `g = 2` satisfies it at `p₁ = X`, `p₂ = -2`, `n = 1` while
`f' = 2X`, of degree one over a reduced ring, is not a unit of `ℤ[1/2][X]`. Mathlib's own
structure docstring has the `/f` and the bullet for it under that file's `## Main definitions`
drops it, so the two disagree upstream; the field is what to read. This
file says that when `R` is a `ComplexAnalytic.PresentedAlgebra` ; the `ℂ`-algebra
`ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` this development analytifies ; that algebra is a presented
`ℂ`-algebra too, on two more variables and two more relations, and exhibits the presentation.

That is the bridge the Riemann-existence line needs: `ComplexAnalytic.analytificationFunctor`
consumes a `ComplexAnalytic.Presentation` and nothing else, so a standard étale morphism of
affine `ℂ`-schemes cannot be analytified until it is written as one.

## The two operations, which are the reusable half

Everything here is assembled out of two operations on presentations, and neither existed:

* **adjoin a variable** ; `ComplexAnalytic.polyPresentation`, the same relations read in one more
  variable, presenting `A[X]` (`ComplexAnalytic.polyPresentedAlgebraEquiv`);
* **add a relation** ; `Fin.snoc`, presenting a quotient
  (`ComplexAnalytic.presentedAlgebraSnocEquiv`).

`ComplexAnalytic.localisationPresentation`, which was already here, is exactly one of each: it is
`Fin.snoc (polyPresentation g) (t·f - 1)`, and that is `rfl`. The étale presentation below is
*two* of each, and is built as a `Fin.snoc` of `localisationPresentation` for that reason rather
than from scratch.

## The route, and what it avoids

`StandardEtalePair.Ring` is **definitionally** `R[X][Y] ⧸ (C f, Y·C g - 1)`, so the target is a
quotient of a bare polynomial ring and no localisation appears. Going through
`StandardEtalePair.equivAwayQuotient` ; `P.Ring ≃ R[X][1/g] ⧸ f` ; would have meant transporting
a `Localization.Away` along an algebra equivalence and matching the two structure maps. Taking the
definition instead costs one chain of quotient isomorphisms and no commutative algebra:

    ℂ[x, X, Y] ⧸ (g, Y·G - 1, F)   →   (A[X][Y]) ⧸ (C f, Y·C g - 1)   =   P.Ring

with the middle step `ComplexAnalytic.biPolyPresentedAlgebraEquiv`, two applications of the
adjoin-a-variable operation.

## The lifts are hypotheses, not choices

`P.f` and `P.g` live in `A[X]`, and a presentation needs polynomials. Rather than choose lifts
with `Classical.choose`, `ComplexAnalytic.etalePresentedAlgebraEquiv` takes them as arguments
together with the two equations saying they *are* lifts, and
`ComplexAnalytic.exists_presentation_standardEtale` supplies them where only existence is wanted.
That keeps the isomorphism explicit in the data a caller already has: a scheme-side standard
étale pair arrives with polynomial representatives, and forcing it through a choice would discard
them.

## Main definitions

- `ComplexAnalytic.polyPresentation`: the relations of `g`, read in one more variable.
- `ComplexAnalytic.etalePresentation`: two more variables and two more relations, `F` and
  `Y·G - 1`.
- `ComplexAnalytic.etalePresHom`: the structure map `A ⟶ A_ét`, as a
  `ComplexAnalytic.PresHom`.

## Main results

- `ComplexAnalytic.presentedAlgebraSnocEquiv`: **appending a relation presents the quotient by
  it.**
- `ComplexAnalytic.polyPresentedAlgebraEquiv`: **adjoining a variable presents the polynomial
  ring** `A[X]`.
- `ComplexAnalytic.etalePresentedAlgebraEquiv`: **the algebra the étale presentation above
  presents is `StandardEtalePair.Ring`**, written as the quotient it definitionally is.
- `ComplexAnalytic.etalePresentedAlgebraEquivRing`: the same equivalence with `P.Ring` for its
  target, which is the form a consumer states things in.
- `ComplexAnalytic.exists_presentation_standardEtale`: the same, with the lifts existentially
  quantified.
- `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv`: **`MvPolynomial.pderiv` of a lift is a
  lift of the `Polynomial.derivative`** ; the bridge between the two derivative notions, and the
  statement a consumer of `StandardEtalePair.cond` has to come through. (The theorem its
  hypothesis feeds is another file's declaration and is named in the proof's docstring rather
  than here.)
- `ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow`: **`StandardEtalePair.cond` read on the
  polynomial lifts**, which is the equation moved from `A[X]` down to the polynomial ring the
  presentation cuts with.
- `ComplexAnalytic.eval_pderiv_ne_zero`: **and evaluated** ; at a point where the relations and
  `F` vanish and `G` does not, the partial derivative of `F` in the last variable does not vanish
  either. (What that hypothesis then feeds is another file's declaration and is named in the
  proof's docstring rather than here.)

## What is not here

* **The analytification.** Nothing below mentions an analytic space; this is the algebraic half
  alone. The next step is `Other/Oka/Analytification/StandardEtaleAnalytification.lean`, which imports
  this file: `ComplexAnalytic.etaleAnalytificationIso` identifies the analytification of
  `ComplexAnalytic.etalePresentation` with the distinguished open `D(G)` inside the analytification
  of `ComplexAnalytic.hypersurfacePresentation`, and
  `ComplexAnalytic.etaleAnalytificationIso_hom_comp` says the identification is one over the base.
* **That the étale algebra is étale.** `Algebra.Etale R P.Ring` is Mathlib's, and nothing here
  reproves or uses it. **`StandardEtalePair.cond` is read**, by the last two results above and by
  nothing else in this file; `monic_f` is carried by `P` and is not read anywhere here, and the
  invertibility of `f'` as an element of a ring ; as opposed to its non-vanishing at one point ;
  is neither stated nor used. Mathlib's `StandardEtalePair.HasMap.isUnit_derivative_f` is that
  stronger statement, at a point of an `R`-algebra; `ComplexAnalytic.eval_pderiv_ne_zero`'s
  docstring says why it is not quoted.
* **Any statement about `ComplexAnalytic.etalePresHom` beyond its existence.** That it is flat, or
  unramified, or that the induced morphism of analytic spaces is a local isomorphism, is the
  content of the stalk half and is not here.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

@[expose] public section

open MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### Adding a relation -/

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (h : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **Appending a relation adds it to the ideal.** -/
theorem presentationIdeal_snoc :
    presentationIdeal.{u} (Fin.snoc g h) = presentationIdeal.{u} g ⊔ Ideal.span {h} := by
  rw [presentationIdeal, presentationIdeal, Fin.range_snoc, Ideal.span_insert, sup_comm]

/-- **A presentation with one more relation presents the quotient by that relation.**

`DoubleQuot.quotQuotEquivQuotSupₐ` on the ideal identity above. The `Ideal.map` in that lemma's
statement is the image of `Ideal.span {h}`, which is `Ideal.span` of the image of `h`; that is the
second `Ideal.quotientEquivAlgOfEq`. -/
def presentedAlgebraSnocEquiv :
    PresentedAlgebra.{u} n (k + 1) (Fin.snoc g h) ≃ₐ[ℂ]
      PresentedAlgebra.{u} n k g ⧸
        Ideal.span {Ideal.Quotient.mk (presentationIdeal.{u} g) h} :=
  (Ideal.quotientEquivAlgOfEq ℂ (presentationIdeal_snoc.{u} g h)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ ℂ (presentationIdeal.{u} g) (Ideal.span {h})).symm.trans
      (Ideal.quotientEquivAlgOfEq ℂ (by rw [Ideal.map_span, Set.image_singleton]; rfl)))

/-! ### Adjoining a variable -/

/-- **The relations of `g`, read in one more variable.**

The new variable is `ComplexAnalytic.localisationVar`, the last one, so that this is literally the
first half of `ComplexAnalytic.localisationPresentation` ; see
`ComplexAnalytic.localisationPresentation_eq_snoc`. -/
def polyPresentation : Fin k → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  fun j ↦ MvPolynomial.rename (localisationIncl.{u} n) (g j)

/-- **`ComplexAnalytic.localisationPresentation` is one of each operation**: adjoin a variable,
then append `t·f - 1`. It holds by `rfl`, and it is why the étale presentation below is built on
top of it rather than beside it. -/
theorem localisationPresentation_eq_snoc (f : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationPresentation.{u} g f =
      Fin.snoc (polyPresentation.{u} g)
        (MvPolynomial.X (localisationVar.{u} n) *
          MvPolynomial.rename (localisationIncl.{u} n) f - 1) := rfl

/-- Under `ComplexAnalytic.localisationVarEquiv`, the new relations are the old ones renamed along
`some`. -/
theorem rename_comp_polyPresentation :
    MvPolynomial.rename (localisationVarEquiv.{u} n) ∘ polyPresentation.{u} g =
      MvPolynomial.rename (some (α := ULift.{u} (Fin n))) ∘ g := by
  funext j
  simp [polyPresentation, MvPolynomial.rename_rename, Function.comp_def]

/-- The ideal statement of `ComplexAnalytic.rename_comp_polyPresentation`. -/
theorem map_presentationIdeal_polyPresentation :
    (presentationIdeal.{u} (polyPresentation.{u} g)).map
        (MvPolynomial.rename (localisationVarEquiv.{u} n)) =
      (presentationIdeal.{u} g).map
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n)))) := by
  rw [presentationIdeal, presentationIdeal, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
    ← Set.range_comp, rename_comp_polyPresentation]

/-- **`MvPolynomial.optionEquivLeft` turns renaming along `some` into `Polynomial.C`**: the new
variable becomes the polynomial variable and the old ones become constants. -/
theorem optionEquivLeft_comp_rename_some :
    ((MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))).toAlgHom.comp
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) =
      (Polynomial.CAlgHom : MvPolynomial (ULift.{u} (Fin n)) ℂ →ₐ[ℂ] _) := by
  ext i
  simp

/-- `ComplexAnalytic.optionEquivLeft_comp_rename_some`, applied. -/
theorem optionEquivLeft_rename_some (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p) = Polynomial.C p :=
  congrArg (fun F ↦ F p) (congrArg (fun F : _ →ₐ[ℂ] _ ↦ (F : _ → _))
    (optionEquivLeft_comp_rename_some.{u} (n := n)))

/-- Step 1 of three: name the new variable `none`. -/
def polyRenameEquiv :
    PresentedAlgebra.{u} (n + 1) k (polyPresentation.{u} g) ≃ₐ[ℂ]
      (MvPolynomial (Option (ULift.{u} (Fin n))) ℂ ⧸
        (presentationIdeal.{u} g).map
          (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv ℂ (localisationVarEquiv.{u} n))
    (map_presentationIdeal_polyPresentation.{u} g).symm

/-- Step 2 of three: `ℂ[x, none]` is `ℂ[x][X]`. -/
def polyOptionEquiv :
    (MvPolynomial (Option (ULift.{u} (Fin n))) ℂ ⧸
        (presentationIdeal.{u} g).map
          (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) ≃ₐ[ℂ]
      (Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ) ⧸
        (presentationIdeal.{u} g).map
          (Polynomial.C : MvPolynomial (ULift.{u} (Fin n)) ℂ →+* _)) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))) (by
    rw [presentationIdeal, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_image]
    exact congrArg Ideal.span
      (Set.image_congr' (fun p ↦ (optionEquivLeft_rename_some.{u} p).symm)))

/-- Step 3 of three: `R[X] ⧸ (I·R[X])` is `(R ⧸ I)[X]`, which is
`Ideal.polynomialQuotientEquivQuotientPolynomial` read backwards.

That is a `RingEquiv` in Mathlib and the `ℂ`-algebra structure has to be supplied; the `commutes`
proof is the computation of both sides on a constant. -/
def polyCoeffEquiv :
    (Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ) ⧸
        (presentationIdeal.{u} g).map
          (Polynomial.C : MvPolynomial (ULift.{u} (Fin n)) ℂ →+* _)) ≃ₐ[ℂ]
      Polynomial (PresentedAlgebra.{u} n k g) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm) (by
    intro c
    simp only [RingEquiv.symm_apply_eq]
    simp only [Ideal.polynomialQuotientEquivQuotientPolynomial, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      Polynomial.coe_eval₂RingHom]
    rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C,
      show (algebraMap ℂ (PresentedAlgebra.{u} n k g)) c =
        Ideal.Quotient.mk (presentationIdeal.{u} g)
          (algebraMap ℂ (MvPolynomial (ULift.{u} (Fin n)) ℂ) c) from rfl,
      Ideal.Quotient.lift_mk]
    rfl)

/-- **Adjoining a variable to a presentation presents the polynomial ring.**

No relation is added, so the ideal does not change: the whole content is that
`ℂ[x₁, …, x_n, X] ⧸ (g)` is `(ℂ[x] ⧸ (g))[X]`, which is
`Ideal.polynomialQuotientEquivQuotientPolynomial` after the two reindexings above. -/
def polyPresentedAlgebraEquiv :
    PresentedAlgebra.{u} (n + 1) k (polyPresentation.{u} g) ≃ₐ[ℂ]
      Polynomial (PresentedAlgebra.{u} n k g) :=
  (polyRenameEquiv.{u} g).trans ((polyOptionEquiv.{u} g).trans (polyCoeffEquiv.{u} g))

/-- **The old variables become constants.** -/
@[simp]
theorem polyPresentedAlgebraEquiv_mk_rename (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n) p)) =
      Polynomial.C (Ideal.Quotient.mk (presentationIdeal.{u} g) p) := by
  rw [polyPresentedAlgebraEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have h1 : polyRenameEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n) p)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    simp [MvPolynomial.rename_rename, Function.comp_def]
  rw [h1]
  have h2 : polyOptionEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p)) =
      Ideal.Quotient.mk _ (Polynomial.C p) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    exact optionEquivLeft_rename_some.{u} p
  rw [h2]
  change (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm _ = _
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]

/-- **The new variable becomes the polynomial variable.** -/
@[simp]
theorem polyPresentedAlgebraEquiv_mk_X_var :
    polyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n))) = Polynomial.X := by
  rw [polyPresentedAlgebraEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have h1 : polyRenameEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (none : Option (ULift.{u} (Fin n)))) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    simp
  rw [h1]
  have h2 : polyOptionEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.X (none : Option (ULift.{u} (Fin n))))) =
      Ideal.Quotient.mk _ Polynomial.X := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    exact MvPolynomial.optionEquivLeft_X_none ℂ (ULift.{u} (Fin n))
  rw [h2]
  change (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm _ = _
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_X]

/-- **Adjoining two variables presents `A[X][Y]`**, by
`ComplexAnalytic.polyPresentedAlgebraEquiv` twice ; once at `g` and once at
`ComplexAnalytic.polyPresentation g`, the second mapped over the coefficients. -/
def biPolyPresentedAlgebraEquiv :
    PresentedAlgebra.{u} (n + 2) k (polyPresentation.{u} (polyPresentation.{u} g)) ≃ₐ[ℂ]
      Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) :=
  (polyPresentedAlgebraEquiv.{u} (polyPresentation.{u} g)).trans
    (Polynomial.mapAlgEquiv (polyPresentedAlgebraEquiv.{u} g))

/-- A polynomial in the first `n + 1` variables becomes a constant of the outer `Polynomial`, with
coefficient its own image. -/
theorem biPolyPresentedAlgebraEquiv_mk_rename
    (F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    biPolyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)) =
      Polynomial.C (polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F)) := by
  rw [biPolyPresentedAlgebraEquiv, AlgEquiv.trans_apply,
    polyPresentedAlgebraEquiv_mk_rename.{u} (polyPresentation.{u} g) F]
  simp [Polynomial.coe_mapAlgEquiv]

/-- The last variable becomes the outer polynomial variable, the `Y` of `A[X][Y]`. -/
theorem biPolyPresentedAlgebraEquiv_mk_X_var :
    biPolyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} (n + 1)))) = Polynomial.X := by
  rw [biPolyPresentedAlgebraEquiv, AlgEquiv.trans_apply,
    polyPresentedAlgebraEquiv_mk_X_var.{u} (polyPresentation.{u} g)]
  simp [Polynomial.coe_mapAlgEquiv]

/-! ### The standard étale presentation -/

variable (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-- **Two more variables and two more relations**: `Y·G - 1`, inverting `G`, and `F`, cutting out
its zero locus.

It is `Fin.snoc` of `ComplexAnalytic.localisationPresentation` at
`ComplexAnalytic.polyPresentation g` ; adjoin `X`, invert `G`, then impose `F` ; which is why the
two variables arrive in that order and why the localisation half is not rebuilt here. -/
def etalePresentation : Fin (k + 2) → MvPolynomial (ULift.{u} (Fin (n + 2))) ℂ :=
  Fin.snoc (localisationPresentation.{u} (polyPresentation.{u} g) G)
    (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)

/-- The ideal of `ComplexAnalytic.etalePresentation`, split as the old relations and the two new
ones. -/
theorem presentationIdeal_etalePresentation :
    presentationIdeal.{u} (etalePresentation.{u} g F G) =
      presentationIdeal.{u} (polyPresentation.{u} (polyPresentation.{u} g)) ⊔
        Ideal.span {MvPolynomial.X (localisationVar.{u} (n + 1)) *
            MvPolynomial.rename (localisationIncl.{u} (n + 1)) G - 1,
          MvPolynomial.rename (localisationIncl.{u} (n + 1)) F} := by
  rw [etalePresentation, presentationIdeal_snoc, localisationPresentation,
    presentationIdeal_snoc, sup_assoc]
  congr 1
  rw [Set.pair_comm, Ideal.span_insert]
  exact sup_comm _ _

variable (P : StandardEtalePair (PresentedAlgebra.{u} n k g))

/-- **`ℂ` acts on the standard étale algebra**, through the presented algebra it is built over.

`StandardEtalePair.Ring` derives `Algebra R P.Ring` at its own base ring, and **instance search
does not compose two `Algebra` instances**, so without this line the type `… ≃ₐ[ℂ] P.Ring` does
not elaborate at all in a file importing this one ; which is the form the consumers of
`ComplexAnalytic.etalePresentedAlgebraEquivRing` below want. There is no diamond: the structure
map factors through `A` by `rfl`, which is what
`ComplexAnalytic.standardEtalePairRingIsScalarTower` records.

**That first clause is about synthesis, and it is measured rather than argued.** At `v4.32.0` ;
the revision `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` ; in a file whose only `import` is `Mathlib`, under
`variable (R T S : Type) [CommRing R] [CommRing T] [CommRing S] [Algebra R T] [Algebra T S]`,
`#synth Algebra R T` and `#synth Algebra T S` each print the binder they find and
`#synth Algebra R S` is `failed to synthesize`. The two positive lines are the control: what the
third measures is the composition step and not a missing hypothesis.

**The composite itself is Mathlib's, as a term.** `Algebra.compHom` builds `Algebra S A` out of
`Algebra R A` and a ring homomorphism `S →+* R`, and `RingHom.toAlgebra` turns a composed
`algebraMap` into an `Algebra` directly; neither is an instance, and an instance of either shape
would let search compose algebra structures indefinitely. So what a file importing this one is
short of is a **search path** and not a construction, and the line above supplies it at one pair
of rings rather than in general. `IsScalarTower` is not that path either: it takes the composed
`Algebra` as a hypothesis, which is why `ComplexAnalytic.standardEtalePairRingIsScalarTower` is
stated below this instance and not in place of it.

**That clause read *and Mathlib has no transitive `Algebra`* until 2026-09-21** ; `git show
c6bfc1f:Other/Oka/Analytification/StandardEtale.lean` carries it at `:369–370`, wrapped after *no*.
**It is corrected and not merely instrumented, because the reading its words carry was false at
the commit that wrote it**: `Algebra.compHom` is in `Mathlib/Algebra/Algebra/Defs.lean` at that
rev, so a reader taking the retired wording at face value would conclude that composing two
algebra structures is something this repository would have to build. The reading that is true is
the one above, about what instance search finds, and this is the one site of the fourteen taxis
#2133 enumerates where those two readings come apart. -/
instance standardEtalePairRingAlgebra : Algebra ℂ P.Ring :=
  inferInstanceAs (Algebra ℂ (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
    Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}))

/-- **The two actions on `StandardEtalePair.Ring` agree**, by `rfl` on the structure maps. -/
instance standardEtalePairRingIsScalarTower :
    IsScalarTower ℂ (PresentedAlgebra.{u} n k g) P.Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- **Mathlib's standard étale algebra is definitionally this quotient**, which is what lets the
isomorphism below land on a bare polynomial ring and never mention a localisation. It is the same
observation `StandardEtalePair.equivPolynomialQuotient` makes, and it is `rfl` there too. -/
theorem standardEtalePair_ring_eq :
    P.Ring =
      (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
        Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}) := rfl

/-- **The algebra `ComplexAnalytic.etalePresentation` presents is the standard étale algebra.**

The hypotheses say that `F` and `G` are polynomial lifts of `P.f` and `P.g`; see the module
docstring on why they are hypotheses rather than choices, and
`ComplexAnalytic.exists_presentation_standardEtale` for the form that quantifies them away.

The chain is: the ideal identity above, then `DoubleQuot.quotQuotEquivQuotSupₐ` to peel off the
two new relations, then `ComplexAnalytic.biPolyPresentedAlgebraEquiv` on what is left. The only
computation is where the two new relations go, and that is the two `simp` lemmas about
`biPolyPresentedAlgebraEquiv` plus the hypotheses. -/
def etalePresentedAlgebraEquiv
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ]
      (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
        Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}) :=
  (Ideal.quotientEquivAlgOfEq ℂ (presentationIdeal_etalePresentation.{u} g F G)).trans
    (((DoubleQuot.quotQuotEquivQuotSupₐ ℂ
        (presentationIdeal.{u} (polyPresentation.{u} (polyPresentation.{u} g))) _).symm).trans
      (Ideal.quotientEquivAlg _ _ (biPolyPresentedAlgebraEquiv.{u} g) (by
        have e1 : biPolyPresentedAlgebraEquiv.{u} g
            (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} (n + 1)) *
              MvPolynomial.rename (localisationIncl.{u} (n + 1)) G - 1)) =
            Polynomial.X * Polynomial.C P.g - 1 := by
          simp only [map_sub, map_one, map_mul]
          rw [biPolyPresentedAlgebraEquiv_mk_X_var.{u} g,
            biPolyPresentedAlgebraEquiv_mk_rename.{u} g G, hG]
        have e2 : biPolyPresentedAlgebraEquiv.{u} g
            (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)) =
            Polynomial.C P.f := by
          rw [biPolyPresentedAlgebraEquiv_mk_rename.{u} g F, hF]
        rw [Ideal.map_span, Set.image_pair, Ideal.map_span, Set.image_pair]
        simp only [RingHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
        rw [e1, e2, Set.pair_comm])))

/-- **The algebra `ComplexAnalytic.etalePresentation` presents is `StandardEtalePair.Ring`**,
spelled with Mathlib's name for it.

`ComplexAnalytic.etalePresentedAlgebraEquiv` with its target read through
`ComplexAnalytic.standardEtalePair_ring_eq`, so this carries **no** transport: it is the same term,
and the two types are the same type. The reason it is a separate declaration is that
`≃ₐ[ℂ] P.Ring` needs the `Algebra ℂ P.Ring` above to elaborate, while the spelled-out quotient is
what the proof of the equivalence has to see. -/
def etalePresentedAlgebraEquivRing
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ] P.Ring :=
  etalePresentedAlgebraEquiv.{u} g F G P hF hG

/-- **Every element of `A[X]` has a polynomial lift**, since
`ComplexAnalytic.polyPresentedAlgebraEquiv` is an equivalence and `Ideal.Quotient.mk` is
surjective. -/
theorem exists_lift_polyPresentedAlgebraEquiv (a : Polynomial (PresentedAlgebra.{u} n k g)) :
    ∃ F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ,
      polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = a := by
  obtain ⟨x, hx⟩ := (polyPresentedAlgebraEquiv.{u} g).surjective a
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨F, hx⟩

/-- **`pderiv` of a lift is a lift of the derivative.**

`ComplexAnalytic.exists_lift_polyPresentedAlgebraEquiv` produces the `F` that
`ComplexAnalytic.etalePresentation` cuts its hypersurface out with, as a *lift* of an element of
`A[X]` and not as the image of one along a named map ; so the statement that turns
`Polynomial.derivative` into `MvPolynomial.pderiv` has to be about lifts, and this is it: whatever
`F` lifts, `pderiv (localisationVar n) F` lifts its derivative.

**This is the bridge `Other/Oka/Analytification/StandardEtaleAnalytification.lean` was written naming
as missing**, and which a consumer of `StandardEtalePair.cond` needs: that field's equation
`derivative f * p₁ + f * p₂ = g ^ n` lives in `A[X]`, and applying this to a lift of each side
turns it into an equation in the presented algebra whose value at a point is the hypothesis of
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`. A caller who has
`hF : polyPresentedAlgebraEquiv g (Ideal.Quotient.mk _ F) = a` rewrites by this and then by `hF`;
no separate `_of_lift` form is stated because that is two rewrites and no content.

**No derivative descends to a quotient here and none needs to.** The statement quantifies over a
representative `F` rather than over a class, so nothing has to be shown well defined ;
`MvPolynomial.pderiv (localisationVar n)` does happen to map `presentationIdeal (polyPresentation
g)` into itself, since the relations are renamed from the old variables and Leibniz does the
rest, but that is a *consequence* and it is not used below and not stated.

**The proof does not open `ComplexAnalytic.polyPresentedAlgebraEquiv` up.** The obvious route is
to take its three steps in order ; `Ideal.quotientEquivAlg` computes on a representative,
`MvPolynomial.pderiv` moves through the reindexing, `MvPolynomial.optionEquivLeft` crosses to
`Polynomial.derivative`, `Polynomial.derivative_map` commutes the last quotient past it ; and it
works, in one `simp only`. It costs **two new lemmas** (the crossing is not in Mathlib at
`v4.32.0` for the `Option` splitting, only for `MvPolynomial.sumRingEquiv`) and it plants **three
auto-generated equation lemmas**, on `ComplexAnalytic.polyRenameEquiv`, `polyOptionEquiv` and
`polyCoeffEquiv`, because a `simp only` at a definition is what generates one.

**That parenthesis is measured by a scan of types rather than of names**, at the rev
`lake-manifest.json` resolves that version to, `81a5d257c8e410db227a6665ed08f64fea08e997`. Over
the environment of `import Mathlib` there, **43** non-internal declarations have a type mentioning
`MvPolynomial.pderiv` and **28** have one mentioning `MvPolynomial.optionEquivLeft` or
`MvPolynomial.optionEquivRight`, and **not one declaration is in both**; crossing
`Polynomial.derivative` with the same two equivalences returns **0** as well, so neither direction
of the `Option` crossing is stated there. **The positive control is the half the sentence already
named**: of the **21** whose type mentions `MvPolynomial.sumRingEquiv` or
`MvPolynomial.sumAlgEquiv`, **three** also mention `MvPolynomial.pderiv` ;
`MvPolynomial.pderiv_sumRingEquiv`, `MvPolynomial.pderiv_sumAlgEquiv` and the deprecated alias
`MvPolynomial.pderiv_sumToIter`. **A lemma commuting a derivative past one of these equivalences
has to mention both constants in its own type**, whatever it is called and whatever namespace is
open, so the two zeros decide the claim where a name-keyed `grep` would only narrow it.

**That parenthesis read *(the crossing is not in Mathlib for the `Option` splitting, only for
`MvPolynomial.sumRingEquiv`)* until 2026-09-21**, with no version beside it; `git show
c6bfc1f:Other/Oka/Analytification/StandardEtale.lean` carries it at `:477–478`, wrapped after *the*.
**The claim is unchanged and only its warrant is**, and it was the cheapest of the fourteen taxis
#2133 enumerates for the reason visible here: the positive control was already inside the sentence
when it was written, and only the run and the version were missing.

What is here instead is `MvPolynomial.induction_on` on `F`, which needs neither: the two
computation lemmas above ; `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` and
`polyPresentedAlgebraEquiv_mk_X_var` ; are exactly the two cases the multiplication step splits
into, by `ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl`. **The old variables
become constants and constants have zero derivative; the new variable becomes `Polynomial.X` and
`Derivation.leibniz` matches `Polynomial.derivative_mul` term for term.** One declaration, no
equation lemma anywhere, and the same `change`-rather-than-unfold discipline the two computation
lemmas themselves are proved with. -/
theorem polyPresentedAlgebraEquiv_mk_pderiv (F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    polyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.pderiv (localisationVar.{u} n) F)) =
      Polynomial.derivative (polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F)) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.pderiv_C, ← MvPolynomial.rename_C (localisationIncl.{u} n) a,
        polyPresentedAlgebraEquiv_mk_rename]
      simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, Polynomial.derivative_mul]
      rcases eq_localisationVar_or_exists_localisationIncl.{u} i with rfl | ⟨j, rfl⟩
      · rw [MvPolynomial.pderiv_X_self, polyPresentedAlgebraEquiv_mk_X_var]
        simp only [map_one, mul_one, Polynomial.derivative_X, hp]
        ring
      · rw [MvPolynomial.pderiv_X_of_ne (by
          simp only [ne_eq, localisationIncl, localisationVar, ULift.up.injEq]
          exact (Fin.castSucc_lt_last j.down).ne),
          ← MvPolynomial.rename_X (localisationIncl.{u} n) j,
          polyPresentedAlgebraEquiv_mk_rename]
        simp only [map_zero, mul_zero, add_zero, Polynomial.derivative_C, hp]
        ring


/-! ### `StandardEtalePair.cond` at a point -/

/-- **`StandardEtalePair.cond`, read on the polynomial lifts.**

The field is `∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n`, an equation in `A[X]`, and a
presentation cuts with polynomials ; so before anything can be evaluated at a point the equation
has to be moved down to `MvPolynomial (ULift (Fin (n + 1))) ℂ`, modulo the relations. That is what
this is: `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv` for the derivative, and
`ComplexAnalytic.exists_lift_polyPresentedAlgebraEquiv` for `p₁` and `p₂`.

**The conclusion is an existential because `p₁` and `p₂` are**, and for one more reason: the lifts
are chosen here rather than supplied, so no caller can be asked for them. `F` and `G` are not
chosen ; they are this file's hypotheses `hF` and `hG` throughout, for the reason the module
docstring gives.

**The `simp only` is not a `rw`, and the difference is not cosmetic.** Both
`Ideal.Quotient.mk` and `ComplexAnalytic.polyPresentedAlgebraEquiv` are ring maps, so a
`rw [map_mul]` fires on the inner one and leaves a goal
`polyPresentedAlgebraEquiv g (mk (pderiv _ F) * mk P₁ + …)` that the bridge above does not match.
The `simp only` distributes both layers first, and then the bridge and the four hypotheses close
it against `StandardEtalePair.cond`'s own equation. -/
theorem exists_mk_pderiv_mul_add_eq_mk_pow
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    ∃ (P₁ P₂ : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) (m : ℕ),
      Ideal.Quotient.mk (presentationIdeal.{u} (polyPresentation.{u} g))
          (MvPolynomial.pderiv (localisationVar.{u} n) F * P₁ + F * P₂) =
        Ideal.Quotient.mk _ (G ^ m) := by
  obtain ⟨p₁, p₂, m, e⟩ := P.cond
  obtain ⟨P₁, hP₁⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g p₁
  obtain ⟨P₂, hP₂⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g p₂
  refine ⟨P₁, P₂, m, (polyPresentedAlgebraEquiv.{u} g).injective ?_⟩
  simp only [map_add, map_mul, map_pow, polyPresentedAlgebraEquiv_mk_pderiv, hF, hG, hP₁, hP₂]
  exact e

/-- **The derivative does not vanish at a point of the hypersurface off `D(G)`'s complement**:
where the relations of `g` and `F` all vanish and `G` does not,
`MvPolynomial.pderiv (localisationVar n) F` does not vanish either.

This is the step `Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean` and
`Other/Oka/Analytification/StandardEtaleAnalytification.lean` were both written naming as absent, and
the index it concludes about is the one
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv` asks for:
`ComplexAnalytic.localisationVar n` is `ULift.up (Fin.last n)` by definition, so nothing has to be
relabelled between the two.

**There is no analysis in it and no geometry either.** The equation above holds modulo
`presentationIdeal (polyPresentation g)`, `hx` says evaluation at `x` kills that ideal, so the
equation holds at `x` as complex numbers; `hFx` deletes the second summand and the right-hand side
is a power of a non-zero number. **`hGx` is not removable**: at a point of the same hypersurface
where `G` does vanish the derivative may vanish too, which is exactly the locus a standard étale
algebra inverts away.

Mathlib proves the same divisibility one level up, as
`StandardEtalePair.HasMap.isUnit_derivative_f`, for a point of any `R`-algebra. It is not quoted
here: `ℂ` is not an algebra over `ComplexAnalytic.PresentedAlgebra n k g`, so using it would mean
building one with `RingHom.toAlgebra` at each point and then proving the resulting `aeval` is the
composite above ; the same bookkeeping, with a local instance added to it. What gets repeated by
not quoting it is two lines. -/
theorem eval_pderiv_ne_zero
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g)
    (x : ULift.{u} (Fin (n + 1)) → ℂ)
    (hx : ∀ j, MvPolynomial.eval x (polyPresentation.{u} g j) = 0)
    (hFx : MvPolynomial.eval x F = 0) (hGx : MvPolynomial.eval x G ≠ 0) :
    MvPolynomial.eval x (MvPolynomial.pderiv (localisationVar.{u} n) F) ≠ 0 := by
  obtain ⟨P₁, P₂, m, hm⟩ := exists_mk_pderiv_mul_add_eq_mk_pow.{u} g F G P hF hG
  have hker : presentationIdeal.{u} (polyPresentation.{u} g) ≤
      RingHom.ker (MvPolynomial.eval x) :=
    Ideal.span_le.2 (Set.range_subset_iff.2 fun j ↦ RingHom.mem_ker.2 (hx j))
  have hsub := RingHom.mem_ker.1 (hker (Ideal.Quotient.eq.1 hm))
  rw [map_sub, sub_eq_zero] at hsub
  intro h
  rw [map_add, map_mul, map_mul, map_pow, h, hFx, zero_mul, zero_mul, add_zero] at hsub
  exact pow_ne_zero m hGx hsub.symm

/-- **A standard étale algebra over a presented `ℂ`-algebra is presented**, on two more variables
and two more relations.

This is `ComplexAnalytic.etalePresentedAlgebraEquiv` with the lifts quantified away. A caller who
has the lifts should use that one: it is the same statement with the isomorphism in hand rather
than under an existential. -/
theorem exists_presentation_standardEtale :
    ∃ F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ,
      Nonempty (PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ]
        P.Ring) := by
  obtain ⟨F, hF⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.f
  obtain ⟨G, hG⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.g
  exact ⟨F, G, ⟨etalePresentedAlgebraEquivRing.{u} g F G P hF hG⟩⟩

/-- **The structure map `A ⟶ A_ét`, as a morphism of presentations.**

Mind the direction, which is the one `ComplexAnalytic.PresHom` runs in: a
`ComplexAnalytic.PresHom (etalePresentation g F G) g` has ring map `A → A_ét` and induces a
morphism of analytic spaces the other way, which is the projection of the étale cover to its base.

It is `ComplexAnalytic.PresHom.ofRename` at the inclusion of the old variables, so it costs no
commutative algebra: the old relations are literally among the new ones. -/
def etalePresHom : PresHom.{u} (etalePresentation.{u} g F G) g :=
  PresHom.ofRename (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (by
    intro j
    have hj : MvPolynomial.rename
        (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (g j) =
        polyPresentation.{u} (polyPresentation.{u} g) j := by
      simp [polyPresentation, MvPolynomial.rename_rename]
    rw [hj, presentationIdeal_etalePresentation.{u} g F G]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))

end

end ComplexAnalytic

end
