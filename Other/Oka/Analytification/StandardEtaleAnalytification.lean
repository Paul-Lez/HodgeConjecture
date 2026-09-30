/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.StandardEtale

/-!
# The analytification of a standard étale presentation is a distinguished open of a hypersurface

`ComplexAnalytic.etalePresentation` carries **two** extra variables over the base presentation `g`:
one adjoined root of `F`, and one `Y` inverting `G`. Mathlib's
`StandardEtalePair.equivAwayAdjoinRoot` says the `Y` is bookkeeping ; `P.Ring` is `(A[X]/f)[1/g]`
; but the presentation does not say so, and every statement anyone wants to quote about the
hypersurface is stated for the **one**-variable presentation `ComplexAnalytic.polyPresentation g`
with `F` appended. This file says the two agree after analytification: the `n + 2`-variable
presentation analytifies to the distinguished open `D(G)` inside the `n + 1`-variable one's
analytification, **over the base**.

## The route, and why it is not a computation

`ComplexAnalytic.etalePresentation` adjoins `X`, inverts `G`, then imposes `F`;
`ComplexAnalytic.localisationIso` wants impose `F`, then invert `G`. Those are different tuples
generating **the same ideal**, and `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` is
exactly the bridge ; `ComplexAnalytic.localisationPresentation`'s own docstring says so. So the
whole content of `ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation` is that the
two `Fin.snoc`s unfold to the same three spans in a different association, and the lattice step is
`a ⊔ (b ⊔ c) = a ⊔ c ⊔ b`.

## Over the base, which is the half worth having

A bare `≅` between two analytifications is worth much less than it looks:
`Other/Oka/Analytification/DistinguishedOpen.lean` says why in terms ; *"without that the statement
would only compare two spaces that happen to be isomorphic, and would say nothing about the
immersion"*. So the file does not stop at the isomorphism.
`ComplexAnalytic.etaleAnalytificationIso_hom_comp` says that the isomorphism, followed by the
inclusion of `D(G)` and then by the hypersurface's own projection to `A^an`, **is** the projection
of the étale cover ; `ComplexAnalytic.analytificationMap` of `ComplexAnalytic.etalePresHom`. Mind
the direction: a `ComplexAnalytic.PresHom (etalePresentation g F G) g` has ring map `A → A_ét` and
induces the morphism of analytic spaces the other way.

The proof is `ComplexAnalytic.hom_ext_analytification` and four coordinate computations, none of
which is about the étale hypothesis: `ComplexAnalytic.transported` of a
`ComplexAnalytic.PresHom.ofRename` is a coordinate, the projection carries coordinates to
coordinates, and so does the comparison. **Nothing here reads `StandardEtalePair.cond`, `F` or `G`
beyond their names**, which is why the statement holds for every `F` and `G` and not only for a
standard étale pair.

## Main definitions

- `ComplexAnalytic.hypersurfacePresentation`: `Fin.snoc (polyPresentation g) F`, the `n + 1`
  variable presentation of `A[X] ⧸ (F)` ; the object every statement about the hypersurface is
  stated for, given a name here because it appears four times in the comparison below.
- `ComplexAnalytic.hypersurfacePresHom`: its structure map `A ⟶ A[X] ⧸ (F)`, as a
  `ComplexAnalytic.PresHom`, by `ComplexAnalytic.PresHom.ofRename` at the inclusion of the old
  variables.
- `ComplexAnalytic.etaleAnalytificationIso`: the isomorphism of the title.

## Main results

- `ComplexAnalytic.hypersurfacePresentation_empty`: **over an empty base presentation the
  hypersurface presentation is `![F]`**, the spelling every statement about a hypersurface of
  `ℂ^(n+1)` is written in. Not `rfl`.
- `ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation`: **the étale presentation
  and the localisation of the hypersurface presentation span the same ideal.**
- `ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict`: the isomorphism followed by the open
  immersion is the localisation projection, composed with the comparison.
- `ComplexAnalytic.etaleAnalytificationIso_hom_comp`: **the isomorphism is one over `A^an`** ; the
  composite down to the base is the projection of the étale cover.
- `ComplexAnalytic.eval_pderiv_ne_zero_of_mem`: **the derivative does not vanish at a point of the
  hypersurface off the zero locus of `G`** ; `StandardEtalePair.cond`, read at a point of the
  analytification of the hypersurface presentation named above.
- `ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply`: **the projection to the base
  forgets the last two coordinates**, coordinate by coordinate ; the only description of that
  morphism on points, and what a statement about its *image* has to be fed.

## What is not here

* **The simple-zero lemma is not here, and until `ComplexAnalytic.eval_pderiv_ne_zero_of_mem`
  below nothing in this development read `StandardEtalePair.cond` at all.** The step a
  local-isomorphism statement needs is that at a point where `F` vanishes and `G` does not, the
  germ of `F` has `PowerSeries.order (MvPowerSeries.partialEval (Fin.last n) …) = 1` ; the
  hypothesis `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` takes. **What is missing is the
  derivative and not the order**: `LocalOkaRing.order_partialEval_eq_natDegree`
  (`Other/Oka/Regular.lean`) reads the order off a **Weierstrass degree**. **`Other/Oka/` still has no
  partial-derivative operator at all**, and that much of what stood here is true ; but the
  conclusion drawn from it, that the hypothesis cannot be reached by anything on hand, does not
  follow and is no longer the case. `MvPowerSeries.order_partialEval_eq_one_iff`
  (`Other/Oka/LocalOkaRing.lean`) says the order condition **is** two coefficient conditions, and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` takes them directly ; and asks for only
  one of the two, since `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` makes the vanishing half
  free: what is left is that the coefficient of the last variable in the Taylor expansion of `F`
  at the point is nonzero. **It needs no derivative operator to state or to supply**, and for a
  cutting section that comes from a polynomial it is now a derivative outright:
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`
  (`Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean`) asks that `MvPolynomial.pderiv` of that
  polynomial in the last variable be nonzero at the point, which `F` above is and which is the
  shape a presentation supplies. **The bridge between the two derivative notions now exists** and is
  `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv` (`Other/Oka/Analytification/StandardEtale.lean`):
  `MvPolynomial.pderiv` of a lift is a lift of the `Polynomial.derivative`, which is the form the
  question takes here because `ComplexAnalytic.exists_lift_polyPresentedAlgebraEquiv` produces
  `F` as a lift and not as the image of anything. So `StandardEtalePair.cond`'s equation
  `derivative f * p₁ + f * p₂ = g ^ n` in `R[X]`, one variable over
  `R = MvPolynomial (ULift (Fin n)) ℂ`, can be read as an equation about
  `MvPolynomial.pderiv (localisationVar n) F`.

  **One step of that chain is here now and one is not, and neither is the identification.** The
  first ; turning the `∃ p₁ p₂ n` behind `cond` into a *non-vanishing* derivative at a point ; is
  `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` below, on top of
  `ComplexAnalytic.eval_pderiv_ne_zero` (`Other/Oka/Analytification/StandardEtale.lean`): an evaluation
  argument at a point where `F` vanishes and `G` does not, with no analysis and no geometry in
  it. **The second has been priced and is half-answered, and the half that is left is not the one
  this bullet used to name.** The theorem above is about the hypersurface in `ℂ^(n+1)` and the
  étale presentation is that hypersurface met with `D(G)` in `ℂ^(n+2)`. Restating the transport at
  the derivative hypothesis ; the part that was unmeasured ; is
  `Other/Oka/AnalyticSpace/OpenBaseProjectionPolynomial.lean` and it is two rewrites, because the
  restriction is absorbed once in the coefficient form
  `ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_coeff`. **What that does not do is
  reach `D(G)`**, and the reason is a difference of shape rather than of cost:
  `ComplexAnalytic.cylinder` is a preimage from the base, a cylinder `V × ℂ`, while `G` involves
  the fibre variable ; `Y·G − 1` is a relation of `ComplexAnalytic.etalePresentation` ; so
  `{G ≠ 0}` cuts the *source*. A cylinder it is only when `G` does not involve the last variable.
  **Nothing below produces a `V` from a `G`**, and that is still true. **What is no longer true
  is that nothing transports the stalk half across a restriction of the source**, and the reason
  it was recorded as an absence at all is worth stating, because it was never the hard half: the
  four stalk theorems are quantified *one point at a time*, so they apply at a point of an open
  subspace with the hypothesis asked only there, and the open immersion contributes an
  isomorphism on stalks by `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`. That
  composition is inside
  `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
  (`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`) and is three lines of it. The half that did cost
  something is the topological one; see the `IsLocalIso` bullet below. A third absence
  was not named here before, is not the same one, and **was misdiagnosed when it was**: it read
  that all four stalk theorems take an `ComplexAnalytic.IsCutOutBy` datum for **one** cutting
  section while `ComplexAnalytic.hypersurfacePresentation` has `k + 1` relations, and that
  *"That one is untouched and no declaration below attempts it."* **The count is right and the
  reading of it was wrong.** Those theorems conclude about the projection to `ℂ^n`, and for
  `k ≥ 1` that conclusion fails ; **whenever the base's analytification `X^an` is a proper closed
  subset of `ℂ^n`** ; unless the hypersurface's analytification is empty. **This sentence gave the
  reason as a hypersurface over a proper closed `X^an ⊆ ℂ^n` having *"its image inside `X^an`"*,
  and that reason is a step short**: a local isomorphism need not be surjective ;
  `Other/Oka/Analytification/StandardEtaleLocalIso.lean`'s `## What is not here` says so of the one
  built there ; so containment in a proper closed subset does not by itself contradict it. The
  step is that the image is **open**: a local isomorphism is a local homeomorphism, which is the
  field `ComplexAnalytic.AnalyticSpace.IsLocalIso.isLocalHomeomorph`, and so an open map; a proper
  closed `X^an ⊆ ℂ^n` has empty interior, since `X^an` is the zero locus of the relations of `g`
  and a polynomial vanishing on a non-empty open subset of `ℂ^n` is zero; and an open subset of a
  set with empty interior is empty. *Unless empty* rather than a bare *false* because both fields
  of `ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the points of the source, so an
  empty analytification satisfies them vacuously and is not a counterexample. ***Proper* is a
  hypothesis and not a consequence of `k ≥ 1`**, which is why the clause above carries it: this
  file's `variable` line asks nothing of `g`, and at `g = 0` the relations cut out nothing, so
  `X^an` is the whole of `ℂ^n`, its interior is everything, and the argument has no step left.
  That configuration is degenerate and nothing on this line calls it, but the clause is a claim
  about **every** `g` at `k ≥ 1`. So `k + 1` against one is not a datum nobody has built; it is
  the signature of a statement whose base is the whole of `ℂ^n`. **This argument is written out
  twice, as two copies and not as one citation**: the other copy is
  `Other/Oka/Analytification/StandardEtaleLocalIso.lean`'s section on why the base is `ℂ^n`, each names
  the other, and a repair to one is not made without the other. At `k = 0` the datum is one
  rewrite ; `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
  (`Other/Oka/Analytification/StandardEtaleLocalIso.lean`) ; and it is built there. **What is untouched
  at `k ≥ 1` is the projection statement, and it is false rather than missing**; the statement
  about the structure map to `X^an` alone is a different theorem, is
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
  (`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`), and takes no implicit function theorem
  **relative to `X^an`** ; only the one relative to `ℂ^n` that the `k = 0` line already spends.

  **Since 2026-09-02 the falsity is compiled and this paragraph is no longer the only record of
  it**: `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleNotLocalIso.lean`), with *proper* restated as
  `∃ j, g j ≠ 0` and *unless empty* as a `Nonempty` on the source. **The argument above stays
  here in full**, and so does the copy this paragraph names, because the two copies are two
  copies by the decision recorded three sentences up and a citation is not what either of them is
  for. What the theorem replaces is one step and not the argument: instead of the interior of
  `X^an` it applies `MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen`
  (`Other/Oka/Algebra/MvPolynomial/Funext.lean`) to the open image directly. **The sentence in this
  paragraph that is still only prose is *"a proper closed `X^an ⊆ ℂ^n` has empty interior"***,
  which nothing states and which that theorem does not need.
* **No witness in this file that the open is ever non-empty.** The statements below are
  hypothesis-free in `F` and `G`, so none of them can be vacuously satisfied ; but that says
  nothing about whether the *objects* are degenerate, and for `F = 1` or `G = 0` both sides of
  `ComplexAnalytic.etaleAnalytificationIso` really are empty.
* **No `IsLocalIso` and no `IsFiniteEtale` *below*, and the reason has changed twice.** The
  restriction of the source is no longer an absence.
  `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
  (`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`) makes an **open subspace** of a polynomial
  hypersurface in `ℂ^(n+1)` project as a local isomorphism, asking the derivative hypothesis only
  at the points of that subspace ; which is the shape
  `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces, since it needs `G` not to vanish and so
  says nothing off `D(G)`.

  **The two halves turned out to cost very different amounts, and the earlier form of this bullet
  said they cost the same.** The stalk half is pointwise and transports by composition; the
  topological one does not, because a local homeomorphism is a condition on a whole space and the
  unrestricted statement's hypothesis is exactly what a restricted source fails to supply. What
  the topological half needed is the implicit function theorem on a *relatively open piece* of a
  level set, `isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter`
  (`Other/Oka/Analysis/Calculus/Implicit.lean`). **That statement is not new mathematics and an earlier
  form of this sentence said it was**: it is a twenty-line corollary of the unrestricted level-set
  theorem, because the `f` there carries no hypothesis off its own level set and so can be
  replaced by one whose level set is already cut down. What does not transport that way is the
  statement one level up, where the cutting section is holomorphic; the docstrings of
  `ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff` and of the
  mirror-tree theorem say which freedom is being spent and where it runs out. **So nothing in
  this transport was out of reach of what the tree already had**: six statements, each proved
  from one that was already there. That is a smaller claim than the one it replaces, and it is
  checkable from the files rather than from a delivery note: the unrestricted level-set theorem
  still
  carries its own fifty-line proof and the restricted one is proved *from* it, so there is no
  direction in which the dependency could be read the other way.

  `Other/Oka/AnalyticSpace/OpenBaseProjection.lean` ; which restricts the **base** and pulls back ; is
  still not a missing counterpart but a statement about a different restriction, and `D(G)` is
  still not a cylinder.

  **What this does not do is put the standard étale morphism itself into that shape, and that
  is now done elsewhere and only over `ℂ^n`.** This paragraph used to end by saying that reaching
  `isLocalIso_ofRestrict_comp_proj_of_pderiv` from `ComplexAnalytic.etaleAnalytificationIso`
  *"needs a `ComplexAnalytic.IsCutOutBy` datum for the `k + 1` relations of
  `ComplexAnalytic.hypersurfacePresentation` against the one cutting section the theorem takes,
  and nothing here supplies it."* The bullet above says why that is a misdiagnosis rather than a
  gap. `Other/Oka/Analytification/StandardEtaleLocalIso.lean` closes the `k = 0` case end to end ;
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` ; and takes
  `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` below as its derivative input. Nothing here
  changes, and nothing below is stated at `k ≥ 1`.
* **No finiteness.** `IsFiniteEtale` of the unrestricted morphism is **false**: a standard étale
  algebra inverts `g`, and `Spec` of `(ℂ[X][x] ⧸ (x² - X))[1/x]` over `ℂ` has the punctured line
  for image, which is not closed. `Other/Oka/Analytification/MonicHypersurface.lean`'s `## What is not
  here` carries that argument. **The finiteness that *is* true ; over an open subset of the base
  on which the inversion is vacuous ; is now built, and this paragraph said it was "a
  construction and is not here" when only the second half was right.** It is
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleFiniteness.lean`), at `k = 0`, and
  `ComplexAnalytic.etaleAnalytificationIso_hom_comp` below is what it spends: the étale
  analytification is `D(G)` inside the hypersurface **over the base**, and over a `V` avoiding
  `ComplexAnalytic.hypersurfaceCommonZeroImage` the part of the hypersurface lying over `V` is
  already inside `D(G)`. Nothing here changes and nothing here is stated at `k ≥ 1`.
* **No comparison with `StandardEtalePair.Ring`.** `ComplexAnalytic.etalePresentedAlgebraEquivRing`
  relates the presented algebra to Mathlib's, and the lifts `hF`, `hG` it needs are hypotheses;
  nothing below takes them, because nothing below needs `F` and `G` to come from a pair.
-/

@[expose] public section

open MvPolynomial CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The hypersurface presentation -/

/-- **The relations of `g` in one more variable, with `F` appended**: the `n + 1`-variable
presentation of `A[X] ⧸ (F)`.

**It is not `ComplexAnalytic.etalePresentation` with a variable dropped**, and the difference is
what the comparison below is a theorem about. Unfolded, `etalePresentation g F G` lists the old
relations, then `X · G - 1`, then `F`; localising *this* tuple at `G` lists the old relations,
then `F`, then `X · G - 1`. **The same three blocks with the last two swapped** ; which is why
that comparison is a statement about ideals and not a `rfl`, and why its proof is a `Fin.snoc`
reassociation. (The two are not even over the same number of variables until the localisation is
taken: `etalePresentation`'s own `Fin.snoc`-init is over `n + 2` and this is over `n + 1`.)

**Nothing in the repository is stated for this tuple yet**, which is an argument for naming it
rather than against: `ComplexAnalytic.isFinite_comp_proj_of_monic` and
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj` both take an arbitrary morphism carrying an
`ComplexAnalytic.IsCutOutBy` datum, not a presentation, so a statement about the hypersurface *of
a presented algebra* has nothing to quote. The nearest thing in the tree is
`ComplexAnalytic.localisationPresentation_eq_snoc`, which is `rfl` and is this shape at the one
`F` of the form `X · f - 1`. Named rather than written out because it occurs four times in the
comparison below. -/
def hypersurfacePresentation : Fin (k + 1) → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  Fin.snoc (polyPresentation.{u} g) F

/-- The ideal of `ComplexAnalytic.hypersurfacePresentation`, split as the old relations and `F`. -/
theorem presentationIdeal_hypersurfacePresentation :
    presentationIdeal.{u} (hypersurfacePresentation.{u} g F) =
      presentationIdeal.{u} (polyPresentation.{u} g) ⊔ Ideal.span {F} :=
  presentationIdeal_snoc.{u} _ _

/-- **Over an empty base presentation the hypersurface presentation is the one-element family
`![F]`**, which is the spelling every statement about a hypersurface of `ℂ^(n+1)` is written in.

`Fin.snoc` of an empty family is that family's single entry, and `Fin.lastCases` is the whole
proof: the `castSucc` branch is indexed by `Fin 0` and is discharged by `Fin.elim0`.

**It is not `rfl`**, measured ; `rfl` at this goal reports *"Type mismatch: rfl has type `?m = ?m`
but is expected to have type `hypersurfacePresentation Fin.elim0 F = ![F]`"* ; which is why the
bridge exists at all rather than being left to unification.

**Stated at an arbitrary `g : Fin 0 → …` and not at `Fin.elim0`**, because nothing in the proof
reads `g`: `Fin.lastCases` never reaches it. So a caller holding a `variable (g : Fin 0 → …)`,
which is how `Other/Oka/Analytification/StandardEtaleLocalIso.lean` and
`Other/Oka/Analytification/StandardEtaleFiniteness.lean` are both written, spends it with no
`Subsingleton` step.

**Here rather than in either consumer, and the cost was measured rather than assumed**: **three**
modules under `Other/Oka/` imported this file when the placement was decided and **four** do after the
consumer below was added ; the figure that priced the decision is the first, and the second is
what a reader recomputing it on the merged tree will get. Either is against the whole of
`Other/Oka/Analytification/`, which is what the two files that would each carry a copy cost.

**The precedent points the other way** ;
`ComplexAnalytic.section_hypersurfacePresentation_empty` is a `k = 0` fact about this definition
living in its consumer ; and it is a weaker precedent than it looks, since that statement is about
`OkaRing.ofMvPolynomial` and belongs to the cut-out datum it feeds, while this one mentions
nothing but the definition. -/
theorem hypersurfacePresentation_empty (g₀ : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    hypersurfacePresentation.{u} g₀ F = ![F] := by
  funext j
  refine Fin.lastCases ?_ (fun i ↦ i.elim0) j
  exact Fin.snoc_last _ _

/-- **The structure map `A ⟶ A[X] ⧸ (F)`, as a morphism of presentations.**

The same shape as `ComplexAnalytic.etalePresHom` one variable down, and for the same reason: the
old relations are literally among the new ones, so `ComplexAnalytic.PresHom.ofRename` at the
inclusion of the old variables costs no commutative algebra. -/
def hypersurfacePresHom : PresHom.{u} (hypersurfacePresentation.{u} g F) g :=
  PresHom.ofRename (localisationIncl.{u} n) (by
    intro j
    rw [presentationIdeal_hypersurfacePresentation.{u} g F]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))

/-- The tuple `ComplexAnalytic.hypersurfacePresHom` names is the coordinates of the hypersurface
on the old variables ; `ComplexAnalytic.PresHom.ofRename` renames a variable to a variable, and
`ComplexAnalytic.quotientToGlobal_mk_X` reads the class of a variable as a coordinate. -/
theorem transported_hypersurfacePresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (hypersurfacePresHom.{u} g F) i =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n i) := by
  rw [transported]
  change quotientToGlobal.{u} _ (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n)
    (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact quotientToGlobal_mk_X.{u} _ _

/-- The same for `ComplexAnalytic.etalePresHom`, whose rename is the two inclusions composed. -/
theorem transported_etalePresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (etalePresHom.{u} g F G) i =
      analytificationCoord.{u} (etalePresentation.{u} g F G)
        (localisationIncl.{u} (n + 1) (localisationIncl.{u} n i)) := by
  rw [transported]
  change quotientToGlobal.{u} _ (Ideal.Quotient.mk _ (MvPolynomial.rename
    (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact quotientToGlobal_mk_X.{u} _ _

/-! ### The comparison -/

/-- **The `Y` variable is bookkeeping, at the level of ideals**: adjoining a root of `F` and then
inverting `G` spans what inverting `G` and then imposing `F` does.

Both sides unfold to the relations of `g` in two more variables, together with `Y·G - 1` and `F`;
the two `Fin.snoc`s associate them differently and nothing else happens. The lattice step is
`a ⊔ (b ⊔ c) = a ⊔ c ⊔ b`, closed by `← sup_assoc, sup_right_comm`. -/
theorem presentationIdeal_etalePresentation_eq_localisation :
    presentationIdeal.{u} (etalePresentation.{u} g F G) =
      presentationIdeal.{u}
        (localisationPresentation.{u} (hypersurfacePresentation.{u} g F) G) := by
  rw [presentationIdeal_etalePresentation, localisationPresentation, presentationIdeal_snoc]
  have h : (fun j : Fin (k + 1) ↦ MvPolynomial.rename (localisationIncl.{u} (n + 1))
      ((hypersurfacePresentation.{u} g F : Fin (k + 1) →
        MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) j)) =
      Fin.snoc (polyPresentation.{u} (polyPresentation.{u} g))
        (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F) := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [hypersurfacePresentation, Fin.snoc_last]
    · simp [hypersurfacePresentation, Fin.snoc_castSucc, polyPresentation]
  rw [h, presentationIdeal_snoc, Ideal.span_insert, ← sup_assoc, sup_right_comm]

/-- **The analytification of the standard étale presentation is `D(G)` inside the analytification
of the hypersurface presentation.**

`ComplexAnalytic.analytificationIsoOfPresentationIdealEq` on the ideal identity above, then
`ComplexAnalytic.localisationIso`. Neither factor knows anything about `F` and `G` beyond their
being polynomials. -/
def etaleAnalytificationIso :
    AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G) ≅
      (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).restrict
        (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) :=
  (analytificationIsoOfPresentationIdealEq.{u}
      (presentationIdeal_etalePresentation_eq_localisation.{u} g F G)).trans
    (localisationIso.{u} (hypersurfacePresentation.{u} g F) G)

/-- **The isomorphism followed by the open immersion is the localisation projection**, composed
with the comparison of the two presentations.

This is `ComplexAnalytic.localisationIso_hom_ofRestrict` for the second factor and nothing for the
first, and it is what makes the statement below a computation about coordinates rather than about
an opaque isomorphism. -/
theorem etaleAnalytificationIso_hom_ofRestrict :
    (etaleAnalytificationIso.{u} g F G).hom ≫
        (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) =
      analytificationCompare.{u}
          (presentationIdeal_etalePresentation_eq_localisation.{u} g F G).ge ≫
        localisationProj.{u} (hypersurfacePresentation.{u} g F) G := by
  rw [etaleAnalytificationIso, Iso.trans_hom, Category.assoc, localisationIso_hom_ofRestrict]
  rfl

/-- **The isomorphism is one over `A^an`**: followed by the inclusion of `D(G)` and then by the
hypersurface's projection to the base, it is the projection of the étale cover.

This is the half without which the isomorphism above says only that two spaces happen to be
isomorphic. The proof is `ComplexAnalytic.hom_ext_analytification` and then four coordinate
computations that meet in the middle: both sides send the `i`-th coordinate of `A^an` to the
`i`-th coordinate of the étale analytification, read through the two variable inclusions. -/
theorem etaleAnalytificationIso_hom_comp :
    (etaleAnalytificationIso.{u} g F G).hom ≫
        (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationMap.{u} (hypersurfacePresHom.{u} g F) =
      analytificationMap.{u} (etalePresHom.{u} g F G) := by
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [coordPullback_analytificationMap_comp, transported_etalePresHom]
  rw [← Category.assoc, etaleAnalytificationIso_hom_ofRestrict, Category.assoc, Category.assoc,
    AnalyticSpace.coordPullback_comp, AnalyticSpace.coordPullback_comp,
    coordPullback_analytificationMap_comp, transported_hypersurfacePresHom]
  refine Eq.trans (congrArg (CommRingCat.Hom.hom (AlgebraicGeometry.LocallyRingedSpace.Γ.map
      (analytificationCompare.{u}
        (presentationIdeal_etalePresentation_eq_localisation.{u} g F G).ge).toLRSHom.op))
      (pullbackΓ_localisationProj_analytificationCoord.{u}
        (hypersurfacePresentation.{u} g F) G (localisationIncl.{u} n i))) ?_
  exact (AnalyticSpace.coordPullback_comp _ _ _).symm.trans
    (coordPullback_analytificationCompare_comp _ _)

/-! ### `StandardEtalePair.cond` at a point of the hypersurface -/

/-- **The two vanishing hypotheses of `ComplexAnalytic.eval_pderiv_ne_zero` are one hypothesis for
a caller: that the point lies on the hypersurface.**

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`, so a point of
its analytification satisfies the relations of `g` read upstairs *and* `F = 0` ; which is exactly
`hx` and `hFx` there. `ComplexAnalytic.eval_eq_zero_of_mem` at `Fin.castSucc j` gives the first
and at `Fin.last k` the second, and the two `Fin.snoc` computations are the whole proof.

**This is the form a consumer holds**, because the hypersurface's analytification is the space
`ComplexAnalytic.etaleAnalytificationIso` compares the étale one to, and `G` is the polynomial
whose distinguished open that isomorphism lands in. **This sentence then said that *"what is
still missing above this is the restriction to `D(G)` and the cut-out datum"*, and neither half is
missing any longer.** The restriction is
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
(`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`), which asks the derivative hypothesis only at the
points of the open subspace ; the shape this theorem produces, since it needs `G` not to vanish
and so says nothing off `D(G)`. The datum at `k = 0` is
`ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
(`Other/Oka/Analytification/StandardEtaleLocalIso.lean`), and that file joins the two end to end:
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` takes this theorem as its
derivative input.

**What stays true is the file-scoped half, and it is why the cross-reference is worth rewriting
rather than deleting**: neither the restriction nor the datum is supplied *here*, and this file's
`## What is not here` is where both were retired ; the first at the `IsLocalIso` bullet, the
second where the `k + 1`-against-one count is read as the signature of a statement over `ℂ^n`
rather than as a datum nobody has built. Untouched at `k ≥ 1` is a *statement* and not this
datum: over a general base it is a different theorem, and the one about the structure map to
`X^an` alone is `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`), which needs no implicit function theorem
relative to `X^an`; the projection one remains false.

The `show … from` is not decoration: `rw [hypersurfacePresentation, Fin.snoc_castSucc]` fails with
*"Failed to rewrite using equation theorems for `hypersurfacePresentation`"*, and naming the
instance of `Fin.snoc_castSucc` is also what keeps an equation lemma for that definition out of
the environment. -/
theorem eval_pderiv_ne_zero_of_mem
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g)
    (y : AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F))
    (hGy : MvPolynomial.eval (y.1.1 : ULift.{u} (Fin (n + 1)) → ℂ) G ≠ 0) :
    MvPolynomial.eval (y.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
      (MvPolynomial.pderiv (localisationVar.{u} n) F) ≠ 0 := by
  refine eval_pderiv_ne_zero.{u} g F G P hF hG _ (fun j ↦ ?_) ?_ hGy
  · have hj := eval_eq_zero_of_mem.{u} (hypersurfacePresentation.{u} g F) y j.castSucc
    rwa [show hypersurfacePresentation.{u} g F j.castSucc = polyPresentation.{u} g j from
      Fin.snoc_castSucc _ _ _] at hj
  · have hl := eval_eq_zero_of_mem.{u} (hypersurfacePresentation.{u} g F) y (Fin.last k)
    rwa [show hypersurfacePresentation.{u} g F (Fin.last k) = F from Fin.snoc_last _ _] at hl

/-! ### The base map of the projection, on points -/

/-- **The projection of the standard étale analytification to the base forgets the last two
coordinates.**

`ComplexAnalytic.etalePresentation` adjoins two variables ; the root of `F` and the inverse of
`G` ; so a point of its analytification is a tuple in `ℂ^(n+2)`, and this says the morphism
`ComplexAnalytic.analytificationMap (etalePresHom g F G) ≫ analytificationInclHom g` sends it to
its first `n` entries. Stated coordinate by coordinate because that is how a caller reads a point
of `ℂ^n`: `ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` is the only description of
the base map of a morphism into `ℂ^n` this repository has, and it is coordinatewise.

**Nothing in it is about `F` and `G`, and it takes no hypothesis on either.** The three steps are
`ComplexAnalytic.coordPullback_analytificationMap_comp`, which names the pullback of the `i`-th
coordinate as `ComplexAnalytic.transported`; the observation that
`ComplexAnalytic.etalePresHom` is `ComplexAnalytic.PresHom.ofRename` at the inclusion of the old
variables, so that transported class is the class of a **variable**; and
`ComplexAnalytic.eval_polyToGlobal`, which evaluates a polynomial's global section at a point as
the polynomial at the tuple. The relations play no part, which is why this is stated here rather
than beside a statement that uses them.

**Why a caller wants it.** A morphism produced by `ComplexAnalytic.analytificationMap` is opaque
on points, so a statement about the *image* ; that it misses a point, or that it is not closed ;
has no route to the definitions without this. It is what
`ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective`
(`Other/Oka/AnalyticSpace/LocalIso.lean`) has to be fed. -/
theorem base_analytificationMap_etalePresHom_comp_apply
    (y : AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G))
    (i : ULift.{u} (Fin n)) :
    (((analytificationMap.{u} (etalePresHom.{u} g F G) ≫
        analytificationInclHom.{u} g).toLRSHom.base y : AnalyticSpace.complexAffineSpace.{u} n) :
      ULift.{u} (Fin n) → ℂ) i =
      (y.1.1 : ULift.{u} (Fin (n + 2)) → ℂ)
        (localisationIncl.{u} (n + 1) (localisationIncl.{u} n i)) := by
  rw [AnalyticSpace.base_eq_eval_coordPullback, coordPullback_analytificationMap_comp]
  change (AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G)).eval (U := ⊤) y trivial
    (quotientToGlobal.{u} _ ((etalePresHom.{u} g F G).toRingHom
      (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = _
  rw [show (etalePresHom.{u} g F G).toRingHom (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (MvPolynomial.X
        (localisationIncl.{u} (n + 1) (localisationIncl.{u} n i))) from by
    simp [etalePresHom, PresHom.ofRename]]
  change (AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G)).eval (U := ⊤) y trivial
    (polyToGlobal.{u} _ (MvPolynomial.X _)) = _
  rw [eval_polyToGlobal, MvPolynomial.eval_X]

end

end ComplexAnalytic

end
