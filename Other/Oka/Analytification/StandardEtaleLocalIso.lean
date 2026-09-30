/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.HypersurfaceFinite
public import Other.Oka.AnalyticSpace.SimpleZeroTopology

/-!
# A standard étale morphism over affine space analytifies to a local isomorphism

`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean` proves that an open subspace of a hypersurface in
`ℂ^(n+1)`, on which a polynomial cutting it out has non-vanishing derivative in the last
variable, projects to `ℂ^n` as a local isomorphism of complex analytic spaces
(`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`).
`Other/Oka/Analytification/StandardEtaleAnalytification.lean` proves that the analytification of a
standard étale presentation **is** such an open subspace ; the distinguished open `D(G)` of the
hypersurface `{F = 0}` ; and that `StandardEtalePair.cond` supplies exactly that derivative
hypothesis there (`ComplexAnalytic.eval_pderiv_ne_zero_of_mem`). This file joins the two, and
**every module under `Other/Oka/` with both subtrees in its import closure is this one or downstream of
it** ; seven at `73176e1`, counting itself, the other six being
`Other/Oka/Analytification/Hausdorff.lean`, `Other/Oka/Analytification/HausdorffBase.lean`,
`Other/Oka/Analytification/StandardEtaleFiniteEtale.lean`,
`Other/Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`,
`Other/Oka/Analytification/StandardEtaleFinitenessBase.lean` and
`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`. **Of the two subtree roots this file
imports `Other/Oka/AnalyticSpace/SimpleZeroTopology.lean` directly and
`Other/Oka/Analytification/StandardEtaleAnalytification.lean` not at all**: its two `import` lines are
that one and `Other/Oka/Analytification/HypersurfaceFinite.lean`, which is what carries the other, one
edge further up. **So the claim is about closures and is measured over them**, by
`scripts/module_graph.py` at that commit.

**That clause read *"it is the first module to import both subtrees"*, and it was false at
`a01e3c4`, the commit that wrote it.** `Oka.lean`, the aggregator `mk_all` generates, imports
every module of the library and so had both on the day. **It is corrected here and not dated**, on
`README.md`'s rule that a clause false when it was written is corrected rather than recorded.
**The argument it was making survives the repair and only its scope was wrong**, which is the
same repair `Other/Oka/Analytification/SpecDistinguishedOpen.lean` records of a clause of this shape.

## The base is `ℂ^n`, and that is the statement rather than a limitation of the proof

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`: the `k`
relations of the base algebra read upstairs, and `F`. The theorem above takes a cut-out datum for
**one** section, and `Other/Oka/Analytification/StandardEtaleAnalytification.lean` recorded the
mismatch as a missing datum for `k + 1` relations against one section.

**It is not a missing datum.** The conclusion of that theorem is about the projection to `ℂ^n`,
and for `k ≥ 1` it fails ; **whenever the base's analytification `X^an` is a proper closed subset
of `ℂ^n`** ; unless the hypersurface's analytification is empty. **This sentence gave the reason
as *"since its image is contained in `X^an`"*, and that reason is a step short**: containment in a
proper closed subset is not on its own incompatible with being a local isomorphism, and this
file's `## What is not here` says in terms that *"a local isomorphism need not be surjective and
this one is not"*. What closes it is that the image is **open**. A local isomorphism is a local
homeomorphism ; that is the field
`ComplexAnalytic.AnalyticSpace.IsLocalIso.isLocalHomeomorph` ; and so an open map, hence its image
is open; a proper closed `X^an ⊆ ℂ^n` has empty interior, since `X^an` is the zero locus of the
relations of `g` and a polynomial vanishing on a non-empty open subset of `ℂ^n` is zero; and an
open subset of a set with empty interior is empty. **So the two sentences are not in tension**:
non-surjectivity is exactly what makes the containment reading fail, and openness is what makes
the corrected one work.

*Unless empty* rather than a bare *false* because the empty case is not a counterexample: both
fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the points of the source, so an
empty analytification satisfies them vacuously.

**Since 2026-09-02 this paragraph is a theorem and not only an argument.**
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
(`Other/Oka/Analytification/StandardEtaleNotLocalIso.lean`) is the failure above, compiled, with the two
qualifications restated so that they are checkable: *proper* becomes `∃ j, g j ≠ 0`, which is what
makes the zero locus a proper subset and is what the proof consumes, and *unless empty* becomes a
`Nonempty` on the source. **The argument above is not the proof's.** The proof does not pass
through the interior of `X^an`: having the image open and inside the zero locus, it applies
`MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen` (`Other/Oka/Algebra/MvPolynomial/Funext.lean`) to make
every relation zero, which contradicts `∃ j, g j ≠ 0` at once. The two routes are the same three
facts in a different order and the paragraph is kept as written because it is the one a reader
meets here; **and it is kept as a paragraph rather than replaced by a citation**, for the reason
the section below gives about the two copies of it.

***Proper* is a hypothesis at `k ≥ 1` and not a consequence of it, which is why the clause above
carries it rather than leaving it to be read out of the argument.** Nothing constrains `g`:
`Other/Oka/Analytification/StandardEtaleAnalytification.lean`, where the `k ≥ 1` configuration is
written down, takes it under a `variable` line that asks nothing of it. At `g = 0` the relations
cut out nothing, `X^an` is the whole of `ℂ^n`, its interior is everything, and the argument has no
step left ; and `ComplexAnalytic.analytificationInclHom g` is then a local isomorphism rather
than a closed immersion onto a proper subset. That configuration is degenerate and nothing on
this line calls it, but the clause is a claim about **every** `g` at `k ≥ 1`, and a reader who
tests it there finds it false rather than unmotivated.

**This argument is written out twice, as two copies and not as one citation, and that is
deliberate.** The other copy is `Other/Oka/Analytification/StandardEtaleAnalytification.lean`'s
`## What is not here`. Each sits inside a section about something else ; there a misdiagnosed
absence, here why the base is `ℂ^n` ; so a citation would send a reader to a paragraph whose
subject is not the one they came for. Both are kept, **each names the other**, and a repair to
one is not made without the other.

The `k + 1` versus one is the signature of a statement whose base is the whole of `ℂ^n`, i.e.
`k = 0`, and that is what everything below is stated at. A statement over a general base is a
different theorem. **This sentence went on to price that theorem ; *"needs an implicit function
theorem relative to `X^an`, which `Other/Oka/Analysis/Calculus/Implicit.lean` does not have"* ; and the
pricing was a misdiagnosis in both directions**, which the two paragraphs below say in full: of
the two statements at `k ≥ 1` the projection one is **false** rather than expensive, and the
other takes no implicit function theorem relative to `X^an` at all.

**That sentence is about the projection to `ℂ^n`, and at `k ≥ 1` there are two statements and not
one.** The other is about the analytified structure map to `X^an` **alone**, without
`ComplexAnalytic.analytificationInclHom g` after it:
`ComplexAnalytic.AnalyticSpace.IsLocalIso (analytificationMap (etalePresHom g F G))`. It is a
different statement, and the argument above does not touch it ; that argument concludes from the
image being an open subset of a proper closed subset **of `ℂ^n`**, and openness in `X^an` is not
openness in `ℂ^n`. **It is now a theorem** ;
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean`), at every `k` ; and *"a statement over a
general base"* above should be read as naming the projection one only, which is the one that is
false. **It is also not obtained by cancelling** the composite against
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`, whose second factor would have to be
`ComplexAnalytic.analytificationInclHom g` ; a closed immersion, and by the argument above not a
local isomorphism whenever `X^an` is a proper non-empty closed subset of `ℂ^n`, since its image is
the whole of `X^an` and a local isomorphism has open image. **Neither qualification follows from
`k ≥ 1`**: at `g = 0` the image is the whole of `ℂ^n` and this morphism is a local isomorphism,
and at a `g` with the constant `1` among its relations the source is empty and it is one
vacuously.

**That other statement takes no implicit function theorem relative to `X^an` ; only the one
relative to `ℂ^n` that everything below already spends ; and this is measured rather than
read.** `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ`
(`Other/Oka/AnalyticSpace/CutOutLocalIso.lean`) transports the class from a local isomorphism
`p : E ⟶ B` to any morphism between subspaces cut out of `E` and of `B` by a family of sections
and by its pullbacks along `p`, and `Other/Oka/Analytification/StandardEtaleLocalIsoBase.lean` supplies
the two cut-out data and the commuting square at these arguments. **Nothing analytic enters those
three**: the datum for the smaller space is a cancellation of cut-out data
(`ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq`), and the one place a naive transcription of
the `k = 0` proof breaks is the open ; `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` supplies the
derivative only on the `k ≥ 1` hypersurface, so the `k = 0` side is stated at `D(G · ∂F)` and
`ComplexAnalytic.localisationOpen_mul_pderiv` says that names `D(G)` on the `k ≥ 1` side. **What
is analytic is the fourth input** ; that the projection of `D(G · ∂F)` is itself a local
isomorphism, which is `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` and is this
file's own input at `k = 0`, spent again and not spent twice.

At `k = 0` the two families agree on the nose: `ComplexAnalytic.hypersurfacePresentation g F` is
a `Fin 1`-family whose only entry is `F`, and
`ComplexAnalytic.section_hypersurfacePresentation_empty` is the one line that says so. The datum
itself is `ComplexAnalytic.isCutOutBy_analytificationInclHom`
(`Other/Oka/Analytification/UniversalProperty.lean`), which holds for every `k` and needed no new
general lemma: `ComplexAnalytic.IsCutOutBy.iso_comp` was already in the tree.

## What the last theorem's target is, and why it is `ℂ^n`

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` concludes about
`ComplexAnalytic.analytificationMap` of the étale structure map **followed by the inclusion of
the base's analytification into `ℂ^n`**, and not about the structure map alone. At `k = 0` the
inclusion `ComplexAnalytic.analytificationInclHom g` is an isomorphism ; the zero locus of the
empty family is everything ; but **nothing in this repository says so**; see `## What is not
here`. Composing with it is therefore not a weakening but a choice of spelling: the target is the
`ℂ^n` that `ComplexAnalytic.AnalyticSpace.proj` maps to, named as itself.

The step that makes that composite the right one is
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp`
(`Other/Oka/Analytification/HypersurfaceFinite.lean`), which says the analytified structure map
followed by the base's inclusion is the hypersurface's own inclusion followed by the projection.
It holds for every `k` and is the only thing this file takes from that module.

## `localisationVar` and `Fin.last`

`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` differentiates at
`ULift.up (Fin.last n)` and `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces a derivative at
`ComplexAnalytic.localisationVar n`. **They are the same term** ;
`Other/Oka/Analytification/DistinguishedOpen.lean` defines the second as the first ; so the statements
below are written with `ComplexAnalytic.localisationVar` throughout and no bridge lemma appears
anywhere. A reader comparing the two signatures will otherwise go looking for one.

## Main results

- `ComplexAnalytic.section_hypersurfacePresentation_empty`: over an empty base presentation, the
  polynomials cutting the hypersurface out of `ℂ^(n+1)` are the one-element family `![F]`.
- `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`: **so the hypersurface's
  analytification carries a cut-out datum for a single section**, which is what every theorem on
  this line asks for.
- `ComplexAnalytic.isLocalIso_hypersurface_ofRestrict_comp_proj`: **`D(G)` inside the
  hypersurface `{F = 0} ⊆ ℂ^(n+1)` projects to `ℂ^n` as a local isomorphism**, given that the
  derivative of `F` in the last variable does not vanish on `D(G)`.
- `ComplexAnalytic.isLocalIso_hypersurface_of_standardEtale`: the same with the derivative
  hypothesis discharged from `StandardEtalePair.cond`.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`: **the analytification of a
  standard étale morphism over `ℂ^n` is a local isomorphism onto `ℂ^n`.**

## What is not here

* **No `IsFiniteEtale`, and this file moves the finiteness field nowhere.** For the *unrestricted*
  standard étale morphism finiteness is **false** ; inverting `G` destroys it, and
  `Other/Oka/Analytification/MonicHypersurface.lean`'s `## What is not here` carries the counterexample
  in terms. So the two fields of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` are not two halves
  of one job here: one of them is a theorem and the other is a false statement waiting for a base
  restriction that nothing below constructs.

  **The base restriction is now constructed, in a file incomparable with this one**:
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleFiniteness.lean`) makes the étale analytification finite over
  an open `V ⊆ ℂ^n` on which the inversion is vacuous. **And the step that paragraph named as
  missing has since been taken.** It said the class
  would be wanted for
  `ComplexAnalytic.AnalyticSpace.restrictHom (… ≫ analytificationInclHom g) V`, whose `IsFinite`
  field is that theorem and whose `IsLocalIso` field would follow from the last theorem below **if
  `IsLocalIso` transported along `ComplexAnalytic.AnalyticSpace.restrictHom`** ; and that it was
  a general fact about open subspaces rather than anything this line owns. Both readings held:
  the transport is `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`
  (`Other/Oka/AnalyticSpace/OpenSubspace.lean`), which reads nothing about étale morphisms, and the
  class is `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleFiniteEtale.lean`). **The last theorem below is its second
  field and is read unrestricted** ; the restriction is asked for by the first field alone,
  because unrestricted finiteness is false and unrestricted local-isomorphy is not.

  **The words *incomparable with this one* above read *"that imports this one's imports and not
  this one"* until 2026-09-07.** The *and not this one* half was exact and the *imports this one's
  imports* half was not:
  `Other/Oka/Analytification/StandardEtaleFiniteness.lean` takes **one** of this file's two imports,
  `Other/Oka/Analytification/HypersurfaceFinite.lean`, and takes
  `Other/Oka/Analytification/OpenBaseFiniteness.lean` where this file takes
  `Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`, which is not in its import closure at all. So
  neither file is in the other's closure and the relation between them is incomparability, which
  is what the sentence was reaching for. Measured at `5a525bc` over this repository's import
  graph with `scripts/import_cost.py`'s `IMPORT` pattern read through its nesting-aware
  `strip_comments`.
* **Nothing at `k ≥ 1`**, for the reason at the top of this docstring: not a gap but a different
  statement.
* **Nothing saying `ComplexAnalytic.analytificationInclHom g` is an isomorphism when `g` is the
  empty family**, and the price is measured rather than guessed.
  `ComplexAnalytic.IsCutOutBy.uniqueIso` against
  `ComplexAnalytic.isCutOutBy_id_restrict_top` gives the isomorphism of *locally ringed* spaces,
  and `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful but not full, so the
  inverse would still have to be shown `ℂ`-linear before the conclusion could be moved to
  `ComplexAnalytic.AnalyticSpace.analytification g`. **This bullet used to offer that as the
  price, and it is no longer one**:
  `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace_reflectsIsomorphisms`
  (`Other/Oka/AnalyticSpace/Basic.lean`) is that linearity for the inverse of any morphism of analytic
  spaces, so an isomorphism of locally ringed spaces between two of them is one of analytic
  spaces without further work. The functor is still faithful and not full ; reflecting
  isomorphisms is neither ; and it is still the reason the two conclusions are different
  statements. **It is not built here because nothing consumes it**, which is unchanged and is the
  reason that stands: the last theorem below is a complete statement with `ℂ^n` as its target, and
  the thing that would want the other spelling is the assembly of the Riemann existence theorem,
  not this file.
* **No `StandardEtalePair` is constructed *here*.** The two theorems below take one as a
  hypothesis rather than constructing it.
* **Nothing about the image.** A local isomorphism need not be surjective and this one is not:
  at `F = X² - x` and `G = X` it misses the origin. No statement below says anything about the
  image, about fibres, or about degree.
* **Nothing about a general étale morphism.** Every étale morphism of schemes is Zariski-locally
  standard étale; gluing the statement below over such a cover is a separate construction and
  nothing here starts it.
-/

@[expose] public section

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ} (g : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The cut-out datum for a single section -/

/-- **Over an empty base presentation the hypersurface is cut out of `ℂ^(n+1)` by `F` alone.**

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`, so at
`k = 0` it is a `Fin 1`-family and its only index is `Fin.last 0`. The `change` names that index ;
`fin_cases` leaves the goal at `(0 : Fin 1)` and `Fin.snoc_last` is stated at `Fin.last`, which
is the same element and not the same term.

**`change` and not `show`, and `lake build --wfail` is what says so.** Mathlib's
`linter.style.show` rejects a `show` that *alters* the goal ; which is the whole point of this
one ; and the build turns that warning into a failure. The two tactics do the same thing here.

The `show … from Fin.snoc_last _ _` inside the `rw` is a different `show`, is a term and not a
tactic, and is untouched by that linter. It is the shape
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` uses one file over, **and here it is a choice rather
than a necessity**. This paragraph said it was forced, for the sibling's reason: that a bare
`rw [hypersurfacePresentation, Fin.snoc_last]` fails with *"Failed to rewrite using equation
theorems for `hypersurfacePresentation`"*, and that naming the instance is what keeps an equation
lemma for that definition out of the environment. **Neither holds at this rewrite**, measured in
tree: the bare form compiles, and `scripts/DumpOkaDecls.lean`'s output is byte-identical either
way, so no equation lemma enters the environment on either spelling. The sibling states its
version of the reason at `Fin.snoc_castSucc` under `rwa … at`, which is a different rewrite and
is untouched here; the named form is kept for consistency with it and for nothing else. -/
theorem section_hypersurfacePresentation_empty :
    (fun j ↦ (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (hypersurfacePresentation.{u} g F j) :
      (AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.obj (op ⊤))) =
      ![OkaRing.ofMvPolynomial ⊤ F] := by
  funext j
  fin_cases j
  change OkaRing.ofMvPolynomial ⊤ (hypersurfacePresentation.{u} g F (Fin.last 0)) = _
  rw [show hypersurfacePresentation.{u} g F (Fin.last 0) = F from Fin.snoc_last _ _]
  rfl

/-- **The hypersurface's analytification is cut out of `ℂ^(n+1)` by the single section `F`.**

`ComplexAnalytic.isCutOutBy_analytificationInclHom` at the hypersurface presentation, rewritten
along the family identity above. This is the datum
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` takes, and supplying it is the whole
of what was missing on this line. -/
theorem isCutOutBy_analytificationInclHom_hypersurface :
    IsCutOutBy (analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)).toLRSHom
      ![OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) F] :=
  section_hypersurfacePresentation_empty.{u} g F ▸
    isCutOutBy_analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)

/-! ### The local isomorphism -/

/-- **The distinguished open `D(G)` of the hypersurface `{F = 0} ⊆ ℂ^(n+1)` projects to `ℂ^n` as
a local isomorphism**, provided the derivative of `F` in the last variable does not vanish at any
of its points.

Nothing here reads `G` beyond its naming the open subset: the hypothesis is asked at the points
of `D(G)` and at no others, which is exactly the shape
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` was stated in. -/
theorem isLocalIso_hypersurface_ofRestrict_comp_proj
    (hlin : ∀ y : (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).restrict
        (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G),
      MvPolynomial.eval (y.1.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
        (MvPolynomial.pderiv (localisationVar.{u} n) F) ≠ 0) :
    AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
          AnalyticSpace.proj.{u} n) :=
  isLocalIso_ofRestrict_comp_proj_of_pderiv
    (isCutOutBy_analytificationInclHom_hypersurface.{u} g F) _ hlin

/-- **The same, with the derivative hypothesis discharged from `StandardEtalePair.cond`.**

`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` turns `cond` into the non-vanishing of the
derivative at a point of the hypersurface off the zero locus of `G`, and a point of the
restriction is a point of the hypersurface together with the proof that `G` does not vanish
there ; `ComplexAnalytic.mem_localisationOpen_iff` read forwards. So the two fit with nothing in
between. -/
theorem isLocalIso_hypersurface_of_standardEtale
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
          AnalyticSpace.proj.{u} n) :=
  isLocalIso_hypersurface_ofRestrict_comp_proj.{u} g F G fun y ↦
    eval_pderiv_ne_zero_of_mem.{u} g F G P hF hG y.1
      ((mem_localisationOpen_iff.{u} _ _).1 y.2)

/-- **The analytification of a standard étale morphism over `ℂ^n` is a local isomorphism onto
`ℂ^n`.**

The statement the whole of this line was for, at the one base the theorems it rests on are about.
Read the composite as a whole: `ComplexAnalytic.analytificationMap` of
`ComplexAnalytic.etalePresHom` lands in the base's analytification, and
`ComplexAnalytic.analytificationInclHom` names that as a subspace of `ℂ^n` ; which at `k = 0` it
is the whole of, though nothing here proves that; see `## What is not here`.

Three rewrites and an instance. `ComplexAnalytic.etaleAnalytificationIso_hom_comp` replaces the
étale analytification by `D(G)` in the hypersurface, over the base;
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` turns the remaining map to the base
followed by the base's inclusion into the hypersurface's inclusion followed by the projection;
and then the composite is an isomorphism followed by the theorem above, which
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` closes.

**`haveI` for both, and that is emphasis rather than necessity.**
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` is an instance and needs the two facts as local
instances to fire, which a plain `have` supplies as well: the proof compiles unchanged with
`have` twice, measured in tree. This paragraph also called that *"the same reason
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso` is a `theorem` and not an instance ; its own
docstring says why"*; that docstring explains a discrimination-tree seam in its own proof and
says nothing about instance-versus-theorem, so the citation is withdrawn rather than replaced. -/
theorem isLocalIso_analytificationMap_etalePresHom_comp
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g) := by
  have hcomp :
      analytificationMap.{u} (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g =
        (etaleAnalytificationIso.{u} g F G).hom ≫
          ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
            (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
            analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
              AnalyticSpace.proj.{u} n) := by
    rw [← etaleAnalytificationIso_hom_comp.{u} g F G, Category.assoc, Category.assoc,
      analytificationMap_hypersurfacePresHom_comp.{u} g F]
  rw [hcomp]
  haveI := isLocalIso_hypersurface_of_standardEtale.{u} g F G P hF hG
  haveI : AnalyticSpace.IsLocalIso (etaleAnalytificationIso.{u} g F G).hom :=
    AnalyticSpace.isLocalIso_of_isIso _
  infer_instance

end

end ComplexAnalytic

end
