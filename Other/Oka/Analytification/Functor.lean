/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Other.Oka.Analytification.ChangeOfVariables

/-!
# The analytification as a functor

`Other/Oka/Analytification/ChangeOfVariables.lean` proves that a `ℂ`-algebra map between two presented
algebras induces a morphism of analytifications, that identities go to identities and composites
to composites. That is the *data* of a functor. This file bundles it as one, and then removes the
presentation from the source.

The two steps are different in kind. Bundling is bookkeeping: a `Category` instance on
presentations whose three laws are `ComplexAnalytic.PresHom.ext` applied to the corresponding
`RingHom` laws. Removing the presentation is the step every previous account of this development
described as *"choosing a presentation for each algebra, which is a construction this file does
not perform"* ; and the point of this file is that **it is not a construction and should not be
one.**

## Do not choose a presentation

`ComplexAnalytic.toFGAlg`, sending a presentation to the algebra it presents, is **fully
faithful** ; a `ComplexAnalytic.PresHom` *is* a `ℂ`-algebra map of the presented algebras, with
both round trips `rfl` ; and **essentially surjective** onto the finitely generated `ℂ`-algebras,
which is `ComplexAnalytic.exists_presentation`. So it is an equivalence, and
`CategoryTheory.Functor.asEquivalence` supplies the inverse. The presentation attached to an
algebra is then whatever `Classical.choice` picks out of essential surjectivity, and nothing
depends on which one it is, because any two are related by the equivalence.

The only mathematical content in essential surjectivity is **Hilbert's basis theorem**: a
finitely *generated* `ℂ`-algebra is a quotient of a polynomial ring in finitely many variables,
and the kernel is finitely generated because that polynomial ring is Noetherian. That is why
"finitely generated" and "finitely presented" are the same condition here, and it is the whole
reason a presentation exists to be chosen.

## The price of the choice, and why the comparison isomorphism is not optional

`analytificationFGAlg.obj (op A)` is **not** definitionally `AnalyticSpace.analytification g` for
a presentation `g` of `A`; it is the analytification of whichever presentation choice produced.
`ComplexAnalytic.analytificationFGAlgCompIso` is what connects the two, and without it the
functor would be a definition nothing can be computed from.

## Main definitions

- `ComplexAnalytic.Presentation`: a finite presentation `(n, k, g)`, bundled so that it can be the
  object of a category. Morphisms are `ComplexAnalytic.PresHom`, which run in the direction of the
  induced morphisms of spaces, so this category is the *opposite* of the category of presented
  algebras.
- `ComplexAnalytic.analytificationFunctor : Presentation ⥤ AnalyticSpace`: **the analytification,
  as a functor on presentations.**
- `ComplexAnalytic.Presentation.isoOfRename`: **a pair of mutually inverse renamings of the
  variables is an isomorphism of presentations**, and so, through the functor, an isomorphism of
  analytifications.
- `ComplexAnalytic.isFiniteType`: finite type, as a property of an object of `CommAlgCat ℂ`.
- `ComplexAnalytic.Presentation.isoOfAlgEquiv`: **an isomorphism of the presented algebras is
  an isomorphism of presentations** ; the general companion of
  `ComplexAnalytic.Presentation.isoOfRename`.
- `ComplexAnalytic.Presentation.algEquivOfIso`: **and back again**, which is what a consumer
  holding an isomorphism of presentations needs before it can reach any statement phrased about
  algebras. That the two really are mutually inverse is the pair of results below, and until they
  were stated *"back again"* was a claim about the construction rather than a theorem about it.
- `ComplexAnalytic.toFGAlg : Presentation ⥤ (isFiniteType.FullSubcategory)ᵒᵖ`: a presentation,
  read as the finitely generated `ℂ`-algebra it presents.
- `ComplexAnalytic.analytificationFGAlg`: **the analytification of a finitely generated
  `ℂ`-algebra, as a functor**, with no presentation in its statement.
- `ComplexAnalytic.analytificationFGAlgCompIso`, `ComplexAnalytic.analytificationFGAlgObjIso`: the
  comparison with the presentation-level construction.

## Main results

- `ComplexAnalytic.toFGAlgFullyFaithful`: a `ℂ`-algebra map of presented algebras is the same
  thing as a morphism of presentations.
- `ComplexAnalytic.exists_presentation`: **every finitely generated `ℂ`-algebra is a presented
  algebra.**
- `ComplexAnalytic.instIsEquivalenceToFGAlg`: presentations *are* finitely generated
  `ℂ`-algebras.
- `ComplexAnalytic.analytificationFGAlgObjIso_hom`: the comparison isomorphism is the functor
  applied to the inverse of the unit ; the only content in it, and what lets a consumer compose
  with it.
- `ComplexAnalytic.analytificationFGAlgObjIso_naturality`: **the comparison isomorphism is
  natural.** This is what a consumer holding a *morphism* needs, and the isomorphism above cannot
  give it: evaluating a natural isomorphism at one object forgets exactly the square.
- `ComplexAnalytic.toFGAlg_comp_analytificationFGAlg_map`: **the functor's morphism at a
  presentation is the presentation-level analytification conjugated by that isomorphism**, which
  is what any property stable under composing with isomorphisms travels across.
- `ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso` and
  `ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv`: **the two constructions above are
  mutually inverse**, both by `rfl`. The first is the one on a consumer's path: a caller who
  arrives with an isomorphism of presentations and feeds its algebra map to a statement whose
  conclusion is phrased with the first construction above gets the isomorphism it started with
  back. (That construction is named in the proofs' docstrings rather than here, since every
  backticked repository name under this heading is read as a result this file advertises, and it
  is a definition advertised above.)

## What is not here

* **Naturality of the comparison with `Spec`** is not here, and is no longer missing: it is
  `Other/Oka/Analytification/Comparison.lean`, which makes `ComplexAnalytic.analytificationToSpec` a
  natural transformation on presentations and then, along the equivalence below, one on the
  finitely generated `ℂ`-algebras themselves. That is what makes `X^an ⟶ X` part of the
  structure rather than a separate construction per presentation. It stays in a separate file
  because this one is about the *source* category and that one is about the target.
* **Anything non-affine.** A functor on schemes locally of finite type would be built from this
  one by gluing, and nothing here glues.
* **Anything analytic.** Every proof in this file is category-theoretic bookkeeping or
  commutative algebra; the analytic content is upstream, in the universal property.

## Design notes

**Why the full subcategory of `CommAlgCat ℂ` and not `AlgCat ℂ`, `Under (CommRingCat.of ℂ)` or
`Scheme`.** The analytification is defined only for commutative algebras, so `CommAlgCat` rather
than `AlgCat`; and `Algebra.FiniteType` is *exactly* the essential image of `Presentation` by
`ComplexAnalytic.exists_presentation`, so cutting the category down to it is not an arbitrary
restriction but the precise statement of what the construction covers. Affine schemes are one
`Spec` away and are a separate step, not a different foundation.

**Why a bespoke `Presentation` rather than a general presentation type.** `ComplexAnalytic.PresHom`
and `ComplexAnalytic.analytificationMap` are stated for a tuple
`g : Fin k → MvPolynomial (ULift (Fin n)) ℂ`; this structure is that tuple with its two indices,
and nothing more. It exists so that `PresHom` has a category to live in.

**And it is not the subject of `Other/Oka/Analytification/Presentation.lean`.**
`ComplexAnalytic.Presentation` here is the bundled triple `(n, k, g)` that gives
`ComplexAnalytic.PresHom` a category to live in; `Other/Oka/Analytification/Presentation.lean` is a
different thing ; the construction of `X^an` from one such tuple, which this file's objects
index.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### Presentations as a category -/

/-- A finite presentation of a `ℂ`-algebra: `n` variables, `k` relations, and the relations. -/
structure Presentation where
  /-- The number of variables. -/
  n : ℕ
  /-- The number of relations. -/
  k : ℕ
  /-- The relations. -/
  g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ

/-- The `ℂ`-algebra a presentation presents. -/
abbrev Presentation.alg (P : Presentation.{u}) : Type u :=
  PresentedAlgebra.{u} P.n P.k P.g

/-- **Presentations form a category**, with `ComplexAnalytic.PresHom` as its morphisms.

Those run in the direction of the induced morphisms of analytic spaces rather than of the
underlying `ℂ`-algebra maps, so this is the *opposite* of the category of presented algebras ;
which is why `ComplexAnalytic.analytificationFunctor` below is covariant and
`ComplexAnalytic.toFGAlg` lands in an opposite category.

All three laws are `ComplexAnalytic.PresHom.ext` applied to the corresponding `RingHom` law: the
commutation with the structure map is a proposition, so a morphism is its ring map. -/
instance : Category Presentation.{u} where
  Hom P Q := PresHom.{u} P.g Q.g
  id P := PresHom.id.{u} P.g
  comp ψ χ := PresHom.comp.{u} ψ χ
  id_comp _ := PresHom.ext (RingHom.comp_id _)
  comp_id _ := PresHom.ext (RingHom.id_comp _)
  assoc _ _ _ := PresHom.ext (RingHom.comp_assoc _ _ _).symm

/-- **The analytification, as a functor on presentations.**

Nothing is proved here: `ComplexAnalytic.analytificationMap_id` and
`ComplexAnalytic.analytificationMap_comp` are the two functor laws on the nose. -/
def analytificationFunctor : Presentation.{u} ⥤ AnalyticSpace.{u} where
  obj P := AnalyticSpace.analytification.{u} P.g
  map ψ := analytificationMap.{u} ψ
  map_id _ := analytificationMap_id.{u}
  map_comp ψ χ := analytificationMap_comp.{u} ψ χ

/-- **The functor's value is the analytification**, by `rfl`.

Stated because it is not `rfl` to `simp`: `Category.id_comp` will not fire on
`𝟙 (analytificationFunctor.obj P) ≫ f` when `f`'s domain is spelled
`ComplexAnalytic.AnalyticSpace.analytification P.g`, which is how every consumer of the functor
spells it.

Three proofs in `Other/Oka/Analytification/CoverFunctoriality.lean` need it, and erasing the attribute
there leaves exactly those three failing and nothing else:
`ComplexAnalytic.comm_coverMapPart_id`, `ComplexAnalytic.comm_coverMapPart_comp` and
`ComplexAnalytic.coverMap_comp`. `ComplexAnalytic.coverMap_id` is not among them ; it needs this
only through the first. -/
@[simp]
theorem analytificationFunctor_obj (P : Presentation.{u}) :
    analytificationFunctor.{u}.obj P = AnalyticSpace.analytification.{u} P.g := rfl

/-- **A pair of mutually inverse renamings of the variables, each carrying the other
presentation's relations into this one's ideal, is an isomorphism of presentations.**

`ComplexAnalytic.PresHom.ofRename` twice, with
`ComplexAnalytic.PresHom.ofRename_comp_ofRename` for both triangles. It is stated here rather
than beside those, because an isomorphism needs the `Category` instance above and that instance
is what this file exists to give.

Mind the direction. A morphism `P ⟶ Q` is a `ComplexAnalytic.PresHom P.g Q.g`, whose ring map
runs `Q.alg → P.alg`, so the renaming `σ` underlying `hom` sends the variables of `Q` to those
of `P`. The two hypotheses `hστ` and `hτσ` are equalities of maps of *variables*, not of
polynomials ; which is why an isomorphism of presented algebras of this shape costs no
commutative algebra at all.

Applying `ComplexAnalytic.analytificationFunctor` to the result is how a change of coordinates
becomes an isomorphism of analytic spaces. -/
def Presentation.isoOfRename {P Q : Presentation.{u}}
    (σ : ULift.{u} (Fin Q.n) → ULift.{u} (Fin P.n))
    (τ : ULift.{u} (Fin P.n) → ULift.{u} (Fin Q.n))
    (h : ∀ j, MvPolynomial.rename σ (Q.g j) ∈ presentationIdeal.{u} P.g)
    (h' : ∀ j, MvPolynomial.rename τ (P.g j) ∈ presentationIdeal.{u} Q.g)
    (hστ : σ ∘ τ = _root_.id) (hτσ : τ ∘ σ = _root_.id) : P ≅ Q where
  hom := PresHom.ofRename.{u} σ h
  inv := PresHom.ofRename.{u} τ h'
  hom_inv_id := PresHom.ofRename_comp_ofRename.{u} σ h τ h' hστ
  inv_hom_id := PresHom.ofRename_comp_ofRename.{u} τ h' σ h hτσ

/-- **A `ℂ`-algebra isomorphism of the presented algebras is an isomorphism of presentations.**

The general companion of `ComplexAnalytic.Presentation.isoOfRename`, which is the special case
where the map comes from a renaming of the variables and costs no commutative algebra. This one
takes the algebra isomorphism as given, which is the shape it arrives in when it comes from
outside ; from a scheme, say, whose two affine members agree on an overlap.

It is `ComplexAnalytic.toFGAlgFullyFaithful.preimageIso` in content, and is stated directly
because assembling the isomorphism in the opposite full subcategory that lemma consumes is longer
than the four lines here. Mind the direction, as in `ComplexAnalytic.Presentation.isoOfRename`:
the algebra map of `P ⟶ Q` runs `Q.alg → P.alg`. -/
def Presentation.isoOfAlgEquiv {P Q : Presentation.{u}} (e : Q.alg ≃ₐ[ℂ] P.alg) : P ≅ Q where
  hom := ⟨e.toRingHom, RingHom.ext fun c ↦ e.commutes c⟩
  inv := ⟨e.symm.toRingHom, RingHom.ext fun c ↦ e.symm.commutes c⟩
  hom_inv_id := PresHom.ext (RingHom.ext fun x ↦ e.apply_symm_apply x)
  inv_hom_id := PresHom.ext (RingHom.ext fun x ↦ e.symm_apply_apply x)

/-- **An isomorphism of presentations is a `ℂ`-algebra isomorphism of the presented algebras**,
the inverse of `ComplexAnalytic.Presentation.isoOfAlgEquiv`.

Both directions of the algebra map are already there ; a `ComplexAnalytic.PresHom` *is* a ring map
and its `commutes` field is the `ℂ`-linearity ; so the four fields below are the two triangles of
the isomorphism read at a point. It is stated because a consumer who holds an isomorphism of
presentations, rather than of algebras, could otherwise reach nothing that is phrased about
algebras: `ComplexAnalytic.Presentation.isoOfAlgEquiv` went one way only until this was written.

Mind the direction, which is that of `ComplexAnalytic.PresHom` itself: the algebra map of
`P ⟶ Q` runs `Q.alg → P.alg`, so an isomorphism `P ≅ Q` gives `Q.alg ≃ₐ[ℂ] P.alg` and not the
other way about. -/
noncomputable def Presentation.algEquivOfIso {P Q : Presentation.{u}} (φ : P ≅ Q) :
    Q.alg ≃ₐ[ℂ] P.alg where
  toFun := φ.hom.toRingHom
  invFun := φ.inv.toRingHom
  left_inv x := congrArg (fun ψ : PresHom.{u} _ _ ↦ ψ.toRingHom x) φ.inv_hom_id
  right_inv x := congrArg (fun ψ : PresHom.{u} _ _ ↦ ψ.toRingHom x) φ.hom_inv_id
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' c := RingHom.congr_fun φ.hom.commutes c

/-- **The two constructions are mutually inverse, in the direction a consumer meets first.**

`ComplexAnalytic.Presentation.algEquivOfIso`'s docstring calls itself the inverse of
`ComplexAnalytic.Presentation.isoOfAlgEquiv`, and this is what makes that a theorem rather than a
description. It matters because statements about localisations of two presentations are phrased
with `isoOfAlgEquiv` on the right-hand side, and the one this was written for is the triangle
`ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp`
(`Other/Oka/Analytification/LocalisationIndependence.lean`) ; while the datum a caller actually holds is
an isomorphism of presentations. Without this, that caller ends up with
`isoOfAlgEquiv (algEquivOfIso φ)` where they want `φ` and nothing closes the gap.

`rfl`, because a `ComplexAnalytic.PresHom` is a ring map and a proof, and both fields come back
unchanged; the two proof fields of the `CategoryTheory.Iso` are propositions. -/
theorem Presentation.isoOfAlgEquiv_algEquivOfIso {P Q : Presentation.{u}} (φ : P ≅ Q) :
    Presentation.isoOfAlgEquiv.{u} (Presentation.algEquivOfIso.{u} φ) = φ := rfl

/-- **And in the other direction**, which costs the same and is stated so that neither half of the
correspondence is the one nobody checked. -/
theorem Presentation.algEquivOfIso_isoOfAlgEquiv {P Q : Presentation.{u}}
    (e : Q.alg ≃ₐ[ℂ] P.alg) :
    Presentation.algEquivOfIso.{u} (Presentation.isoOfAlgEquiv.{u} e) = e := rfl

/-! ### Presentations are the finitely generated `ℂ`-algebras -/

/-- A `ComplexAnalytic.PresHom`, as a `ℂ`-algebra map. The commutation it carries *is* the
`AlgHom` field `commutes'`, so this is a repackaging and not a construction. -/
def PresHom.toAlgHom {n k n' k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
    {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ} (ψ : PresHom.{u} g g') :
    PresentedAlgebra.{u} n' k' g' →ₐ[ℂ] PresentedAlgebra.{u} n k g :=
  { ψ.toRingHom with commutes' := fun c ↦ RingHom.congr_fun ψ.commutes c }

/-- Being of finite type, as a property of an object of `CommAlgCat ℂ`. By
`ComplexAnalytic.exists_presentation` this is exactly the essential image of
`ComplexAnalytic.toFGAlg`. -/
abbrev isFiniteType : ObjectProperty (CommAlgCat.{u} ℂ) := fun A ↦ Algebra.FiniteType ℂ A

/-- **The algebra a presentation presents is of finite type over `ℂ`**, structurally: it is a
quotient of a polynomial ring in `P.n` variables. `ComplexAnalytic.toFGAlg` below is this instance
read as a functor and `ComplexAnalytic.instIsEquivalenceToFGAlg` is the sharp form of it.

**It was anonymous until 2026-08-31**, which is enough to be inferred and not enough to be cited,
and being uncitable is how it came to be overlooked: `Other/Oka/Analytification/SpecAffineCover.lean`'s
admissibility section needs exactly this statement ; *each member of an admissible cover is of
finite type over `ℂ`* ; and the branch that wrote that section first added a second proof of it
next to `ComplexAnalytic.PresentedAlgebra` before finding this one. The name is so that the
section can cite it. -/
instance finiteType_presentationAlg (P : Presentation.{u}) : Algebra.FiniteType ℂ P.alg :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (presentationIdeal.{u} P.g))
    Ideal.Quotient.mk_surjective

/-- **A presentation, read as the finitely generated `ℂ`-algebra it presents.**

The target is an opposite category because `ComplexAnalytic.PresHom` already runs in the
direction of spaces; see the `Category` instance above. -/
def toFGAlg : Presentation.{u} ⥤ (isFiniteType.{u}.FullSubcategory)ᵒᵖ where
  obj P := .op ⟨CommAlgCat.of ℂ P.alg, inferInstance⟩
  map ψ := (ObjectProperty.homMk (P := isFiniteType.{u})
    (CommAlgCat.ofHom (PresHom.toAlgHom ψ))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A `ℂ`-algebra map of presented algebras is the same thing as a morphism of presentations.**

Both round trips are `rfl`: a `ComplexAnalytic.PresHom` is a ring map plus a commutation, an
`AlgHom` is a ring map plus a commutation, and they are the same commutation. -/
def toFGAlgFullyFaithful : toFGAlg.{u}.FullyFaithful where
  preimage {P Q} f := ⟨(f.unop.hom.hom : Q.alg →ₐ[ℂ] P.alg).toRingHom,
    RingHom.ext fun c ↦ (f.unop.hom.hom).commutes c⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : toFGAlg.{u}.Full := toFGAlgFullyFaithful.{u}.full

instance : toFGAlg.{u}.Faithful := toFGAlgFullyFaithful.{u}.faithful

open MvPolynomial in
/-- **Every finitely generated `ℂ`-algebra is a presented algebra.**

This is the essential surjectivity that lets a presentation be *chosen* rather than constructed,
and the only content in it is **Hilbert's basis theorem**: finite type gives a surjection from a
polynomial ring in finitely many variables, and its kernel is finitely generated because that
polynomial ring is Noetherian. Everything else is reindexing ; `MvPolynomial.renameEquiv` to move
from `Fin n` to `ULift (Fin n)` variables, and `Finset.equivFin` to index the relations by
`Fin k`. -/
theorem exists_presentation (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    ∃ P : Presentation.{u}, Nonempty (P.alg ≃ₐ[ℂ] A) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let e : MvPolynomial (ULift.{u} (Fin n)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    renameEquiv ℂ Equiv.ulift
  set F : MvPolynomial (ULift.{u} (Fin n)) ℂ →ₐ[ℂ] A := f.comp e.toAlgHom with hF
  have hFs : Function.Surjective F := hf.comp e.surjective
  obtain ⟨s, hs⟩ : (RingHom.ker F.toRingHom).FG := IsNoetherian.noetherian _
  refine ⟨⟨n, s.card, fun i ↦ s.equivFin.symm i⟩, ⟨?_⟩⟩
  have hrange : Set.range (fun i : Fin s.card ↦ ((s.equivFin.symm i : s) :
      MvPolynomial (ULift.{u} (Fin n)) ℂ)) = (s : Set (MvPolynomial (ULift.{u} (Fin n)) ℂ)) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (s.equivFin.symm i).2,
      fun hx ↦ ⟨s.equivFin ⟨x, hx⟩, congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, hx⟩)⟩⟩
  have h : presentationIdeal.{u} (fun i : Fin s.card ↦ (s.equivFin.symm i : _)) =
      RingHom.ker F.toRingHom :=
    (congrArg Ideal.span hrange).trans hs
  exact (Ideal.quotientEquivAlgOfEq ℂ h).trans (Ideal.quotientKerAlgEquivOfSurjective hFs)

instance : toFGAlg.{u}.EssSurj where
  mem_essImage X := by
    obtain ⟨⟨A, hA⟩⟩ := X
    obtain ⟨P, ⟨e⟩⟩ := exists_presentation.{u} A
    exact ⟨P, ⟨(ObjectProperty.isoMk (P := isFiniteType.{u}) (CommAlgCat.isoMk e.symm)).op⟩⟩

/-- **Presentations *are* the finitely generated `ℂ`-algebras.** Fully faithful and essentially
surjective, so an equivalence; this is what makes the analytification a functor of the algebra
alone. -/
instance instIsEquivalenceToFGAlg : toFGAlg.{u}.IsEquivalence where

/-! ### The analytification of a finitely generated `ℂ`-algebra -/

/-- **The analytification of a finitely generated `ℂ`-algebra, as a functor.**

The presentation is gone from the statement. It is still there in the proof ; the inverse of an
equivalence is built from essential surjectivity and so from `Classical.choice` ; but nothing
depends on which presentation is chosen, because any two are related by the equivalence. That is
the whole content of presentation-independence, and it was proved on objects in
`Other/Oka/Analytification/ChangeOfVariables.lean`. -/
def analytificationFGAlg : (isFiniteType.{u}.FullSubcategory)ᵒᵖ ⥤ AnalyticSpace.{u} :=
  toFGAlg.{u}.asEquivalence.inverse ⋙ analytificationFunctor.{u}

/-- **On a presentation, the functor of algebras agrees with the presentation-level
construction**, naturally.

This is not decoration. `ComplexAnalytic.analytificationFGAlg` is defined through the inverse of
an equivalence, so its value on an algebra is the analytification of *some* presentation and not
of the one in hand; this isomorphism is the only way back to the concrete construction, and
without it the functor would be a definition nothing can be computed from. -/
def analytificationFGAlgCompIso :
    toFGAlg.{u} ⋙ analytificationFGAlg.{u} ≅ analytificationFunctor.{u} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight toFGAlg.{u}.asEquivalence.unitIso.symm analytificationFunctor.{u} ≪≫
      analytificationFunctor.{u}.leftUnitor

/-- `ComplexAnalytic.analytificationFGAlgCompIso` at one presentation: the analytification of the
algebra a presentation presents is the analytification of that presentation. -/
def analytificationFGAlgObjIso (P : Presentation.{u}) :
    analytificationFGAlg.{u}.obj (toFGAlg.{u}.obj P) ≅ AnalyticSpace.analytification.{u} P.g :=
  analytificationFGAlgCompIso.{u}.app P

/-- **The comparison isomorphism is the functor applied to the inverse of the unit.**

Everything in `ComplexAnalytic.analytificationFGAlgCompIso` except this is associators and
unitors, so this is the only content in it, and it is what a consumer needs in order to compose
with it. The two identities are dropped by hand because the two spellings of the objects are
definitionally but not syntactically equal and `Category.id_comp` has to be told which category
it is in. -/
theorem analytificationFGAlgObjIso_hom (P : Presentation.{u}) :
    (analytificationFGAlgObjIso.{u} P).hom =
      analytificationFunctor.{u}.map (toFGAlg.{u}.asEquivalence.unitIso.inv.app P) := by
  simp only [analytificationFGAlgObjIso, analytificationFGAlgCompIso, NatIso.trans_app,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.id_obj,
    Functor.leftUnitor_hom_app]
  refine (Category.id_comp (obj := AnalyticSpace.{u}) _).trans
    (Category.comp_id (obj := AnalyticSpace.{u}) _)

/-- **The comparison isomorphism is natural**: the square over a morphism of presentations
commutes.

`ComplexAnalytic.analytificationFGAlgObjIso` compares the two constructions one object at a time,
and that is all an object-level consumer needs.  A consumer holding a *morphism* needs this, and
the two are not interchangeable: the object isomorphism is
`ComplexAnalytic.analytificationFGAlgCompIso` evaluated at one presentation, and evaluating a
natural isomorphism forgets exactly the square.  So a statement about
`(toFGAlg ⋙ analytificationFGAlg).map` that cites only the object isomorphism has named an
ingredient that cannot prove it.

The proof is `CategoryTheory.NatTrans.naturality` and nothing else; what this declaration
contributes is the statement, in the vocabulary of the object isomorphism and of
`ComplexAnalytic.analytificationMap`, rather than of the natural isomorphism a consumer would
otherwise have to unfold to.

**The right-hand factor is written `ComplexAnalytic.analytificationMap` and not
`analytificationFunctor.map`**, which is not cosmetic.  The codomain of
`(analytificationFGAlgObjIso P).hom` is spelled `ComplexAnalytic.AnalyticSpace.analytification`,
the domain of `analytificationFunctor.map` is spelled `analytificationFunctor.obj`, and the two
are definitionally but not syntactically equal ; so the second spelling puts a different implicit
argument into any class applied to the composite, and instance search, which runs at `instances`
transparency, will not unfold either one to the other. -/
theorem analytificationFGAlgObjIso_naturality {P Q : Presentation.{u}} (ψ : P ⟶ Q) :
    (toFGAlg.{u} ⋙ analytificationFGAlg.{u}).map ψ ≫ (analytificationFGAlgObjIso.{u} Q).hom =
      (analytificationFGAlgObjIso.{u} P).hom ≫ analytificationMap.{u} ψ :=
  analytificationFGAlgCompIso.{u}.hom.naturality ψ

/-- **The functor on algebras, read at a presentation, is the presentation-level analytification
conjugated by the comparison isomorphism.**

This is `ComplexAnalytic.analytificationFGAlgObjIso_naturality` solved for the morphism, and it is
the form a consumer wants: every property of `ComplexAnalytic.analytificationMap` that is stable
under composing with isomorphisms transfers to `(toFGAlg ⋙ analytificationFGAlg).map` by
rewriting with it.  `Other/Oka/Analytification/FGAlgFinite.lean` reads finiteness across it; nothing
here is about finiteness, and nothing here is about the property.

The composite is written left-associated because that is what
`CategoryTheory.Iso.eq_comp_inv` produces, and the shape a rewrite leaves behind is part of what a
consumer has to work with. -/
theorem toFGAlg_comp_analytificationFGAlg_map {P Q : Presentation.{u}} (ψ : P ⟶ Q) :
    (toFGAlg.{u} ⋙ analytificationFGAlg.{u}).map ψ =
      ((analytificationFGAlgObjIso.{u} P).hom ≫ analytificationMap.{u} ψ) ≫
        (analytificationFGAlgObjIso.{u} Q).inv :=
  (Iso.eq_comp_inv _).mpr (analytificationFGAlgObjIso_naturality.{u} ψ)

end

end ComplexAnalytic

end
