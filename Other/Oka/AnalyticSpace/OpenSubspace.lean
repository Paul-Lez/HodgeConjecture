/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.LocalIso
public import Other.Oka.AnalyticSpace.LocalModel
public import Other.Oka.AnalyticSpace.Restrict
public import Other.Oka.Geometry.RingedSpace.OpenImmersion

/-!
# An open subspace of a complex analytic space is a complex analytic space

`ComplexAnalytic.AnalyticSpace.restrict X U` is the open subspace of `X` on an open subset `U`:
the locally ringed space `X|U`, with the `ℂ`-algebra structure obtained by restricting sections,
and ; which is the content ; a chart at every one of its points.
`ComplexAnalytic.AnalyticSpace.ofRestrict` is its inclusion into `X`, as a morphism of complex
analytic spaces.

Until this file there was no `AnalyticSpace.restrict`: `LocallyRingedSpace.restrict` appeared
only *inside* the statement of what a chart is, never as a construction producing an analytic
space. (Checked by grep against `85b9251`: the only occurrence of the name was in
`Other/Oka/AnalyticSpace/Restrict.lean`'s docstring, saying it was missing.)

## Why it is not immediate

A chart of `X` at a point of `U` is a closed immersion `i : X|U₀ ⟶ ℂ^n|V` for some open
neighbourhood `U₀` of that point in `X`. What `AnalyticSpace.local_model` wants for `X|U` is a
chart on an open neighbourhood **inside `U`**, and its target must again be `ℂ^n` restricted to
an open subset **of `ℂ^n`**. Three things have to happen.

* **The chart must be shrunk to the overlap.** `i` is a closed embedding, hence an embedding, so
  the preimage of `U` in `X|U₀` is the preimage of some open `V'` of `ℂ^n|V`
  (`IsInducing.isOpen_iff`) ; and `ComplexAnalytic.IsCutOutBy.restrictOpen` then cuts out the
  overlap inside `ℂ^n|V|V'` by the restricted family. **`V'` is obtained rather than
  constructed**: the topological input is that an embedding's opens all come from the target.
* **The source has to be recognised as an open subspace of `X|U` rather than of `X|U₀`.** Both
  `X|U|W` and `X|U₀|W₀` are open immersions into `X` with the same image ; the overlap ; so
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` identifies them. No
  `restrictRestrict` is needed.
* **The target has to be flattened.** `ℂ^n|V|V'` and `ℂ^n|V''`, for `V''` the image of `V'` in
  `ℂ^n`, are again two open immersions into `ℂ^n` with the same image, so the same lemma
  applies; and `ComplexAnalytic.IsCutOutBy.iso_comp` transports the cut-out along it.

The `ℂ`-linearity of both identifications is `ComplexAnalytic.IsCLinearHom.of_comp`: each is a
morphism *over* the ambient space, and every algebra structure in sight is the ambient one
restricted, so linearity is contravariant functoriality of `Γ` applied to the factorisation. No
transport of algebra structures along an isomorphism is needed anywhere.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.restrict`: **an open subspace of a complex analytic space is a
  complex analytic space.**
- `ComplexAnalytic.AnalyticSpace.ofRestrict`: its inclusion, as a morphism of complex analytic
  spaces.
- `ComplexAnalytic.AnalyticSpace.restrictLE`: the inclusion of a smaller open subspace into a
  larger one, as a morphism of complex analytic spaces.
- `ComplexAnalytic.AnalyticSpace.liftRestrict`: **a morphism whose image lies in an open subspace
  factors through it**, as a morphism of complex analytic spaces. This is what builds a morphism
  whose *target* is an open subspace; `restrictLE` is its special case at an inclusion.
- `ComplexAnalytic.AnalyticSpace.restrictHom`: **a morphism restricted to the preimage of an open
  subset of the target**, as a morphism of complex analytic spaces. This is the other way to land
  in an open subspace, and it asks nothing of the image: `liftRestrict` keeps the source and needs
  the image to lie in `V`, this shrinks the source to the preimage of `V` instead.
- `ComplexAnalytic.AnalyticSpace.liftTop`: **the section of the inclusion at an open that is
  everything**, which is `ComplexAnalytic.AnalyticSpace.liftRestrict` at the identity.
- `ComplexAnalytic.AnalyticSpace.resΓ`: the restriction of a global section of `𝒪_X` to an open
  subspace.
- `ComplexAnalytic.AnalyticSpace.clopenCompl`: **the complement of an open subspace whose carrier
  is closed**, as an open subspace, with `ComplexAnalytic.AnalyticSpace.coe_clopenCompl` for its
  carrier. The closedness is what makes the complement open, so this cannot be written without it.

## Main results

- `ComplexAnalytic.exists_local_model_restrict`: the chart of `X|U` at a point, which is the
  `local_model` field of `AnalyticSpace.restrict`.
- `ComplexAnalytic.restrict_eq_ofCutOut`: **an open subspace carrying a chart on the whole of
  itself is, on the nose, the `ComplexAnalytic.AnalyticSpace.ofCutOut` that chart presents** ; an
  equality of analytic spaces and not an isomorphism, so a statement about local models applies to
  it with nothing to transport.
- `ComplexAnalytic.exists_restrict_eq_ofCutOut`: **every point has an open neighbourhood on which
  the space is a local model in that sense**, which is `ComplexAnalytic.restrict_eq_ofCutOut` at
  the chart the `local_model` field supplies.
- `ComplexAnalytic.AnalyticSpace.range_base_ofRestrict`: **the image of the inclusion of an open
  subspace is that open subset**, which is the form a factorisation asks its range hypothesis in;
  that declaration's own docstring names the two constructions which ask for it.
- `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`: **the inclusion of an open subspace
  is an isomorphism on stalks**, at the spelling a caller of `ofRestrict` holds. Mathlib has the
  statement; what this adds is a discrimination-tree key, exactly as
  `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` does one field further in.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`: **the inclusion of an open subspace is a
  local isomorphism.**
- `ComplexAnalytic.AnalyticSpace.restrictHom_comp`: **restricting a composite is composing the
  restrictions.**
- `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`: **a morphism whose base is
  an embedding restricts to a finite morphism over any open subset of its image** ; the shape an
  *open* immersion needs, since it is finite over such a subset and is not finite at all.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`: **a local isomorphism restricted over an
  open subset of the target is a local isomorphism**, with no hypothesis on the morphism or the
  open beyond that. Unlike the bullet above this needs nothing of the base map's image, because
  both fields are local at a point and a restriction changes neither.
- `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`: **the inclusion of an open subspace is a
  monomorphism**, reflected along the faithful forgetful functor.
- `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`: **it is an isomorphism when the
  open is everything.**
- `ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top`: **a morphism is its own
  restriction over `⊤`, conjugated by two inclusions** ; which is what carries a property of
  `ComplexAnalytic.AnalyticSpace.restrictHom f ⊤` back to `f`.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top`: **a morphism whose restriction over
  `⊤` is finite is finite**, which is that transfer at the one property two `## What is not here`
  bullets elsewhere were asking about.
- `ComplexAnalytic.AnalyticSpace.isClosedEmbedding_ofRestrict_of_isClosed`: **the inclusion of an
  open subspace whose carrier is closed is a closed embedding**, which is
  `IsClosed.isClosedEmbedding_subtypeVal` at a base map that is `Subtype.val` by `rfl`.
- `ComplexAnalytic.AnalyticSpace.isFinite_ofRestrict_of_isClosed`: **and it is finite.** The
  closedness is the whole of the content: the base map is injective, so the fibre half holds for
  any open at all, and it is the closed half that fails for a general one.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_of_isClosed`: **and finite étale**, the
  second field being `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`, which asks nothing.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_comp`: **that inclusion followed by a
  finite étale morphism is finite étale.** The mathematics is composition and the binders are the
  point: the property is an explicit argument because its consumer holds it at a spelling instance
  search cannot match.
- `ComplexAnalytic.AnalyticSpace.isClosed_clopenCompl`: **the complement of an open subspace is
  closed**, so the complement of a clopen one is clopen and
  `ComplexAnalytic.AnalyticSpace.isFinite_ofRestrict_of_isClosed` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_of_isClosed` apply to it.

## Why `Other/Oka/AnalyticSpace/LocalIso.lean` is imported here, when no import was forced

`ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` needs `ofRestrict`, defined here, and
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, defined there. **That does not mean one of the two
files had to import the other, and an earlier draft of this paragraph said it did.** Three files
already reach both: `Other/Oka/AnalyticSpace/CoveringSpace.lean`, `Other/Oka/AnalyticSpace/Degree.lean` and
`Other/Oka/AnalyticSpace/SigmaFiniteEtale.lean`. Any of them would have cost **nothing**. **None of the
three is where the instance is used**, and that draft said the first of them was.

**This paragraph also said the import "can be undone by moving one instance", and that is no
longer true.** `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` below is a second
declaration in this file whose statement mentions `ComplexAnalytic.AnalyticSpace.IsLocalIso`, and
it has a consumer **under `Other/Oka/`**, `Other/Oka/Analytification/StandardEtaleFiniteEtale.lean`. So
undoing the edge now means moving two declarations and giving that consumer an import it does not
have. The edge is still cheap, for the reason measured below; what it is no longer is free.

**It is here because both of its ingredients are.** The first field is
`Topology.IsOpenEmbedding.isLocalHomeomorph` at `U.isOpenEmbedding`; the second is
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict` three declarations above, found by
`inferInstance` ; a lemma that exists *only* to put Mathlib's statement at the
discrimination-tree key a caller of `ofRestrict` holds. Putting its one consumer in another file
is how such a lemma comes to look unused. The statement is also about open subspaces and not about
covering spaces: a `## Main results` bullet in `Other/Oka/AnalyticSpace/CoveringSpace.lean` reading *the
inclusion of an open subspace is a local isomorphism* would be a claim in the wrong file.

**What the edge costs, and what the reverse would have.** Transitive closure of each file's import
list, expanding and counting **only modules under `Other/Oka/` and `Mathlib/`** ; other packages are
leaves and are dropped, which is the convention `scripts/import_cost.py` states as *"Mathlib
modules only"*, widened to this repository:

* this file, **3095 → 3100**, and the five are named: `Oka.AnalyticSpace.LocalIso`,
  `Oka.AnalyticSpace.Finite`, `Mathlib.Topology.IsLocalHomeomorph`,
  `Mathlib.Topology.OpenPartialHomeomorph.Composition`, `Mathlib.Topology.SeparatedMap`;
* `Other/Oka/AnalyticSpace/LocalIso.lean`, **2160 → 3100**, since this file reaches
  `Oka.AnalyticSpace.Coherent` and the whole local-model apparatus.

**Five against 940 is the comparison, and it is what decided the direction.**

**Read the closures off Lean's own environment rather than off a parser over the header lines.**
The figures above are `lake env lean` on a scratch file whose imports are the list being measured,
with

```
open Lean in
#eval show CoreM Unit from do
  let ms := (← getEnv).header.moduleNames
  IO.println (ms.filter fun m => (`Oka).isPrefixOf m || (`Mathlib).isPrefixOf m).size
```

That is not fussiness. An earlier draft of this section gave 3075 and 2141 from a parser of its
own, and three hand-written parsers ; that one and two reviewers' ; disagreed with each other and
with Lean before the environment settled it. Three traps account for the spread and none of them
announces itself: matching the word *import* outside the header picks it up inside a docstring
code block and pulls in the whole of Mathlib; **seventy** Mathlib header lines carry a trailing
*shake* comment ; `grep -rlE '^module[ \t]+--' .lake/packages/mathlib/Mathlib/`, in five
spellings ; so a parser comparing the stripped line against the module keyword stops at each of
them, and one of the seventy is `Mathlib/Tactic/Common.lean`, which by itself takes the tactic
modules with it; and this Mathlib writes both *public meta import* and *import all*, which a
pattern anchored on the bare keyword misses.
`scripts/import_cost.py` cannot be used instead ; it resolves only under `Mathlib/`, and neither
of these two files is a mirror file.

**All four figures are counterfactual, so recomputing them here needs the import above removed
first** ; left in place the first reads `3100 → 3100`, and the second `3101`, one more, because
the union then contains `Oka.AnalyticSpace.LocalIso` itself. The five-module delta is what the
decision rests on and it is convention-invariant; the baselines are not.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

open AlgebraicGeometry.LocallyRingedSpace in
/-- **An open subspace of a complex analytic space has a chart at every point**, which is the
`local_model` field of `ComplexAnalytic.AnalyticSpace.restrict`. See the module docstring for
the three steps. -/
theorem exists_local_model_restrict (X : AnalyticSpace.{u}) (U : X.Opens)
    (x : X.toLocallyRingedSpace.restrict U.isOpenEmbedding) :
    ∃ (W : OpenNhds x) (n k : ℕ) (V : Opens (complexAffineSpace.{u} n))
      (c : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).restrict W.1.isOpenEmbedding ⟶
        (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
      (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)),
      IsCutOutBy c f ∧
        IsCLinearHom c
          ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).resAlgMap
            (X.toLocallyRingedSpace.resAlgMap X.algebraMap U) W.1)
          (constantsAlgMap n V) := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := X.local_model x.1
  set ιU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding with hιU
  set ι₀ := X.toLocallyRingedSpace.ofRestrict U₀.1.isOpenEmbedding with hι₀
  -- `i` is an embedding, so the preimage of `U` in `X|U₀` comes from an open of `ℂ^n|V`.
  obtain ⟨t, ht, htpre⟩ := hcut.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.1
    ((Opens.map ι₀.base).obj U).2
  set V' : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding) := ⟨t, ht⟩ with hV'
  set W₀ : Opens (X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    (Opens.map i.base).obj V' with hW₀
  have hW₀eq : W₀ = (Opens.map ι₀.base).obj U := Opens.ext htpre
  set W : Opens (X.toLocallyRingedSpace.restrict U.isOpenEmbedding) :=
    (Opens.map ιU.base).obj U₀.1 with hW
  have hxW : x ∈ W := U₀.2
  -- `X|U|W` and `X|U₀|W₀` are open immersions into `X` with the same image.
  have hrange : Set.range (((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).ofRestrict
        W.isOpenEmbedding ≫ ιU).base) =
      Set.range (((X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).ofRestrict
        W₀.isOpenEmbedding ≫ ι₀).base) := by
    refine Eq.trans (range_ofRestrict_comp X.toLocallyRingedSpace U W) ?_
    refine Eq.trans ?_ (range_ofRestrict_comp X.toLocallyRingedSpace U₀.1 W₀).symm
    rw [hW₀eq]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y.1, hy⟩, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y.1, hy⟩, y.2, rfl⟩
  -- and so are `ℂ^n|V|V'` and `ℂ^n|V''`.
  set V'' : Opens (complexAffineSpace.{u} n) := V.isOpenEmbedding.isOpenMap.functor.obj V' with hV''
  have hrange₂ : Set.range ((((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).ofRestrict
        V'.isOpenEmbedding ≫ (complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base) =
      Set.range (((complexAffineSpace.{u} n).ofRestrict V''.isOpenEmbedding).base) := by
    refine Eq.trans (range_ofRestrict_comp (complexAffineSpace.{u} n) V V') ?_
    exact (LocallyRingedSpace.range_ofRestrict (complexAffineSpace.{u} n) V'').symm
  set e₁ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange with he₁def
  set e₂ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange₂ with he₂def
  have he₁ : IsCLinearHom e₁.hom
      ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).resAlgMap
        (X.toLocallyRingedSpace.resAlgMap X.algebraMap U) W)
      ((X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).resAlgMap
        (X.toLocallyRingedSpace.resAlgMap X.algebraMap U₀.1) W₀) :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)
      ((isCLinearHom_ofRestrict _ _ W).comp (isCLinearHom_ofRestrict X.toLocallyRingedSpace _ U))
      ((isCLinearHom_ofRestrict _ _ W₀).comp
        (isCLinearHom_ofRestrict X.toLocallyRingedSpace _ U₀.1))
  have he₂ : IsCLinearHom e₂.hom
      (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).resAlgMap
        (constantsAlgMap n V) V') (constantsAlgMap n V'') :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange₂)
      ((isCLinearHom_ofRestrict _ _ V').comp (isCLinearHom_ofRestrict_constants n V))
      (isCLinearHom_ofRestrict_constants n V'')
  exact ⟨⟨W, hxW⟩, n, k, V'', (e₁.hom ≫ restrictHom i V') ≫ e₂.hom,
    fun j ↦ (LocallyRingedSpace.Γ.map e₂.inv.op).hom (restrictSections V' f j),
    ((hcut.restrictOpen V').comp_iso e₁).iso_comp e₂,
    (he₁.comp (isCLinearHom_restrictHom hlin V')).comp he₂⟩

namespace AnalyticSpace

/-- **An open subspace of a complex analytic space is a complex analytic space.**

The underlying locally ringed space is `X|U` and the `ℂ`-algebra structure is the ambient one
restricted; the charts are `ComplexAnalytic.exists_local_model_restrict`. -/
def restrict (X : AnalyticSpace.{u}) (U : X.Opens) : AnalyticSpace.{u} where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict U.isOpenEmbedding
  algebraMap := X.toLocallyRingedSpace.resAlgMap X.algebraMap U
  local_model := exists_local_model_restrict X U

/-- The underlying locally ringed space of an open subspace. Not a `simp` lemma: rewriting with
it inside the type of `base_ofRestrict` is what takes that lemma out of simp normal form. -/
lemma restrict_toLocallyRingedSpace (X : AnalyticSpace.{u}) (U : X.Opens) :
    (X.restrict U).toLocallyRingedSpace = X.toLocallyRingedSpace.restrict U.isOpenEmbedding :=
  rfl

/-- The `ℂ`-algebra structure of an open subspace. -/
lemma restrict_algebraMap (X : AnalyticSpace.{u}) (U : X.Opens) :
    (X.restrict U).algebraMap = X.toLocallyRingedSpace.resAlgMap X.algebraMap U :=
  rfl

/-- **The inclusion of an open subspace, as a morphism of complex analytic spaces.**

It is `ℂ`-linear because the algebra structure on the subspace was defined by restricting
sections, which is `ComplexAnalytic.isCLinearHom_ofRestrict`. -/
def ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) : X.restrict U ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding,
    isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap U⟩

@[simp]
lemma base_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) (x : X.restrict U) :
    (X.ofRestrict U).toLRSHom.base x = x.1 :=
  rfl

/-- **The image of the inclusion of an open subspace is that open subset.**

`ComplexAnalytic.AnalyticSpace.base_ofRestrict` says what the underlying map does to a point and
this says what it does to the whole of the source, which is the form a factorisation hypothesis
takes: `ComplexAnalytic.AnalyticSpace.liftRestrict` asks for a range containment and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` asks for one against exactly this
range.

**The proof is `Subtype.range_val` and not a rewrite of `…base_ofRestrict`**, because the
underlying map *is* `Subtype.val` definitionally rather than up to that lemma ; which is why
`…base_ofRestrict` itself is `rfl`. Stating it through the point lemma would elaborate the same
term and generate a match lemma for the destructuring; this way the module's contribution to
`scripts/DumpOkaDecls.lean` is one row and not two.

**The coercion on the right is `(U : Set X)` and not `U`**, which is the same spelling
`ComplexAnalytic.AnalyticSpace.liftRestrict` uses for its hypothesis, so a caller chaining the two
needs no rewriting between them. -/
lemma range_base_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) :
    Set.range ((X.ofRestrict U).toLRSHom.base : X.restrict U → X) = (U : Set X) :=
  Subtype.range_val

/-- **The inclusion of an open subspace is an isomorphism on stalks**, at the spelling a caller
who built the morphism with `ComplexAnalytic.AnalyticSpace.ofRestrict` actually holds.

Mathlib's `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_stalkMap_isIso` is the same statement,
and it is **not** found here: the two terms are `rfl`-equal and headed by
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` and by
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` respectively, so they are different
discrimination-tree keys. This is the same seam that
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` exists for, one field further
in, and it is settled the same way ; by naming the instance at the spelling that is used. -/
instance isIso_stalkMap_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) (x : X.restrict U) :
    IsIso ((X.ofRestrict U).toLRSHom.stalkMap x) :=
  inferInstanceAs (IsIso
    ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).stalkMap x))

/-- **The inclusion of an open subspace is a local isomorphism.**

Both fields are already here and neither needs a hypothesis. The underlying map is the inclusion
of an open set, so `Topology.IsOpenEmbedding.isLocalHomeomorph` gives the first; the second is
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict` above, found by instance search ; which
is what that lemma exists for, Mathlib's own statement being at a different
discrimination-tree key.

It is **not** finite étale in general, and nothing here says otherwise: the inclusion of the
punctured line into the line is an open subspace whose inclusion is not a closed map. -/
instance isLocalIso_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) :
    AnalyticSpace.IsLocalIso (X.ofRestrict U) where
  isLocalHomeomorph := U.isOpenEmbedding.isLocalHomeomorph
  isIso_stalkMap _ := inferInstance

/-- **The inclusion of a smaller open subspace into a larger one**, as a morphism of complex
analytic spaces.

The underlying morphism of locally ringed spaces is
`AlgebraicGeometry.LocallyRingedSpace.restrictLE`. It is `ℂ`-linear because it is a morphism
*over* `X` and both algebra structures are the ambient one restricted, which is exactly the
hypothesis of `ComplexAnalytic.IsCLinearHom.of_comp`; no transport of algebra structures along
anything is needed. -/
def restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    X.restrict V ⟶ X.restrict W :=
  ⟨X.toLocallyRingedSpace.restrictLE h,
    IsCLinearHom.of_comp (LocallyRingedSpace.restrictLE_fac _ h)
      (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap V)
      (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap W)⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.restrictLE`. -/
lemma toLRSHom_restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    (X.restrictLE h).toLRSHom = X.toLocallyRingedSpace.restrictLE h :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.restrictLE` is a morphism over `X`.** This, rather than the
morphism itself, is what every use of it consumes. -/
lemma restrictLE_fac (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    X.restrictLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  forgetToLocallyRingedSpace.map_injective (LocallyRingedSpace.restrictLE_fac _ h)

/-- **The restriction of a morphism to the preimage of an open subset of the target**, as a
morphism of complex analytic spaces.

`ComplexAnalytic.restrictHom` at the underlying morphisms, which is where every fact about it
lives ; `ComplexAnalytic.base_restrictHom` for the underlying map,
`ComplexAnalytic.stalkMap_restrictHom_eq'` for the stalk map,
`ComplexAnalytic.isClosedEmbedding_base_restrictHom` and
`ComplexAnalytic.IsCutOutBy.restrictOpen` for what a chart keeps. It is `ℂ`-linear by
`ComplexAnalytic.isCLinearHom_restrictHom`, whose two algebra structures are the two
`ComplexAnalytic.AnalyticSpace.restrict` puts on the two open subspaces, so nothing is
transported.

Unlike `ComplexAnalytic.AnalyticSpace.liftRestrict` this does not ask the image of `A` to lie in
`V`: it shrinks the *source* to the preimage instead. Neither is a special case of the other.

**The name shadows `ComplexAnalytic.restrictHom` inside `namespace AnalyticSpace`** ; sixteen
files, and not the bulk of the development, which is written one namespace up in
`ComplexAnalytic`, where the bare name still resolves to the locally-ringed-space one. That is why
exactly one existing call site needed qualifying rather than dozens. A use of the bare name inside
`AnalyticSpace` now means this one; the locally-ringed-space one has to be written
`ComplexAnalytic.restrictHom`, as it is in `Other/Oka/AnalyticSpace/HolomorphicMapGeneral.lean`. That is
the price of the name matching the one it wraps, and the mismatch is a type error rather than a
silent change of meaning: the two have different sources and targets.

**Count the sixteen with `grep -rlE '^namespace (ComplexAnalytic\.)?AnalyticSpace'`.** Nine of
them open `namespace AnalyticSpace` and seven open `namespace ComplexAnalytic.AnalyticSpace`
directly; the bare name is shadowed in both, and a grep for the first form alone answers nine and
is the natural thing to reach for. **No denominator is given, on purpose**: the file count moves
with every module added, and this figure is here to say the hazard is confined rather than to
give a ratio. -/
def restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    A.restrict ((Opens.map f.toLRSHom.base).obj V) ⟶ B.restrict V :=
  ⟨ComplexAnalytic.restrictHom f.toLRSHom V, isCLinearHom_restrictHom f.isCLinear V⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.restrictHom`. -/
lemma toLRSHom_restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    (restrictHom f V).toLRSHom = ComplexAnalytic.restrictHom f.toLRSHom V :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.restrictHom` is a morphism over `f`.** -/
lemma restrictHom_fac {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    restrictHom f V ≫ B.ofRestrict V = A.ofRestrict ((Opens.map f.toLRSHom.base).obj V) ≫ f :=
  forgetToLocallyRingedSpace.map_injective (ComplexAnalytic.restrictHom_fac f.toLRSHom V)

/-- **Restricting a composite is composing the restrictions.**

`ComplexAnalytic.restrictHom_comp` one category down, reflected along the faithful
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` ; which is all a morphism of analytic
spaces needs, since the `ℂ`-linearity field is a proposition and equality of the two underlying
morphisms is equality of the two. The two sides have definitionally the same source; see the
locally-ringed-space statement for why its proof is a term rather than a `rw` chain. -/
lemma restrictHom_comp {A B C : AnalyticSpace.{u}} (f : A ⟶ B) (h : B ⟶ C) (V : C.Opens) :
    restrictHom (f ≫ h) V =
      restrictHom f ((Opens.map h.toLRSHom.base).obj V) ≫ restrictHom h V :=
  forgetToLocallyRingedSpace.map_injective
    (ComplexAnalytic.restrictHom_comp f.toLRSHom h.toLRSHom V)

/-- **A morphism whose base is an embedding restricts to a finite morphism over any open subset of
its image.**

`ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range` and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`, and nothing between them.

**It is stated because the unrestricted morphism is usually not finite and this is not a weakening
of a stronger fact.** The case it exists for is an *open* immersion: `X.ofRestrict U` is never a
closed map unless `U` is clopen, so `IsFinite` of it is false in general, and yet its restriction
over a `V` contained in `U` is finite ; the two ranges then agree and the restricted map is a
homeomorphism. That is what
`Other/Oka/Analytification/StandardEtaleFiniteness.lean` spends, and it is why the hypothesis is on `V`
rather than on the morphism.

The import that makes this statable is `Other/Oka/AnalyticSpace/LocalIso.lean`'s, whose closure carries
`Other/Oka/AnalyticSpace/Finite.lean`; the section above prices that edge for a different reason and
this is a second consumer of it. -/
theorem isFinite_restrictHom_of_subset_range {A B : AnalyticSpace.{u}} {f : A ⟶ B}
    (hemb : IsEmbedding (f.toLRSHom.base : A → B)) {V : B.Opens}
    (hV : (V : Set B) ⊆ Set.range (f.toLRSHom.base : A → B)) :
    IsFinite (restrictHom f V) :=
  isFinite_of_isClosedEmbedding _
    (ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range hemb hV)

/-- **A local isomorphism restricted over an open subset of the target is a local isomorphism.**

Nothing about the morphism is asked and nothing about the open subset is: both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` are conditions at a point, and a restriction changes
the point's neighbourhoods on neither side. **That is what separates this from
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` above**, whose hypothesis is
there because the morphism that statement is about is not itself finite: the inclusion of an open
subspace restricts to a finite morphism only over a `V` inside its image, and is a local
isomorphism over every `V`.

**That sentence gave the reason as *finiteness is not local on the target*, until 2026-09-14**,
when `Other/Oka/AnalyticSpace/LocalAtTarget.lean` proved that finiteness **is** local on the target:
`ComplexAnalytic.AnalyticSpace.isFinite_iff_restrictHom`, over an open cover of the target with no
hypothesis on the morphism. The forward half of that had been unconditional since
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom`, which asks nothing of `V` either. **The
contrast the sentence draws is unchanged**, and it is a contrast about one morphism at one open:
what was wrong was the property named as the reason for it.

**The topological field is the commuting square and not a lemma about restrictions.**
`ComplexAnalytic.base_restrictHom` says `ofRestrict V ∘ restrictHom f V = f ∘ ofRestrict (f⁻¹ V)`
on points; the right-hand side is a local homeomorphism because both factors are, and
`IsLocalHomeomorph.of_comp` then peels off the left factor, which is one because
`Topology.IsOpenEmbedding.isLocalHomeomorph` applies to `V.isOpenEmbedding`. The continuity
`of_comp` asks for is the base map's own.

**The stalk field is a term and not a `rw`, and that is forced.**
`ComplexAnalytic.stalkMap_restrictHom_eq'` already writes the stalk map as an isomorphism, then
`f`'s stalk map, then an isomorphism, so instance search closes it once that factorisation is in
the goal ; but `rw` fails to find the pattern, because `V : B.Opens` elaborates at the `toTopCat`
spelling of the carrier while the lemma wants `Opens ↑B.toTopCat` reached through
`toPresheafedSpace`. That seam runs through this corner of the tree and
`Other/Oka/Analytification/StandardEtaleFiniteness.lean` records two more instances of it. -/
theorem isLocalIso_restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) [IsLocalIso f] (V : B.Opens) :
    IsLocalIso (restrictHom f V) where
  isLocalHomeomorph := by
    have hsq : ((B.ofRestrict V).toLRSHom.base : B.restrict V → B) ∘
        ((restrictHom f V).toLRSHom.base : _ → B.restrict V) =
        (f.toLRSHom.base : A → B) ∘
          ((A.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base : _ → A) :=
      funext fun x ↦ ComplexAnalytic.base_restrictHom f.toLRSHom V x
    refine IsLocalHomeomorph.of_comp (g := ((B.ofRestrict V).toLRSHom.base : B.restrict V → B))
      ?_ V.isOpenEmbedding.isLocalHomeomorph
      (restrictHom f V).toLRSHom.base.hom.continuous
    rw [hsq]
    exact (IsLocalIso.isLocalHomeomorph (f := f)).comp
      ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding.isLocalHomeomorph
  isIso_stalkMap x :=
    (ComplexAnalytic.stalkMap_restrictHom_eq' f.toLRSHom V x).symm ▸
      (inferInstance : IsIso ((ComplexAnalytic.restrictStalkEquiv f.toLRSHom V x).hom ≫
        f.toLRSHom.stalkMap ((A.toLocallyRingedSpace.ofRestrict
            ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding).base x) ≫
          (A.toLocallyRingedSpace.ofRestrict
            ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding).stalkMap x))

/-- **The restriction of a global section of `𝒪_X` to an open subspace**, as a global section of
`𝒪_{X|U}`.

An `abbrev` rather than a `def`, so that a caller holding
`(LocallyRingedSpace.Γ.map (X.ofRestrict U).op).hom g` ; which is how a computation with
`ComplexAnalytic.AnalyticSpace.coordPullback` produces it ; does not have to unfold anything to
recognise it. -/
abbrev resΓ (X : AnalyticSpace.{u}) (U : X.Opens) (g : X.presheaf.obj (op ⊤)) :
    (X.restrict U).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).op).hom g

/-- **Restricting twice is restricting once.**

Spelled at the level of locally ringed spaces throughout ; `Γ.map` of the underlying morphism
rather than of the morphism of analytic spaces. That is not cosmetic: the same proof written
against `X.restrictLE h` and `X.ofRestrict W` as morphisms of analytic spaces **exceeds the
default heartbeat budget**, because unifying `(f ≫ g).toLRSHom` with `f.toLRSHom ≫ g.toLRSHom`
forces the category instance open at every step.

**Measured 2026-08-31**, by replacing the `congrArg` below with one whose motive is over
`X.restrict V ⟶ X` and whose argument is `ComplexAnalytic.AnalyticSpace.restrictLE_fac` rather
than `AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac`:
`(deterministic) timeout at whnf, maximum number of heartbeats (200000)`, reached in 20s.
**200000 is the budget in force** ; `lakefile.toml` sets no `maxHeartbeats`, so a figure of a
million, which this paragraph gave until today, names a budget nobody set.

**Unlike the seam in `Other/Oka/AnalyticSpace/Glue.lean`, this one is not known to be merely
expensive.** There the same counterfactual under `set_option maxHeartbeats 0` finishes, at about
eight times the file; here it was still elaborating after 21m29s and 5.4GB and was stopped, so
nothing measured says it terminates and nothing says it does not. -/
lemma resΓ_restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W)
    (g : X.presheaf.obj (op ⊤)) :
    (LocallyRingedSpace.Γ.map (X.toLocallyRingedSpace.restrictLE h).op).hom (X.resΓ W g) =
      X.resΓ V g :=
  (LocallyRingedSpace.Γ_map_comp_apply (X.toLocallyRingedSpace.restrictLE h)
      (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding) g).symm.trans
    (congrArg (fun m : X.toLocallyRingedSpace.restrict V.isOpenEmbedding ⟶
        X.toLocallyRingedSpace ↦ (LocallyRingedSpace.Γ.map m.op).hom g)
      (LocallyRingedSpace.restrictLE_fac X.toLocallyRingedSpace h))

/-- **A morphism whose image lies in an open subspace factors through it**, as a morphism of
complex analytic spaces.

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict` at the underlying morphisms. It is `ℂ`-linear
for the same reason `ComplexAnalytic.AnalyticSpace.restrictLE` is, and by the same lemma: the
factorisation makes it a morphism *over* `X`, `φ` is `ℂ`-linear by assumption and
`ComplexAnalytic.AnalyticSpace.ofRestrict` by construction, so
`ComplexAnalytic.IsCLinearHom.of_comp` applies. Nothing is transported.

**This is the construction that builds a morphism whose *target* is an open subspace.** Before it,
everything here produced morphisms *out* of a restriction ; `ofRestrict`, `restrictLE`,
`ComplexAnalytic.localisationProj` ; and `restrictLE` was the only one landing in a restriction,
at the special case where the source is one too and the map is an inclusion. -/
noncomputable def liftRestrict {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) : Z ⟶ X.restrict V :=
  ⟨LocallyRingedSpace.liftRestrict φ.toLRSHom V h,
    IsCLinearHom.of_comp (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom V h)
      φ.isCLinear (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap V)⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.liftRestrict`. -/
lemma toLRSHom_liftRestrict {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) :
    (liftRestrict φ V h).toLRSHom = LocallyRingedSpace.liftRestrict φ.toLRSHom V h :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.liftRestrict` is a factorisation of `φ`.** This, rather than
the morphism itself, is what a caller consumes ; in particular it is how the underlying map of the
lift is computed, since the lift is opaque and the composite is not. -/
lemma liftRestrict_fac {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) :
    liftRestrict φ V h ≫ X.ofRestrict V = φ :=
  forgetToLocallyRingedSpace.map_injective (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom V h)

/-! ### The open subspace at an open that is everything -/

/-- **The inclusion of an open subspace is a monomorphism.**

`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful and a faithful functor
*reflects* monomorphisms, so this is `AlgebraicGeometry.LocallyRingedSpace.ofRestrict`'s own
`Mono` instance carried back. **Nothing is transported and no `ℂ`-linearity is checked**: a
monomorphism is a cancellation property of the category, not structure on the morphism.

**The `show` is essential and is the seam this file's neighbours already record.**
`forgetToLocallyRingedSpace.map (X.ofRestrict U)` and
`X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding` are `rfl`-equal and are *different
discrimination-tree keys*, so `infer_instance` finds the Mathlib instance only at the second
spelling. `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso`'s docstring calls that its third
appearance; this is the fourth. **The step is a `change` and not a `show`**: the two spellings are
`rfl`-equal but not syntactically equal, so `linter.style.show` fires and `lake build --wfail`
turns the warning into an error, which `lake env lean` on a scratch file does not.

Before this, `Mono` of an inclusion was available in this repository only through
`AlgebraicGeometry.LocallyRingedSpace`, so a cancellation argument at the analytic level had to
be routed through the underlying morphisms by hand. -/
instance mono_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) : Mono (X.ofRestrict U) := by
  refine forgetToLocallyRingedSpace.{u}.mono_of_mono_map (f := X.ofRestrict U) ?_
  change Mono (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)
  infer_instance

/-- **The section of `ComplexAnalytic.AnalyticSpace.ofRestrict` at an open that is everything**:
`ComplexAnalytic.AnalyticSpace.liftRestrict` applied to the identity, whose range condition is
then `Set.range id ⊆ Set.univ`.

**The hypothesis is `(U : Set X) = Set.univ` and not `U = ⊤`, deliberately**, and it is the
difference between this being usable and not. A caller holding
`(Opens.map f.toLRSHom.base).obj ⊤` ; which is what
`ComplexAnalytic.AnalyticSpace.restrictHom` produces at `⊤` ; can discharge the set-level equality
by `rfl` and keep the open it already has. Stating it at `U = ⊤` instead forces the caller to
transport `X.restrict ((Opens.map f.toLRSHom.base).obj ⊤)` to `X.restrict ⊤`, and **those two are
`rfl`-equal but not type-correct at `instances` transparency**: the resulting goal elaborates and
then `rw` reports *"Did not find an occurrence of the pattern"* with an application type mismatch
underneath. Taking the open as a parameter removes the transport rather than discharging it. -/
noncomputable def liftTop (X : AnalyticSpace.{u}) (U : X.Opens) (hU : (U : Set X) = Set.univ) :
    X ⟶ X.restrict U :=
  liftRestrict (𝟙 X) U (by rw [hU]; exact Set.subset_univ _)

/-- **`ComplexAnalytic.AnalyticSpace.liftTop` is a section of the inclusion**, which is
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac` at the identity, **as a term and not as a
`simpa [liftTop]`**: naming the definition asks Lean to generate its equation lemma, and here it
planted two rows in this module's declaration dump ; `ComplexAnalytic.AnalyticSpace.liftTop.eq_1`
and a `congr_simp` under `ComplexAnalytic.AnalyticSpace.liftRestrict`, a definition declared thirty
lines above. The term goes through definitional unfolding and generates neither. -/
theorem liftTop_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) (hU : (U : Set X) = Set.univ) :
    liftTop X U hU ≫ X.ofRestrict U = 𝟙 X :=
  liftRestrict_fac (𝟙 X) U (by rw [hU]; exact Set.subset_univ _)

/-- **The inclusion of an open subspace at an open that is everything is an isomorphism.**

One composite is `ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict`; the other follows from it by
cancelling the mono `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`, which is why that instance is
above rather than elsewhere.

**Not an `instance`**: `hU` occurs in no instance-implicit argument and in no index of the
conclusion, so Lean rejects the declaration outright ; *"1 argument that cannot be inferred using
typeclass synthesis"*. Callers use `haveI`. -/
theorem isIso_ofRestrict_of_eq_univ (X : AnalyticSpace.{u}) (U : X.Opens)
    (hU : (U : Set X) = Set.univ) : IsIso (X.ofRestrict U) := by
  refine ⟨liftTop X U hU, ?_, liftTop_ofRestrict X U hU⟩
  rw [← cancel_mono (X.ofRestrict U), Category.assoc, liftTop_ofRestrict, Category.comp_id,
    Category.id_comp]

/-- **`ComplexAnalytic.AnalyticSpace.liftTop` is an isomorphism**, being the two-sided inverse of
an inclusion that `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ` inverts. Stated
separately from that theorem because two consumers need this side of it ;
`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` below and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top` in
`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean`, so only one of the two is below ; and for the same
reason neither can be an `instance`: `hU` is inferable from nothing. -/
theorem isIso_liftTop (X : AnalyticSpace.{u}) (U : X.Opens) (hU : (U : Set X) = Set.univ) :
    IsIso (liftTop X U hU) := by
  refine ⟨X.ofRestrict U, liftTop_ofRestrict X U hU, ?_⟩
  rw [← cancel_mono (X.ofRestrict U), Category.assoc, liftTop_ofRestrict, Category.comp_id,
    Category.id_comp]

/-- **A morphism is its own restriction over `⊤`, conjugated by two inclusions.**

`ComplexAnalytic.AnalyticSpace.restrictHom_fac` composed with
`ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict`. Both inclusions are isomorphisms by
`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`, so this is what carries a property of
`ComplexAnalytic.AnalyticSpace.restrictHom f ⊤` to the same property of `f` whenever the property
respects isomorphisms and is stable under composition.

**`h` is `rfl`** at every `f` ; the preimage of `⊤` is `Set.univ` on the nose ; and is taken as a
hypothesis rather than proved here so that the open stays the one
`ComplexAnalytic.AnalyticSpace.restrictHom` produced, for the reason
`ComplexAnalytic.AnalyticSpace.liftTop`'s docstring gives. -/
theorem liftTop_comp_restrictHom_top {A B : AnalyticSpace.{u}} (f : A ⟶ B)
    (h : ((Opens.map f.toLRSHom.base).obj (⊤ : B.Opens) : Set A) = Set.univ) :
    liftTop A _ h ≫ restrictHom f ⊤ ≫ B.ofRestrict ⊤ = f := by
  rw [restrictHom_fac f ⊤, ← Category.assoc, liftTop_ofRestrict, Category.id_comp]

/-- **A morphism whose restriction over `⊤` is finite is finite.**

`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` conjugated by the two isomorphisms,
with `ComplexAnalytic.AnalyticSpace.isFinite_comp` and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isIso` doing the transfer. **`IsFinite` is not a
`CategoryTheory.MorphismProperty` in this repository** ; only the class is ; so this is
`inferInstance` over `ComplexAnalytic.AnalyticSpace.isFinite_comp`, which *is* an instance, rather
than the `RespectsIso` route the finite étale version in
`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean` takes. The two `haveI`s are what instance search cannot
find on its own: `ComplexAnalytic.AnalyticSpace.isFinite_of_isIso` is a theorem and not an
instance, so the isomorphisms have to be fed in by hand.

**This is the version a `## What is not here` bullet was about**, and it was about finiteness
rather than about finite étaleness:
`Other/Oka/Analytification/StandardEtaleFiniteness.lean`'s *"nothing in this repository relates the two
at `V = ⊤`"* names `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`.
The finite étale statement alone would not have retired it. -/
theorem isFinite_of_restrictHom_top {A B : AnalyticSpace.{u}} (f : A ⟶ B)
    (hfin : IsFinite (restrictHom f (⊤ : B.Opens))) : IsFinite f := by
  set U : A.Opens := (Opens.map f.toLRSHom.base).obj (⊤ : B.Opens) with hUdef
  have h : (U : Set A) = Set.univ := rfl
  have hB : ((⊤ : B.Opens) : Set B) = Set.univ := rfl
  haveI : IsIso (B.ofRestrict (⊤ : B.Opens)) := isIso_ofRestrict_of_eq_univ B ⊤ hB
  haveI : IsIso (liftTop A U h) := isIso_liftTop A U h
  haveI : IsFinite (restrictHom f (⊤ : B.Opens)) := hfin
  haveI : IsFinite (B.ofRestrict (⊤ : B.Opens)) := isFinite_of_isIso _
  haveI : IsFinite (liftTop A U h) := isFinite_of_isIso _
  have hp : IsFinite (liftTop A U h ≫ restrictHom f ⊤ ≫ B.ofRestrict ⊤) := inferInstance
  rwa [liftTop_comp_restrictHom_top] at hp

/-- **The inclusion of an open subspace whose carrier is closed is a closed embedding.**

The base map of `ComplexAnalytic.AnalyticSpace.ofRestrict` *is* `Subtype.val` ; that is what
`ComplexAnalytic.AnalyticSpace.base_ofRestrict` records, and it holds by `rfl` ; so the whole of
this is `IsClosed.isClosedEmbedding_subtypeVal`.

**The hypothesis is on the carrier as a set and not on `U` as an element of the lattice of
opens**, because that is the form `IsClosed` is stated in and the form
`ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` supplies. Nothing here asks `U` to be
non-empty or proper, and the two extreme opens are both allowed: at `⊥` the source is empty and
at `⊤` the inclusion is an isomorphism
(`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`). -/
theorem isClosedEmbedding_ofRestrict_of_isClosed (X : AnalyticSpace.{u}) (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    IsClosedEmbedding ((X.ofRestrict U).toLRSHom.base : X.restrict U → X) :=
  hU.isClosedEmbedding_subtypeVal

/-- **The inclusion of an open subspace whose carrier is closed is finite.**

The closedness is the content and the fibres are not: the base map is injective, so a fibre is a
subsingleton and `Set.Finite.to_subtype` finishes it from the preimage of a singleton. The closed
half is what fails for a general open subspace ; the inclusion of the punctured line into the
line has image open and not closed.

**Both fields are stated at the `ComplexAnalytic.AnalyticSpace.IsFinite` spelling and neither goes
through `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding`**, which asks for a
second morphism this statement does not have. -/
theorem isFinite_ofRestrict_of_isClosed (X : AnalyticSpace.{u}) (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsFinite (X.ofRestrict U) where
  isClosedMap := (isClosedEmbedding_ofRestrict_of_isClosed X U hU).isClosedMap
  finite_fiber y :=
    Set.Finite.to_subtype ((Set.finite_singleton y).preimage
      (isClosedEmbedding_ofRestrict_of_isClosed X U hU).injective.injOn)

/-- **The inclusion of a clopen subspace is finite étale.**

The two fields are `ComplexAnalytic.AnalyticSpace.isFinite_ofRestrict_of_isClosed` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`,
which asks nothing at all. So the hypothesis of this statement is the closedness alone: an open
subspace is always a local isomorphism over the ambient space, and what a clopen carrier buys is
the finiteness.

**This is where `⊥` and `⊤` stop being the interesting opens.** A cover with a disconnected
total space has clopen subsets that are neither empty nor everything ;
`ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` says the image of a member of a
disjoint union is one ; and it is at those that the consumer in
`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean` has content. -/
theorem isFiniteEtale_ofRestrict_of_isClosed (X : AnalyticSpace.{u}) (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsFiniteEtale (X.ofRestrict U) where
  isFinite := isFinite_ofRestrict_of_isClosed X U hU
  isLocalIso := inferInstance

/-- **A clopen subspace inclusion followed by a finite étale morphism is finite étale.**

Mathematically this is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp` at
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_ofRestrict_of_isClosed` and nothing else. **It is a
named declaration because of how its consumer holds the finite étale hypothesis on `g`, and the
shape of the binders is the whole point of it.**

`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean`'s objects live in a comma category, where a structure map
has type `(𝟭 AnalyticSpace).obj A.left ⟶ (CategoryTheory.Functor.fromPUnit X).obj A.right`. The
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` an object carries therefore has those two terms in
its implicit arguments; they are `rfl`-equal to `A.left` and to `X` and are **different
discrimination-tree keys**, so putting that hypothesis in scope with a `haveI` does not answer the
search `ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp` runs. Taking it as an **explicit
argument** does, because unification discharges the defeq that search will not look through.

**This is the seam `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`'s docstring
describes from the other side, and the repair it names does not work here.** Fixing the source
with a named argument leaves the failure unchanged, reported as a synthesis failure against a goal
that prints identically to the hypothesis; fixing the target as well leaves it unchanged too.
Moving the hypothesis out of the instance binders is what removes it. -/
theorem isFiniteEtale_ofRestrict_comp {X Y : AnalyticSpace.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) (g : X ⟶ Y) (hg : IsFiniteEtale g) :
    IsFiniteEtale (X.ofRestrict U ≫ g) :=
  haveI := hg
  haveI := isFiniteEtale_ofRestrict_of_isClosed X U hU
  isFiniteEtale_comp _ _

/-- **The complement of a clopen subspace, as an open subspace.**

`ComplexAnalytic.AnalyticSpace.clopenCompl U hU` is the open whose carrier is the complement of
`U`'s. **The hypothesis is what makes it open**, so it cannot be built from `U` alone; and it is
again clopen, by `ComplexAnalytic.AnalyticSpace.isClosed_clopenCompl`, which needs no
hypothesis because the complement of an open set is closed.

So the pair `U`, `clopenCompl U hU` is a partition of the ambient space into two clopen opens, and
that is the shape the direct-summand axiom of a Galois category asks a monomorphism's image to sit
in. -/
def clopenCompl {X : AnalyticSpace.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) : X.Opens :=
  ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩

/-- The carrier of `ComplexAnalytic.AnalyticSpace.clopenCompl`. -/
@[simp]
lemma coe_clopenCompl {X : AnalyticSpace.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) :
    ((clopenCompl U hU : X.Opens) : Set X) = (U : Set X)ᶜ :=
  rfl

/-- **The complement of a clopen subspace is closed**, so it is clopen too.

`U.isOpen.isClosed_compl`, and it reads no hypothesis: the complement of an *open* set is closed
whatever else is true of it. The `hU` in the binders is there only because
`ComplexAnalytic.AnalyticSpace.clopenCompl` cannot be written without it. -/
theorem isClosed_clopenCompl {X : AnalyticSpace.{u}} (U : X.Opens) (hU : IsClosed (U : Set X)) :
    IsClosed ((clopenCompl U hU : X.Opens) : Set X) :=
  U.isOpen.isClosed_compl

end AnalyticSpace

/-! ### The open subspace on a chart *is* the local model that chart presents -/

variable {n k : ℕ} {X : AnalyticSpace.{u}} {U : X.Opens}
  {V : Opens (complexAffineSpace.{u} n)}
  {i : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶
    (complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}

/-- **An open subspace carrying a chart on the whole of itself is, on the nose, the local model
that chart presents.**

The two locally ringed spaces are the same by `rfl`:
`ComplexAnalytic.AnalyticSpace.restrict`'s is `X|U` and
`ComplexAnalytic.AnalyticSpace.ofCutOut`'s is the source of the chart, which is that space. The
two `ℂ`-algebra structures are the same **because that is what `hlin` says**:
`ComplexAnalytic.IsCLinearHom i α β` is `∀ c, Γ.map i.op (β c) = α c`, `ofCutOut`'s structure is
`Γ.map i.op` composed with the constants and `restrict`'s is the ambient structure restricted, so
the hypothesis is the equation of the two read pointwise. The only remaining component of an
analytic space is `ComplexAnalytic.AnalyticSpace.local_model`, which is a `Prop`;
`ComplexAnalytic.AnalyticSpace.ext'` is what carries it.

**It is an equality and not an isomorphism, and that is the point.** A statement whose subject is
a `ComplexAnalytic.AnalyticSpace.ofCutOut` applies to `X.restrict U` with nothing to transport
across. The consumer this was written for is the fibre product of two local models, taxis #1830,
whose pull request is approved and **unmerged** at the commit that adds this paragraph ; so no
declaration of it is cited here, and the sentence that will cite one belongs to the push that
uses it.

The hypotheses are exactly the two conjuncts the `local_model` field of
`ComplexAnalytic.AnalyticSpace` carries, which is what makes
`ComplexAnalytic.exists_restrict_eq_ofCutOut` below one `obtain`. -/
theorem restrict_eq_ofCutOut (hcut : IsCutOutBy i f)
    (hlin : IsCLinearHom i (X.toLocallyRingedSpace.resAlgMap X.algebraMap U)
      (constantsAlgMap n V)) :
    X.restrict U = AnalyticSpace.ofCutOut hcut :=
  AnalyticSpace.ext' rfl (heq_of_eq (RingHom.ext fun c ↦ (hlin c).symm))

/-- **Every point of a complex analytic space has an open neighbourhood on which the space is a
local model, on the nose.**

`ComplexAnalytic.AnalyticSpace.local_model` unfolded and fed to
`ComplexAnalytic.restrict_eq_ofCutOut`. What the field gives is a chart *datum*; what this adds
is the identification of the space that datum presents with the open subspace it is a chart of,
which is the half `ComplexAnalytic.exists_local_model_restrict` above discards.

**This is stated in the `ComplexAnalytic` namespace and not in `ComplexAnalytic.AnalyticSpace`**,
as `ComplexAnalytic.exists_local_model_restrict` is: inside a declaration whose name begins
`AnalyticSpace.` the tokens `complexAffineSpace` and `Opens` resolve to
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` and `ComplexAnalytic.AnalyticSpace.Opens`
rather than to the locally ringed space and to `TopologicalSpace.Opens`, and the statement below
would then be about a different `ℂ^n`. -/
theorem exists_restrict_eq_ofCutOut (X : AnalyticSpace.{u}) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (n k : ℕ) (V : Opens (complexAffineSpace.{u} n))
      (i : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶
        (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
      (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤))
      (hcut : IsCutOutBy i f), X.restrict U = AnalyticSpace.ofCutOut hcut := by
  obtain ⟨U, n, k, V, i, f, hcut, hlin⟩ := X.local_model x
  exact ⟨U.1, U.2, n, k, V, i, f, hcut, restrict_eq_ofCutOut hcut hlin⟩

end ComplexAnalytic

end

end
