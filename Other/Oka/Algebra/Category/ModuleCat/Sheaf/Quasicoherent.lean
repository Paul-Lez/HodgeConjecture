/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finiteness of presentations: binding, mapping, and restricting along a morphism of the site

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`; see `README.md` on
the mirror tree. Nothing here needs an import that file does not already have.

Three gaps in Mathlib's `SheafOfModules.Presentation` API, all of the same shape: a presentation
is transported by a construction that does not touch either index type, and
`SheafOfModules.Presentation.IsFinite` is finiteness of the two index types and nothing else, so
the finiteness wanted **is** the finiteness given ; but instance search does not see it, because
each transport is an ordinary definition.

**The instance to state is the one at the outer definition, and not the one at
`SheafOfModules.Presentation.map` underneath it.** An instance
`(P.map F η).IsFinite` was written, at the full generality of `map`, and then deleted: nothing can
consume it. Every consumer here ; `SheafOfModules.Presentation.restrict` below,
`SheafOfModules.Presentation.quasicoherentData`,
`AlgebraicGeometry.Scheme.Modules.presentationRestrict` ; is an ordinary definition wrapping the
`map`, and the two fields have to be given at the wrapper regardless.

**An earlier version of this paragraph said the reason was that search "does not reach the `map`
goal at all", and that is wrong; the conclusion is right and the correct reason is stronger.**
A `set_option trace.Meta.synthInstance true` run on the goal left by `unfold` shows Mathlib's
`SheafOfModules.Presentation.ofIsIso` instance firing and producing exactly the `map` goal ; so
search does reach it ; and then failing to unify that goal with an instance whose head prints
identically, the two `SheafOfModules.Presentation.map` applications differing in an argument that
is not reducibly defeq. Supplying the missing instance does not help: not as a `haveI`, and **not
as a global `instance` declared at exactly the shape `SheafOfModules.Presentation.restrict` uses**,
which is a stronger negative than delete-and-rebuild gives. A `tryResolve` line whose two sides
print the same is the signature of that, and it means no declaration is missing.

`SheafOfModules.QuasicoherentData.bind` refines a cover: given a cover on which `M` has
quasicoherent data, and, for each member, a cover of that member on which the restriction has
presentations, it produces quasicoherent data of `M` on the composite cover. Mathlib records that
the composite is quasicoherent data and **not** that it is finite when the pieces are, which is
what a construction producing local *finite* presentations needs on the way out.

## The proof is definitional, and that is the whole point

`SheafOfModules.Presentation.IsFinite` is finiteness of the two index types and nothing else, and
neither transport `bind` performs ; `SheafOfModules.Presentation.map` along the equivalence with
the iterated slice, then `SheafOfModules.Presentation.ofIsIso` ; touches an index type.
`SheafOfModules.Presentation.map_generators_I` and `SheafOfModules.Presentation.map_relations_I`
are the statements of that for the first, and both hold by `rfl`. So the finiteness wanted **is**
the finiteness given, up to definitional unfolding, and each field below is the source's
`SheafOfModules.GeneratingSections.IsFiniteType.finite` put back inside the constructor.

Instance search does not find it on its own, and **the blocker is
`SheafOfModules.QuasicoherentData.bind` itself and not the layer below it**. `bind` is an ordinary
definition, so search does not unfold it far enough to see the presentations it is assembled from,
and never reaches `SheafOfModules.Presentation.ofIsIso` or `SheafOfModules.Presentation.map` at
all. Mathlib does have an `IsFinite` instance for `ofIsIso` and none for `map`, but that gap is not
the cause: supplying the missing one ; three lines, since both index types are the source's ;
still leaves `infer_instance` failing on the composite goal. That is why this is stated rather
than left to the elaborator at the call site.

## Restricting a presentation along a morphism of the site

`SheafOfModules.Presentation.restrict` is the presentation-level analogue of this repository's
`SheafOfModules.GeneratingSections.restrict`: if `M` has a presentation over `Y`, it has one over
any `X` lying over `Y`. It is what an argument that refines a covering needs when the data being
carried is a presentation rather than a generating family ;
`SheafOfModules.IsFinitePresentation` hands out presentations over the members of *some* covering,
and a caller which wants them over a covering of its own choosing has to move them.

**There was a reason to doubt that it would be as cheap as the generating-sections version, and
it is worth recording that the doubt was well placed and wrong.**
`SheafOfModules.GeneratingSections.restrict` finishes with
`SheafOfModules.GeneratingSections.ofEpi`, and a presentation does *not* transport along an
epimorphism: one would need generators of the
kernel too. What makes it cheap is that the morphism `ofEpi` is applied to there is not merely an
epimorphism ; `SheafOfModules.overFunctorMap` is a natural *isomorphism*, built by
`CategoryTheory.NatIso.ofComponents` from `Iso.refl` ; and Mathlib already has the transport of a
presentation along an isomorphism, `SheafOfModules.Presentation.ofIsIso`. So the definition below
is the generating-sections one with `ofEpi` replaced by `ofIsIso`, under exactly the hypotheses
that one carries and no new one.

## A global presentation is a local one

`SheafOfModules.Presentation.isFinitePresentation` says that a sheaf with a finite **global**
presentation satisfies Mathlib's `SheafOfModules.IsFinitePresentation`, the class asserting a
finite presentation over the members of *some* covering. Mathlib has
`SheafOfModules.Presentation.quasicoherentData`, which puts a global presentation on the trivial
covering, and `SheafOfModules.Presentation.isQuasicoherent`, which reads off quasicoherence from
it; the finite version of the second is not there, and the instance it needs is the finite version
of `SheafOfModules.Presentation.map` above, because `quasicoherentData` presents `M.over X` as
`P.map` along a pushforward.

It is what makes a theorem stated at `SheafOfModules.IsFinitePresentation` strictly stronger than
the same theorem stated at a global presentation, rather than merely differently stated.

## A presentation exhibits its sheaf as a cokernel of free sheaves

`SheafOfModules.Presentation.cokernelIso` is the isomorphism `cokernel ψ ≅ M`, where
`ψ : free P.relations.I ⟶ free P.generators.I` is the map a presentation is built out of. Mathlib
has `SheafOfModules.Presentation.isColimit`, which says the relevant cofork is a colimit, and
`SheafOfModules.presentationOfIsCokernelFree`, which goes the other way; what is missing is the
isomorphism itself, which is what a consumer stated for a cokernel ; such as
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` ; actually wants. It is
`CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` and nothing else.

**The map is written out rather than named**, because at `v4.32.0` ; the revision
`lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` ; Mathlib does not name it either: the only
declaration anyone there wrote whose statement mentions it is
`SheafOfModules.Presentation.isColimit`, inside whose type it appears as
`(freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π`. Anything downstream has to spell
it the same way.

**The instrument is a scan of types over the environment of `import Mathlib` at that rev, and a
grep over the source could not have decided this.** Of that environment's declarations, **20**
have a type mentioning `SheafOfModules.freeHomEquiv` and **182** one mentioning
`CategoryTheory.Limits.kernel.ι` ; the two positive controls ; and exactly **two** mention both.

**The second of the two is why the sentence above says *anyone wrote*, and it is the rule's third
question answered *yes*.** `SheafOfModules.Presentation.map_relations_I` is generated by the
`@[simps!]` on `SheafOfModules.Presentation.map`; its statement as printed,
`(P.map F η).relations.I = P.relations.I`, names neither factor, and the composite is in the
elaborated type behind that notation, where each factor occurs **1596** times. So it is not a
name a consumer could spell, no scan of Mathlib's source can see it, and a scan of the
environment that did not say so would be reporting two written declarations where there is one.

**That clause read *because Mathlib does not name it either: it appears only inside the type of
`SheafOfModules.Presentation.isColimit`* until 2026-09-22**, with no version, no instrument and
no account of the generated second occurrence;
`git show c6bfc1f:Other/Oka/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` carries the retired
wording at `:113–114`, wrapped after *it appears*. **The claim is unchanged and only its warrant
is.**

## Main definitions

- `SheafOfModules.Presentation.restrict`
- `SheafOfModules.Presentation.cokernelIso`

## Main results

- `SheafOfModules.QuasicoherentData.isFinitePresentation_bind`
- `SheafOfModules.Presentation.isFinite_restrict`
- `SheafOfModules.Presentation.isFinitePresentation`
-/

@[expose] public section

universe u v' u'

open CategoryTheory Limits

namespace SheafOfModules

section bind

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`SheafOfModules.QuasicoherentData.bind` preserves finiteness of the presentations.**

Each presentation of the composite datum is one of the given presentations read through an
equivalence, and reading through an equivalence leaves the index types of the generators and of
the relations alone; `SheafOfModules.Presentation.IsFinite` asks for nothing else, so each field
is the corresponding field of the source. See the module docstring on why `infer_instance` does
not do this by itself. -/
instance QuasicoherentData.isFinitePresentation_bind (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, QuasicoherentData (M.over (X i)))
    [∀ i, (D i).IsFinitePresentation] :
    (QuasicoherentData.bind M X hX D).IsFinitePresentation where
  isFinite_presentation i :=
    { isFiniteType_generators :=
        ⟨GeneratingSections.IsFiniteType.finite (σ := ((D i.1).presentation i.2).generators)⟩
      isFiniteType_relations :=
        ⟨GeneratingSections.IsFiniteType.finite (σ := ((D i.1).presentation i.2).relations)⟩ }

end bind

section restrict

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasPullbacks C] [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A presentation restricts along a morphism of the site.**

If `M` has a presentation over `Y`, it has one over any `X` lying over `Y`. This is the
presentation-level analogue of this repository's `SheafOfModules.GeneratingSections.restrict`,
and it is that definition with `SheafOfModules.GeneratingSections.ofEpi` replaced by
`SheafOfModules.Presentation.ofIsIso`; see the module docstring for why that replacement is
available and why it is the whole content. The hypotheses are the ones
`SheafOfModules.GeneratingSections.restrict` already carries, `HasPullbacks C` being the
essential one: it is what makes `SheafOfModules.overMap` a left adjoint, hence colimit
preserving, hence eligible for `SheafOfModules.Presentation.map`. Nothing here is specific to a
topological site. -/
noncomputable def Presentation.restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (P : (M.over Y).Presentation) : (M.over X).Presentation :=
  (P.map (overMap R f) (overMapUnitIso f).symm).ofIsIso (((overFunctorMap R f).app M).hom)

/-- **Restriction preserves finiteness of a presentation**, because neither
`SheafOfModules.Presentation.map` nor `SheafOfModules.Presentation.ofIsIso` changes either index
type.

The two fields are the source's, exactly as for
`SheafOfModules.QuasicoherentData.isFinitePresentation_bind` and for the same reason. **They are
given rather than left to `unfold` followed by `infer_instance`**, which is what
`SheafOfModules.GeneratingSections.isFiniteType_restrict` does: after `unfold` the goal is
`SheafOfModules.Presentation.ofIsIso`'s, whose `IsFinite` instance Mathlib does state, and search
still fails on it ; measured, and not explained here. -/
instance Presentation.isFinite_restrict {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (P : (M.over Y).Presentation) [P.IsFinite] : (P.restrict f).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

end restrict

section globalPresentation

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The quasicoherent datum a finite global presentation puts on the trivial covering is
finite.**

`SheafOfModules.Presentation.quasicoherentData` presents `M.over X` as `P.map` along a pushforward
along an identity, and `SheafOfModules.Presentation.map` changes neither index type; the two
fields are the source's, as everywhere else in this file. -/
instance Presentation.isFinitePresentation_quasicoherentData {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] : P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation _ :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩ }

/-- **A sheaf with a finite global presentation is of finite presentation.**

The finite analogue of `SheafOfModules.Presentation.isQuasicoherent`, and the trivial covering is
the whole of it. It is stated because it is what relates the two shapes a theorem about finite
presentations can take ; a hypothesis of a global `SheafOfModules.Presentation` that is finite,
and Mathlib's class `SheafOfModules.IsFinitePresentation` ; and without it a theorem at the class
cannot be checked against a sheaf that was *built* as a cokernel of finite free sheaves, which is
the only kind this repository has on a `Spec`.

**Not an instance.** A `SheafOfModules.Presentation` is data and is not found by search, so this
would be a hypothesis-free instance that can never fire; it is applied at a presentation in
hand. -/
theorem Presentation.isFinitePresentation {M : SheafOfModules.{u} R} (P : M.Presentation)
    [P.IsFinite] : M.IsFinitePresentation :=
  ⟨⟨P.quasicoherentData, inferInstance⟩⟩

end globalPresentation

section cokernel

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A presentation exhibits its sheaf as the cokernel of a map of free sheaves.**

`SheafOfModules.Presentation.isColimit` says that the cofork on
`(freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π` with `P.generators.π` for its
projection is a colimit; this reads that off as an isomorphism from the chosen cokernel, by
`CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`. There is no content beyond that.

It is stated because the *cokernel* form is what consumers ask for. A theorem proved about
`cokernel ψ` for a map of finite free sheaves ; this repository's is
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` ; applies to a sheaf with a finite
presentation only through this isomorphism, and Mathlib provides the colimit but not the
isomorphism.

Note that the map is written out and not abbreviated, so a consumer has to spell it identically
or the two will not match. **Why Mathlib leaves it anonymous is measured once, in this file's
module docstring**, with the version, the scan of types and its two controls; this sentence
carries the consequence for a consumer and not the absence a second time.

**That clause read *Mathlib does not name it: it exists only inside the type of
`SheafOfModules.Presentation.isColimit`* until 2026-09-22**, asserting in a declaration docstring
what the module docstring's *A presentation exhibits its sheaf as a cokernel of free sheaves*
asserts as well; `git show c6bfc1f:Other/Oka/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`
carries the retired wording at `:260–262`, wrapped after *it exists only*. **The claim is
unchanged and only where it is warranted is.** -/
noncomputable def Presentation.cokernelIso {M : SheafOfModules.{u} R} (P : M.Presentation) :
    cokernel ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π) ≅ M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit

end cokernel

end SheafOfModules
