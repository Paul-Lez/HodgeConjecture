/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Other.Oka.Algebra.Module.FinitePresentation
public import Other.Oka.RingTheory.Finiteness.Basic

/-!
# Restricting a module along an open immersion: generators, presentations, finiteness of sections

Material for `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`; see `README.md` on the mirror tree.

**Upstreaming all of it adds eight modules to that target's closure of 2264**, and the eight are
attributable to the results that need them. Every figure below is `scripts/import_cost.py` against
that target; which result needs which import is read off what stops elaborating when the import is
dropped, rather than off the import list.

* `AlgebraicGeometry.Scheme.Modules.overEquivUnitIso`, `generatingSectionsRestrict` and
  `finite_I_generatingSectionsRestrict` need
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, which the target does not import: **3**,
  that module together with `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` and
  `Mathlib.CategoryTheory.Limits.Preserves.SigmaConst`.
* `presentationOverRestrict` and `isFinite_presentationOverRestrict` need
  `SheafOfModules.Presentation` and `SheafOfModules.Presentation.ofIsIso`, which are Mathlib's own
  and are declared in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: **5**, the three
  above plus that module and `Mathlib.CategoryTheory.Sites.CoversTop.Over`.
* `AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_restrict` needs
  `Module.FinitePresentation` itself, from `Mathlib.Algebra.Module.FinitePresentation`: **3**, that
  module with `Mathlib.RingTheory.Finiteness.Projective` and
  `Mathlib.RingTheory.TensorProduct.Finite`.
* `AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict` needs
  `Module.Finite.of_ringEquiv`, which this repository states in the mirror of
  `Mathlib/RingTheory/Finiteness/Basic.lean` ; a file already in that closure: **0**.

**Those four figures do not add up.** `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
imports `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, so the 3 sits *inside* the 5 rather
than beside it, while the 3 for `Mathlib.Algebra.Module.FinitePresentation` is independent of both.
The total is 8 and not 11, and **3 is the bottom of a range and not the price of the file**.

Two things the 8 does not say. The two `of_ringEquiv` lemmas do not travel upstream with this
file: each belongs to the mirror target it is stated in, and the 3 and the 0 above are what
importing those two targets would cost this one. And
`Oka.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` is imported for Mathlib's file underneath it
and for none of its own declarations: replacing that import by
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` leaves every declaration here elaborating
unchanged, so nothing from that mirror has to go up with these results.

Facts about `AlgebraicGeometry.Scheme.Modules.restrict`, all of them bookkeeping in the sense that
none uses anything about the sheaves beyond what Mathlib already proves, and all of them
prerequisites for reading a statement about an open subscheme as a statement about the ambient
scheme. They come in two pairs, one for generating sections and one for presentations, and the
two members of each pair say the same thing about the two levels of finiteness this development
uses.

* **`AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrict`** turns generating sections of
  `M.over U` ; which live over the *slice site* `Over U` of `X.Opens` ; into generating sections
  of `M.restrict U.ι`, which live over the open subscheme `U`'s own site. The index type is
  unchanged, so "finitely many generators" survives.
* **`AlgebraicGeometry.Scheme.Modules.presentationOverRestrict`** is the same for a
  `SheafOfModules.Presentation`, built the same way out of the same equivalence, with
  `SheafOfModules.Presentation.ofIsIso` in place of
  `SheafOfModules.GeneratingSections.equivOfIso`.
* **`AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`** says that finiteness
  of `Γ(M.restrict f, U)` over `Γ(V, U)` is finiteness of `Γ(M, f ''ᵁ U)` over `Γ(W, f ''ᵁ U)`.
* **`AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_restrict`** is the same
  statement for `Module.FinitePresentation`, with `Module.FinitePresentation.of_ringEquiv` in
  place of `Module.Finite.of_ringEquiv`; every word of the note on the first applies unchanged
  to the second, including the `letI`.

## The site comparison is Mathlib's, not this file's

`SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent` are stated with `M.over X` for
objects `X` of the site, so every generating family this development can obtain over a
distinguished open arrives on the slice site. Reading it on the open subscheme needs an
equivalence of the two sites, and **that equivalence is already in Mathlib**:
`AlgebraicGeometry.Scheme.Modules.overEquiv` and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. All this file adds is the unit comparison
`overEquiv` needs before `SheafOfModules.GeneratingSections.map` will accept it, and that
comparison is assembled from `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` and
`overFunctorEquiv` ; `(SheafOfModules.unit X.ringCatSheaf).over U` and
`SheafOfModules.unit (X.ringCatSheaf.over U)` are the same object, by `rfl`.

## The two actions on one carrier

`AlgebraicGeometry.Scheme.Modules.restrict_obj` says `Γ(M.restrict f, U)` and `Γ(M, f ''ᵁ U)` are
the same type ; Mathlib proves it by `rfl` and asks that it not be used, preferring the
isomorphism `restrictAppIso`, which is `Iso.refl`. What genuinely differs is the ring acting:
`Γ(V, U)` on the left and `Γ(W, f ''ᵁ U)` on the right, matched by the isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso` rather than by any map of carriers.
`Module.Finite.of_ringEquiv` is exactly that situation, which is why it is stated in the mirror of
`Mathlib/RingTheory/Finiteness/Basic.lean` rather than here;
`Module.FinitePresentation.of_ringEquiv` is its sibling and is in the mirror of
`Mathlib/Algebra/Module/FinitePresentation.lean` for the same reason.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.overEquivUnitIso`
- `AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrict`
- `AlgebraicGeometry.Scheme.Modules.presentationOverRestrict`

## Main results

- `AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`
- `AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_restrict`
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- **The unit comparison for `AlgebraicGeometry.Scheme.Modules.overEquiv`**: the structure sheaf
of the open subscheme `U`, read as a module over itself, is the image under `overEquiv U` of the
structure sheaf of `X` read over the slice site.

This is what `SheafOfModules.GeneratingSections.map` asks for on top of preservation of colimits,
and it is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` composed with
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`; the `overFunctor` half needs no comparison at
all, since `(SheafOfModules.unit X.ringCatSheaf).over U` **is** `SheafOfModules.unit
(X.ringCatSheaf.over U)` ; the two are the same term, and this file relies on that. -/
def overEquivUnitIso {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅
      (overEquiv.{u} U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (restrictUnitIso.{u} U.ι).symm ≪≫
    ((overFunctorEquiv.{u} U).app (SheafOfModules.unit X.ringCatSheaf)).symm

/-- **Generating sections over the slice site become generating sections of the restriction.**

`SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent` produce generating families of
`M.over U`; a statement about the open subscheme `U` needs them for `M.restrict U.ι`. The functor
that moves them is `AlgebraicGeometry.Scheme.Modules.overEquiv`, an equivalence and so
colimit-preserving, and `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` identifies its
composite with `overFunctor` as `restrictFunctor U.ι`.

The index type is not touched: `(generatingSectionsRestrict M U σ).I` is `σ.I` by `rfl`, which is
what the instance below records. -/
def generatingSectionsRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (σ : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso ((overFunctorEquiv.{u} U).app M)
    (σ.map (overEquiv.{u} U).functor (overEquivUnitIso U))

/-- **Restricting does not change the index type of a generating family**, so finitely many
generators over the slice site are finitely many generators of the restriction. -/
instance finite_I_generatingSectionsRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (σ : (M.over U).GeneratingSections) [Finite σ.I] :
    Finite (generatingSectionsRestrict M U σ).I :=
  inferInstanceAs (Finite σ.I)

/-- **A presentation over the slice site becomes a presentation of the restriction.**

The presentation-level analogue of
`AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrict`, and it is that definition with
`SheafOfModules.GeneratingSections.equivOfIso` replaced by
`SheafOfModules.Presentation.ofIsIso`: the same equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv` carries the presentation, and the same natural
isomorphism `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` lands it at `M.restrict U.ι`.

**Named `presentationOverRestrict` rather than `presentationRestrict`**, which Mathlib already
uses (`AlgebraicGeometry.Scheme.Modules.presentationRestrict`) for restriction along a morphism
of *schemes*. The two are different operations: that one moves a presentation along an open
immersion `Y ⟶ X`, this one crosses from the slice site `Over U` of `X.Opens` to the open
subscheme `U`'s own site. An argument that starts from `SheafOfModules.IsFinitePresentation`
needs both, in that order. -/
def presentationOverRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) : (M.restrict U.ι).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u, u, u} ((overFunctorEquiv.{u} U).app M).hom
    (P.map (overEquiv.{u} U).functor (overEquivUnitIso U))

/-- **Restricting does not change either index type of a presentation**, so a finite presentation
over the slice site is a finite presentation of the restriction.

The two fields are the source's, as in `SheafOfModules.Presentation.isFinite_restrict` and for the
same reason: `AlgebraicGeometry.Scheme.Modules.presentationOverRestrict` is an ordinary
definition, so instance search does not see the two constructions it is built from. -/
instance isFinite_presentationOverRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] : (presentationOverRestrict M U P).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

/-- **Finiteness of the sections of a restriction is finiteness of the sections of the original.**

The carriers are the same type (`AlgebraicGeometry.Scheme.Modules.restrict_obj`, and
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`); the rings acting are
`Γ(V, U)` and `Γ(W, f ''ᵁ U)`, matched by `AlgebraicGeometry.Scheme.Hom.appIso`. So this is
`Module.Finite.of_ringEquiv`, and the hypothesis it wants is exactly
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` read elementwise ; after which the
proof is that lemma applied, with no rewriting.

The two `Module` instances are named rather than searched for. They exist at the spelling
`Γ(M.restrict f, U)`, and search will not find them at `Γ(M, f ''ᵁ U)`: the two are defeq but not
reducibly so ; `exact x` compiles across them and `with_reducible exact x` is a type mismatch ;
and search unifies at reducible transparency.

**Use `letI` and not `haveI` for the first of them.** With `haveI` the proof fails, and not with
a synthesis error: the given instance *is* used, and
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` then sits at a different `Module`
structure from the one `•` elaborates at.
`set_option backward.isDefEq.respectTransparency false` does not rescue it either. Why `letI`
succeeds is not established here and no explanation should be read into this note; what
reproduces is the above, and `AlgebraicGeometry.Scheme.Modules.module_finite_Γ_of_isAffine`
hands over the same kind of instance across the same two spellings the same way. -/
theorem module_finite_sections_of_restrict {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (M : W.Modules) (U : V.Opens) [Module.Finite Γ(V, U) Γ(M.restrict f, U)] :
    Module.Finite Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U) := by
  letI : Module Γ(V, U) Γ(M, f ''ᵁ U) := inferInstanceAs (Module Γ(V, U) Γ(M.restrict f, U))
  haveI : Module.Finite Γ(V, U) Γ(M, f ''ᵁ U) :=
    inferInstanceAs (Module.Finite Γ(V, U) Γ(M.restrict f, U))
  exact Module.Finite.of_ringEquiv (f.appIso U).symm.commRingCatIsoToRingEquiv
    fun a n ↦ smul_restrictAppIso_hom_apply f M U a n

/-- **Finite presentation of the sections of a restriction is finite presentation of the sections
of the original.**

`AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict` with
`Module.FinitePresentation.of_ringEquiv` in place of `Module.Finite.of_ringEquiv`. Everything that
note records holds here word for word ; the same two spellings of one carrier, the same two rings
matched by `AlgebraicGeometry.Scheme.Hom.appIso`, the same named instances, and the same `letI`,
which is again essential: with `haveI` the given instance is used and
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` then sits at a different `Module`
structure from the one `•` elaborates at. -/
theorem finitePresentation_sections_of_restrict {V W : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] (M : W.Modules) (U : V.Opens)
    [Module.FinitePresentation Γ(V, U) Γ(M.restrict f, U)] :
    Module.FinitePresentation Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U) := by
  letI : Module Γ(V, U) Γ(M, f ''ᵁ U) := inferInstanceAs (Module Γ(V, U) Γ(M.restrict f, U))
  haveI : Module.FinitePresentation Γ(V, U) Γ(M, f ''ᵁ U) :=
    inferInstanceAs (Module.FinitePresentation Γ(V, U) Γ(M.restrict f, U))
  exact Module.FinitePresentation.of_ringEquiv (f.appIso U).symm.commRingCatIsoToRingEquiv
    fun a n ↦ smul_restrictAppIso_hom_apply f M U a n

end

end AlgebraicGeometry.Scheme.Modules
