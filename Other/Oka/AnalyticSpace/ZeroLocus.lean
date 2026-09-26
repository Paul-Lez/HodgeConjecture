/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.CutOutCompose
public import Other.Oka.AnalyticSpace.Local
public import Other.Oka.Geometry.RingedSpace.ZeroLocus

/-!
# The zero locus of finitely many global sections of a complex analytic space

For `X` a complex analytic space and `s : Fin p → Γ(X, 𝒪_X)`, the closed subspace of `X` cut out
by the `s r` is again a complex analytic space, and the inclusion is a monomorphism of
`ComplexAnalytic.AnalyticSpace`. The underlying locally ringed space is
`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace` ; the common zero set carrying the
inverse image of the sheafified quotient `𝒪_X ⧸ (s)` ; so nothing about the space is chosen here;
what is proved is that it has charts.

**The ambient space is arbitrary, and that is the whole of what this file costs.**
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` cuts a *local model* down by sections that are
already pullbacks of sections of that model's own ambient `ℂ^n|V`, so the appended family which
presents the result is handed to it. Here the ambient carries only charts and the `s r` are its
own global sections, which no chart need extend: a chart of `X` at a point is a closed immersion
into some `ℂ^n|V`, and there is no reason for `s r` to be the pullback of anything on that
`ℂ^n|V` beyond a neighbourhood of the point.

## The name to be careful with

`ComplexAnalytic.AnalyticSpace.zeroLocus` is a **different** construction in this same namespace.
Its ambient is fixed by its signature to an open subset of some `ℂ^n`, and it is what
`ComplexAnalytic.AnalyticSpace.analytification` is defined from. The two names are kept apart
because the constructions are: `ComplexAnalytic.AnalyticSpace.zeroLocus` is a local model by
`ComplexAnalytic.isLocalModel_zeroLocus`, and **nothing below makes
`ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` a local model** ; what is proved of it here is
that it has charts, `ComplexAnalytic.hasLocalModels_zeroLocusSubspace`, which is what an object of
`ComplexAnalytic.AnalyticSpace` needs and is strictly weaker.
No statement here relates them, and `## What is not here` says what a statement relating them
would have to say.

**The clause replaced here read `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` `is a local
model only when X is` until 2026-09-07, and it was false when written rather than falsified later,
so this is a correction and not one of this repository's dated records.** *Only when* is the
single implication *the zero locus is a local model, therefore so is `X`*, **that implication is
false**, and its converse is **not settled here**; nothing below states either. The structure
`ComplexAnalytic.AnalyticSpace` has two fields, `ComplexAnalytic.AnalyticSpace.algebraMap` and
`ComplexAnalytic.AnalyticSpace.local_model`, and neither is a separation hypothesis, while a local
model is closed in an open subspace of `ℂ^n` and so is Hausdorff; a zero locus of an `X` that is
not Hausdorff can therefore be a local model while `X` is not one, which kills *only when* ; and
that is the whole of what retiring the clause needs, because the retired clause is that one
implication.

**The converse is where this record used to say more than it shows.** A global section of a local
model need not lift to its ambient `ℂ^n|V` ; the observation the paragraph ending `beyond a
neighbourhood of the point` makes ; so `X` being a local model does not *by that route* present
its zero loci. **That is the failure of an argument and not a counterexample**: it exhibits no
space, and deciding the converse either way wants either a theorem extending global sections of
`X` to the ambient or a witness admitting no such extension, and this file has neither.
**This paragraph read *Neither direction of it holds and neither is in the tree* and called the
retired clause *the retired biconditional* until 2026-09-07.** *Only when* is one implication and
not two, and the summary said the converse was false where the sentence beginning *A global
section of a local model need not lift* gives a route that fails and no space.

**The repair is to say what the file has**, which is charts and not a local-model statement, and
neither direction is filed as a thing to prove: they are statements about spaces this file
constructs nothing for.

## The route

Fix `z` in the zero locus and write `x` for its image in `X`.

1. **The ambient chart.** `X.local_model x` gives an open `U₀ ∋ x`, a closed immersion
   `i : X|U₀ ⟶ ℂ^n|V` and a family `f` cutting it out.
2. **The local lift.** `AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family` at
   `i ≫ (ℂ^n).ofRestrict V` ; composed with the inclusion, so that the lifted sections live on an
   open `A` of `ℂ^n` and no comparison of `(ℂ^n|V)|A` with `ℂ^n|A` is ever needed, which is the
   design choice `ComplexAnalytic.AnalyticSpace.exists_chartLift` makes for the same reason ;
   returns `A`, sections `t` over it, and an open `B` of `X|U₀` on which the pullbacks of the `t`
   agree with the `s r`. **Its stalk-surjectivity hypothesis costs nothing**: it is
   `ComplexAnalytic.IsCutOutBy.surjective_stalkMap` of the datum step 1 already produced,
   composed with an inclusion of an open subspace, which is an isomorphism on stalks.
3. **The intersection.** `B` is only *contained* in the preimage of `A`, and what the next step
   needs is an open of `ℂ^n|V` whose preimage **is** `B`. The chart is an embedding, so
   `Topology.IsInducing.isOpen_iff` writes `B` as the preimage of some open `O`, and `V'` is
   taken to be `O` meet the preimage of `A`: its preimage is `B` because `B` is already inside
   the second factor, and it lies inside `A` so that the `t` restrict to it.
4. **Two restrictions and one composition.** `ComplexAnalytic.IsCutOutBy.restrictOpen` at `V'`
   shrinks the ambient chart to a closed immersion `X|U₀|B ⟶ (ℂ^n|V)|V'`, and the same lemma
   twice over shrinks the inclusion of the zero locus to a closed immersion into `X|U₀|B`. The
   sections cutting the second one out are the pullbacks of the first one's target sections ;
   which is exactly step 2's equation, moved across `ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ`
   ; so `ComplexAnalytic.IsCutOutBy.comp_append` composes them.
5. **Two changes of chart.** `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`
   identifies the source with an open subspace of the zero locus itself and the target with an
   open subspace of `ℂ^n`, and `ComplexAnalytic.IsCutOutBy.comp_iso` and
   `ComplexAnalytic.IsCutOutBy.iso_comp` carry the datum across them. The `ℂ`-linearity of both
   is `ComplexAnalytic.IsCLinearHom.of_comp` against the factorisation each isomorphism comes
   with, which is what `ComplexAnalytic.exists_local_model_restrict` already does for an open
   subspace.

**Nothing is glued and no cover is used.** `ComplexAnalytic.HasLocalModels` is a statement at each
point separately and the `ℂ`-algebra structure is pulled back along the inclusion, which is
defined on the whole zero locus; `ComplexAnalytic.HasLocalModels.of_iSup_eq_top` is not invoked
below.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace`: **the zero locus of finitely many global
  sections of a complex analytic space, as a complex analytic space.** The name is the locally
  ringed space one, and the underlying locally ringed space is that one on the nose.
- `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceι`: **its closed immersion into `X`**, as a
  morphism of complex analytic spaces rather than of locally ringed spaces.

## Main results

- `ComplexAnalytic.hasLocalModels_zeroLocusSubspace`: **the zero locus has charts**, which is the
  content of this file and the whole of its proof.
- `ComplexAnalytic.AnalyticSpace.isCutOutBy_zeroLocusSubspaceι`: the immersion carries its
  cut-out datum, at the analytic level.
- `ComplexAnalytic.AnalyticSpace.mono_zeroLocusSubspaceι`: **the immersion is a monomorphism**, so
  it cancels in `ComplexAnalytic.AnalyticSpace` itself; that declaration's own docstring names the
  functor a cancellation would otherwise be routed through.
- `ComplexAnalytic.AnalyticSpace.pullbackΓ_zeroLocusSubspaceι_eq_zero`: the cutting sections
  pull back to zero.

## What is not here

* **No fibre product, and no `CategoryTheory.Limits.HasPullbacks`.**
  `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` **fails** at the
  commit that adds this file, on my own run, with the category positional so that it is fixed by
  the statement and not by a named argument. What this supplies is the ingredient
  `Other/Oka/AnalyticSpace/CutOutCompose.lean`'s header records as missing for the fibre product of two
  local models over a third: the differences of the two composites to `ℂ^p` are sections of the
  product and not of the product's ambient space, and cutting a space down by *its own* sections
  is what is below.

  **The fibre product itself is in `Other/Oka/AnalyticSpace/CutOutFibreProduct.lean`**, which imports
  this file ; one edge, measured ; and which is the first
  `CategoryTheory.Limits.HasPullback` instance in this repository over a cospan neither of whose
  legs is the inclusion of an open subspace or is finite étale. **This bullet is unchanged by
  that**: the `#synth` above is pinned to the commit that adds *this* file, and
  `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` still fails at the commit
  that adds that one, since a general analytic space is only locally a local model. This paragraph
  was added on 2026-09-07 by the push that added that file.

  **Being only locally a local model turned out to be enough**, so the clause above records a run
  and not a reason. `Other/Oka/AnalyticSpace/PullbackReduction.lean` glued the local fibre products on
  2026-09-08 and `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` is a theorem
  there, `ComplexAnalytic.AnalyticSpace.hasPullbacks`. **Both `#synth` sentences above are pinned
  to their own commits and neither is retired**; what this note adds is that the *since* clause
  says why the probe failed then and not why it would go on failing.
* **No comparison with `ComplexAnalytic.AnalyticSpace.zeroLocus`.** At an ambient which is an open
  subspace of `ℂ^n`, `ComplexAnalytic.AnalyticSpace.zeroLocus` and
  `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace` have the same underlying locally ringed space,
  both being `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace` of the same family; nothing
  below says that, and saying it would also have to compare the `ℂ`-algebra structure
  `ComplexAnalytic.AnalyticSpace.ofCutOut` gives with the one
  `ComplexAnalytic.AnalyticSpace.ofHasLocalModels` gives.
* **Nothing about the ideal sheaf.** `AlgebraicGeometry.LocallyRingedSpace.idealSheaf` is the
  subsheaf of `𝒪_X` generated by a family of global sections, as a
  `SheafOfModules` and not as a subspace, and it is coherent when `𝒪_X` is. Nothing below relates
  the structure sheaf of the space here to the quotient of `𝒪_X` by that subsheaf, and the
  quotient the space *is* built from is the inverse image of the sheafified quotient presheaf,
  which is how `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace` is defined.
* **No mapping property.** The two halves of one are available and nothing below composes them.
  `ComplexAnalytic.IsCutOutBy.existsUnique_lift` applies to the datum below ; it is stated at an
  arbitrary ambient locally ringed space ; and gives the unique factorisation through
  `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceι` as a morphism of *locally ringed spaces*;
  `ComplexAnalytic.IsCutOutBy.isCLinearHom_lift` applies too, and the `ℂ`-algebra structure in its
  conclusion is this space's on the nose, which is what
  `ComplexAnalytic.AnalyticSpace.zeroLocusSubspace_algebraMap` says. What is missing is those two
  together with the faithfulness of `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` for
  the uniqueness ; which is the recipe `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom`'s own
  docstring gives, and `ComplexAnalytic.AnalyticSpace.liftHom` is the named analytic-space
  morphism that recipe produces for a local model. Nothing below is that morphism for this space.

  **It is `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceLift`, in
  `Other/Oka/AnalyticSpace/CutOutFibreProduct.lean`, and it could not have been here**:
  `Oka.AnalyticSpace.Factorisation`, which declares `ComplexAnalytic.IsCutOutBy.lift` and
  `ComplexAnalytic.IsCutOutBy.isCLinearHom_lift`, is **not** in this module's import closure ;
  measured with `scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware
  `strip_comments`, and confirmed by a scratch importing this module alone, which reports
  `Unknown constant 'ComplexAnalytic.IsCutOutBy.lift'`. **The bullet is unchanged and nothing is
  retired**: *below* is this file, and the two halves are still not composed in it. This paragraph
  was added on 2026-09-07 by the push that added that file.

  **This bullet read `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` `would give one from the
  datum below` until 2026-09-07. It was false when written rather than true and falsified, so this
  is a correction and not one of this repository's dated records**: that lemma fixes its ambient by
  its signature to `(complexAffineSpace n).restrict V.isOpenEmbedding`, which is the same
  observation `## The name to be careful with` makes above about
  `ComplexAnalytic.AnalyticSpace.zeroLocus`, and handing it the datum below is an application type
  mismatch ; the elaborator reports `IsCutOutBy (X.zeroLocusSubspaceι s) s` against an expected
  `IsCutOutBy ?m ?m`. **Both names resolve, so `scripts/check_docstring_names.py` is green either
  way**: what separates them is elaborating the application, and a claim that a named lemma
  *applies* is not a claim any name checker on this board can see.
* **Nothing about coherence, Hausdorffness or finiteness of the immersion.** Coherence of the
  structure sheaf, Hausdorffness of the space, and finiteness of
  `ComplexAnalytic.AnalyticSpace.zeroLocusSubspaceι` are each a statement about the zero locus
  that this file does not make.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {p : ℕ}

/-- **The zero locus of finitely many global sections of a complex analytic space has charts.**

See the module docstring for the five steps. The `ℂ`-algebra structure is the ambient one pulled
back along the inclusion ; `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`, which is defined on
the whole zero locus, so no gluing of structures occurs. -/
theorem hasLocalModels_zeroLocusSubspace (X : AnalyticSpace.{u})
    (s : Fin p → X.presheaf.obj (op ⊤)) :
    HasLocalModels (X.toLocallyRingedSpace.zeroLocusSubspace s)
      (LocallyRingedSpace.comapAlgMap (X.toLocallyRingedSpace.zeroLocusSubspaceι s)
        X.algebraMap) := by
  set ι := X.toLocallyRingedSpace.zeroLocusSubspaceι s with hιdef
  have hZ : IsCutOutBy ι s := X.toLocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι s
  intro z
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := X.local_model (ι.base z)
  -- the chart composed with the inclusion of its target is still surjective on stalks
  have hsurj : ∀ x : X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding,
      Function.Surjective
        (((i ≫ (complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap x).hom) :=
      fun x c ↦ by
    obtain ⟨b, rfl⟩ := hcut.surjective_stalkMap x c
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (((complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap (i.base x))).surjective b
    refine ⟨a, ?_⟩
    rw [LocallyRingedSpace.stalkMap_comp]
    exact ConcreteCategory.comp_apply _ _ a
  obtain ⟨A, hA, t, B, hBtop, hBA, hzB, heq⟩ :=
    LocallyRingedSpace.exists_localLift_family
      (i ≫ (complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) hsurj (B₀ := ⊤)
      (restrictSections U₀.1 s)
      (⟨ι.base z, U₀.2⟩ : X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) trivial
  -- the chart is an embedding, so `B` is the preimage of an open of `ℂ^n|V`; meeting that open
  -- with the preimage of `A` keeps the preimage and buys `V' ≤ A`
  obtain ⟨O, hO, hOpre⟩ := hcut.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.1 B.2
  set A' : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding) :=
    (Opens.map ((complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base).obj A with hA'
  set V' : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding) :=
    ⟨O, hO⟩ ⊓ A' with hV'
  set B₁ : Opens (X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    (Opens.map i.base).obj V' with hB₁def
  have hB₁ : B₁ = B := by
    refine Opens.ext (Set.ext fun w ↦ ?_)
    have h1 : (i.base w ∈ O) ↔ w ∈ B := Set.ext_iff.1 hOpre w
    exact ⟨fun hw ↦ h1.1 hw.1, fun hw ↦ ⟨h1.2 hw, hBA hw⟩⟩
  have hV'A' : V' ≤ A' := inf_le_right
  -- the lifted sections, read on `V'`
  set u : Fin p → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op V') :=
    fun r ↦ ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).res hV'A'
      (((complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).c.app (op A) (t r)) with hu
  have hkey : ∀ r, i.c.app (op V') (u r) =
      (X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).res (le_top : B₁ ≤ ⊤)
        (restrictSections U₀.1 s r) := by
    intro r
    have h1 := congrArg
      ((X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).res (le_of_eq hB₁)) (heq r)
    rw [LocallyRingedSpace.res_res, LocallyRingedSpace.res_res] at h1
    rw [← h1, hu]
    exact LocallyRingedSpace.c_app_res i hV'A' _
  set t' : Fin p → (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).restrict
      V'.isOpenEmbedding).presheaf.obj (op ⊤) :=
    fun r ↦ ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).toRestrictΓ V' (u r) with ht'
  -- the sections cutting the inner subspace out are the pullbacks of the `t'`
  have hfam : restrictSections B₁ (restrictSections U₀.1 s)
      = fun r ↦ (LocallyRingedSpace.Γ.map (restrictHom i V').op).hom (t' r) := by
    funext r
    -- `restrictSections` is unfolded by a `rfl` rather than named in the `rw`, which would plant
    -- its auto-generated equation lemma into this module under that file's name
    have hrs : restrictSections B₁ (restrictSections U₀.1 s) r
        = (LocallyRingedSpace.Γ.map ((X.toLocallyRingedSpace.restrict
            U₀.1.isOpenEmbedding).ofRestrict B₁.isOpenEmbedding).op).hom
          (restrictSections U₀.1 s r) := rfl
    rw [ht', Γ_map_restrictHom_toRestrictΓ, hkey r, hrs,
      LocallyRingedSpace.Γ_map_ofRestrict_apply]
    exact (LocallyRingedSpace.map_map_apply _ _ _ _ _).symm
  have hinner : IsCutOutBy (restrictHom (restrictHom ι U₀.1) B₁)
      (fun r ↦ (LocallyRingedSpace.Γ.map (restrictHom i V').op).hom (t' r)) :=
    hfam ▸ ((hZ.restrictOpen U₀.1).restrictOpen B₁)
  have hcomp := (hcut.restrictOpen V').comp_append hinner
  -- the two changes of chart: the source into the zero locus, the target into `ℂ^n`
  set UZ : Opens (X.toLocallyRingedSpace.zeroLocusSubspace s) :=
    (Opens.map ι.base).obj U₀.1 with hUZ
  set Bstar : Opens ((X.toLocallyRingedSpace.zeroLocusSubspace s).restrict UZ.isOpenEmbedding) :=
    (Opens.map (restrictHom ι U₀.1).base).obj B₁ with hBstar
  set WZ : Opens (X.toLocallyRingedSpace.zeroLocusSubspace s) :=
    UZ.isOpenEmbedding.isOpenMap.functor.obj Bstar with hWZ
  set V'' : Opens (complexAffineSpace.{u} n) :=
    V.isOpenEmbedding.isOpenMap.functor.obj V' with hV''
  have hrange : Set.range
        (((X.toLocallyRingedSpace.zeroLocusSubspace s).ofRestrict WZ.isOpenEmbedding).base) =
      Set.range (((((X.toLocallyRingedSpace.zeroLocusSubspace s).restrict
        UZ.isOpenEmbedding).ofRestrict Bstar.isOpenEmbedding ≫
        (X.toLocallyRingedSpace.zeroLocusSubspace s).ofRestrict UZ.isOpenEmbedding).base)) :=
    (LocallyRingedSpace.range_ofRestrict _ WZ).trans
      (LocallyRingedSpace.range_ofRestrict_comp _ UZ Bstar).symm
  have hrange₂ : Set.range ((((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).ofRestrict
        V'.isOpenEmbedding ≫ (complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base) =
      Set.range (((complexAffineSpace.{u} n).ofRestrict V''.isOpenEmbedding).base) :=
    (LocallyRingedSpace.range_ofRestrict_comp (complexAffineSpace.{u} n) V V').trans
      (LocallyRingedSpace.range_ofRestrict (complexAffineSpace.{u} n) V'').symm
  set e₁ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange with he₁
  set e₂ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange₂ with he₂
  have hfinal := (hcomp.iso_comp e₂).comp_iso e₁
  have hbase : (restrictHom ι U₀.1).base (⟨z, U₀.2⟩ :
      (X.toLocallyRingedSpace.zeroLocusSubspace s).restrict UZ.isOpenEmbedding)
      = (⟨ι.base z, U₀.2⟩ : X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    Subtype.ext (base_restrictHom ι U₀.1 _)
  have hzWZ : z ∈ WZ := by
    refine ⟨⟨z, U₀.2⟩, ?_, rfl⟩
    change (restrictHom ι U₀.1).base (⟨z, U₀.2⟩ :
      (X.toLocallyRingedSpace.zeroLocusSubspace s).restrict UZ.isOpenEmbedding) ∈ B₁
    rw [hbase, hB₁]
    exact hzB
  have he₁lin : IsCLinearHom e₁.hom
      ((X.toLocallyRingedSpace.zeroLocusSubspace s).resAlgMap
        (LocallyRingedSpace.comapAlgMap ι X.algebraMap) WZ)
      (((X.toLocallyRingedSpace.zeroLocusSubspace s).restrict UZ.isOpenEmbedding).resAlgMap
        ((X.toLocallyRingedSpace.zeroLocusSubspace s).resAlgMap
          (LocallyRingedSpace.comapAlgMap ι X.algebraMap) UZ) Bstar) :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)
      (isCLinearHom_ofRestrict _ _ WZ)
      ((isCLinearHom_ofRestrict _ _ Bstar).comp (isCLinearHom_ofRestrict _ _ UZ))
  have he₂lin : IsCLinearHom e₂.hom
      (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).resAlgMap
        (constantsAlgMap n V) V') (constantsAlgMap n V'') :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange₂)
      ((isCLinearHom_ofRestrict _ _ V').comp (isCLinearHom_ofRestrict_constants n V))
      (isCLinearHom_ofRestrict_constants n V'')
  exact ⟨⟨WZ, hzWZ⟩, n, k + p, V'', _, _, hfinal,
    he₁lin.comp (((isCLinearHom_restrictHom
      (isCLinearHom_restrictHom (isCLinearHom_comapAlgMap ι X.algebraMap) U₀.1) B₁).comp
      (isCLinearHom_restrictHom hlin V')).comp he₂lin)⟩

namespace AnalyticSpace

variable (X : AnalyticSpace.{u}) (s : Fin p → X.presheaf.obj (op ⊤))

/-- **The zero locus of finitely many global sections of a complex analytic space, as a complex
analytic space.**

`ComplexAnalytic.AnalyticSpace.ofHasLocalModels` at
`ComplexAnalytic.hasLocalModels_zeroLocusSubspace`. The underlying locally ringed space is
`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace` and the `ℂ`-algebra structure is the
ambient one pulled back along the inclusion; neither is a choice made here. -/
def zeroLocusSubspace : AnalyticSpace.{u} :=
  AnalyticSpace.ofHasLocalModels _ _ (hasLocalModels_zeroLocusSubspace X s)

/-- The underlying locally ringed space of the zero locus is the zero locus. Not a `simp` lemma,
for the reason `ComplexAnalytic.AnalyticSpace.restrict_toLocallyRingedSpace` gives of itself. -/
lemma zeroLocusSubspace_toLocallyRingedSpace :
    (zeroLocusSubspace X s).toLocallyRingedSpace =
      X.toLocallyRingedSpace.zeroLocusSubspace s :=
  rfl

/-- The `ℂ`-algebra structure on the zero locus is the ambient one pulled back along the
inclusion. -/
lemma zeroLocusSubspace_algebraMap :
    (zeroLocusSubspace X s).algebraMap =
      LocallyRingedSpace.comapAlgMap (X.toLocallyRingedSpace.zeroLocusSubspaceι s)
        X.algebraMap :=
  rfl

/-- **The closed immersion of the zero locus, as a morphism of complex analytic spaces.**

Its `ℂ`-linearity is `ComplexAnalytic.isCLinearHom_comapAlgMap` and is the statement that the
structure the space was given is the pulled-back one, so it holds by definition. -/
def zeroLocusSubspaceι : zeroLocusSubspace X s ⟶ X :=
  ⟨X.toLocallyRingedSpace.zeroLocusSubspaceι s,
    isCLinearHom_comapAlgMap (X.toLocallyRingedSpace.zeroLocusSubspaceι s) X.algebraMap⟩

/-- The underlying morphism of locally ringed spaces of the closed immersion. -/
lemma toLRSHom_zeroLocusSubspaceι :
    (zeroLocusSubspaceι X s).toLRSHom = X.toLocallyRingedSpace.zeroLocusSubspaceι s :=
  rfl

/-- **The closed immersion of the zero locus is cut out by the sections it is the zero locus
of**, at the analytic level. `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`
restated through `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom`, which is where every consumer of a
cut-out datum for a morphism of analytic spaces reads it. -/
theorem isCutOutBy_zeroLocusSubspaceι :
    IsCutOutBy (zeroLocusSubspaceι X s).toLRSHom s :=
  X.toLocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι s

/-- **The cutting sections pull back to zero on the zero locus.**
`ComplexAnalytic.IsCutOutBy.c_app_eq_zero` at the datum above, in the
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` spelling. -/
theorem pullbackΓ_zeroLocusSubspaceι_eq_zero (r : Fin p) :
    (zeroLocusSubspaceι X s).pullbackΓ (s r) = 0 :=
  (isCutOutBy_zeroLocusSubspaceι X s).c_app_eq_zero r

/-- **The closed immersion of the zero locus is a monomorphism**, so it cancels in
`ComplexAnalytic.AnalyticSpace` itself. `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` at the
datum above; without it a cancellation argument has to be routed through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` by hand, which is the reason
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` gives for existing. -/
instance mono_zeroLocusSubspaceι : Mono (zeroLocusSubspaceι X s) :=
  mono_of_isCutOutBy _ (isCutOutBy_zeroLocusSubspaceι X s)

end AnalyticSpace

end ComplexAnalytic

end
