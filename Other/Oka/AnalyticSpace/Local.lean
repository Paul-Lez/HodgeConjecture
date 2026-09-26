/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.OpenSubspace

/-!
# Being a complex analytic space is a local condition

`ComplexAnalytic.AnalyticSpace` is a locally ringed space carrying two further things: a
`ℂ`-algebra structure `algebraMap` on its global sections, which is **data**, and the
`local_model` field, which is a **property**. This file isolates the property as a predicate
`ComplexAnalytic.HasLocalModels` and proves that it is local on the space: a locally ringed
space covered by open subspaces that have charts has charts.

`local_model` is stated pointwise ; *every point has a neighbourhood carrying a chart* ; so
locality is not surprising. What makes it a theorem rather than a triviality is that the chart
produced by the hypothesis lives on a restriction of a restriction, `(X|Uᵢ)|W`, while the
conclusion wants one on a single restriction `X|W'`. Those two are isomorphic and not equal,
and the isomorphism has to be checked `ℂ`-linear before the chart can be transported along it.

## Why this file exists

Every statement about gluing complex analytic spaces needs it. `Other/Oka/Geometry/RingedSpace/
PresheafedSpace/Gluing.lean` supplies `AlgebraicGeometry.LocallyRingedSpace.OpenCover` and
identifies a locally ringed space with the gluing of a cover of it, so the locally-ringed-space
half of gluing is available; what is missing to glue *analytic* spaces is this property being
local, together with the `ℂ`-algebra structure of a glued space.

**Both are here.** They behave differently and that is why they are separated: `local_model` is a
*property* and is local, while `algebraMap` is *data* and lands in **global** sections, so it does
not restrict from a cover for free ; recovering it from structures on the members is a gluing,
and it is `AlgebraicGeometry.LocallyRingedSpace.glueAlgMap`, which lives in the mirror tree
because nothing about it is analytic. `ComplexAnalytic.AnalyticSpace.ofOpensCompatible` is the two
halves together.

## Main definitions

- `ComplexAnalytic.HasLocalModels`: the `local_model` field of `ComplexAnalytic.AnalyticSpace`,
  as a predicate on a locally ringed space together with a `ℂ`-algebra structure on its global
  sections.
- `ComplexAnalytic.AnalyticSpace.ofOpens`: a locally ringed space covered by open subspaces that
  have local models, as a complex analytic space, for a `ℂ`-algebra structure given on the
  ambient space.
- `ComplexAnalytic.AnalyticSpace.ofOpensCompatible`: the same with the `ℂ`-algebra structure
  given on the **members** of the cover and glued, which is the form a gluing construction
  produces.

## Main results

- `ComplexAnalytic.HasLocalModels.restrict`: an open subspace of a space with local models has
  local models. This is `ComplexAnalytic.exists_local_model_restrict` restated, and it is the
  hard direction.
- `ComplexAnalytic.HasLocalModels.of_iSup_eq_top`: **having local models is local** ; a space
  covered by open subspaces that have local models has local models.
- `ComplexAnalytic.hasLocalModels_iff_iSup_eq_top`: the two together.
- `ComplexAnalytic.AnalyticSpace.map_ofOpensCompatible_algebraMap`: the glued `ℂ`-algebra
  structure restricts to the given one on each member of the cover.

## What is not here

* **`ℂ`-linearity of the transition maps as a hypothesis.** `ofOpensCompatible` asks only that
  the algebra structures agree on the overlaps, spelled as `TopCat.Presheaf.IsCompatible`, which
  is all the sheaf condition needs. A formulation in terms of `ComplexAnalytic.IsCLinearHom` of
  the inclusions would be equivalent and is not stated, because nothing produces its hypothesis
  in that shape.
* **Gluing along abstract open immersions rather than open subsets.** The cover here is a family
  of `TopologicalSpace.Opens X`, not an `AlgebraicGeometry.LocallyRingedSpace.OpenCover`, whose
  members are arbitrary spaces mapping in by open immersions. That bridge is
  `Other/Oka/AnalyticSpace/Glue.lean`: `ComplexAnalytic.HasLocalModels.of_iso` transports the property
  along a `ℂ`-linear isomorphism and `ComplexAnalytic.AnalyticSpace.ofOpenCover` is the resulting
  construction. It is not here because it needs
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`, which this file does not import.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-- **A locally ringed space `X` with a `ℂ`-algebra structure `α` on its global sections *has
local models* if every point has a chart**: a neighbourhood which, compatibly with the
`ℂ`-algebra structures, is cut out by finitely many holomorphic functions inside an open subset
of some `ℂ^n`.

This is the `local_model` field of `ComplexAnalytic.AnalyticSpace` verbatim, extracted so that
it can be *hypothesised* about a locally ringed space that is not yet packaged as an analytic
space ; which is what every construction of an analytic space out of pieces needs. The
packaging in the other direction is `ComplexAnalytic.AnalyticSpace.ofOpens`. -/
def HasLocalModels (X : LocallyRingedSpace.{u}) (α : ℂ →+* X.presheaf.obj (op ⊤)) : Prop :=
  ∀ x : X, ∃ (U : OpenNhds x) (n k : ℕ) (V : Opens (complexAffineSpace.{u} n))
    (i : X.restrict U.1.isOpenEmbedding ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
    (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)),
    IsCutOutBy i f ∧ IsCLinearHom i (X.resAlgMap α U.1) (constantsAlgMap n V)

/-- A complex analytic space has local models: this is its `local_model` field, which is
`ComplexAnalytic.HasLocalModels` by definition. -/
theorem AnalyticSpace.hasLocalModels (X : AnalyticSpace.{u}) :
    HasLocalModels X.toLocallyRingedSpace X.algebraMap :=
  X.local_model

/-- **A space with local models, with a `ℂ`-algebra structure, as a complex analytic space.**
The three fields of `ComplexAnalytic.AnalyticSpace` in the order they are given. -/
@[simps! toLocallyRingedSpace algebraMap]
def AnalyticSpace.ofHasLocalModels (X : LocallyRingedSpace.{u})
    (α : ℂ →+* X.presheaf.obj (op ⊤)) (h : HasLocalModels X α) : AnalyticSpace.{u} where
  toLocallyRingedSpace := X
  algebraMap := α
  local_model := h

/-- **An open subspace of a space with local models has local models**, for the restricted
`ℂ`-algebra structure.

This is `ComplexAnalytic.exists_local_model_restrict` ; the chart of `X|U` at a point ; with the
analytic space packed and unpacked around it, and it is the substantial direction of
`ComplexAnalytic.hasLocalModels_iff_iSup_eq_top`. -/
theorem HasLocalModels.restrict {X : LocallyRingedSpace.{u}}
    {α : ℂ →+* X.presheaf.obj (op ⊤)} (h : HasLocalModels X α) (U : Opens X) :
    HasLocalModels (X.restrict U.isOpenEmbedding) (X.resAlgMap α U) :=
  exists_local_model_restrict (AnalyticSpace.ofHasLocalModels X α h) U

/-- **Having local models is local on the space**: if the open sets `U i` cover `X` and each
`X|U i` has local models for the restricted `ℂ`-algebra structure, then `X` has local models.

Given `x`, pick a member `U i` containing it and a chart of `X|U i` at `x`, defined on some
`W : Opens (X|U i)`. That chart is not yet a chart of `X`: it lives on `(X|U i)|W`, and what is
wanted is a chart on `X|W'` for `W'` the image of `W` in `X`. The two are open subspaces of `X`
with the same image, so `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`
identifies them; that identification is `ℂ`-linear because both of its legs are inclusions of
open subspaces (`ComplexAnalytic.IsCLinearHom.of_comp` applied to
`ComplexAnalytic.isCLinearHom_ofRestrict`), and `ComplexAnalytic.IsCutOutBy.comp_iso` carries
the chart across it. -/
theorem HasLocalModels.of_iSup_eq_top {X : LocallyRingedSpace.{u}}
    {α : ℂ →+* X.presheaf.obj (op ⊤)} {ι : Type*} {U : ι → Opens X}
    (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding) (X.resAlgMap α (U i))) :
    HasLocalModels X α := by
  intro x
  have hx : x ∈ ⨆ i, U i := hU ▸ trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨W, n, k, V, c, f, hcut, hlin⟩ := h i ⟨x, hxi⟩
  set W' : Opens X := (U i).isOpenEmbedding.isOpenMap.functor.obj W.1 with hW'
  have hxW' : x ∈ W' := ⟨⟨x, hxi⟩, W.2, rfl⟩
  have hrange : Set.range (X.ofRestrict W'.isOpenEmbedding).base =
      Set.range (((X.restrict (U i).isOpenEmbedding).ofRestrict W.1.isOpenEmbedding ≫
        X.ofRestrict (U i).isOpenEmbedding).base) :=
    (X.range_ofRestrict W').trans (X.range_ofRestrict_comp (U i) W.1).symm
  set e := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange with he'
  have he : IsCLinearHom e.hom (X.resAlgMap α W')
      ((X.restrict (U i).isOpenEmbedding).resAlgMap (X.resAlgMap α (U i)) W.1) :=
    IsCLinearHom.of_comp
      (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)
      (isCLinearHom_ofRestrict X α W')
      ((isCLinearHom_ofRestrict _ _ W.1).comp (isCLinearHom_ofRestrict X α (U i)))
  exact ⟨⟨W', hxW'⟩, n, k, V, e.hom ≫ c, f, hcut.comp_iso e, he.comp hlin⟩

/-- **Having local models is a local condition**, in both directions: `X` has local models
exactly when every member of an open cover of `X` does. -/
theorem hasLocalModels_iff_iSup_eq_top {X : LocallyRingedSpace.{u}}
    {α : ℂ →+* X.presheaf.obj (op ⊤)} {ι : Type*} {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) :
    HasLocalModels X α ↔
      ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding) (X.resAlgMap α (U i)) :=
  ⟨fun h i ↦ h.restrict (U i), HasLocalModels.of_iSup_eq_top hU⟩

/-- **A locally ringed space covered by open subspaces that are analytic is analytic.**

The `ℂ`-algebra structure is given on the ambient space and restricted to each member; it is
*not* glued from structures on the members, which is a separate problem and is not solved here.
See the module docstring. -/
@[simps! toLocallyRingedSpace algebraMap]
def AnalyticSpace.ofOpens (X : LocallyRingedSpace.{u}) (α : ℂ →+* X.presheaf.obj (op ⊤))
    {ι : Type*} (U : ι → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding) (X.resAlgMap α (U i))) :
    AnalyticSpace.{u} :=
  AnalyticSpace.ofHasLocalModels X α (HasLocalModels.of_iSup_eq_top hU h)

/-- **A locally ringed space covered by analytic open subspaces, with no ambient `ℂ`-algebra
structure given, is a complex analytic space.**

`ComplexAnalytic.AnalyticSpace.ofOpens` takes the `ℂ`-algebra structure on the *ambient* space
and restricts it; this version takes one on each member of the cover, agreeing on the overlaps,
and glues them with `AlgebraicGeometry.LocallyRingedSpace.glueAlgMap`. That is the form a gluing
construction produces, because the pieces are what one has and the ambient space is what one is
building.

The algebra structures are indexed by `U i` rather than by `(U i).functor.obj ⊤`, which is how
`AlgebraicGeometry.LocallyRingedSpace.resAlgMap` indexes them; the restriction map between the
two is what the hypothesis `h` carries, and
`AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap` is what crosses it. -/
def AnalyticSpace.ofOpensCompatible (X : LocallyRingedSpace.{u})
    {ι : Type*} (U : ι → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤)
    (α : ∀ i, ℂ →+* X.presheaf.obj (op (U i)))
    (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible X.presheaf U fun i ↦ α i c)
    (h : ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding)
      ((X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top (U i)).le).op).hom.comp (α i))) :
    AnalyticSpace.{u} :=
  AnalyticSpace.ofOpens X (LocallyRingedSpace.glueAlgMap hU α hα) U hU fun i ↦ by
    rw [LocallyRingedSpace.resAlgMap_glueAlgMap]
    exact h i

@[simp]
lemma AnalyticSpace.ofOpensCompatible_toLocallyRingedSpace (X : LocallyRingedSpace.{u})
    {ι : Type*} (U : ι → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤)
    (α : ∀ i, ℂ →+* X.presheaf.obj (op (U i)))
    (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible X.presheaf U fun i ↦ α i c)
    (h : ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding)
      ((X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top (U i)).le).op).hom.comp (α i))) :
    (AnalyticSpace.ofOpensCompatible X U hU α hα h).toLocallyRingedSpace = X :=
  rfl

/-- **The glued `ℂ`-algebra structure restricts to the given one on each member of the cover.**
Stated as the sections over `U i` rather than as the global sections of `X|U i`, which is the
side of the seam the input lives on.

Not a `simp` lemma: `AnalyticSpace.ofOpensCompatible_toLocallyRingedSpace` rewrites inside its
own left-hand side, which the `simpNF` linter reports. -/
lemma AnalyticSpace.map_ofOpensCompatible_algebraMap (X : LocallyRingedSpace.{u})
    {ι : Type*} (U : ι → TopologicalSpace.Opens X) (hU : ⨆ i, U i = ⊤)
    (α : ∀ i, ℂ →+* X.presheaf.obj (op (U i)))
    (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible X.presheaf U fun i ↦ α i c)
    (h : ∀ i, HasLocalModels (X.restrict (U i).isOpenEmbedding)
      ((X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top (U i)).le).op).hom.comp (α i)))
    (i : ι) (c : ℂ) :
    (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom
        ((AnalyticSpace.ofOpensCompatible X U hU α hα h).algebraMap c) = α i c :=
  LocallyRingedSpace.map_glueAlgMap hU α hα i c

end ComplexAnalytic

end
