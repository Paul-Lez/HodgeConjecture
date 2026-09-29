/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.OpenSubspace
public import Mathlib.Topology.Sets.OpenCover

/-!
# Being a local isomorphism is local on the source

A property `P` of morphisms is **local on the source** when, for every open cover `{Vᵢ}` of the
*source*, `P f` holds exactly if `P` holds of each composite `Vᵢ ↪ X ⟶ Y`. This file says that of
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, and of that class alone.

`Other/Oka/AnalyticSpace/LocalAtTarget.lean` is the other half of this pair and covers the *target*, for
`ComplexAnalytic.AnalyticSpace.IsFinite`, `ComplexAnalytic.AnalyticSpace.IsLocalIso` and
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` alike. **The cover there is of `Y` and the cover
here is of `X`, and neither
statement is the other read backwards**: over a cover of the target a morphism is cut into
morphisms of open subspaces on both sides, while over a cover of the source the target is left
alone and the members are composites into the whole of `Y`.

## Why this class and not the other two

`ComplexAnalytic.AnalyticSpace.IsLocalIso` is *defined* by two conditions at a point of the
source ; its `isLocalHomeomorph` field is a condition at each point of `X`, and its
`isIso_stalkMap` field is indexed by a point of `X` ; so a cover of `X` reaches every instance of
both. **`ComplexAnalytic.AnalyticSpace.IsFinite` is not of that shape and this file claims
nothing about it**: its fields are `isClosedMap`, a condition on the underlying map as a whole,
and `finite_fiber`, indexed by a point of the **target** ; so a cover of the source reaches
neither. **Nothing here is a source-local
statement for `ComplexAnalytic.AnalyticSpace.IsFinite` or for
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, and nothing here is about analytification.**

## Nothing in the proof is this repository's, and here is the accounting

Every step is a quotation, and the table and the sentence after it are the whole list. These are
Mathlib's, at the revision `lakefile.toml` pins:

| step | where it comes from |
| --- | --- |
| one on `Set.univ` iff one everywhere | `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ` |
| an open embedding is a local homeomorphism | `Topology.IsOpenEmbedding.isLocalHomeomorph` |
| cancelling the right factor of a composite | `IsLocalHomeomorphOn.of_comp_right` |
| the stalk map of a composite | `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` |

and these two are `Other/Oka/AnalyticSpace/OpenSubspace.lean`'s:
`ComplexAnalytic.AnalyticSpace.range_base_ofRestrict`, which says the range of an open subspace's
inclusion is the open set, and the `IsIso` instance for that inclusion's stalk maps,
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`, which `inferInstance` finds. **That
instance being found by `inferInstance` is the point of that file's discrimination-tree-key
paragraph, and this is a consumer of it.**

## Two traps, both paid for below and both worth keeping paid

1. **Do not `rw` the equation `(X.ofRestrict U).toLRSHom.base ⟨x, hx⟩ = x`.** It holds by `rfl`,
   but the stalk it indexes is dependent on it, so `rw` fails with *motive is not type correct*.
   The `exact` that closes `isIso_stalkMap` elaborates at default transparency and takes the term
   with the index unrewritten, which is why no rewrite of it appears.
2. **`CategoryTheory.IsIso.of_isIso_comp_right` needs its instance argument passed by hand.**
   `Other/Oka/Geometry/RingedSpace/OpenImmersion.lean` records the same thing of
   `CategoryTheory.IsIso.of_isIso_comp_left` and says that no explanation should be read into it;
   this is that shape again and takes the same remedy.

## Why a module of its own, measured rather than argued

Three homes were priced with `scripts/module_graph.py` and with the Mathlib closure computed from
`scripts/import_cost.py`'s own graph.

* **`Other/Oka/AnalyticSpace/LocalIso.lean`, where the class lives, is impossible and not merely
  expensive.** The proof needs `ComplexAnalytic.AnalyticSpace.ofRestrict` and the two ingredients
  named above, all declared in `Other/Oka/AnalyticSpace/OpenSubspace.lean`, and
  `scripts/module_graph.py`, given those two paths, answers that `OpenSubspace` is downstream of
  `LocalIso` **at distance 1**. The import would be a cycle.
* **`Other/Oka/AnalyticSpace/LocalAtTarget.lean` is reachable and costs more of the graph.** Its own
  upstream closure is **46** `Oka` modules against this file's **44**, the two it adds being
  `Oka.AnalyticSpace.PullbackOpen` and `Oka.Topology.IsLocalHomeomorph`; on the Mathlib side it is
  **3039** modules against this file's **3037**, the two being `Mathlib.Topology.LocalAtTarget` and
  `Mathlib.Topology.LocallyClosed`. **`Mathlib.Topology.Sets.OpenCover`, the one Mathlib import
  this file adds by hand, costs nothing**: it is already in the closure of
  `Other/Oka/AnalyticSpace/OpenSubspace.lean`, which is why the leaf's figure equals that file's.
* And a file whose title, docstring and framing are *local on the target* would have become *local
  on the target, except one*. `Other/Oka/Analytification/StandardEtaleFiniteEtale.lean` refused an append
  on that ground and said so; **the measurement above means this file does not have to rest on
  it**, since the cheaper graph and the honest framing point the same way.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover_source`: **being a local isomorphism
  descends along an open cover of the source.**
- `ComplexAnalytic.AnalyticSpace.isLocalIso_iff_isOpenCover_source`: **the two directions
  together.** The converse asks nothing of the cover and is
  `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_comp`, both instances, so it is `inferInstance`. It is
  here because `Other/Oka/AnalyticSpace/LocalAtTarget.lean` pairs each of its descent theorems with an
  `iff` and a reader who knows that file will look for this one.

## What is not here

* **No source-local statement for the other two classes**, for the reason given above. Finiteness
  is not source-local, and the shape of a counterexample is an infinite discrete source over a
  single point of the target: each singleton of the cover by singletons is a closed immersion and
  so finite, while one fibre is infinite. **That is reasoning and not a run ; no such object is
  built in this repository ; and nothing below depends on it**; what this file does is decline the
  statement rather than refute it.
* **And no source-local statement of any kind stood here before this file, which is measured
  rather than assumed.** `git grep -nE "IsOpenCover" -- 'Other/Oka/**.lean'` returns, outside this file,
  **23** lines in **two**: `Other/Oka/AnalyticSpace/LocalAtTarget.lean`, whose `variable` line reads
  `{U : ι → Y.Opens}`, so every statement in it is a cover of the target and none is of the
  source, and
  `Other/Oka/Topology/IsLocalHomeomorph.lean`, which is mirror-tree material about continuous maps and
  names no class of this development. **That figure is a record of the commit this file is added
  at and the next append to either file falsifies it**; the property it is evidence for ; that the
  cover vocabulary reached only the target ; is what a later reader should re-run rather than
  quote.
* **Nothing about analytification and nothing étale.** The consumer this was written for is the
  Zariski-local route mapped in taxis #2178, where an étale algebra is standard étale after
  localising at each prime and the opens that hands back cover the source. **This file supplies
  one rung of that route and touches no other**, and it narrows none of the eight prose sites that
  record the analytification of a finite étale morphism of schemes as absent ; those are
  enumerated in `Other/Oka/Analytification/SpecFiniteAnalytification.lean` and no word of this file is
  about analytification at all. It is a statement about the class, and it stands whatever becomes
  of that route.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

namespace ComplexAnalytic.AnalyticSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

variable {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) {ι : Type u} (V : ι → X.Opens)

/-- **Being a local isomorphism descends along an open cover of the source.**

If every composite `Vᵢ ↪ X ⟶ Y` is a local isomorphism, so is `f`. Both fields are read at a
point `x` of `X`, and the cover supplies a member containing it; the work is then entirely
cancellation of the inclusion `Vᵢ ↪ X`, on the left for the stalk map and on the right for the
local homeomorphism.

**No step of the proof is this repository's**; the module docstring above accounts for each one
and names the two traps that shaped how the two fields are written. -/
theorem isLocalIso_of_isOpenCover_source (hV : IsOpenCover V)
    (h : ∀ i, IsLocalIso (X.ofRestrict (V i) ≫ f)) : IsLocalIso f where
  isLocalHomeomorph := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    intro x _
    obtain ⟨i, hi⟩ := hV.exists_mem x
    have hcomp : IsLocalHomeomorphOn
        ((f.toLRSHom.base : X → Y) ∘ ((X.ofRestrict (V i)).toLRSHom.base : X.restrict (V i) → X))
        Set.univ := (h i).isLocalHomeomorph.isLocalHomeomorphOn
    have hincl : IsLocalHomeomorphOn
        ((X.ofRestrict (V i)).toLRSHom.base : X.restrict (V i) → X) Set.univ :=
      ((V i).isOpenEmbedding.isLocalHomeomorph).isLocalHomeomorphOn
    have hres := hcomp.of_comp_right hincl
    rw [Set.image_univ, AnalyticSpace.range_base_ofRestrict] at hres
    exact hres x hi
  isIso_stalkMap x := by
    obtain ⟨i, hi⟩ := hV.exists_mem x
    have hcomp : IsIso ((X.ofRestrict (V i) ≫ f).toLRSHom.stalkMap ⟨x, hi⟩) :=
      (h i).isIso_stalkMap _
    have he : (X.ofRestrict (V i) ≫ f).toLRSHom = (X.ofRestrict (V i)).toLRSHom ≫ f.toLRSHom := rfl
    rw [he, LocallyRingedSpace.stalkMap_comp] at hcomp
    have hiso : IsIso ((X.ofRestrict (V i)).toLRSHom.stalkMap ⟨x, hi⟩) := inferInstance
    exact @CategoryTheory.IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((X.ofRestrict (V i)).toLRSHom.stalkMap ⟨x, hi⟩) hiso hcomp

/-- **Being a local isomorphism is local on the source.**

The forward direction asks nothing of the cover:
`ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` are both instances, so it is `inferInstance`. The
hypothesis on `V` is there for the other direction, which is
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover_source` above.

This is the shape `Other/Oka/AnalyticSpace/LocalAtTarget.lean` gives each of its three descent theorems,
kept here so that the two halves of the pair read alike. -/
theorem isLocalIso_iff_isOpenCover_source (hV : IsOpenCover V) :
    IsLocalIso f ↔ ∀ i, IsLocalIso (X.ofRestrict (V i) ≫ f) :=
  ⟨fun _ _ ↦ inferInstance, isLocalIso_of_isOpenCover_source f V hV⟩

end ComplexAnalytic.AnalyticSpace

end
