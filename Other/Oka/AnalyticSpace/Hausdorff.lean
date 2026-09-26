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
# The analytic spaces this development constructs are Hausdorff

`ComplexAnalytic.AnalyticSpace` imposes no separation axiom, for the reason
`AlgebraicGeometry.Scheme` does not ; `Other/Oka/AnalyticSpace/Basic.lean` says so twice, and **those two
sentences stay true**: nothing here adds a field to the structure, and an analytic space is not
Hausdorff in general.

What *is* true is narrower and is enough. Every space this development builds is a zero locus
inside an open subset of `ℂ^n`, or an open subspace of such a thing, and a subspace of `ℂ^n` is
Hausdorff because `ℂ^n` is. So the separation hypothesis that four results carry ;
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`,
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` and
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` on the source,
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` on the middle space ; is discharged by
instance search at every construction below rather than being a hypothesis a caller has to carry.

**Every declaration in this file is one `inferInstanceAs` and nothing else.** There is no
mathematics here; what the file supplies is *heads*, and the only content is which heads are
needed.

## Why seven and not three, and it is a fact about definitional unfolding

Instance search does not unfold a `def`, so each spelling of a carrier is its own head even when
two of them are `rfl`-equal. Three of the seven exist only for that reason, and each was measured
by deleting it and re-elaborating the rest:

* without `ComplexAnalytic.t2Space_complexSpace` the *second* one fails, with
  `failed to synthesize T2Space ↥V`;
* without `ComplexAnalytic.t2Space_restrict_complexAffineSpace` the *third* fails, with
  `failed to synthesize T2Space ↑(((complexAffineSpace n).restrict ⋯).zeroLocus f)`;
* without `ComplexAnalytic.t2Space_zeroLocusSubspace` the analytic-space one fails, with
  `failed to synthesize T2Space` of
  `↑(((complexAffineSpace n).restrict ⋯).zeroLocusSubspace f).toTopCat`.

The middle two are at the **locally ringed space** level and not at the analytic-space level, which
is forced and is easy to miss: `ComplexAnalytic.AnalyticSpace.zeroLocus`'s ambient is an
`AlgebraicGeometry.LocallyRingedSpace.restrict` of the root-namespace `complexAffineSpace`
(`Other/Oka/ComplexSpace.lean`), not a `ComplexAnalytic.AnalyticSpace.restrict` of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace`, so the analytic-space instance for open
subspaces never reaches it.

## Two spellings that are essential in the statements

**The `_root_` prefix on `complexAffineSpace`, and not the bare name.** Inside
`namespace ComplexAnalytic` the bare name resolves to
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` in any declaration whose own name is prefixed
`AnalyticSpace.`, because Lean opens the namespace of the declaration being elaborated. The names
below avoid that prefix, and the `_root_` is kept anyway so that the statements can be copied out
of here into a file that does use it.

**`TopologicalSpace.Opens` and not `Opens`.** `ComplexAnalytic.AnalyticSpace.Opens` takes a
`ComplexAnalytic.AnalyticSpace`, and the ambient of a zero locus is a
`AlgebraicGeometry.LocallyRingedSpace`; writing the short form there fails with
`Application type mismatch: … has type LocallyRingedSpace but is expected to have type
AnalyticSpace`.

## What is not here

* **No separation axiom on `ComplexAnalytic.AnalyticSpace`**, and no change to
  `Other/Oka/AnalyticSpace/Basic.lean`. Nothing here claims the class is empty of non-Hausdorff
  objects, and the general statement is simply not made.
* **No general locally-ringed-space instance, and that is a decision rather than an omission.**
  `[T2Space Y] → T2Space (Y.zeroLocusSubspace f)` and the same for
  `AlgebraicGeometry.LocallyRingedSpace.restrict` are genuinely general, hold with the same
  one-line proof, and by `README.md`'s mirror-tree rule would belong under
  `Other/Oka/Geometry/RingedSpace/`. They are needed here at one ambient space only, so the concrete
  instances are stated instead and a third file is not opened. A consumer that wants the general
  form should file for it rather than widen these.
* **Nothing about `ComplexAnalytic.AnalyticSpace.sigma`.** A disjoint union of Hausdorff spaces is
  Hausdorff and `Other/Oka/AnalyticSpace/SigmaFiniteEtale.lean` would be the consumer; nothing asks for
  it yet.
* **No `degree` corollary.** `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` also asks
  `[PreconnectedSpace Y]` of the base, which no instance below supplies at any construction, so
  the separation hypothesis is not the only thing between it and a caller.

## Main results

- `ComplexAnalytic.t2Space_complexSpace`: `ℂ^ι` is Hausdorff.
- `ComplexAnalytic.t2Space_restrict_complexAffineSpace` and
  `ComplexAnalytic.t2Space_zeroLocusSubspace`: the two locally-ringed-space heads on the way to
  the zero locus.
- `ComplexAnalytic.t2Space_restrict`: **an open subspace of a Hausdorff analytic space is
  Hausdorff.**
- `ComplexAnalytic.t2Space_complexAffineSpace`: `ℂ^n` as an analytic space is Hausdorff.
- `ComplexAnalytic.t2Space_zeroLocus`: **the analytic subspace of an open subset of `ℂ^n` cut out
  by finitely many holomorphic functions is Hausdorff.**
- `ComplexAnalytic.t2Space_node`: the node is Hausdorff ; the first singular space here to be so.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

/-- **`ℂ^ι` is Hausdorff**, as a locally ringed space: its carrier is `ι → ℂ`.

This is the root of every instance below, and it is essential rather than decorative ; an
`Opens` of the root-namespace `complexAffineSpace` is a subtype of *this* carrier, and without this
head `ComplexAnalytic.t2Space_restrict_complexAffineSpace` fails with
`failed to synthesize T2Space ↥V`. -/
instance t2Space_complexSpace (ι : Type u) [Fintype ι] : T2Space (complexSpace.{u} ι) :=
  inferInstanceAs (T2Space (ι → ℂ))

/-- **An open subset of `ℂ^n` is Hausdorff**, at the locally-ringed-space spelling
`ComplexAnalytic.AnalyticSpace.zeroLocus` builds its ambient with.

`AlgebraicGeometry.LocallyRingedSpace.restrict` carries the open set itself as its carrier, so
this is the subtype instance. -/
instance t2Space_restrict_complexAffineSpace (n : ℕ)
    (V : Opens (_root_.complexAffineSpace.{u} n)) :
    T2Space ((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding) :=
  inferInstanceAs (T2Space V)

/-- **The zero locus of finitely many holomorphic functions on an open subset of `ℂ^n` is
Hausdorff**, at the locally-ringed-space level.

`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace`'s carrier is
`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSpace`, a `def` wrapping the subtype of the zero
locus, and instance search does not unfold it; that is why this head exists at all and why
`ComplexAnalytic.t2Space_zeroLocus` cannot be proved from the instance above alone. -/
instance t2Space_zeroLocusSubspace {n k : ℕ} (V : Opens (_root_.complexAffineSpace.{u} n))
    (f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj
      (op ⊤)) :
    T2Space (((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocusSubspace f) :=
  inferInstanceAs (T2Space
    (((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocus f))

/-- **An open subspace of a Hausdorff analytic space is Hausdorff.**

This is the one instance below that is about an arbitrary analytic space, and it is the one every
consumer of `ComplexAnalytic.AnalyticSpace.restrictHom` needs: the source of a restricted morphism
is an open subspace of the source of the original. -/
instance t2Space_restrict (X : AnalyticSpace.{u}) [T2Space X] (U : X.Opens) :
    T2Space (X.restrict U : Type u) :=
  inferInstanceAs (T2Space U)

/-- **`ℂ^n` as a complex analytic space is Hausdorff.**

Not consumed by anything in `Other/Oka/`; it is here because `ComplexAnalytic.AnalyticSpace.zeroLocus`
reaches `ℂ^n` through the locally-ringed-space spelling and never through this one, so a caller
holding the analytic space would otherwise find no instance. -/
instance t2Space_complexAffineSpace (n : ℕ) :
    T2Space (AnalyticSpace.complexAffineSpace.{u} n : Type u) :=
  inferInstanceAs (T2Space (ULift.{u} (Fin n) → ℂ))

/-- **The analytic subspace of an open subset of `ℂ^n` cut out by finitely many holomorphic
functions is Hausdorff.**

`ComplexAnalytic.AnalyticSpace.ofCutOut` does not change the underlying locally ringed space
(`ComplexAnalytic.AnalyticSpace.ofCutOut_toLocallyRingedSpace`), so this is the instance above
read at the analytic space. -/
instance t2Space_zeroLocus {n k : ℕ} (V : TopologicalSpace.Opens (_root_.complexAffineSpace.{u} n))
    (f : Fin k → ((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj
      (op ⊤)) :
    T2Space (AnalyticSpace.zeroLocus.{u} V f : Type u) :=
  inferInstanceAs (T2Space
    (((_root_.complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocusSubspace f))

/-- **The node is Hausdorff.**

`ComplexAnalytic.AnalyticSpace.node` is `ComplexAnalytic.AnalyticSpace.zeroLocus ⊤ nodeSection`, so
this is one more `inferInstanceAs`. It is worth stating because the node is the first space here
that is *singular* ; the two coordinate axes of `ℂ²` meeting at the origin ; and separation is not
where singularity shows up. -/
instance t2Space_node : T2Space (AnalyticSpace.node.{u} : Type u) :=
  inferInstanceAs (T2Space (AnalyticSpace.zeroLocus.{u} ⊤ nodeSection.{u}))

end ComplexAnalytic

end
