/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.IsLocalHomeomorph
public import Other.Oka.AnalyticSpace.Finite

/-!
# Local isomorphisms of complex analytic spaces, and finite étale morphisms

A holomorphic map is a **local isomorphism** when its underlying map is a local homeomorphism and
every stalk map is an isomorphism, and **finite étale** when it is that and finite
(`ComplexAnalytic.AnalyticSpace.IsFinite`). This is the second rung of the Riemann existence
theorem's analytic side; the first is `Other/Oka/AnalyticSpace/Finite.lean` and the third is
`Other/Oka/AnalyticSpace/CoveringMap.lean`, which deduces from these two that the underlying map of a
finite étale morphism out of a Hausdorff analytic space is a covering map.

## Why two fields, and why one of them is not topological

`ComplexAnalytic.AnalyticSpace.IsFinite` is a condition on the underlying map and nothing else.
**A local isomorphism cannot be**: two analytic spaces with the same underlying space and
different structure sheaves are not locally isomorphic, so the condition has to see the sheaves,
and the two rungs therefore do *not* compose the way `IsFinite`'s two fields do. The definition
below meets that rather than hiding it ; one field is topological and one is about stalks, and the
class carries both.

**Why stalks rather than "locally an open immersion".**
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` is available and one could ask for a cover
of the source on which the morphism restricts to one. That is presumably equivalent ; a theorem,
and not proved here ; and it is worse to *use* either way: it quantifies over covers, so every
consumer begins by choosing one, whereas the stalk condition is checkable at a point, and this
repository already has the machinery for it: `ComplexAnalytic.IsCutOutBy` carries
`surjective_stalkMap` and `ker_stalkMap` as fields, and
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` is what makes the composition below one line.

**Why not `IsCoveringMap`.** Mathlib has it, and it is a *global* condition ; every point of the
target has an evenly covered neighbourhood ; strictly stronger than being a local homeomorphism.
For a **finite** local isomorphism the two agree, and that agreement is a theorem, of the same
kind as properness-versus-finiteness, which `Other/Oka/AnalyticSpace/Finite.lean` keeps out of its
definition and proves separately as
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber`. It is not in the
definition and it is not proved here; it is
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` in
`Other/Oka/AnalyticSpace/CoveringMap.lean`, the third rung, which imports this file.

**This paragraph used to say "onto a connected base", and connectedness is not a hypothesis of
that theorem.** A point outside the range is evenly covered by the empty index type. What
connectedness gives is that the number of sheets is constant ; a different statement, and now a
proved one: `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, in the same file as
the rung.

## What is not here

* **The Riemann existence theorem**, and any statement relating covers to field extensions. This
  is the notion RET is *about*; nothing here mentions `ℂ(X)`.
* **A `degree` function on morphisms ; this is no longer absent, and it is not in this file.**
  The bullet that used to stand here has been retired in four steps. It first said the constancy
  of the number of sheets over a connected base was not proved anywhere; it is, as
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` in
  `Other/Oka/AnalyticSpace/CoveringMap.lean`. It then said the common value was computed for no morphism;
  it is ; `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` puts the fibres of the trivial
  `ι`-sheeted cover at `Nat.card ι`, so every value is realised. **The fourth step retires it
  altogether**: `ComplexAnalytic.AnalyticSpace.degree` in `Other/Oka/AnalyticSpace/Degree.lean` is the
  `Nat`-valued invariant, the well-definedness obligation this bullet made the condition of
  having one is `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`, and the consumer it asked
  for is `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`. The computation
  above is now read as a degree, `ComplexAnalytic.AnalyticSpace.degree_sigmaFold`.
* **The analytification of a finite étale morphism** ; the other blocker of #551, stateable only
  now that this exists.
* **Cancellation for `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` ; this is no longer absent, and
  it is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the foot of this file.** A
  Galois-category structure on the finite étale covers of a fixed base ;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`, in `Other/Oka/AnalyticSpace/FiniteEtaleOver.lean` ;
  wants *"if `g` and `f ≫ g` are finite étale then `f` is"*. All four halves cancel and **the only
  hypothesis any of them needs is `[T2Space Y]` on the middle space**: three ask nothing at all ;
  `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` is both halves of the local-isomorphism rung
  and `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` is the fibre half of the finite one ;
  and the fourth, closedness of `f`, is
  `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` in `Other/Oka/AnalyticSpace/Finite.lean`,
  which asks nothing of `g` either.

  **What this bullet used to say was that closedness does not follow**, with the real line with
  two origins over the real line as the witness and the classical graph-and-fibre-product proof as
  the only route. **The witness is right and both conclusions drawn from it were wrong.** It is a
  counterexample ; but what it exhibits is a **non-Hausdorff middle space**, and not anything
  about the second factor: its two origins are
  two points of `Y` that no open set separates. At `[T2Space Y]` the cancellation holds for an
  arbitrary second factor, by `isProperMap_of_comp_of_t2` and the properness of a finite morphism,
  and no separatedness notion and no fibre product is needed at any point.

  **This repository has both of the things this bullet used to say it has not, and it acquired
  them on two different days.** `ComplexAnalytic.AnalyticSpace.isSeparatedMap`, declared in
  `Other/Oka/AnalyticSpace/SeparatedFiniteEtale.lean` on 2026-09-08, is the separatedness notion; and
  `ComplexAnalytic.AnalyticSpace.hasPullback`, declared in
  `Other/Oka/AnalyticSpace/PullbackReduction.lean` later the same day, is the fibre product over an
  arbitrary cospan, which includes the one the graph construction forms ; both spellings taken from
  `scripts/DumpOkaDecls.lean`'s output and not from a grep. **So the classical route is available
  now and this bullet is still not about it**:
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` is proved without either, at
  `[T2Space Y]`, by `isProperMap_of_comp_of_t2` and the properness of a finite morphism, and
  nothing below was changed by their arrival.

  **This sentence read *neither a separatedness notion … nor fibre products* until
  `Other/Oka/AnalyticSpace/PullbackOpen.lean` landed, and the second half of it is what that file
  falsified; it then read *no fibre product over a cospan neither of whose legs is the inclusion of
  an open subspace ; `Other/Oka/AnalyticSpace/PullbackOpen.lean` builds that one shape and prices the
  rest* until 2026-09-07, when `Other/Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` added a second shape;
  and it named those two shapes and no third until later the same day, when
  `Other/Oka/AnalyticSpace/CutOutFibreProduct.lean` added a third; and it opened *This repository still
  has no separatedness notion for `ComplexAnalytic.AnalyticSpace`, and no fibre product over a
  cospan neither of whose legs is …* until 2026-09-08, when both halves were falsified in one
  day.** The enumeration of shapes is retired with it: an arbitrary cospan has a fibre product, so
  there is no longer a list of shapes to keep.
  **Neither was ever what obstructed this**; a
  separation axiom on `Y` is a hypothesis and not a construction, and it is the whole of what was
  missing.
* **Grauert's finite mapping theorem**, which `Other/Oka/AnalyticSpace/Finite.lean` already records as
  absent.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsLocalIso`: **a local homeomorphism whose stalk maps are
  isomorphisms.**
- `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`: finite and a local isomorphism.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocalIso_id`, `isLocalIso_comp` and `isLocalIso_of_isIso`:
  the local isomorphisms contain the isomorphisms and are closed under composition.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`: **local isomorphism cancels** ; if `f ≫ g`
  and `g` are local isomorphisms then so is `f`, and neither half of the proof asks for anything
  this repository had to supply.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_id` and `isFiniteEtale_comp`: the same for finite
  étale morphisms, from the two rungs' versions.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`: **finite étale morphisms cancel** ; if
  `f ≫ g` is finite étale and `g` is a local isomorphism then so is `f`, for a Hausdorff middle
  space. That separation axiom is the whole cost of it and is spent entirely in the finite rung.
- `ComplexAnalytic.AnalyticSpace.isClopen_range_of_isLocalIso_of_isFinite` and
  `ComplexAnalytic.AnalyticSpace.isClopen_range_of_isFiniteEtale`: **the image of a finite local
  isomorphism is clopen** ; open because the morphism is a local isomorphism and closed because it
  is finite. No separation axiom, no connectedness, nothing about the source being inhabited.
- `ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite` and
  `ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale`: **a finite local isomorphism
  out of a non-empty space onto a preconnected base is surjective** ; the clopen image above, and a
  preconnected base has no other clopen set than `∅` and itself.
- `ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale`: **the same
  dichotomy with `[Nonempty]` moved out of the hypotheses and into the conclusion** ; over a
  preconnected base a finite étale morphism is surjective or its source is empty. The clopen
  argument is the one above and this adds none of its own; what it adds is that a caller who does
  not know the source is inhabited still gets an answer, which is what a statement quantifying
  over all objects of a category of covers needs.
- `ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective`: **the
  contrapositive**, which is the form a non-example is stated in ; it refutes finiteness from a
  missing point rather than from a non-closed set exhibited by hand.
- `ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective`: **a local isomorphism whose
  underlying map is bijective is an isomorphism**, which is the converse of
  `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso` under that one extra hypothesis. The sheaf
  comparison it needs is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` and
  the only repository-side step is the `ℂ`-linearity of the inverse.
- `ComplexAnalytic.AnalyticSpace.isIso_of_isFiniteEtale_of_injective`: **an injective finite étale
  morphism out of a non-empty space onto a preconnected base is an isomorphism** ;
  `ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` with the surjective half
  supplied by the clopen dichotomy, so that only injectivity is asked of the caller.
- `ComplexAnalytic.AnalyticSpace.isIso_of_isEmpty`: **a morphism whose target is empty is an
  isomorphism**, which is the same criterion with both halves of bijectivity and both fields of
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` discharged vacuously. It asks nothing of the source,
  which is empty as soon as the target is.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **A morphism of complex analytic spaces is a local isomorphism when its underlying map is a
local homeomorphism and every stalk map is an isomorphism.**

The underlying map is spelled `f.toLRSHom.base` and the stalk map `f.toLRSHom.stalkMap`, as
everywhere else here: `ComplexAnalytic.AnalyticSpace.Hom` is a
`AlgebraicGeometry.LocallyRingedSpace.Hom` together with a `ℂ`-linearity condition and its
category structure is defined through `toLRSHom`.

**Note which points the second field ranges over.** `isIso_stalkMap` is quantified over points
of the **source**, so it says nothing at points of the target outside the image. That is a remark
about how to read the field, not a reason the other one is needed: a local homeomorphism can miss
most of the target too.

**Neither implication between the fields is settled here.** No counterexample to either direction
is exhibited and neither is proved, so the two-field definition is a design choice and not a
theorem. -/
class IsLocalIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- The underlying map is a local homeomorphism. -/
  isLocalHomeomorph : IsLocalHomeomorph f.toLRSHom.base
  /-- Every stalk map is an isomorphism. -/
  isIso_stalkMap (x : X) : IsIso (f.toLRSHom.stalkMap x)

attribute [instance] IsLocalIso.isIso_stalkMap

/-- **The identity is a local isomorphism.** -/
instance isLocalIso_id (X : AnalyticSpace.{u}) : IsLocalIso (𝟙 X) where
  isLocalHomeomorph := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h]
    exact (Homeomorph.refl X).isLocalHomeomorph
  isIso_stalkMap x := by
    have h : (𝟙 X : X ⟶ X).toLRSHom = 𝟙 X.toLocallyRingedSpace := rfl
    rw [h, LocallyRingedSpace.stalkMap_id]
    exact CategoryTheory.IsIso.id _

/-- **A composite of local isomorphisms is a local isomorphism.**

`IsLocalHomeomorph.comp` and `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`.

**Why the two stalk hypotheses are passed explicitly, through
`CategoryTheory.IsIso.comp_isIso'`, rather than left to instance search.** After the rewrite the
goal's first stalk is indexed at `(f ≫ g).base x` while `h2` is indexed at `g.base (f.base x)`.
Those are the same point by `rfl` **at default transparency only**: reducing `(f ≫ g).base` to
`g.base ∘ f.base` unfolds the composition of `AlgebraicGeometry.LocallyRingedSpace.Hom`, which is
not reducible. **Instance search runs at reducible transparency**, so it cannot see that the two
`IsIso` statements are about the same morphism, and neither `infer_instance` with both hypotheses
as local instances nor `apply CategoryTheory.IsIso.comp_isIso` succeeds ; the latter unifies the
composite at default transparency and then fails on the very hypothesis in scope, one level down
and by the same cause.

The control is one keyword: `with_reducible exact CategoryTheory.IsIso.comp_isIso' h2 h1` fails
with exactly that mismatch of stalk objects, and removing `with_reducible` compiles. Nothing about
the composite shape is at fault ; `CategoryTheory.IsIso.comp_isIso` is an instance and closes the
generic goal; `comp_isIso'` is Mathlib's explicit-argument form, provided for this situation. -/
instance isLocalIso_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalIso f] [IsLocalIso g] : IsLocalIso (f ≫ g) where
  isLocalHomeomorph := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h]
    exact (IsLocalIso.isLocalHomeomorph (f := g)).comp (IsLocalIso.isLocalHomeomorph (f := f))
  isIso_stalkMap x := by
    have h : (f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom := rfl
    have h1 : IsIso (f.toLRSHom.stalkMap x) := IsLocalIso.isIso_stalkMap _
    have h2 : IsIso (g.toLRSHom.stalkMap ((ConcreteCategory.hom f.toLRSHom.base) x)) :=
      IsLocalIso.isIso_stalkMap _
    rw [h, LocallyRingedSpace.stalkMap_comp]
    exact CategoryTheory.IsIso.comp_isIso' h2 h1

/-- **Local isomorphism cancels**: if `f ≫ g` and `g` are local isomorphisms, then so is `f`.

**Both halves are free and neither is this repository's work**, which is the content of the
statement rather than a remark about the proof. The topological one is `IsLocalHomeomorph.of_comp`,
whose third hypothesis is the *continuity* of `f` alone ; and a morphism's base map is a `TopCat`
morphism, so it carries that with it. The stalk one is
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` read as a factorisation of the composite's
stalk map, plus two-out-of-three in the shape `CategoryTheory.IsIso.of_isIso_comp_left`.

**Nothing is asked of `f` that a morphism does not already have**, so this is a cancellation
statement with no side condition, unlike the finite rung's
`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`, which asks for injectivity of the second
factor. The module docstring's `## What is not here` says what that difference costs the finite
étale rung.

**It is a `theorem` and not an `instance`, deliberately.** As an instance it would fire on every
`ComplexAnalytic.AnalyticSpace.IsLocalIso` goal and ask instance search to invent both the object
`Z` and the morphism `g` to factor through, neither of which is determined by the goal.

`ComplexAnalytic.AnalyticSpace.isLocalIso_comp`, directly above, is the composition companion.
**The third position of two-out-of-three ; concluding about `g` from `f` and `f ≫ g` ; is not
stated here and should not be expected**: both hypotheses see `g` only along the image of `f`, the
stalk field of each being quantified over points of its own source, so `g` is unconstrained away
from that image. No morphism below is asked to witness that, and this sentence is a reading of the
two definitions rather than a theorem. -/
theorem isLocalIso_of_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalIso (f ≫ g)] [IsLocalIso g] : IsLocalIso f where
  isLocalHomeomorph :=
    IsLocalHomeomorph.of_comp (IsLocalIso.isLocalHomeomorph (f := f ≫ g))
      (IsLocalIso.isLocalHomeomorph (f := g)) f.toLRSHom.base.hom.continuous
  isIso_stalkMap x := by
    haveI : IsIso (g.toLRSHom.stalkMap (f.toLRSHom.base x) ≫ f.toLRSHom.stalkMap x) := by
      rw [← LocallyRingedSpace.stalkMap_comp]
      exact IsLocalIso.isIso_stalkMap (f := f ≫ g) x
    exact IsIso.of_isIso_comp_left (g.toLRSHom.stalkMap (f.toLRSHom.base x))
      (f.toLRSHom.stalkMap x)

/-- **An isomorphism is a local isomorphism.**

Its underlying map is a homeomorphism and its stalk maps are isomorphisms because the whole
morphism is one. The `haveI` has to be ascribed at `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom f`
and **not** at `forgetToLocallyRingedSpace.map f`: the two are `rfl`-equal and are different
discrimination-tree keys, so with the second spelling `infer_instance` fails. That seam is
recorded in `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`'s docstring and in
`ComplexAnalytic.range_base_localisationProj`'s; this is its third appearance. -/
theorem isLocalIso_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsLocalIso f where
  isLocalHomeomorph :=
    (LocallyRingedSpace.homeoOfIso
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f))).isLocalHomeomorph
  isIso_stalkMap x := by
    haveI : IsIso (AnalyticSpace.Hom.toLRSHom f) :=
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f)).isIso_hom
    infer_instance

/-- **A morphism is finite étale when it is finite and a local isomorphism.**

This is what the Riemann existence theorem is about on the analytic side. It is stated as a class
of its own rather than as a conjunction so that the instances below are found, and it carries no
field beyond the two.

**It is not `IsCoveringMap`** ; that is a condition on the underlying map alone, and this one is
not ; but it does imply it for a Hausdorff source:
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` in
`Other/Oka/AnalyticSpace/CoveringMap.lean`. This docstring used to say the implication was unproved; see
the module docstring for why the two notions are still kept apart. -/
class IsFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- It is finite. -/
  isFinite : IsFinite f
  /-- It is a local isomorphism. -/
  isLocalIso : IsLocalIso f

attribute [instance] IsFiniteEtale.isFinite IsFiniteEtale.isLocalIso

/-- **The identity is finite étale.** -/
instance isFiniteEtale_id (X : AnalyticSpace.{u}) : IsFiniteEtale (𝟙 X) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-- **A composite of finite étale morphisms is finite étale**, from the two rungs' composition
lemmas and nothing else. -/
instance isFiniteEtale_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFiniteEtale f] [IsFiniteEtale g] : IsFiniteEtale (f ≫ g) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-- **An isomorphism is finite étale.** -/
theorem isFiniteEtale_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsFiniteEtale f where
  isFinite := isFinite_of_isIso f
  isLocalIso := isLocalIso_of_isIso f

/-- **Finite étale morphisms cancel**: if `f ≫ g` is finite étale and `g` is a local isomorphism,
then `f` is finite étale ; provided `Y` is Hausdorff.

This is the statement `Other/Oka/AnalyticSpace/FiniteEtaleOver.lean` records as the first thing a
Galois-category structure on `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` would need, and it is
the two rungs' cancellations put together:
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` in `Other/Oka/AnalyticSpace/Finite.lean`,
and `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` above.

**`g` is asked to be a local isomorphism and not to be finite étale**, because that is all that is
used: the finite half of the cancellation asks nothing of `g` at all, and the local-isomorphism
half asks exactly this. A caller holding `[IsFiniteEtale g]` ; which is the Galois-category case ;
has it by `ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isLocalIso`, so nothing is lost by stating
the weaker hypothesis.

**`[T2Space Y]` is the whole cost of the statement**, it is on the middle space, and it is not
removable; see `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space`, which is where it is
spent and where the witness against dropping it is cited. Whether it can be dropped when `g` is
additionally *finite* étale is not asked here ; that witness has a second factor which is not a
local isomorphism, so it does not settle the question.

**It does not make the category Galois**, and `Other/Oka/AnalyticSpace/FiniteEtaleOver.lean` says what
else is wanted: `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is not carried across a general
square. **This clause read *no fibre product over a general cospan, hence no base change* until
2026-09-08**, when `Other/Oka/AnalyticSpace/PullbackReduction.lean` gave the general cospan its fibre
product; the base change that is still wanted is of the class and not of the limit, which is the
narrowing that file's bullet took on the same day. **The fibre functor
is no longer among it** ; `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` is in
that file, and its
fibres are finite with no hypothesis. **This sentence used to add *and every statement about that
functor beyond its two laws*, and it had already stopped being true before the branch that
removed it**: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq`
falsified it ; a statement about that functor, and neither of its laws ; and nothing swept this
file when it landed. What retires the clause outright rather than narrowing it is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq`, which is
faithfulness wherever its hypotheses hold. What is missing there is base change of the class over
a cospan of morphisms of covers, and `CategoryTheory.Functor.Faithful` as a class. **That clause
read *base change
over a general cospan* until 2026-09-08**, and was narrowed for the reason
`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet
gave ; the limit exists and the class carried across it does not ; which is the narrowing
the clause of this docstring naming `Other/Oka/AnalyticSpace/PullbackReduction.lean` took, in the same
push and by the same landing. **And it read *base change of the class over a general cospan*, and
named that bullet by the heading `## No base change of the class over a general cospan`, until
2026-09-15**, when
`Other/Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean` stated the class over every cospan of
`ComplexAnalytic.AnalyticSpace` and that bullet was re-headed
**No base change of the class over a cospan of morphisms of covers**. What is missing where a
Galois category needs it is unchanged across both moves, those cospans being cospans of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` throughout. -/
theorem isFiniteEtale_of_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [T2Space Y] [IsFiniteEtale (f ≫ g)] [IsLocalIso g] : IsFiniteEtale f where
  isFinite := isFinite_of_comp_of_t2Space f g
  isLocalIso := isLocalIso_of_comp f g

/-! ### The image of a finite local isomorphism, and surjectivity over a preconnected base -/

/-- **The image of a finite local isomorphism is clopen.**

The two rungs pull the image in opposite directions: a local isomorphism is a local
homeomorphism, hence an open map, so its image is **open** (`IsLocalHomeomorph.isOpenMap`); a
finite morphism has `IsClosedMap` as its first field, so the image of the whole source is
**closed**. Nothing else is used, and in particular no separation axiom and no connectedness.

**This was the anonymous `IsClopen` constructor that `IsClopen.eq_univ` was applied to inside
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite`'s proof, and is stated
here because it has a consumer that is not about surjectivity.** That theorem hands the clopen set
to `IsClopen.eq_univ`, which is where its `[PreconnectedSpace Y]` and `[Nonempty X]` are spent;
a caller that wants to *restrict the target to the image* ; which is what a direct-summand
statement does ; needs the clopen set and neither hypothesis. Splitting it costs the surjectivity
proof nothing: it now names this instead of repeating it.

**`[IsLocalIso f]` and `[IsFinite f]` rather than `[IsFiniteEtale f]`**, because that is what the
argument reads; the class form is
`ComplexAnalytic.AnalyticSpace.isClopen_range_of_isFiniteEtale` below. -/
theorem isClopen_range_of_isLocalIso_of_isFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsLocalIso f] [IsFinite f] : IsClopen (Set.range (f.toLRSHom.base : X → Y)) :=
  ⟨by simpa [Set.image_univ] using IsFinite.isClosedMap (f := f) Set.univ isClosed_univ,
    (IsLocalIso.isLocalHomeomorph (f := f)).isOpenMap.isOpen_range⟩

/-- **The image of a finite étale morphism is clopen**:
`ComplexAnalytic.AnalyticSpace.isClopen_range_of_isLocalIso_of_isFinite` at a caller holding the
class, whose two fields are instances. -/
theorem isClopen_range_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsFiniteEtale f] :
    IsClopen (Set.range (f.toLRSHom.base : X → Y)) :=
  isClopen_range_of_isLocalIso_of_isFinite f

/-- **A finite local isomorphism out of a non-empty space onto a preconnected base is
surjective.**

Connectedness closes the gap the two rungs leave:
`ComplexAnalytic.AnalyticSpace.isClopen_range_of_isLocalIso_of_isFinite` says the image is clopen,
on a preconnected base a clopen set is empty or everything, and a non-empty source rules out
empty.

**`[PreconnectedSpace Y]` and not `[ConnectedSpace Y]`**, because that is what the argument reads;
under `[Nonempty X]` the two coincide here, a point of `X` giving a point of `Y`. This headline
and the two below it said *connected* in an earlier draft, which is the slip the module
docstring already records once ; there in a place where connectedness was not a hypothesis at
all.

**This is what the module docstring's *"a point outside the range is evenly covered by the empty
index type"* costs.** That sentence is about why
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` needs no connectedness, and it
is right; this says that such a point exists only in the two cases named ; an empty source, or a
disconnected base ; so the two statements are about the same gap from opposite sides.

**Neither hypothesis is shown necessary here, and both have an evident candidate witness.** Both
fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` quantify over the source and so do both of
`ComplexAnalytic.AnalyticSpace.IsFinite`'s, so an empty source satisfies everything above
vacuously and `[Nonempty X]` cannot be dropped by any argument in this file;
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι` makes the inclusion of a member of a disjoint
union finite étale for **every** family, which is where a witness against `[PreconnectedSpace Y]`
would come from. **Neither is carried out: these are readings of two theorems and not statements
of this file**, and nothing below asserts that either hypothesis is irredundant.

**`[IsLocalIso f]` and `[IsFinite f]` rather than `[IsFiniteEtale f]`**, because that is what the
proof reads, and a caller holding the class has both by
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isFinite` and
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isLocalIso`, which are instances. The `IsFiniteEtale`
form is `ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale` below. -/
theorem surjective_base_of_isLocalIso_of_isFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsLocalIso f] [IsFinite f] [Nonempty X] [PreconnectedSpace Y] :
    Function.Surjective (f.toLRSHom.base : X → Y) :=
  Set.range_eq_univ.1
    (IsClopen.eq_univ (isClopen_range_of_isLocalIso_of_isFinite f) (Set.range_nonempty _))

/-- **A finite étale morphism out of a non-empty space onto a preconnected base is surjective**:
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite` at a caller holding the
class, whose two fields are instances. -/
theorem surjective_base_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [Nonempty X] [PreconnectedSpace Y] :
    Function.Surjective (f.toLRSHom.base : X → Y) :=
  surjective_base_of_isLocalIso_of_isFinite f

/-- **A finite étale morphism onto a preconnected base is surjective, or its source is empty.**

The same clopen dichotomy as
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale`, with `[Nonempty X]` read as the
other branch instead of as a hypothesis: a preconnected base has no clopen set but `∅` and itself,
and the range is empty exactly when the source is. **The proof is a case split and the theorem
above; no topology is done here that is not done there.**

**Why the weaker-looking form is the useful one.** The theorem above cannot be applied to an
object of a category of covers without first knowing that its total space is inhabited, which is
a fact about the object and not about the category; the disjunction can, and the empty branch is
then discharged by whatever the caller can say about maps out of an empty space. That is exactly
how `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq`
(`Other/Oka/AnalyticSpace/FiniteEtaleOver.lean`) removes the *point of the fibre* hypothesis from
faithfulness of the fibre functor.

**`[PreconnectedSpace Y]` and not `[ConnectedSpace Y]`**, following the theorem above; at an empty
base both branches hold and the statement says nothing, which is what a vacuous case ought to look
like rather than a defect. -/
theorem surjective_base_or_isEmpty_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [PreconnectedSpace Y] :
    Function.Surjective (f.toLRSHom.base : X → Y) ∨ IsEmpty (X : Type u) := by
  rcases isEmpty_or_nonempty (X : Type u) with h | h
  · exact Or.inr h
  · exact Or.inl (surjective_base_of_isFiniteEtale f)

/-- **A local isomorphism out of a non-empty space onto a preconnected base that misses a point
is not finite** ; the contrapositive of
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite`, and the form a
non-example is stated in.

It is the only *general criterion* the library has for refuting
`ComplexAnalytic.AnalyticSpace.IsFinite`'s **first** field;
`ComplexAnalytic.AnalyticSpace.not_isFinite_of_infinite_fiber` (`Other/Oka/AnalyticSpace/Finite.lean`)
refutes the second field. -/
theorem not_isFinite_of_isLocalIso_of_not_surjective {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsLocalIso f] [Nonempty X] [PreconnectedSpace Y]
    (hf : ¬ Function.Surjective (f.toLRSHom.base : X → Y)) : ¬ IsFinite f :=
  fun _ ↦ hf (surjective_base_of_isLocalIso_of_isFinite f)

/-! ### From a local isomorphism to an isomorphism -/

/-- **A local isomorphism whose underlying map is bijective is an isomorphism.**

This is the converse direction to `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso`, and it is
the step `Other/Oka/AnalyticSpace/Degree.lean` recorded as missing. **The reason recorded there was that
it needs a comparison of the two structure sheaves across the homeomorphism, and it does not**:
the comparison exists, for locally ringed spaces, at the generality this file needs, and the whole
of the proof is three Mathlib statements and one instance of this repository's.

* `IsLocalHomeomorph.isOpenEmbedding_of_injective` turns the topological field of
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` plus injectivity into an open embedding;
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` turns an open embedding
  whose stalk maps are isomorphisms into an open immersion ; **this is the sheaf comparison, and
  it was in Mathlib the whole time**; the stalk maps it asks for are
  `ComplexAnalytic.AnalyticSpace.IsLocalIso.isIso_stalkMap`, which is an instance;
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso` turns an open immersion with epi
  base into an isomorphism, `TopCat.epi_iff_surjective` supplying the epi from surjectivity;
* and `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace_reflectsIsomorphisms`
  (`Other/Oka/AnalyticSpace/Basic.lean`) carries the resulting isomorphism of locally ringed spaces back
  to one of analytic spaces. That is the only repository-side obligation and it is the
  `ℂ`-linearity of the inverse.

**Surjectivity is a hypothesis here and is not deduced.** The bijectivity asked for is of the
underlying map and both halves of it are used: injectivity for the open embedding, surjectivity
for the epi. Neither field of `ComplexAnalytic.AnalyticSpace.IsLocalIso` supplies either ; a local
homeomorphism can miss most of the target and can identify points.

**The `haveI` at the functor spelling is essential**, for the reason
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace_reflectsIsomorphisms`'s docstring gives:
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso` produces
`IsIso f.toLRSHom` and `CategoryTheory.isIso_of_reflects_iso` consumes
`IsIso (forgetToLocallyRingedSpace.map f)`, the two are `rfl`-equal, and they are different
discrimination-tree keys. -/
theorem isIso_of_isLocalIso_of_bijective {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [hf : IsLocalIso f] (hb : Function.Bijective (f.toLRSHom.base : X → Y)) : IsIso f := by
  have hoe : IsOpenEmbedding (f.toLRSHom.base : X → Y) :=
    hf.isLocalHomeomorph.isOpenEmbedding_of_injective hb.injective
  haveI : LocallyRingedSpace.IsOpenImmersion f.toLRSHom :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f.toLRSHom hoe
  haveI : Epi f.toLRSHom.base := (TopCat.epi_iff_surjective _).2 hb.surjective
  haveI : IsIso (forgetToLocallyRingedSpace.map f) :=
    LocallyRingedSpace.IsOpenImmersion.to_iso f.toLRSHom
  exact isIso_of_reflects_iso f forgetToLocallyRingedSpace

/-- **A morphism whose target is empty is an isomorphism.**

Everything `ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` asks is vacuous here.
A map into an empty type has an empty source, so both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` are discharged at a point of the source that does not
exist, injectivity likewise, and surjectivity at a point of the target that does not exist either.
**Nothing is asked of the source**: it is empty as soon as the target is, and `Function.isEmpty`
is that step.

**The hypothesis is an explicit argument and not an `[IsEmpty Y]` instance**, and the reason is a
run rather than a taste. The caller this is written for is a cover of an empty base, whose
structure morphism has target `(CategoryTheory.Functor.fromPUnit X).obj A.right` and not `X`:
search there reports `failed to synthesize IsEmpty` of that expression although the base's own
instance is in scope, so the instance form would have to be unfolded by hand at every use.
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty` takes the explicit form one shape down
and its docstring gives a reason of the same kind, about a carrier instance search does not
find. -/
theorem isIso_of_isEmpty {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (hY : IsEmpty (Y : Type u)) :
    IsIso f := by
  have hX : IsEmpty (X : Type u) := Function.isEmpty (β := (Y : Type u)) f.toLRSHom.base
  haveI : IsLocalIso f :=
    { isLocalHomeomorph := fun x ↦ (hX.false x).elim
      isIso_stalkMap := fun x ↦ (hX.false x).elim }
  exact isIso_of_isLocalIso_of_bijective f
    ⟨fun a ↦ (hX.false a).elim, fun y ↦ (hY.false y).elim⟩

/-- **An injective finite étale morphism out of a non-empty space onto a preconnected base is an
isomorphism.**

`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` wants bijectivity and this
supplies the surjective half from
`ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale`, whose empty branch
`[Nonempty X]` rules out. **No fibre is counted and no degree appears**, which is why this is
stated here and not with the degree: the hypothesis is injectivity of a map, not a number.

**`[Nonempty X]` and not `[Nonempty Y]`**, because that is what the dichotomy's other branch
refutes; a point of the target says nothing about whether the source is empty, and over an empty
source the unique morphism to a non-empty base is injective and is not an isomorphism.

The degree form of the hypothesis is
`ComplexAnalytic.AnalyticSpace.isIso_of_degree_eq_one` (`Other/Oka/AnalyticSpace/Degree.lean`), which
asks `[T2Space X]` in exchange for the covering-map theory that identifies the degree with a fibre
count; **this asks for no separation axiom at all**, and the two are therefore not the same
statement with the hypothesis rewritten. -/
theorem isIso_of_isFiniteEtale_of_injective {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [PreconnectedSpace (Y : Type u)] [Nonempty (X : Type u)]
    (hi : Function.Injective (f.toLRSHom.base : X → Y)) : IsIso f := by
  refine isIso_of_isLocalIso_of_bijective f ⟨hi, ?_⟩
  rcases surjective_base_or_isEmpty_of_isFiniteEtale f with h | h
  · exact h
  · exact absurd h (not_isEmpty_of_nonempty _)

end ComplexAnalytic.AnalyticSpace

end
