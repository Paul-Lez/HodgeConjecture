/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Basic
public import Other.Oka.Topology.Sheaves.Stalks

/-!
# Being cut out by global sections is local on the target

`ComplexAnalytic.IsCutOutBy i f` says that the closed immersion `i : A ⟶ B` exhibits `A` as the
analytic subspace of `B` cut out by the global sections `f`. This file proves that the property
survives shrinking the target to an open subset:

```
ComplexAnalytic.IsCutOutBy.restrictOpen :
  IsCutOutBy i f → ∀ V : Opens B, IsCutOutBy (restrictHom i V) (restrictSections V f)
```

where `restrictHom i V` restricts `i` to the preimage of `V` and `restrictSections V f` restricts
the family. Together with `ComplexAnalytic.isCLinearHom_restrictHom` this is what says a *chart*
of a complex analytic space may be shrunk, which is what an open subspace of an analytic space
needs in order to be one itself.

## Why the target rather than the source

One wants to shrink the *source* ; to pass from a chart on `U₀` to a chart on `U₀ ⊓ U`. Stating
it that way would require manufacturing the open subset of the target, and the natural candidate
is `B ∖ i '' (A ∖ A')`, which is open because `i` is a **closed** embedding and whose preimage is
exactly `A'` because `i` is **injective**. That works, but it is not needed: `i` is an embedding,
so every open subset of `A` already *is* the preimage of an open subset of `B`, and taking the
target open as given makes the closedness of the image free ; `i '' A` is closed in `B`, hence
`i '' A ∩ V` is closed in `V`.

## How the four conditions restrict

`ComplexAnalytic.restrictHom` is built with `LocallyRingedSpace.IsOpenImmersion.lift`, so it
comes with `ComplexAnalytic.restrictHom_fac` and nothing else; every fact about it is derived
from that one equation.

* the closed embedding is `IsEmbedding.of_comp` against the inclusion of `V`, with the range
  computed by `ComplexAnalytic.mem_range_base_restrictHom_iff`;
* `range_base` is the only condition that is not stalk-local, and it reduces to the original one
  because the germ of a restricted section is the image of the original germ under the stalk map
  of `LocallyRingedSpace.ofRestrict` (`ComplexAnalytic.Γgerm_restrictSections`), which is an
  isomorphism and therefore reflects the maximal ideal;
* the two stalk conditions come from
  `ComplexAnalytic.stalkMap_restrictHom_eq`, which factors the stalk map of `restrictHom i V`
  as an isomorphism, then `i.stalkMap`, then an isomorphism. Applying `stalkMap` to
  `restrictHom_fac` produces a `TopCat.Presheaf.stalkSpecializes` transport between the stalks at
  two points which are equal but not definitionally so, and
  `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom` together with
  `TopCat.Presheaf.stalkCongr_hom_germ` is what makes that transport tractable.

## Shrinking a chart

Together with `ComplexAnalytic.IsCutOutBy.iso_comp` ; the companion of
`ComplexAnalytic.IsCutOutBy.comp_iso` for an isomorphism of the **target** ; this is what makes
an open subspace of a complex analytic space a complex analytic space, in
`Other/Oka/AnalyticSpace/OpenSubspace.lean`.

`iso_comp` is here rather than next to `comp_iso` in `Other/Oka/AnalyticSpace/Basic.lean` because its
`range_base` condition goes through `ComplexAnalytic.mem_maximalIdeal_stalkMap_iff`, which is in
this file. The reason the pair is
needed at all: `AnalyticSpace.local_model` demands a chart whose target is `ℂ^n` restricted to
an open subset **of `ℂ^n`**, and what `restrictOpen` produces is a chart whose target is
`(ℂ^n|V)|V'`, a restriction of a restriction. The two are isomorphic ; by
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`, since both map into `ℂ^n`
with the same image, so no bespoke `restrictRestrict` is needed ; and `iso_comp` transports the
cut-out along that isomorphism.

## Main definitions

- `ComplexAnalytic.restrictHom`: the restriction of a morphism to the preimage of an open subset
  of the target.
- `ComplexAnalytic.restrictSections`: the restriction of a family of global sections.
- `ComplexAnalytic.restrictStalkEquiv`: the isomorphism through which the stalk map of
  `restrictHom` factors.

## Main results

- `ComplexAnalytic.IsCutOutBy.restrictOpen`: **being cut out by global sections is local on the
  target.**
- `ComplexAnalytic.isCLinearHom_restrictHom`: the restriction of a `ℂ`-linear morphism is
  `ℂ`-linear.
- `ComplexAnalytic.stalkMap_restrictHom_eq`: the stalk map of the restriction, factored.
- `ComplexAnalytic.isClosedEmbedding_base_restrictHom`: the restriction of a morphism whose base
  is a closed embedding is one, with no condition on the open subset.
- `ComplexAnalytic.IsCutOutBy.iso_comp`: being cut out is transported by an isomorphism of the
  target, along which the cutting family is pulled back.
- `ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ`: **the sheaf map of the restriction is the
  sheaf map of `i`**, on a section over `V` viewed as a global section of `𝒪_{B|V}` ; which is
  what makes a chart usable on a section that does not extend.
- `ComplexAnalytic.restrictHom_comp`: **restricting a composite is composing the restrictions.**
- `ComplexAnalytic.surjective_base_restrictHom` and
  `ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range`: **over an open subset of
  the target that lies inside the image, the restriction is surjective, and is a closed embedding
  as soon as the base is an embedding.** The second is the companion of
  `ComplexAnalytic.isClosedEmbedding_base_restrictHom` at the opposite trade ; a weaker hypothesis
  on `i` against a hypothesis on `V` ; and is what an *open* immersion needs, whose base is never
  a closed embedding unless it is surjective.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {A B : LocallyRingedSpace.{u}}

lemma range_comp_le (i : A ⟶ B) (V : Opens B) :
    Set.range ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding ≫ i).base) ⊆
      Set.range (B.ofRestrict V.isOpenEmbedding).base := by
  rw [LocallyRingedSpace.range_ofRestrict]
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  exact hx

/-- The restriction of `i` to the preimage of an open subset of the target. -/
def restrictHom (i : A ⟶ B) (V : Opens B) :
    A.restrict ((Opens.map i.base).obj V).isOpenEmbedding ⟶ B.restrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (B.ofRestrict V.isOpenEmbedding)
    (A.ofRestrict _ ≫ i) (range_comp_le i V)

lemma restrictHom_fac (i : A ⟶ B) (V : Opens B) :
    restrictHom i V ≫ B.ofRestrict V.isOpenEmbedding =
      A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding ≫ i :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

lemma base_restrictHom (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.ofRestrict V.isOpenEmbedding).base ((restrictHom i V).base x) =
      i.base ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding ⟶ B ↦ m.base)
      (restrictHom_fac i V)) x

/-- **Restricting a composite is composing the restrictions.**

The two sides have *definitionally* the same source ; `(Opens.map (f ≫ h).base).obj V` and
`(Opens.map f.base).obj ((Opens.map h.base).obj V)` are both the preimage of a preimage ; which
is why the equation typechecks with no transport in it.

**Written as a term and not as a `rw` chain, and that is forced rather than stylistic.** The goal
after `← cancel_mono` mentions `(Opens.map (f ≫ h).base).obj V`, and there `V` is elaborated at
the `toTopCat` spelling of the carrier while `Opens.map` asks for the `toPresheafedSpace` one; the
two are the same type and `rw` cannot build a motive across them, failing with *"Did not find an
occurrence of the pattern"* on a `Category.assoc` whose pattern is visibly present. That is the
same seam `ComplexAnalytic.isFinite_analytification_comp_projRestrict` records at its range step
in `Other/Oka/Analytification/OpenBaseFiniteness.lean`; a term proof sidesteps the motive entirely.

`ComplexAnalytic.restrictHom` is `LocallyRingedSpace.IsOpenImmersion.lift`, so the only equation
available about it is `ComplexAnalytic.restrictHom_fac` ; and the inclusion of an open subspace is
a monomorphism, which is what turns three uses of that equation into this one. -/
lemma restrictHom_comp {C : LocallyRingedSpace.{u}} (f : A ⟶ B) (h : B ⟶ C) (V : Opens C) :
    restrictHom (f ≫ h) V =
      restrictHom f ((Opens.map h.base).obj V) ≫ restrictHom h V :=
  (cancel_mono (C.ofRestrict V.isOpenEmbedding)).1 <|
    (restrictHom_fac (f ≫ h) V).trans <|
      Eq.symm <|
        (Category.assoc (restrictHom f ((Opens.map h.base).obj V)) (restrictHom h V)
            (C.ofRestrict V.isOpenEmbedding)).trans <|
          (congrArg (restrictHom f ((Opens.map h.base).obj V) ≫ ·) (restrictHom_fac h V)).trans <|
            ((Category.assoc (restrictHom f ((Opens.map h.base).obj V))
                (B.ofRestrict ((Opens.map h.base).obj V).isOpenEmbedding) h).symm.trans
              ((congrArg (· ≫ h) (restrictHom_fac f ((Opens.map h.base).obj V))).trans
                (Category.assoc _ f h)))

lemma stalkMap_restrictHom (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x) ≫
        (restrictHom i V).stalkMap x =
      (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom ≫
        i.stalkMap ((A.ofRestrict _).base x) ≫ (A.ofRestrict _).stalkMap x := by
  rw [← LocallyRingedSpace.stalkMap_comp, ← LocallyRingedSpace.stalkMap_comp]
  exact LocallyRingedSpace.stalkMap_congr_hom _ _ (restrictHom_fac i V) x

variable {k : ℕ}

/-- The family `f` of global sections of `𝒪_B`, restricted to an open subset. -/
def restrictSections (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤)) :
    Fin k → (B.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) :=
  fun j ↦ (LocallyRingedSpace.Γ.map (B.ofRestrict V.isOpenEmbedding).op).hom (f j)

lemma Γgerm_restrictSections (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤))
    (y : B.restrict V.isOpenEmbedding) (j : Fin k) :
    (B.restrict V.isOpenEmbedding).presheaf.Γgerm y (restrictSections V f j) =
      ((B.ofRestrict V.isOpenEmbedding).stalkMap y).hom
        (B.presheaf.Γgerm ((B.ofRestrict V.isOpenEmbedding).base y) (f j)) :=
  (LocallyRingedSpace.stalkMap_germ_apply (B.ofRestrict V.isOpenEmbedding) ⊤ y trivial (f j)).symm

/-- The stalk map of an open immersion reflects and preserves the maximal ideal. -/
lemma mem_maximalIdeal_stalkMap_iff {X Y : LocallyRingedSpace.{u}} (g : X ⟶ Y) (x : X)
    [IsIso (g.stalkMap x)] (a : Y.presheaf.stalk (g.base x)) :
    (g.stalkMap x).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x)) := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_map_iff (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv a)

lemma mem_range_base_restrictHom_iff (i : A ⟶ B) (V : Opens B)
    (y : B.restrict V.isOpenEmbedding) :
    y ∈ Set.range (restrictHom i V).base ↔
      (B.ofRestrict V.isOpenEmbedding).base y ∈ Set.range i.base := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(A.ofRestrict _).base x, (base_restrictHom i V x).symm⟩
  · rintro ⟨a, ha⟩
    have haV : a ∈ (Opens.map i.base).obj V := by
      change i.base a ∈ V
      rw [ha]
      exact y.2
    refine ⟨⟨a, haV⟩, ?_⟩
    apply Subtype.ext
    exact (base_restrictHom i V ⟨a, haV⟩).trans ha

theorem isClosedEmbedding_base_restrictHom {i : A ⟶ B} (hce : IsClosedEmbedding i.base)
    (V : Opens B) : IsClosedEmbedding (restrictHom i V).base := by
  have hcomp : ⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base =
      ⇑i.base ∘ ⇑(A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base :=
    funext (base_restrictHom i V)
  have hemb : IsEmbedding (⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base) := by
    rw [hcomp]
    exact hce.isEmbedding.comp ((Opens.map i.base).obj V).isOpenEmbedding.isEmbedding
  have hset : Set.range (restrictHom i V).base =
      ⇑(B.ofRestrict V.isOpenEmbedding).base ⁻¹' Set.range i.base :=
    Set.ext fun y ↦ mem_range_base_restrictHom_iff i V y
  refine ⟨IsEmbedding.of_comp (restrictHom i V).base.hom.continuous
    (B.ofRestrict V.isOpenEmbedding).base.hom.continuous hemb, ?_⟩
  rw [hset]
  exact hce.isClosed_range.preimage (B.ofRestrict V.isOpenEmbedding).base.hom.continuous

/-- **An open subset of the target that lies inside the image is covered by the restriction.**

Read the other way round: shrinking the target to a `V` the morphism already surjects onto makes
the restricted morphism surjective. It is `ComplexAnalytic.mem_range_base_restrictHom_iff` and
nothing else ; that lemma decides membership of the range upstairs by membership downstairs, and
`hV` supplies the latter at every point of `V` by construction.

**No embedding hypothesis is used here**, which is why it is stated apart from the closed
embedding below: surjectivity of the restriction is a statement about the two ranges alone. -/
theorem surjective_base_restrictHom (i : A ⟶ B) {V : Opens B}
    (hV : (V : Set B) ⊆ Set.range i.base) :
    Function.Surjective (restrictHom i V).base :=
  fun y ↦ (mem_range_base_restrictHom_iff i V y).2 (hV y.2)

/-- **A morphism whose base is an embedding restricts to a closed embedding over any open subset
of its image.**

The companion of `ComplexAnalytic.isClosedEmbedding_base_restrictHom` at the opposite trade: that
one asks the base to be *closed* and puts no condition on `V`; this one weakens the hypothesis on
`i` to an embedding and asks instead that `V` lie inside the image. The embedding half of the two
proofs is the same `IsEmbedding.of_comp` argument, and only the closedness of the range is
different ; here the range is **everything**, by `ComplexAnalytic.surjective_base_restrictHom`,
and `isClosed_univ` closes it.

**The pair is what an open immersion needs**, and neither member covers it: the inclusion of an
open subspace is an embedding whose base is not closed, so the first theorem does not apply to it,
while `V ⊆ range` is a real hypothesis that the first theorem does not need. The consumer is
`Other/Oka/Analytification/StandardEtaleFiniteness.lean`, where `i` is the standard étale
analytification read as `D(G)` inside a hypersurface and `V` is the part of that hypersurface
lying over an open subset of the base on which `G` cannot vanish. -/
theorem isClosedEmbedding_base_restrictHom_of_subset_range {i : A ⟶ B}
    (hemb : IsEmbedding i.base) {V : Opens B} (hV : (V : Set B) ⊆ Set.range i.base) :
    IsClosedEmbedding (restrictHom i V).base := by
  have hcomp : ⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base =
      ⇑i.base ∘ ⇑(A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base :=
    funext (base_restrictHom i V)
  have hemb' : IsEmbedding (⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base) := by
    rw [hcomp]
    exact hemb.comp ((Opens.map i.base).obj V).isOpenEmbedding.isEmbedding
  refine ⟨IsEmbedding.of_comp (restrictHom i V).base.hom.continuous
    (B.ofRestrict V.isOpenEmbedding).base.hom.continuous hemb', ?_⟩
  rw [Set.range_eq_univ.2 (surjective_base_restrictHom i hV)]
  exact isClosed_univ

theorem range_base_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B) :
    Set.range (restrictHom i V).base =
      {y | ∀ j, (B.restrict V.isOpenEmbedding).presheaf.Γgerm y (restrictSections V f j) ∈
        IsLocalRing.maximalIdeal ((B.restrict V.isOpenEmbedding).presheaf.stalk y)} := by
  refine Set.ext fun y ↦ (mem_range_base_restrictHom_iff i V y).trans
    ((Set.ext_iff.1 hcut.range_base _).trans (forall_congr' fun j ↦ ?_))
  rw [Γgerm_restrictSections]
  exact (mem_maximalIdeal_stalkMap_iff (B.ofRestrict V.isOpenEmbedding) y _).symm

lemma stalkMap_restrictHom_eq (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (restrictHom i V).stalkMap x =
      inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)) ≫
        (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom ≫
          i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) ≫
            (A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x := by
  rw [← stalkMap_restrictHom, IsIso.inv_hom_id_assoc]

theorem surjective_stalkMap_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    Function.Surjective ((restrictHom i V).stalkMap x).hom := by
  rw [stalkMap_restrictHom_eq]
  intro c
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x)).surjective c
  obtain ⟨a, rfl⟩ := hcut.surjective_stalkMap _ b
  obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom).surjective a
  obtain ⟨e, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)))).surjective d
  exact ⟨e, rfl⟩

lemma inv_hom_apply {R S : CommRingCat.{u}} (e : R ⟶ S) [IsIso e] (v : R) :
    (inv e).hom (e.hom v) = v := by
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- The composite isomorphism from the stalk of `B|V` at `(restrictHom i V) x` to the stalk of
`B` at `i x`, through which the stalk map of the restriction factors. -/
def restrictStalkEquiv (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.restrict V.isOpenEmbedding).presheaf.stalk ((restrictHom i V).base x) ≅
      B.presheaf.stalk (i.base ((A.ofRestrict _).base x)) :=
  asIso (inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)) ≫
    (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom)

lemma restrictStalkEquiv_Γgerm (i : A ⟶ B) (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤))
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) (j : Fin k) :
    (restrictStalkEquiv i V x).hom.hom
        ((B.restrict V.isOpenEmbedding).presheaf.Γgerm ((restrictHom i V).base x)
          (restrictSections V f j)) =
      B.presheaf.Γgerm (i.base ((A.ofRestrict _).base x)) (f j) := by
  rw [Γgerm_restrictSections]
  change ((B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom).hom
      ((inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x))).hom
        (((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)).hom _)) = _
  rw [inv_hom_apply]
  exact TopCat.Presheaf.stalkCongr_hom_germ B.presheaf _ ⊤ trivial trivial (f j)

lemma stalkMap_restrictHom_eq' (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (restrictHom i V).stalkMap x =
      (restrictStalkEquiv i V x).hom ≫
        i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) ≫
          (A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x := by
  rw [stalkMap_restrictHom_eq, restrictStalkEquiv, asIso_hom, Category.assoc]

theorem ker_stalkMap_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    RingHom.ker ((restrictHom i V).stalkMap x).hom =
      Ideal.span (Set.range fun j ↦ (B.restrict V.isOpenEmbedding).presheaf.Γgerm
        ((restrictHom i V).base x) (restrictSections V f j)) := by
  have hθinj : Function.Injective
      ⇑((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x).hom :=
    (ConcreteCategory.bijective_of_isIso _).injective
  have hval : ∀ v, ((restrictHom i V).stalkMap x).hom v =
      ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x).hom
        ((i.stalkMap _).hom ((restrictStalkEquiv i V x).hom.hom v)) := fun v ↦ by
    rw [stalkMap_restrictHom_eq']
    rfl
  set eq := (restrictStalkEquiv i V x).commRingCatIsoToRingEquiv with heq
  have hstep : RingHom.ker ((restrictHom i V).stalkMap x).hom =
      Ideal.comap eq (RingHom.ker (i.stalkMap
        ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x)).hom) := by
    ext v
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, hval]
    constructor
    · intro hf
      exact hθinj (hf.trans (map_zero _).symm)
    · intro hf
      have hf' : (i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x)).hom
          ((restrictStalkEquiv i V x).hom.hom v) = 0 := hf
      rw [hf', map_zero]
  rw [hstep, hcut.ker_stalkMap, ← Ideal.map_symm eq, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  refine congrArg Set.range (funext fun j ↦ ?_)
  exact (eq.symm_apply_eq).2 (restrictStalkEquiv_Γgerm i V f x j).symm

/-- **Being cut out by global sections is local on the target**: restricting a closed immersion
to the preimage of an open subset of the target still cuts it out, by the restricted family. -/
theorem IsCutOutBy.restrictOpen {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B) :
    IsCutOutBy (restrictHom i V) (restrictSections V f) where
  isClosedEmbedding := isClosedEmbedding_base_restrictHom hcut.isClosedEmbedding V
  range_base := range_base_restrictHom hcut V
  surjective_stalkMap := surjective_stalkMap_restrictHom hcut V
  ker_stalkMap := ker_stalkMap_restrictHom hcut V

/-- **Being cut out by global sections is transported by an isomorphism of the target**: if
`i : A ⟶ B` cuts out `A` by `f` and `e : B ≅ C`, then `i ≫ e.hom` cuts out `A` by the family `f`
pulled back along `e.inv`.

This is the companion of `ComplexAnalytic.IsCutOutBy.comp_iso`, which does the same for an
isomorphism of the *source* and needs no change of family. Here the family has to move, because
the cutting sections live on the target.

Everything reduces to one computation, `hgerm`: the germ of `f j` at `b` is the image of the
germ of the pulled-back section at `e.hom.base b` under `e.hom.stalkMap b`. The two stalk
conditions are then compositions with an isomorphism, and `range_base` is the same computation
read through `ComplexAnalytic.mem_maximalIdeal_stalkMap_iff`. -/
theorem IsCutOutBy.iso_comp {C : LocallyRingedSpace.{u}} {i : A ⟶ B}
    {f : Fin k → B.presheaf.obj (op ⊤)} (hcut : IsCutOutBy i f) (e : B ≅ C) :
    IsCutOutBy (i ≫ e.hom) (fun j ↦ (LocallyRingedSpace.Γ.map e.inv.op).hom (f j)) := by
  set g : Fin k → C.presheaf.obj (op ⊤) :=
    fun j ↦ (LocallyRingedSpace.Γ.map e.inv.op).hom (f j) with hg
  have hgerm (b : B) (j : Fin k) :
      (e.hom.stalkMap b).hom (C.presheaf.Γgerm (e.hom.base b) (g j)) =
        B.presheaf.Γgerm b (f j) := by
    rw [← LocallyRingedSpace.Γgerm_Γ_map, hg]
    refine congrArg (B.presheaf.Γgerm b) ?_
    rw [← LocallyRingedSpace.Γ_map_comp_apply, e.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hmem (b : B) (j : Fin k) :
      C.presheaf.Γgerm (e.hom.base b) (g j) ∈
          IsLocalRing.maximalIdeal (C.presheaf.stalk (e.hom.base b)) ↔
        B.presheaf.Γgerm b (f j) ∈ IsLocalRing.maximalIdeal (B.presheaf.stalk b) := by
    rw [← hgerm b j]
    exact (mem_maximalIdeal_stalkMap_iff e.hom b _).symm
  have hcomp (a : A) (v : C.presheaf.stalk ((i ≫ e.hom).base a)) :
      ((i ≫ e.hom).stalkMap a).hom v =
        (i.stalkMap a).hom ((e.hom.stalkMap (i.base a)).hom v) := by
    rw [LocallyRingedSpace.stalkMap_comp]
    rfl
  refine ⟨(LocallyRingedSpace.homeoOfIso e).isClosedEmbedding.comp hcut.isClosedEmbedding, ?_,
    fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [show ⇑(i ≫ e.hom).base = ⇑e.hom.base ∘ ⇑i.base from rfl, Set.range_comp,
      hcut.range_base]
    refine Set.ext fun y ↦ ?_
    obtain ⟨b, rfl⟩ := (LocallyRingedSpace.homeoOfIso e).surjective y
    exact ((LocallyRingedSpace.homeoOfIso e).injective.mem_set_image (a := b)).trans
      (forall_congr' fun j ↦ (hmem b j).symm)
  · intro c
    obtain ⟨v, rfl⟩ := hcut.surjective_stalkMap a c
    obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (e.hom.stalkMap (i.base a))).surjective v
    exact ⟨w, hcomp a w⟩
  · set eq := (asIso (e.hom.stalkMap (i.base a))).commRingCatIsoToRingEquiv with heq
    have hstep : RingHom.ker ((i ≫ e.hom).stalkMap a).hom =
        Ideal.comap eq (RingHom.ker (i.stalkMap a).hom) := by
      ext v
      change ((i ≫ e.hom).stalkMap a).hom v = 0 ↔
        (i.stalkMap a).hom ((e.hom.stalkMap (i.base a)).hom v) = 0
      rw [hcomp a v]
    rw [hstep, hcut.ker_stalkMap, ← Ideal.map_symm eq, Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    refine congrArg Set.range (funext fun j ↦ ?_)
    exact (eq.symm_apply_eq).2 (hgerm (i.base a) j).symm

/-- **The sheaf map of `ComplexAnalytic.restrictHom` is the sheaf map of `i`**, on a section of
`𝒪_B` over `V` viewed as a global section of `𝒪_{B|V}`.

This is the fact that makes a chart usable on a section that does **not** extend to the whole
chart target. `restrictHom_fac` computes `Γ.map (restrictHom i V).op` only on sections pulled
back from `Γ(B, 𝒪)`, and `restrictHom` is an `IsOpenImmersion.lift`, whose sheaf map is not
otherwise computable ; so `AlgebraicGeometry.LocallyRingedSpace.exists_localLift`'s output, which
is a section over an open subset and generally over nothing larger, was out of reach.

The proof is entirely on stalks and uses **no equation of opens**: `section_ext` reduces to
germs, `Γgerm_Γ_map` turns `Γ.map` into `stalkMap`, `stalkMap_restrictHom` factors that through
`i.stalkMap`, and
`AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict` handles both restrictions. -/
theorem Γ_map_restrictHom_toRestrictΓ (i : A ⟶ B) (V : Opens B) (u : B.presheaf.obj (op V)) :
    (LocallyRingedSpace.Γ.map (restrictHom i V).op).hom (B.toRestrictΓ V u) =
      A.toRestrictΓ ((Opens.map i.base).obj V) (i.c.app (op V) u) := by
  refine TopCat.Presheaf.section_ext
    (A.restrict ((Opens.map i.base).obj V).isOpenEmbedding).sheaf ⊤ _ _ fun y _ ↦ ?_
  refine Eq.trans (LocallyRingedSpace.Γgerm_Γ_map (restrictHom i V) (B.toRestrictΓ V u) y) ?_
  refine Eq.trans (congrArg (fun a ↦ ((restrictHom i V).stalkMap y).hom a)
    (B.Γgerm_toRestrictΓ V u ((restrictHom i V).base y))) ?_
  refine Eq.trans (ConcreteCategory.comp_apply
    ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base y))
    ((restrictHom i V).stalkMap y) _).symm ?_
  refine Eq.trans (congrArg (fun m : B.presheaf.stalk
      ((B.ofRestrict V.isOpenEmbedding).base ((restrictHom i V).base y)) ⟶
      (A.restrict ((Opens.map i.base).obj V).isOpenEmbedding).presheaf.stalk y ↦
    m.hom (B.presheaf.germ V _ ((restrictHom i V).base y).2 u))
      (stalkMap_restrictHom i V y)) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (fun a ↦
    ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap y).hom
      ((i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base y)).hom a))
    (TopCat.Presheaf.stalkCongr_hom_germ B.presheaf
      (Inseparable.of_eq (base_restrictHom i V y)) V _ y.2 u)) ?_
  refine Eq.trans (congrArg (fun a ↦
      ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap y).hom a)
    (LocallyRingedSpace.stalkMap_germ_apply i V
      ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base y) _ u)) ?_
  exact (A.Γgerm_toRestrictΓ ((Opens.map i.base).obj V) (i.c.app (op V) u) y).symm

/-- Restricting a `ℂ`-linear morphism to the preimage of an open subset of the target is
`ℂ`-linear for the restricted algebra structures. -/
theorem isCLinearHom_restrictHom {i : A ⟶ B} {α : ℂ →+* A.presheaf.obj (op ⊤)}
    {β : ℂ →+* B.presheaf.obj (op ⊤)} (h : IsCLinearHom i α β) (V : Opens B) :
    IsCLinearHom (restrictHom i V) (A.resAlgMap α ((Opens.map i.base).obj V)) (B.resAlgMap β V) :=
  fun c ↦ by
    have key := LocallyRingedSpace.Γ_map_comp_apply (restrictHom i V)
      (B.ofRestrict V.isOpenEmbedding) (β c)
    rw [restrictHom_fac, LocallyRingedSpace.Γ_map_comp_apply, h c] at key
    exact key.symm

end ComplexAnalytic

end
