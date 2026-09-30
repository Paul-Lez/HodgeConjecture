/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Other.Oka.Algebra.Category.ModuleCat.Presheaf.Skyscraper

/-!
# The stalk of a pullback of presheaves of modules is the base change of the stalk

Material for `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean`.

For a continuous map `f : X ⟶ Y`, a morphism of presheaves of commutative rings
`φ : S ⟶ (Opens.map f).op ⋙ R` and a point `x : X`,

```
PresheafOfModules.pullbackStalkIso :
  pullback φ ⋙ stalkFunctor x ≅ stalkFunctor (f x) ⋙ ModuleCat.extendScalars (ringStalkMap f φ x)
```

That is, **`(f^* M)_x ≅ R_x ⊗_{S_{f x}} M_{f x}`, naturally in `M`.**

## Why this is a theorem rather than a rewrite

`PresheafOfModules.pullback φ` is defined as `(pushforward φ).leftAdjoint`. The proof below
uses that defining adjunction directly rather than relying on a pointwise tensor-product model.

## The proof, which never touches the definition of `pullback`

Both sides are left adjoints, and the whole content is that their right adjoints agree:

* `pullback φ ⋙ stalkFunctor x` is left adjoint to
  `skyscraperFunctor x ⋙ pushforward φ`, by `pullbackPushforwardAdjunction` composed with
  `stalkSkyscraperAdj`;
* `stalkFunctor (f x) ⋙ extendScalars` is left adjoint to
  `restrictScalars ⋙ skyscraperFunctor (f x)`, by `stalkSkyscraperAdj` composed with
  `ModuleCat.extendRestrictScalarsAdj`;

and `skyscraperFunctorPushforwardIso` says the two right adjoints are isomorphic: **pushing a
skyscraper at `x` forward along `f` is the skyscraper at `f x`**. That is where the geometry is,
and it is almost definitional: the underlying abelian presheaves are *equal*, since
`x ∈ (Opens.map f).obj V` is `f x ∈ V`, so the comparison morphism is built by `homMk (𝟙 _)` and
its two round trips are `rfl`. The only thing to prove is that the two module structures agree,
and that is `ringStalkMap_germ`.

`Adjunction.leftAdjointUniq` then produces the natural isomorphism.

**No flatness is used anywhere and none is needed.** The base-change *formula* holds for an
arbitrary morphism of ringed spaces; flatness is what turns it into an exactness statement, and
that is a separate theorem.

## Main definitions

- `PresheafOfModules.ringStalkMap`: the induced map `S_{f x} ⟶ R_x` on stalks of the presheaves
  of rings.

## Main results

- `PresheafOfModules.skyscraperFunctorPushforwardIso`: the pushforward of a skyscraper is a
  skyscraper.
- `PresheafOfModules.pullbackStalkIso`: **the stalk of a pullback is the base change of the
  stalk.**

## What is not here

* **The sheaf-level statement.** `SheafOfModules.pullback` is a presheaf pullback followed by
  sheafification, so the sheaf-level version needs additionally that the skyscraper is a sheaf.
* **Exactness.** See above: this file consumes no flatness because the statement needs none.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PresheafOfModules

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {S : Y.Presheaf CommRingCat.{u}}
  {R : X.Presheaf CommRingCat.{u}} (φ : S ⟶ (Opens.map f).op ⋙ R) (x : X)

/-- The map on stalks induced by a morphism of presheaves of rings over a continuous map. -/
def ringStalkMap : S.stalk (f x) ⟶ R.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f x)).map φ ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} f R x

@[simp]
lemma ringStalkMap_germ (V : Opens Y) (hx : f x ∈ V) (s : S.obj (op V)) :
    ringStalkMap f φ x (S.germ V (f x) hx s) =
      R.germ ((Opens.map f).obj V) x hx (φ.app (op V) s) := by
  change TopCat.Presheaf.stalkPushforward CommRingCat.{u} f R x
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f x)).map φ (S.germ V (f x) hx s)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply (C := CommRingCat.{u}) V (f x) hx φ s]
  erw [TopCat.Presheaf.stalkPushforward_germ_apply]

/-- The morphism of presheaves of rings, at the `RingCat` spelling `pushforward` consumes. -/
abbrev forgetRingHom :
    S ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (Opens.map f).op ⋙ (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  Functor.whiskerRight φ (forget₂ CommRingCat.{u} RingCat.{u})

/-- **Pushing a skyscraper forward along `f` is the skyscraper at `f x`**, over the restriction
of scalars along the stalk map. -/
def pushforwardSkyscraperIso (N : ModuleCat.{u} (R.stalk x)) :
    (pushforward (forgetRingHom f φ)).obj (skyscraper x N) ≅
      skyscraper (f x) ((ModuleCat.restrictScalars (ringStalkMap f φ x).hom).obj N) :=
  { hom := homMk (𝟙 _) (fun V r m ↦ by
      funext h
      change R.germ ((Opens.map f).obj V.unop) x h.down (φ.app V r) • m h =
        ringStalkMap f φ x (S.germ V.unop (f x) h.down r) • m h
      rw [ringStalkMap_germ])
    inv := homMk (𝟙 _) (fun V r m ↦ by
      funext h
      change ringStalkMap f φ x (S.germ V.unop (f x) h.down r) • m h =
        R.germ ((Opens.map f).obj V.unop) x h.down (φ.app V r) • m h
      rw [ringStalkMap_germ])
    hom_inv_id := by ext V m; rfl
    inv_hom_id := by ext V m; rfl }

/-- The pushforward of a skyscraper is a skyscraper, naturally. -/
def skyscraperFunctorPushforwardIso :
    skyscraperFunctor x ⋙ pushforward (forgetRingHom f φ) ≅
      ModuleCat.restrictScalars (ringStalkMap f φ x).hom ⋙ skyscraperFunctor (f x) :=
  NatIso.ofComponents (pushforwardSkyscraperIso f φ x) (fun _ ↦ by ext V m; rfl)

/-- **The stalk of a pullback of presheaves of modules is the base change of the stalk.** -/
def pullbackStalkIso :
    PresheafOfModules.pullback (forgetRingHom f φ) ⋙ stalkFunctor x ≅
      stalkFunctor (f x) ⋙ ModuleCat.extendScalars (ringStalkMap f φ x).hom :=
  Adjunction.leftAdjointUniq
    (((PresheafOfModules.pullbackPushforwardAdjunction (forgetRingHom f φ)).comp
      (stalkSkyscraperAdj x)).ofNatIsoRight (skyscraperFunctorPushforwardIso f φ x))
    ((stalkSkyscraperAdj (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (ringStalkMap f φ x).hom))

end PresheafOfModules
