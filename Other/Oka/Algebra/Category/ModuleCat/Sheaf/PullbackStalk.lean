/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Other.Oka.Algebra.Category.ModuleCat.Presheaf.PullbackStalk

/-!
# The stalk of a pullback of sheaves of modules is the base change of the stalk

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`. This is the
sheaf-level form of
`Other/Oka/Algebra/Category/ModuleCat/Presheaf/PullbackStalk.lean`:

```
SheafOfModules.pullbackStalkIso :
  pullback φ ⋙ stalkFunctor x ≅ stalkFunctor (f x) ⋙ ModuleCat.extendScalars (ringStalkMap f φ x)
```

That is, **`(f^* M)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}`, naturally in `M`.**

## What the sheaf level costs over the presheaf level

Exactly one thing: `PresheafOfModules.skyscraper_isSheaf`. Everything else transfers across
`SheafOfModules.forget`, which is fully faithful and which `SheafOfModules.pushforward` commutes
with **definitionally**: `((pushforward φ).obj M).val` is
`(PresheafOfModules.pushforward φ.hom).obj M.val` by `rfl`. So the natural isomorphism of right
adjoints is the presheaf one wrapped in `⟨·⟩`, and
the two triangle identities are `SheafOfModules.hom_ext` applied to the presheaf ones.

Nothing here unfolds `SheafOfModules.pullback`. Although `SheafOfModules.pullbackIso` decomposes
that functor through presheaf pullback and sheafification, the adjoint-uniqueness proof avoids
needing a separate comparison between module sheafification and stalks.

## Sheaves of *commutative* rings

`SheafOfModules R` wants `R : Sheaf J RingCat`, and the stalk of a `RingCat`-valued presheaf is a
`RingCat`. `ModuleCat.extendScalars` is available only between **commutative** rings, so the
statement has to know that the stalks are commutative. `SheafOfModules.ofCommRingCat` is the
wrapper that says so: it takes a `CommRingCat`-valued presheaf together with a proof that its
composite with `forget₂` is a sheaf, which is exactly the data
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` is built from, and `ringSheaf` is
*definitionally* of this form, recorded as
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf_eq_ofCommRingCat`.

## Main definitions

- `SheafOfModules.ofCommRingCat`, `SheafOfModules.stalkFunctor`,
  `SheafOfModules.skyscraper`, `SheafOfModules.skyscraperFunctor`.
- `SheafOfModules.sheafRingHom`: the morphism of sheaves of rings attached to a morphism of
  presheaves of commutative rings over a continuous map.

## Main results

- `SheafOfModules.stalkSkyscraperAdj`: `stalkFunctor x ⊣ skyscraperFunctor x`.
- `SheafOfModules.skyscraperFunctorPushforwardIso`: the pushforward of a skyscraper sheaf is a
  skyscraper sheaf.
- `SheafOfModules.pullbackStalkIso`: **the stalk of a pullback is the base change of the stalk.**

## What is not here

* **Exactness.** No flatness is used and none is needed; the base-change formula holds for an
  arbitrary morphism of ringed spaces. Turning it into exactness of the pullback is where
  flatness enters, and that is a separate theorem.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

@[expose] public noncomputable section

namespace SheafOfModules

section

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})
  (hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- The sheaf of rings attached to a presheaf of commutative rings whose underlying presheaf of
rings is a sheaf.

`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` is definitionally of this form, which is what
lets everything below be instantiated at a locally ringed space. -/
abbrev ofCommRingCat : Sheaf (Opens.grothendieckTopology ↑X) RingCat.{u} := ⟨_, hR⟩

variable {R hR} (x : X)

/-- **The stalk of a sheaf of modules at a point of the space, as a functor** to modules over the
stalk of the sheaf of rings.

This is the module-valued stalk functor used in the base-change statement below. -/
def stalkFunctor :
    SheafOfModules.{u} (ofCommRingCat R hR) ⥤ ModuleCat.{u} (R.stalk x) :=
  forget _ ⋙ PresheafOfModules.stalkFunctor x

/-- The skyscraper sheaf of modules at `x` with value `N`. -/
def skyscraper (N : ModuleCat.{u} (R.stalk x)) : SheafOfModules.{u} (ofCommRingCat R hR) :=
  ⟨PresheafOfModules.skyscraper x N, PresheafOfModules.skyscraper_isSheaf x N⟩

/-- The skyscraper functor. -/
def skyscraperFunctor :
    ModuleCat.{u} (R.stalk x) ⥤ SheafOfModules.{u} (ofCommRingCat R hR) where
  obj N := skyscraper (hR := hR) x N
  map g := ⟨(PresheafOfModules.skyscraperFunctor x).map g⟩
  map_id _ := hom_ext ((PresheafOfModules.skyscraperFunctor x).map_id _)
  map_comp _ _ := hom_ext ((PresheafOfModules.skyscraperFunctor x).map_comp _ _)

/-- **The stalk functor is left adjoint to the skyscraper functor** for sheaves of modules.

Transferred from `PresheafOfModules.stalkSkyscraperAdj` across the fully faithful
`SheafOfModules.forget`; the sheaf condition on the skyscraper is what makes the transfer
possible and is the only thing the sheaf level costs. -/
def stalkSkyscraperAdj :
    stalkFunctor (hR := hR) x ⊣ skyscraperFunctor (hR := hR) x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        ((PresheafOfModules.stalkSkyscraperAdj x).homEquiv M.val N).trans
          { toFun := fun ψ ↦ ⟨ψ⟩
            invFun := Hom.val
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
      homEquiv_naturality_left_symm := fun f g ↦
        (PresheafOfModules.stalkSkyscraperAdj x).homEquiv_naturality_left_symm f.val g.val
      homEquiv_naturality_right := fun f g ↦ hom_ext
        ((PresheafOfModules.stalkSkyscraperAdj x).homEquiv_naturality_right f g) }

end

section

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {S : Y.Presheaf CommRingCat.{u}}
  {R : X.Presheaf CommRingCat.{u}}
  {hS : TopCat.Presheaf.IsSheaf (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  {hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (φ : S ⟶ (Opens.map f).op ⋙ R) (x : X)

/-- The morphism of sheaves of rings determined by a morphism of presheaves of commutative rings
over a continuous map.

`AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom` is definitionally of this form. -/
def sheafRingHom :
    ofCommRingCat S hS ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ofCommRingCat R hR) :=
  ⟨PresheafOfModules.forgetRingHom f φ⟩

local instance presheafPushforwardIsRightAdjoint :
    (PresheafOfModules.pushforward.{u}
      (sheafRingHom (hS := hS) (hR := hR) φ).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top
      (sheafRingHom (hS := hS) (hR := hR) φ).hom)

local instance sheafPushforwardIsRightAdjoint :
    (pushforward.{u} (sheafRingHom (hS := hS) (hR := hR) φ)).IsRightAdjoint :=
  (PullbackConstruction.adjunction
    (sheafRingHom (hS := hS) (hR := hR) φ)).isRightAdjoint

/-- **Pushing a skyscraper sheaf at `x` forward along `f` is the skyscraper sheaf at `f x`.**

This is where the geometry is; see `PresheafOfModules.pushforwardSkyscraperIso`, of which this is
the image under `SheafOfModules.forget`. -/
def skyscraperFunctorPushforwardIso :
    skyscraperFunctor (hR := hR) x ⋙ pushforward (sheafRingHom (hS := hS) (hR := hR) φ) ≅
      ModuleCat.restrictScalars (PresheafOfModules.ringStalkMap f φ x).hom ⋙
        skyscraperFunctor (hR := hS) (f x) :=
  NatIso.ofComponents
    (fun N ↦
      { hom := ⟨(PresheafOfModules.pushforwardSkyscraperIso f φ x N).hom⟩
        inv := ⟨(PresheafOfModules.pushforwardSkyscraperIso f φ x N).inv⟩
        hom_inv_id := hom_ext (PresheafOfModules.pushforwardSkyscraperIso f φ x N).hom_inv_id
        inv_hom_id := hom_ext (PresheafOfModules.pushforwardSkyscraperIso f φ x N).inv_hom_id })
    (fun g ↦ hom_ext ((PresheafOfModules.skyscraperFunctorPushforwardIso f φ x).hom.naturality g))

/-- **The stalk of a pullback of sheaves of modules is the base change of the stalk**:
`(f^* M)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}`, naturally in `M`.

Both sides are left adjoints and the proof is that their right adjoints agree, which is
`skyscraperFunctorPushforwardIso`. Nothing unfolds `pullback`. -/
def pullbackStalkIso :
    pullback.{u} (sheafRingHom (hS := hS) (hR := hR) φ) ⋙ stalkFunctor (hR := hR) x ≅
      stalkFunctor (hR := hS) (f x) ⋙
        ModuleCat.extendScalars (PresheafOfModules.ringStalkMap f φ x).hom :=
  Adjunction.leftAdjointUniq
    (((pullbackPushforwardAdjunction.{u} (sheafRingHom (hS := hS) (hR := hR) φ)).comp
      (stalkSkyscraperAdj (hR := hR) x)).ofNatIsoRight
        (skyscraperFunctorPushforwardIso (hS := hS) (hR := hR) φ x))
    ((stalkSkyscraperAdj (hR := hS) (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (PresheafOfModules.ringStalkMap f φ x).hom))

end

end SheafOfModules
