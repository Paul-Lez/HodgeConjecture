/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Other.Oka.Algebra.Category.ModuleCat.Stalk

/-!
# Skyscraper presheaves of modules, and the adjunction with the stalk

Material for `Mathlib/Algebra/Category/ModuleCat/Presheaf/Skyscraper.lean`.

For a presheaf of commutative rings `R` on a space `X`, a point `x`, and a module `N` over the
stalk `R.stalk x`, the **skyscraper presheaf of modules** `PresheafOfModules.skyscraper x N` has

```
(skyscraper x N).obj U = PLift (x ∈ U.unop) → N
```

with `r : R.obj U` acting through the germ map `R.germ U x h : R.obj U ⟶ R.stalk x`. It is right
adjoint to `PresheafOfModules.stalkFunctor x`, and **that adjunction is the whole point of the
file**: it is what identifies a stalk of a pullback as a base change, in
`Other/Oka/Algebra/Category/ModuleCat/Presheaf/PullbackStalk.lean`.

## Why the construction uses `PLift`

The obvious model is `(x ∈ U.unop) → N`, and it has no `AddCommGroup` instance: `Pi.addCommGroup`
is stated for an index in `Type _`, and `x ∈ U.unop` is a `Prop`. `PLift` moves it into `Type`
and everything else goes through, including the two places where the identification has to be
definitional: `x ∈ (Opens.map f).obj V` is `f x ∈ V`, and `PLift` of the one is `PLift` of the
other.

## Why not Mathlib's `skyscraperPresheaf`

`Mathlib/Topology/Sheaves/Skyscraper.lean` has `skyscraperPresheaf p₀ A`, defined with
`if p₀ ∈ U then A else terminal C`. That model is the wrong one to carry a module structure: the
*type* depends on the `if`, so `Module (R.obj U) (if … then … else …)` has to be produced by a
`dite` on types and every restriction map splits into four cases. The `PLift`-of-a-`Prop` model
has one uniform formula for the action, `r • s = fun h ↦ R.germ _ x h.down r • s h`, and the
degenerate case is handled by there being no `h` to feed it.

The two models are isomorphic; nothing here needs that, and it is not proved.

## Main definitions

- `PresheafOfModules.skyscraper`, `PresheafOfModules.skyscraperFunctor`.
- `PresheafOfModules.toSkyscraper` and `PresheafOfModules.fromStalk`: the two directions of the
  adjunction bijection.

## Main results

- `PresheafOfModules.stalkSkyscraperAdj`: **`stalkFunctor x ⊣ skyscraperFunctor x`.**

## The sheaf condition

`PresheafOfModules.skyscraperAb_isSheaf` says the underlying abelian presheaf is a sheaf, by
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`. The gluing of a compatible family
`sf i : PLift (x ∈ U i) → N` over a cover is *choose an `i` with `x ∈ U i` and take `sf i`*, and
compatibility is what makes the choice immaterial. That is the entire proof, and it is short
because the `PLift` model has no degenerate branch to treat separately.

This is not needed by the presheaf-level base-change theorem; it is needed to move that theorem
to `SheafOfModules`, which is what
`Other/Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean` does.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}} (x : X)

/-- The abelian presheaf underlying the skyscraper presheaf of modules. -/
def skyscraperAb (N : ModuleCat.{u} (R.stalk x)) : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map i := AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun s h ↦ s ⟨i.unop.le h.down⟩) (fun _ _ ↦ rfl))
  map_id _ := rfl
  map_comp _ _ := rfl

instance skyscraperModule (N : ModuleCat.{u} (R.stalk x)) (U : (Opens X)ᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) ((skyscraperAb x N).obj U) :=
  letI : ∀ _ : PLift (x ∈ U.unop), Module (R.obj U) N := fun h ↦
    Module.compHom N (R.germ U.unop x h.down).hom
  inferInstanceAs (Module (R.obj U) (PLift (x ∈ U.unop) → N))

lemma skyscraperAb_smul_apply (N : ModuleCat.{u} (R.stalk x)) (U : (Opens X)ᵒᵖ)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (s : (skyscraperAb x N).obj U)
    (h : PLift (x ∈ U.unop)) :
    (r • s) h = R.germ U.unop x h.down r • s h :=
  rfl

lemma skyscraperAb_map_smul (N : ModuleCat.{u} (R.stalk x)) ⦃U V : (Opens X)ᵒᵖ⦄ (i : U ⟶ V)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (m : (skyscraperAb x N).obj U) :
    (skyscraperAb x N).map i (r • m) =
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map i r • (skyscraperAb x N).map i m := by
  funext h
  change R.germ U.unop x _ r • m _ = R.germ V.unop x h.down (R.map i r) • m _
  rw [TopCat.Presheaf.germ_res_apply' R i x h.down r]

/-- The skyscraper presheaf of modules at `x` with value `N`. -/
def skyscraper (N : ModuleCat.{u} (R.stalk x)) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  ofPresheaf (skyscraperAb x N) (skyscraperAb_map_smul x N)

/-- The skyscraper functor. -/
def skyscraperFunctor :
    ModuleCat.{u} (R.stalk x) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) where
  obj N := skyscraper x N
  map {N₁ N₂} g := homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun s h ↦ g (s h))
        (fun _ _ ↦ by funext h; exact map_add g.hom _ _))
      naturality := fun _ _ _ ↦ rfl }
    (fun U r s ↦ by funext h; exact map_smul g.hom _ _)
  map_id _ := by ext U s; rfl
  map_comp _ _ := by ext U s; rfl

variable {x}

variable {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  {N : ModuleCat.{u} (R.stalk x)}

/-- The cocone under which `fromStalk` is a colimit descent. -/
@[simps]
def skyscraperCocone (ψ : M ⟶ skyscraper x N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m ↦ Hom.app ψ (op U.unop.1) m ⟨U.unop.2⟩)
        (fun a b ↦ congrFun (map_add (Hom.app ψ (op U.unop.1)).hom a b) _))
      naturality := fun U V i ↦ by
        ext m
        exact congrFun (naturality_apply ψ ((OpenNhds.inclusion x).op.map i) m) _ }

/-- The additive map out of the stalk determined by a morphism into the skyscraper. -/
def fromStalkAb (ψ : M ⟶ skyscraper x N) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x ⟶ AddCommGrpCat.of N :=
  colimit.desc _ (skyscraperCocone ψ)

/- Not `@[simp]`, for the same reason as `PresheafOfModules.stalkFunctor_map_germ`: the
left-hand side is not in simp-normal form. -/
lemma fromStalkAb_germ (ψ : M ⟶ skyscraper x N) (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) :
    fromStalkAb ψ (TopCat.Presheaf.germ M.presheaf U x hx m) = Hom.app ψ (op U) m ⟨hx⟩ :=
  ConcreteCategory.congr_hom (colimit.ι_desc (skyscraperCocone ψ) (op ⟨U, hx⟩)) m

/-- The map out of the stalk determined by a morphism into the skyscraper. -/
def fromStalk (ψ : M ⟶ skyscraper x N) : (stalkFunctor x).obj M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fromStalkAb ψ
      map_add' a b := map_add _ a b
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
        obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
        rw [← TopCat.Presheaf.germ_res_apply R (homOfLE (inf_le_left : U ⊓ V ≤ U)) x
              ⟨hxU, hxV⟩ r,
            ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (inf_le_right : U ⊓ V ≤ V)) x
              ⟨hxU, hxV⟩ m,
            ← germ_smul, fromStalkAb_germ, fromStalkAb_germ, RingHom.id_apply]
        exact (congrFun (map_smul (Hom.app ψ (op (U ⊓ V))).hom _ _) _).trans
          (skyscraperAb_smul_apply x N (op (U ⊓ V)) _ _ _) }

/-- The morphism into the skyscraper determined by a map out of the stalk. -/
def toSkyscraper (g : (stalkFunctor x).obj M ⟶ N) : M ⟶ skyscraper x N :=
  homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m h ↦ g (TopCat.Presheaf.germ M.presheaf U.unop x h.down m))
        (fun a b ↦ by funext h; erw [map_add, map_add]; rfl))
      naturality := fun U V i ↦ by
        ext m
        funext h
        exact congrArg _ (TopCat.Presheaf.germ_res_apply' M.presheaf i x h.down m) }
    (fun U r m ↦ by
      funext h
      change g (TopCat.Presheaf.germ M.presheaf U.unop x h.down (r • m)) =
        R.germ U.unop x h.down r • g (TopCat.Presheaf.germ M.presheaf U.unop x h.down m)
      erw [germ_smul]
      exact map_smul g.hom _ _)

@[simp]
lemma toSkyscraper_app_apply (g : (stalkFunctor x).obj M ⟶ N) (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) :
    Hom.app (toSkyscraper g) (op U) m ⟨hx⟩ =
      g (TopCat.Presheaf.germ M.presheaf U x hx m) :=
  rfl

lemma fromStalk_toSkyscraper (g : (stalkFunctor x).obj M ⟶ N) :
    fromStalk (toSkyscraper g) = g := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  exact fromStalkAb_germ (toSkyscraper g) U hxU m

lemma toSkyscraper_fromStalk (ψ : M ⟶ skyscraper x N) :
    toSkyscraper (fromStalk ψ) = ψ := by
  ext U m
  funext h
  exact fromStalkAb_germ ψ U.unop h.down m

lemma fromStalk_comp {M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (f : M' ⟶ M) (ψ : M ⟶ skyscraper x N) :
    fromStalk (f ≫ ψ) = (stalkFunctor x).map f ≫ fromStalk ψ := by
  ext m
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M'.presheaf m
  change fromStalkAb (f ≫ ψ) (TopCat.Presheaf.germ M'.presheaf U x hxU m) =
    fromStalkAb ψ ((stalkFunctor x).map f (TopCat.Presheaf.germ M'.presheaf U x hxU m))
  rw [fromStalkAb_germ, stalkFunctor_map_germ, fromStalkAb_germ]
  rfl

variable (x)

/-- **The stalk functor is left adjoint to the skyscraper functor**, for presheaves of
modules on a topological space. -/
def stalkSkyscraperAdj : stalkFunctor (R := R) x ⊣ skyscraperFunctor (R := R) x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := toSkyscraper
          invFun := fromStalk
          left_inv := fromStalk_toSkyscraper
          right_inv := toSkyscraper_fromStalk }
      homEquiv_naturality_left_symm := fun f g ↦ fromStalk_comp f g
      homEquiv_naturality_right := by
        intro M N N' f g
        ext U m
        funext h
        rfl }


variable (N : ModuleCat.{u} (R.stalk x))

/-- **The abelian presheaf underlying a skyscraper presheaf of modules is a sheaf.**

The gluing of a compatible family over a cover of `U` is: given `x ∈ U`, choose an `i` with
`x ∈ U i` and take the value of the `i`-th section. Compatibility is exactly what makes the
choice immaterial, and uniqueness is the same computation read backwards. -/
theorem skyscraperAb_isSheaf : (skyscraperAb x N).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  refine ⟨fun h ↦ sf (Classical.choose (Opens.mem_iSup.mp h.down))
      ⟨Classical.choose_spec (Opens.mem_iSup.mp h.down)⟩, ?_, ?_⟩
  · intro i
    funext h
    have hx : x ∈ iSup U := (Opens.leSupr U i).le h.down
    exact congrFun (hsf (Classical.choose (Opens.mem_iSup.mp hx)) i)
      ⟨⟨Classical.choose_spec (Opens.mem_iSup.mp hx), h.down⟩⟩
  · intro y hy
    funext h
    exact congrFun (hy (Classical.choose (Opens.mem_iSup.mp h.down)))
      ⟨Classical.choose_spec (Opens.mem_iSup.mp h.down)⟩

/-- **The skyscraper presheaf of modules is a sheaf.** -/
theorem skyscraper_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↑X) (skyscraper x N).presheaf :=
  skyscraperAb_isSheaf x N

end PresheafOfModules
