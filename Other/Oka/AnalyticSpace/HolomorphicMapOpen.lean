/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.HomToComplex
public import Other.Oka.AnalyticSpace.OpenSubspace

/-!
# Holomorphic maps out of an open subset of `ℂ^n`

`Other/Oka/AnalyticSpace/HolomorphicMap.lean` turns a family of `κ` **entire** functions on `ℂ^ι` into
a morphism of complex analytic spaces `ℂ^ι ⟶ ℂ^κ`. This file does the same for a family of
holomorphic functions on an **open subset** `V ⊆ ℂ^ι`, producing
`ComplexAnalytic.okaMapOpenHom : ℂ^ι|V ⟶ ℂ^κ`, and deduces

```
ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict :
  ∀ g : Γ(ℂ^n|V, 𝒪), ∃ φ : ℂ^n|V ⟶ ℂ, AnalyticSpace.coordPullback φ 0 = g
```

which is taxis #628 for `Z` an open subspace of `ℂ^n`, one step past the `Z = ℂ^n` of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine`.

## Why this is the next step and not a generalisation for its own sake

Taxis #654 asks for a morphism `Z ⟶ ℂ` from a global section of `𝒪_Z` for an **arbitrary**
complex analytic space `Z`. On a chart, `Z` is cut out inside an open `V ⊆ ℂ^m`, and a section
of `𝒪_Z` lifts ; only locally, and only to a holomorphic function on an open subset of `ℂ^m`,
never to an entire one (`AlgebraicGeometry.LocallyRingedSpace.exists_localLift`). So the entire
case of `Other/Oka/AnalyticSpace/HolomorphicMap.lean` cannot be composed with a chart, and this file
is the missing input rather than a convenience.

## The one piece of analysis

`OkaAnalytic.comp_analytic` requires the inner map to be analytic **everywhere**, which the
extension by zero of a holomorphic function on a proper open subset is not. The weakening is
`OkaAnalytic.comp_analyticOn` in `Other/Oka/StructureSheaf.lean`: analyticity is required only at the
points of the open set the conclusion is about, which is all the conclusion can see. That one
hypothesis is the whole difference between the entire case and this one; everything else here
is bookkeeping about `AlgebraicGeometry.LocallyRingedSpace.restrict`.

## The bookkeeping, stated once

The global sections of `ℂ^ι|V` are `OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)`, not
`OkaRing V`: the two opens have the same points but are **not** definitionally equal, and
neither are the two rings. This file takes its input in the first form, because that is what a
global section of the analytic space `ℂ^ι|V` actually is, and converts membership with
`ComplexAnalytic.mem_functor_obj_top_iff` exactly twice ; once for analyticity and once for
continuity.

## Main definitions

- `ComplexAnalytic.okaMapOpenHom`: a family of `κ` holomorphic functions on `V ⊆ ℂ^ι` as a
  morphism of locally ringed spaces `ℂ^ι|V ⟶ ℂ^κ`.
- `ComplexAnalytic.AnalyticSpace.okaMapOpen`: the same as a morphism of complex analytic spaces.

## Main results

- `ComplexAnalytic.Γ_map_okaMapOpenHom_coord`: **pulling the `j`-th coordinate of `ℂ^κ` back
  along `okaMapOpenHom u` gives `u j`** ; the construction is inverse to taking coordinates.
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_restrict`: every family of `m`
  global sections of `𝒪_{ℂ^n|V}` is the tuple of coordinate pullbacks along a morphism
  `ℂ^n|V ⟶ ℂ^m`, and `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict`, its
  `m = 1` case, which is the spelling callers want.
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict`: every global section of
  `𝒪_{ℂ^n|V}` is the pullback of the coordinate along a morphism `ℂ^n|V ⟶ ℂ`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {ι κ : Type u} [Fintype ι]

section Bridge

/-- **A point lies in the image of `⊤` under an open subset's inclusion exactly when it lies in
that subset.** The global sections of `X|V` are indexed by
`V.isOpenEmbedding.isOpenMap.functor.obj ⊤` rather than by `V`, and those two opens are equal
but not definitionally so. -/
theorem mem_functor_obj_top_iff (V : Opens (complexSpace.{u} ι)) (z : complexSpace.{u} ι) :
    z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ⊤ ↔ z ∈ V :=
  ⟨fun ⟨y, _, hy⟩ ↦ hy ▸ y.2, fun h ↦ ⟨⟨z, h⟩, trivial, rfl⟩⟩

/-- The set version of `ComplexAnalytic.mem_functor_obj_top_iff`. -/
theorem coe_functor_obj_top (V : Opens (complexSpace.{u} ι)) :
    (V.isOpenEmbedding.isOpenMap.functor.obj ⊤).carrier = V.carrier :=
  Set.ext (mem_functor_obj_top_iff V)

end Bridge

variable {V : Opens (complexSpace.{u} ι)}

/-- The map `ℂ^ι → ℂ^κ` whose `j`-th coordinate is the holomorphic function `u j` on `V`,
extended by zero off `V`. It is only meaningful ; and only analytic ; on `V`. -/
def okaMapOpenFun
    (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) : (ι → ℂ) → (κ → ℂ) :=
  fun z j ↦ (u j).toGlobalFun _ z

/-- The `j`-th coordinate of `okaMapOpenFun u z` is the value of `u j` at `z`. -/
lemma okaMapOpenFun_apply (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))
    {z : complexSpace.{u} ι} (hz : z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ⊤) (j : κ) :
    okaMapOpenFun u z j = OkaRing.evalHom hz (u j) :=
  (u j).toGlobalFun_apply hz

/-- **On `V`, a family of holomorphic functions is jointly analytic.** Off `V` it is the zero
extension and this says nothing, which is exactly why `OkaAnalytic.comp_analyticOn` is the
lemma this file needs. -/
lemma analyticAt_okaMapOpenFun [Fintype κ]
    (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))
    {z : complexSpace.{u} ι} (hz : z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ⊤) :
    AnalyticAt ℂ (okaMapOpenFun u) z :=
  AnalyticAt.pi fun j ↦ (okaAnalytic_iff _).1 (u j).2 z hz

/-- A family of holomorphic functions on `V` is continuous on `V`. -/
lemma continuousOn_okaMapOpenFun (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) :
    ContinuousOn (okaMapOpenFun u) V.carrier :=
  coe_functor_obj_top V ▸ continuousOn_pi.2 fun j ↦ (u j).continuousOn_toGlobalFun

/-- The underlying continuous map of `ComplexAnalytic.okaMapOpenHom`. -/
def okaMapOpenBase (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) :
    TopCat.of ↥V ⟶ TopCat.of (κ → ℂ) :=
  TopCat.ofHom ⟨fun y : ↥V ↦ okaMapOpenFun u y.1,
    continuousOn_iff_continuous_restrict.1 (continuousOn_okaMapOpenFun u)⟩

variable (u : κ → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) (W : Opens (κ → ℂ))

/-- A point of the preimage open, as a point of `V` mapping into `W`. -/
lemma mem_okaMapOpen_source
    (p : ↥(V.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map (okaMapOpenBase u)).obj W))) :
    okaMapOpenFun u p.1 ∈ W := by
  obtain ⟨y, hy, hyp⟩ := p.2
  exact hyp ▸ hy

/-- A point of the preimage open lies in `V`. -/
lemma mem_of_mem_okaMapOpen_source {z : complexSpace.{u} ι}
    (hz : z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map (okaMapOpenBase u)).obj W)) :
    z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ⊤ := by
  obtain ⟨y, _, hyz⟩ := hz
  exact (mem_functor_obj_top_iff V z).2 (hyz ▸ y.2)

variable [Fintype κ]

/-- Precomposition with `ComplexAnalytic.okaMapOpenFun`, as a ring homomorphism from the
holomorphic functions on `W ⊆ ℂ^κ` to the holomorphic functions on its preimage in `V`. -/
def okaMapOpenC :
    OkaRing W →+* ((complexSpace.{u} ι).restrict V.isOpenEmbedding).presheaf.obj
      (op ((Opens.map (okaMapOpenBase u)).obj W)) where
  toFun f := OkaRing.mk (fun p ↦ f.toFun _ ⟨okaMapOpenFun u p.1, mem_okaMapOpen_source u W p⟩)
    (OkaAnalytic.comp_analyticOn (hf := show OkaAnalytic f.toFun from f.2) (okaMapOpenFun u)
      (fun _ hy ↦ analyticAt_okaMapOpenFun u (mem_of_mem_okaMapOpen_source u W hy))
      (fun y hy ↦ mem_okaMapOpen_source u W ⟨y, hy⟩))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `h ∘ u` at `z` is the value of `h` at `u z`; this holds by definition and is
what makes `okaMapOpenHom` a morphism of *locally* ringed spaces. -/
lemma evalHom_okaMapOpenC (s : OkaRing W) {z : complexSpace.{u} ι}
    (hz : z ∈ V.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map (okaMapOpenBase u)).obj W)) :
    OkaRing.evalHom hz (okaMapOpenC u W s) =
      OkaRing.evalHom (U := W) (x := okaMapOpenFun u z) (mem_okaMapOpen_source u W ⟨z, hz⟩) s :=
  rfl

variable {W}

/-- The morphism of presheafed spaces underlying `ComplexAnalytic.okaMapOpenHom`. -/
def okaMapOpenPre :
    ((complexSpace.{u} ι).restrict V.isOpenEmbedding).toPresheafedSpace.Hom
      (complexSpace.{u} κ).toPresheafedSpace where
  base := okaMapOpenBase u
  c :=
    { app := fun W ↦ CommRingCat.ofHom (okaMapOpenC u W.unop)
      naturality := fun _ _ _ ↦ rfl }

/-- **The stalk maps of `ComplexAnalytic.okaMapOpenPre` are local homomorphisms.**

The argument is the one for entire families: a germ on `ℂ^κ` is a unit exactly when the function
does not vanish at the point, and precomposition does not change that value. The extra step is
that the source germ lives on `ℂ^ι|V`, so it is carried to `ℂ^ι` by
`AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso`, which is an isomorphism and therefore
does not change which elements are units. -/
lemma isLocalHom_stalkMap_okaMapOpenPre
    (z : ((complexSpace.{u} ι).restrict V.isOpenEmbedding)) :
    IsLocalHom (((okaMapOpenPre u).stalkMap z).hom) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨W, hw, s, rfl⟩ := (okaCommPresheaf.{u} κ).exists_germ_eq a
  have hz : z ∈ (Opens.map (okaMapOpenBase u)).obj W := hw
  have hmap : ((okaMapOpenPre u).stalkMap z).hom
        ((okaCommPresheaf.{u} κ).germ W ((okaMapOpenPre u).base z) hw s) =
      ((complexSpace.{u} ι).restrict V.isOpenEmbedding).presheaf.germ
        ((Opens.map (okaMapOpenBase u)).obj W) z hz (okaMapOpenC u W s) :=
    PresheafedSpace.stalkMap_germ_apply (okaMapOpenPre u) W z hw s
  rw [hmap] at ha
  have hiso := (complexSpace.{u} ι).restrictStalkIso_hom_eq_germ_apply V.isOpenEmbedding
    ((Opens.map (okaMapOpenBase u)).obj W) z hz (okaMapOpenC u W s)
  have ha' := hiso ▸ ha.map ((complexSpace.{u} ι).restrictStalkIso V.isOpenEmbedding z).hom.hom
  by_contra hcon
  have h1 : OkaRing.evalHom (U := W) (x := (okaMapOpenPre u).base z) hw s = 0 :=
    (germ_mem_maximalIdeal_iff hw s).1 ((IsLocalRing.mem_maximalIdeal _).2 hcon)
  refine (IsLocalRing.mem_maximalIdeal _).1
    ((germ_mem_maximalIdeal_iff ?_ (okaMapOpenC u W s)).2 ?_) ha'
  · exact ⟨z, hz, rfl⟩
  · exact (evalHom_okaMapOpenC u W s _).trans h1

/-- **A family of `κ` holomorphic functions on an open `V ⊆ ℂ^ι` is a morphism of locally ringed
spaces `ℂ^ι|V ⟶ ℂ^κ`**, pulling a holomorphic function `h` on `W ⊆ ℂ^κ` back to `h ∘ u`. -/
def okaMapOpenHom : (complexSpace.{u} ι).restrict V.isOpenEmbedding ⟶ complexSpace.{u} κ :=
  ⟨okaMapOpenPre u, isLocalHom_stalkMap_okaMapOpenPre u⟩

/-- The underlying map of `okaMapOpenHom u` is `okaMapOpenFun u`. -/
@[simp]
lemma base_okaMapOpenHom (y : ↥V) : (okaMapOpenHom u).base y = okaMapOpenFun u y.1 :=
  rfl

/-- **Pulling the `j`-th coordinate of `ℂ^κ` back along `okaMapOpenHom u` gives `u j`.**

This is what says the construction is inverse to taking coordinates, and it is the reason the
family is taken to be a family of *global sections of `ℂ^ι|V`* rather than of `OkaRing V`: those
are the same functions, but only the first makes both sides of this equation the same type. -/
theorem Γ_map_okaMapOpenHom_coord (j : κ) :
    (LocallyRingedSpace.Γ.map (okaMapOpenHom u).op).hom (coord j) = u j := by
  refine OkaRing.ext (funext fun y ↦ ?_)
  change MvPolynomial.eval (okaMapOpenFun u y.1) (MvPolynomial.X j) = _
  rw [MvPolynomial.eval_X]
  exact (u j).toGlobalFun_apply y.2

/-- `okaMapOpenHom u` is `ℂ`-linear: the pullback of a constant function is that constant. -/
theorem isCLinearHom_okaMapOpenHom :
    IsCLinearHom (okaMapOpenHom u)
      (Algebra.algebraMap ℂ (OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)))
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (κ → ℂ)))) :=
  fun _ ↦ rfl

section AnalyticSpace

variable {n m : ℕ} {V : (AnalyticSpace.complexAffineSpace.{u} n).Opens}
  (u : ULift.{u} (Fin m) → OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))

/-- **A family of `m` holomorphic functions on an open subset `V` of `ℂ^n` is a morphism of
complex analytic spaces `ℂ^n|V ⟶ ℂ^m`.** -/
def AnalyticSpace.okaMapOpen :
    (AnalyticSpace.complexAffineSpace.{u} n).restrict V ⟶
      AnalyticSpace.complexAffineSpace.{u} m :=
  ⟨okaMapOpenHom u, isCLinearHom_okaMapOpenHom u⟩

/-- The coordinates of `AnalyticSpace.okaMapOpen u` are `u`. -/
theorem AnalyticSpace.coordPullback_okaMapOpen (j : ULift.{u} (Fin m)) :
    AnalyticSpace.coordPullback (AnalyticSpace.okaMapOpen u) j = u j :=
  Γ_map_okaMapOpenHom_coord u j

/-- **Every family of `m` global sections of `𝒪_{ℂ^n|V}` is the tuple of coordinate pullbacks
along a morphism of complex analytic spaces `ℂ^n|V ⟶ ℂ^m`.**

This is one line because `ComplexAnalytic.AnalyticSpace.okaMapOpen` is already `m`-fold: a
family of holomorphic functions on `V` *is* a map to `ℂ^m`, with no product structure on
analytic spaces needed here and none reachable from this file, which is upstream of
`Other/Oka/AnalyticSpace/AffineProduct.lean`. Only the statement was ever one-dimensional. -/
theorem AnalyticSpace.exists_hom_complexAffineSpace_restrict
    (g : ULift.{u} (Fin m) →
      ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj (op ⊤)) :
    ∃ φ : (AnalyticSpace.complexAffineSpace.{u} n).restrict V ⟶
        AnalyticSpace.complexAffineSpace.{u} m,
      ∀ j, AnalyticSpace.coordPullback φ j = g j :=
  ⟨AnalyticSpace.okaMapOpen g, AnalyticSpace.coordPullback_okaMapOpen g⟩

/-- **Every global section of `𝒪_{ℂ^n|V}` is the pullback of the coordinate along a morphism of
complex analytic spaces `ℂ^n|V ⟶ ℂ`.**

This is taxis #628 for `Z` an open subspace of `ℂ^n`. Together with
`ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`, which is already general in `Z`, it gives
`Hom(ℂ^n|V, ℂ) ≃ Γ(ℂ^n|V, 𝒪)`.

It is the `m = 1` case of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_restrict` rather than a parallel
statement, and it is kept because the `m = 1` spelling ; one section, one equation, no index ;
is what every caller of it wants. -/
theorem AnalyticSpace.exists_hom_complexLine_restrict
    (g : ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj (op ⊤)) :
    ∃ φ : (AnalyticSpace.complexAffineSpace.{u} n).restrict V ⟶
        AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g :=
  let ⟨φ, hφ⟩ := AnalyticSpace.exists_hom_complexAffineSpace_restrict (m := 1) fun _ ↦ g
  ⟨φ, hφ (ULift.up 0)⟩

end AnalyticSpace

end ComplexAnalytic

end

end
