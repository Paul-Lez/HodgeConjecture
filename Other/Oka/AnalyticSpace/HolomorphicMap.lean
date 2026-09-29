/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Evaluation

/-!
# Holomorphic maps as morphisms of complex analytic spaces

A family `u₁, …, u_m` of entire holomorphic functions on `ℂ^n` defines a map `ℂ^n → ℂ^m`, and
this file upgrades that map to a **morphism of complex analytic spaces**
`ComplexAnalytic.AnalyticSpace.okaMap`. Pulling back a holomorphic function `h` on an open
`W ⊆ ℂ^m` is composition, `h ↦ h ∘ u`; that this lands in the holomorphic functions is
`OkaAnalytic.comp_analytic`, and that the resulting map is *local* on stalks is the observation
that a germ on `ℂ^m` is a unit exactly when the function does not vanish at the point
(`germ_mem_maximalIdeal_iff`), a condition composition preserves in both directions.

Specialising to `m = 1` gives, for every global section `g` of `𝒪_{ℂ^n}`, a morphism
`ℂ^n ⟶ ℂ` whose pullback of the coordinate function is `g`
(`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine`). Composing with the inclusion of a
closed analytic subspace gives morphisms out of spaces which are not `ℂ^n`: the last section
does this for the **node** `{z ∈ ℂ² | z₀ z₁ = 0}` and its two coordinate functions, and shows
the resulting morphism is surjective on points.

Until this file the development contained no morphism of complex analytic spaces other than
identities, isomorphisms and the closed immersions defining local models; `nodeToLine` is the
first morphism between two genuinely different analytic spaces.

## What this does *not* give

The general statement one wants is: **for every complex analytic space `Z` and every global
section `g` of `𝒪_Z` there is a morphism `Z ⟶ ℂ` pulling the coordinate back to `g`.** This
file proves that only when `g` is (the pullback of) a *globally defined holomorphic function on
an ambient `ℂ^n`* ; which is what `ℂ^n` itself and the node give, but is not the general case.
For a general `Z` a section of `𝒪_Z` lifts to a holomorphic function only *locally*, on a chart
and on a neighbourhood of each point (`AlgebraicGeometry.LocallyRingedSpace.exists_localLift`),
so the construction above produces a morphism only on each member of an open cover of `Z`.

**That gap is closed, elsewhere in this tree, by the route this paragraph anticipated.**
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general` of
`Other/Oka/AnalyticSpace/HolomorphicMapGeneral.lean` is the general statement above, as the `m = 1`
case of `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general`; the morphisms on
the members of the cover are glued by
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` of
`Other/Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, which supplies for a locally ringed
space what `AlgebraicGeometry.Scheme.Cover.glueMorphisms` is for a scheme. **Mathlib still has
the scheme version and nothing for `LocallyRingedSpace`**, so that half of the obstruction was
real and is met inside this repository rather than upstream. Neither file is imported here and
nothing below needs either.

The other thing the general statement was expected to need ; **independence of the local
construction of the two choices it makes**, the local lift `G` of `g` and the chart ; was never
proved and is not needed: uniqueness on an overlap replaces both arguments, once
`ComplexAnalytic.AnalyticSpace.restrict` makes an overlap an analytic space.
`AnalyticAt.dslope_comp` of `Other/Oka/Analytic/DividedDifference.lean` was built for the
independence-of-lift half ; two lifts differ by a section of the ideal cutting out the chart,
and `h ∘ G - h ∘ G' = (G - G') · dslope h G' G` therefore lies in that ideal too ; and is
consequently unused. Its disposition is the `## Status` section of that file, and the fuller
account of why the independence arguments are unnecessary is in
`Other/Oka/AnalyticSpace/HolomorphicMapGeneral.lean`. `Other/Oka/Analytic/DividedDifference.lean` is
deliberately not imported here: nothing below uses it.

## Main definitions

- `ComplexAnalytic.okaMapFun`: the map `ℂ^ι → ℂ^κ` given by a family of entire functions.
- `ComplexAnalytic.okaMapHom`: the same, as a morphism of locally ringed spaces.
- `ComplexAnalytic.coord`: the coordinate functions of `ℂ^κ`, as global sections of `𝒪_{ℂ^κ}`.
- `ComplexAnalytic.AnalyticSpace.okaMap`: the same, as a morphism of complex analytic spaces
  `ℂ^n ⟶ ℂ^m`.
- `ComplexAnalytic.nodeToLine`: the morphism from the node to `ℂ` given by a coordinate.

## Main results

- `ComplexAnalytic.Γ_map_okaMapHom_coord`: **pulling the `j`-th coordinate of `ℂ^κ` back along
  `okaMapHom u` gives `u j`** ; the construction really is the inverse of "take the coordinates".
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine`: **every global section of `𝒪_{ℂ^n}` is
  the pullback of the coordinate along a morphism of analytic spaces `ℂ^n ⟶ ℂ`.**
- `ComplexAnalytic.Γ_map_nodeToLineHom_coord`: on the node, the section recovered from
  `nodeToLine j` is `ComplexAnalytic.nodeCoord j`.
- `ComplexAnalytic.surjective_base_nodeToLineHom` and
  `ComplexAnalytic.not_injective_base_nodeToLineHom`: `nodeToLine j` is surjective on points and
  is **not** injective on them, so it is not a bijection on points. That the node is not
  homeomorphic to `ℂ` by *any* map is true and is not proved here.
- `ComplexAnalytic.nodeToLine_ne`: the two coordinate morphisms out of the node are different.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {ι κ : Type u} [Fintype ι]

/-- The map `ℂ^ι → ℂ^κ` whose `j`-th coordinate is the entire function `u j`. -/
def okaMapFun (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) : (ι → ℂ) → (κ → ℂ) :=
  fun z j ↦ (u j).toGlobalFun ⊤ z

/-- The `j`-th coordinate of `okaMapFun u z` is the value of `u j` at `z`. -/
lemma okaMapFun_apply (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (z : ι → ℂ) (j : κ) :
    okaMapFun u z j = OkaRing.evalHom (U := ⊤) (x := z) trivial (u j) :=
  (u j).toGlobalFun_apply trivial

/-- A map given by entire functions is analytic, jointly in all coordinates. -/
lemma analyticAt_okaMapFun [Fintype κ] (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (z : ι → ℂ) :
    AnalyticAt ℂ (okaMapFun u) z :=
  AnalyticAt.pi fun j ↦ (okaAnalytic_iff _).1 (u j).2 z trivial

/-- A map given by entire functions is continuous. -/
lemma continuous_okaMapFun (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) :
    Continuous (okaMapFun u) :=
  continuous_pi fun j ↦
    continuousOn_univ.1 (fun z _ ↦ (u j).continuousOn_toGlobalFun z trivial)

/-- The underlying continuous map of `ComplexAnalytic.okaMapHom`. -/
def okaMapBase (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) :
    TopCat.of (ι → ℂ) ⟶ TopCat.of (κ → ℂ) :=
  TopCat.ofHom ⟨okaMapFun u, continuous_okaMapFun u⟩

variable [Fintype κ]

/-- Precomposition with `ComplexAnalytic.okaMapFun`, as a ring homomorphism from the holomorphic
functions on `W ⊆ ℂ^κ` to the holomorphic functions on its preimage. -/
def okaMapC (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (W : Opens (κ → ℂ)) :
    OkaRing W →+* OkaRing ((Opens.map (okaMapBase u)).obj W) where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨okaMapFun u y.1, y.2⟩)
    (OkaAnalytic.comp_analytic (okaMapFun u) (analyticAt_okaMapFun u) (fun _ hy ↦ hy) f.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `h ∘ u` at `z` is the value of `h` at `u z`; this holds by definition and is
the whole reason `okaMapHom` is a morphism of *locally* ringed spaces. -/
lemma evalHom_okaMapC (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (W : Opens (κ → ℂ))
    (s : OkaRing W) {z : ι → ℂ} (hz : z ∈ (Opens.map (okaMapBase u)).obj W) :
    OkaRing.evalHom hz (okaMapC u W s) =
      OkaRing.evalHom (U := W) (x := okaMapFun u z) hz s :=
  rfl

/-- The morphism of presheafed spaces underlying `ComplexAnalytic.okaMapHom`. -/
def okaMapPre (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) :
    (complexSpace.{u} ι).toPresheafedSpace.Hom (complexSpace.{u} κ).toPresheafedSpace where
  base := okaMapBase u
  c :=
    { app := fun W ↦ CommRingCat.ofHom (okaMapC u W.unop)
      naturality := fun _ _ _ ↦ rfl }

/-- **The stalk maps of `ComplexAnalytic.okaMapPre` are local homomorphisms.**

A germ on `ℂ^κ` is a unit exactly when the function does not vanish at the point
(`germ_mem_maximalIdeal_iff`), and precomposition with `okaMapFun u` does not change that value,
so the stalk map reflects units on the nose. -/
lemma isLocalHom_stalkMap_okaMapPre (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (z : ι → ℂ) :
    IsLocalHom (((okaMapPre u).stalkMap z).hom) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨W, hw, s, rfl⟩ := (okaCommPresheaf.{u} κ).exists_germ_eq a
  have hz : z ∈ (Opens.map (okaMapBase u)).obj W := hw
  have hmap : ((okaMapPre u).stalkMap z).hom
        ((okaCommPresheaf.{u} κ).germ W ((okaMapPre u).base z) hw s) =
      (okaCommPresheaf.{u} ι).germ ((Opens.map (okaMapBase u)).obj W) z hz
        (okaMapC u W s) :=
    PresheafedSpace.stalkMap_germ_apply (okaMapPre u) W z hw s
  rw [hmap] at ha
  by_contra hcon
  have h1 : OkaRing.evalHom (U := W) (x := okaMapFun u z) hw s = 0 :=
    (germ_mem_maximalIdeal_iff hw s).1 ((IsLocalRing.mem_maximalIdeal _).2 hcon)
  refine (IsLocalRing.mem_maximalIdeal _).1
    ((germ_mem_maximalIdeal_iff hz (okaMapC u W s)).2 ?_) ha
  exact (evalHom_okaMapC u W s hz).trans h1

/-- **A family of `κ` entire functions on `ℂ^ι` is a morphism of locally ringed spaces
`ℂ^ι ⟶ ℂ^κ`**, pulling a holomorphic function `h` on `W ⊆ ℂ^κ` back to `h ∘ u`. -/
def okaMapHom (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) :
    complexSpace.{u} ι ⟶ complexSpace.{u} κ :=
  ⟨okaMapPre u, isLocalHom_stalkMap_okaMapPre u⟩

/-- The underlying map of `okaMapHom u` is `okaMapFun u`. -/
@[simp]
lemma base_okaMapHom (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (z : ι → ℂ) :
    (okaMapHom u).base z = okaMapFun u z :=
  rfl

/-- Pulling a holomorphic function back along `okaMapHom u` is composing it with
`okaMapFun u`.

Not `@[simp]`: the left-hand side is not in `simp` normal form, since `complexSpace_presheaf`
rewrites `(complexSpace κ).presheaf` to `okaCommPresheaf κ` inside it. -/
lemma c_app_okaMapHom (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (W : Opens (κ → ℂ))
    (s : OkaRing W) :
    (okaMapHom u).c.app (op W) s = okaMapC u W s :=
  rfl

/-- The `j`-th coordinate function `z_j` of `ℂ^κ`, as a global section of its structure sheaf. -/
def coord (j : κ) : OkaRing (⊤ : Opens (κ → ℂ)) :=
  OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X j)

/-- The coordinate function, unfolded. -/
lemma coord_def (j : κ) : coord j = OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X j) := rfl

/-- The `j`-th coordinate function takes at `z` the value `z j`.

Not `@[simp]`: `OkaRing.evalHom_apply` already unfolds the left-hand side. -/
lemma evalHom_coord {z : κ → ℂ} (j : κ) :
    OkaRing.evalHom (U := ⊤) (x := z) trivial (coord j) = z j :=
  (OkaRing.evalHom_ofMvPolynomial ⊤ trivial (MvPolynomial.X j)).trans (MvPolynomial.eval_X j)

/-- **Pulling the `j`-th coordinate of `ℂ^κ` back along `okaMapHom u` gives `u j`.** -/
theorem Γ_map_okaMapHom_coord (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) (j : κ) :
    (LocallyRingedSpace.Γ.map (okaMapHom u).op).hom (coord j) = u j := by
  refine OkaRing.ext (funext fun y ↦ ?_)
  change MvPolynomial.eval (okaMapFun u y.1) (MvPolynomial.X j) = _
  rw [MvPolynomial.eval_X]
  exact (u j).toGlobalFun_apply trivial

/-- `okaMapHom u` is `ℂ`-linear for the constant functions on either side. -/
theorem isCLinearHom_okaMapHom (u : κ → OkaRing (⊤ : Opens (ι → ℂ))) :
    IsCLinearHom (okaMapHom u) (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ι → ℂ))))
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (κ → ℂ)))) :=
  fun _ ↦ rfl

/-- Pulling back a holomorphic function along the inclusion of an open subspace of `ℂ^ι` is
restriction of holomorphic functions. -/
lemma Γ_map_ofRestrict (V : Opens (complexSpace.{u} ι))
    (f : OkaRing (⊤ : Opens (ι → ℂ))) :
    (LocallyRingedSpace.Γ.map ((complexSpace.{u} ι).ofRestrict V.isOpenEmbedding).op).hom f =
      OkaRing.restrict le_top f :=
  rfl

/-- **A family of `m` entire functions on `ℂ^n` is a morphism of complex analytic spaces
`ℂ^n ⟶ ℂ^m`.** -/
def AnalyticSpace.okaMap {n m : ℕ}
    (u : ULift.{u} (Fin m) →
      OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))) :
    AnalyticSpace.complexAffineSpace.{u} n ⟶ AnalyticSpace.complexAffineSpace.{u} m :=
  ⟨okaMapHom u, isCLinearHom_okaMapHom u⟩

/-- **Every global section of `𝒪_{ℂ^n}` is the pullback of the coordinate along a morphism of
analytic spaces `ℂ^n ⟶ ℂ`.** -/
theorem AnalyticSpace.exists_hom_complexLine {n : ℕ}
    (g : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤)) :
    ∃ φ : AnalyticSpace.complexAffineSpace.{u} n ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom (coord (ULift.up 0)) = g :=
  ⟨AnalyticSpace.okaMap fun _ ↦ g, Γ_map_okaMapHom_coord _ _⟩

section Node

open AnalyticSpace in
/-- The inclusion of the node into `ℂ²` is `ℂ`-linear, by the very choice of the `ℂ`-algebra
structure on the node. -/
lemma isCLinearHom_zeroLocusSubspaceι_nodeSection :
    IsCLinearHom (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
      (AnalyticSpace.node.{u}).algebraMap (constantsAlgMap 2 ⊤) :=
  fun _ ↦ rfl

/-- The inclusion of an open subspace of `ℂ^ι` is `ℂ`-linear: restriction of a constant
function is that constant. -/
lemma isCLinearHom_ofRestrict_complexSpace (V : Opens (complexSpace.{u} ι)) :
    IsCLinearHom ((complexSpace.{u} ι).ofRestrict V.isOpenEmbedding)
      (Algebra.algebraMap ℂ (OkaRing (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)))
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ι → ℂ)))) :=
  fun _ ↦ rfl

/-- The inclusion of the node into `ℂ²`, followed by the `j`-th coordinate: a morphism of
locally ringed spaces from the node to `ℂ`. -/
def nodeToLineHom (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).toLocallyRingedSpace ⟶ complexAffineSpace.{u} 1 :=
  nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} ≫
    (complexAffineSpace.{u} 2).ofRestrict (⊤ : Opens (complexAffineSpace.{u} 2)).isOpenEmbedding ≫
      okaMapHom (fun _ : ULift.{u} (Fin 1) ↦ coord j)

/-- **The `j`-th coordinate of `ℂ` pulls back along `nodeToLineHom j` to the `j`-th coordinate
function of the node.** -/
theorem Γ_map_nodeToLineHom_coord (j : ULift.{u} (Fin 2)) :
    (LocallyRingedSpace.Γ.map (nodeToLineHom.{u} j).op).hom (coord (ULift.up 0)) =
      nodeCoord.{u} j := by
  rw [nodeToLineHom, LocallyRingedSpace.Γ_map_comp_apply, LocallyRingedSpace.Γ_map_comp_apply,
    Γ_map_okaMapHom_coord,
    Γ_map_ofRestrict, coord_def, OkaRing.restrict_ofMvPolynomial]
  rfl

/-- **The underlying map of `nodeToLineHom j` is the `j`-th coordinate.** -/
@[simp]
theorem base_nodeToLineHom (j : ULift.{u} (Fin 2)) (p : AnalyticSpace.node.{u})
    (l : ULift.{u} (Fin 1)) :
    ((nodeToLineHom.{u} j).base p : ULift.{u} (Fin 1) → ℂ) l = p.1.1 j :=
  ((coord j).toGlobalFun_apply trivial).trans (evalHom_coord j)

/-- **The morphism `nodeToLineHom j` is surjective on points**, so in particular it is neither
constant nor an isomorphism onto a point: the `j`-th axis of the node already maps onto `ℂ`.

This is what makes it the first genuinely non-trivial morphism of complex analytic spaces in the
development. -/
theorem surjective_base_nodeToLineHom (j : ULift.{u} (Fin 2)) :
    Function.Surjective fun p : AnalyticSpace.node.{u} ↦
      ((nodeToLineHom.{u} j).base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  classical
  intro c
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  set x : ULift.{u} (Fin 2) → ℂ := fun l ↦ if l = j then c else 0 with hx
  have hx0 : x (ULift.up 0) * x (ULift.up 1) = 0 := by
    rw [hx]
    dsimp only
    rcases eq_or_ne (ULift.up 0 : ULift.{u} (Fin 2)) j with h | h
    · rw [if_neg (fun hcon : (ULift.up 1 : ULift.{u} (Fin 2)) = j ↦ hne (h.trans hcon.symm)),
        mul_zero]
    · rw [if_neg h, zero_mul]
  exact ⟨⟨⟨x, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 hx0⟩,
    (base_nodeToLineHom j _ (ULift.up 0)).trans (if_pos rfl)⟩

/-- **The morphism `nodeToLineHom j` is not injective on points**: the other axis of the node is
a whole line of preimages of `0`.

With `surjective_base_nodeToLineHom` this says the map is onto but not one-to-one; surjectivity
alone would not, since a surjection can be a bijection. It says nothing about maps other than
this one, so it is not the statement that the node is not homeomorphic to `ℂ`. The points
exhibited are a pair on the axis whose
`j`-th coordinate vanishes, so `k` ; the coordinate `nodeToLine j` forgets ; has to be chosen
rather than fixed. -/
theorem not_injective_base_nodeToLineHom (j : ULift.{u} (Fin 2)) :
    ¬ Function.Injective fun p : AnalyticSpace.node.{u} ↦
      ((nodeToLineHom.{u} j).base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  classical
  set k : ULift.{u} (Fin 2) := if j = ULift.up 0 then ULift.up 1 else ULift.up 0 with hk
  have hjk : j ≠ k := by
    rw [hk]
    split
    · next h => rw [h]; exact fun hcon ↦ by simpa using congrArg ULift.down hcon
    · next h => exact fun hcon ↦ h hcon
  have hmem : ∀ c : ℂ, (fun l ↦ if l = k then c else 0 : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) *
      (fun l ↦ if l = k then c else 0 : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 0 := by
    intro c
    dsimp only
    rcases eq_or_ne (ULift.up 0 : ULift.{u} (Fin 2)) k with h | h
    · rw [if_neg (fun hcon : (ULift.up 1 : ULift.{u} (Fin 2)) = k ↦ by
        simpa using congrArg ULift.down (h.trans hcon.symm)), mul_zero]
    · rw [if_neg h, zero_mul]
  intro hinj
  have h := hinj (a₁ := ⟨⟨fun l ↦ if l = k then 1 else 0, trivial⟩,
      (mem_zeroLocus_nodeSection_iff _).2 (hmem 1)⟩)
    (a₂ := ⟨⟨fun l ↦ if l = k then 2 else 0, trivial⟩,
      (mem_zeroLocus_nodeSection_iff _).2 (hmem 2)⟩) ?_
  · have h2 := congrArg (fun p : AnalyticSpace.node.{u} ↦ p.1.1 k) h
    dsimp only at h2
    rw [if_pos rfl, if_pos rfl] at h2
    norm_num at h2
  · dsimp only
    rw [base_nodeToLineHom, base_nodeToLineHom]
    dsimp only
    rw [if_neg hjk, if_neg hjk]

/-- **The node maps to `ℂ` by each of its two coordinate functions**, as a morphism of complex
analytic spaces. -/
def nodeToLine (j : ULift.{u} (Fin 2)) :
    AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1 :=
  ⟨nodeToLineHom j,
    isCLinearHom_zeroLocusSubspaceι_nodeSection.comp
      ((isCLinearHom_ofRestrict_complexSpace _).comp
        (isCLinearHom_okaMapHom fun _ : ULift.{u} (Fin 1) ↦ coord j))⟩

/-- **The two coordinate morphisms out of the node are different.**

The point exhibited is `(1, 0)`, which lies on the node. This is a statement about the
morphisms rather than a check on any one construction; `ComplexAnalytic.nodeCoord_ne` turns it
into the corresponding statement about *sections* using the rigidity of
`ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`. -/
theorem nodeToLine_ne : nodeToLine.{u} (ULift.up 0) ≠ nodeToLine.{u} (ULift.up 1) := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  set x : ULift.{u} (Fin 2) → ℂ := fun l ↦ if l = ULift.up 0 then 1 else 0 with hx
  have hx0 : x (ULift.up 0) * x (ULift.up 1) = 0 := by
    rw [hx]
    dsimp only
    rw [if_neg hne.symm, mul_zero]
  set p : AnalyticSpace.node.{u} :=
    ⟨⟨x, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 hx0⟩ with hp
  intro hcon
  have h := congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦
    (φ.toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) hcon
  rw [show ((nodeToLine.{u} (ULift.up 0)).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ)
      (ULift.up 0) = x (ULift.up 0) from base_nodeToLineHom _ p _,
    show ((nodeToLine.{u} (ULift.up 1)).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ)
      (ULift.up 0) = x (ULift.up 1) from base_nodeToLineHom _ p _, hx] at h
  dsimp only at h
  rw [if_pos rfl, if_neg hne.symm] at h
  exact one_ne_zero h

end Node

end ComplexAnalytic

end
