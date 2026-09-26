/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyBaseChange
public import Other.Oka.Topology.Sheaves.Cohomology.PushforwardAcyclic

/-!
# Cohomology of pushforwards of acyclic sheaves of modules

Let `f : Y ⟶ X` be a morphism of locally ringed spaces and `G` a sheaf of `𝒪_Y`-modules whose
underlying abelian sheaf is `f`-acyclic (`TopCat.Sheaf.IsPushforwardAcyclic`), i.e. the higher
direct images `Rᵠ f_* G` vanish. Then `Hᵠ(Y, G) ≃+ Hᵠ(X, f_* G)`
(`AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardModulesAcyclicAddEquiv`), the inverse of the
edge map `TopCat.Sheaf.H.pushforwardEdge`.

For a commutative square of locally ringed spaces

```
Y' --f'--> X'
|g'        |g
v          v
Y  --f-->  X
```

(`h : f' ≫ g = g' ≫ f`), the comparison maps `Hᵠ(X, f_* G) → Hᵠ(X', g^* f_* G)` and
`Hᵠ(Y, G) → Hᵠ(Y', g'^* G)` (`AlgebraicGeometry.LocallyRingedSpace.Hom.cohomologyMap`) are
intertwined by the edge maps, up to the base change morphism `g^* f_* G ⟶ f'_* g'^* G`
(`AlgebraicGeometry.LocallyRingedSpace.pushforwardEdge_cohomologyMap`,
`AlgebraicGeometry.LocallyRingedSpace.pushforwardModulesAcyclicAddEquiv_cohomologyMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y X' Y' : LocallyRingedSpace.{u}}

/-- **Cohomology of the pushforward of an acyclic sheaf of modules**: `Hᵠ(Y, G) ≃+ Hᵠ(X, f_* G)`
if the underlying abelian sheaf of `G` is `f`-acyclic. -/
noncomputable def Hom.pushforwardModulesAcyclicAddEquiv (f : Y ⟶ X)
    {G : SheafOfModules.{u} Y.ringSheaf} (hG : TopCat.Sheaf.IsPushforwardAcyclic f.base G.toAb)
    (q : ℕ) : H G q ≃+ H ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) q :=
  TopCat.Sheaf.H.pushforwardAcyclicAddEquiv f.base hG q

/-- The edge map inverts `Hᵠ(Y, G) ≃+ Hᵠ(X, f_* G)`. -/
@[simp]
lemma Hom.pushforwardEdge_pushforwardModulesAcyclicAddEquiv (f : Y ⟶ X)
    {G : SheafOfModules.{u} Y.ringSheaf} (hG : TopCat.Sheaf.IsPushforwardAcyclic f.base G.toAb)
    {q : ℕ} (x : H G q) :
    TopCat.Sheaf.H.pushforwardEdge f.base G.toAb q (f.pushforwardModulesAcyclicAddEquiv hG q x) =
      x :=
  TopCat.Sheaf.H.pushforwardEdge_pushforwardAcyclicAddEquiv f.base hG x

/-- `Hᵠ(Y, G) ≃+ Hᵠ(X, f_* G)` is natural in `G`. -/
lemma Hom.pushforwardModulesAcyclicAddEquiv_map (f : Y ⟶ X)
    {G G' : SheafOfModules.{u} Y.ringSheaf} (hG : TopCat.Sheaf.IsPushforwardAcyclic f.base G.toAb)
    (hG' : TopCat.Sheaf.IsPushforwardAcyclic f.base G'.toAb) (φ : G ⟶ G') {q : ℕ}
    (x : H G q) :
    f.pushforwardModulesAcyclicAddEquiv hG' q (H.map φ q x) =
      H.map ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) q
        (f.pushforwardModulesAcyclicAddEquiv hG q x) :=
  TopCat.Sheaf.H.pushforwardAcyclicAddEquiv_map f.base hG hG' ((modulesToAb Y).map φ) x

variable {f : Y ⟶ X} {f' : Y' ⟶ X'} {g : X' ⟶ X} {g' : Y' ⟶ Y} (h : f' ≫ g = g' ≫ f)

set_option backward.isDefEq.respectTransparency false in
/-- **The edge maps commute with the comparison maps**: for a commutative square
`f' ≫ g = g' ≫ f` of locally ringed spaces, a sheaf of modules `G` on `Y` and
`y ∈ Hⁿ(X, f_* G)`, the edge map of `f'` applied to the image of `g^*(y) ∈ Hⁿ(X', g^* f_* G)`
under the base change morphism `g^* f_* G ⟶ f'_* g'^* G` is `g'^*` of the edge map of `y`. -/
theorem pushforwardEdge_cohomologyMap (G : SheafOfModules.{u} Y.ringSheaf) {n : ℕ}
    (y : H ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) n) :
    TopCat.Sheaf.H.pushforwardEdge f'.base (g'.pullbackModules.obj G).toAb n
        (H.map (pushforwardModulesBaseChange h G) n
          (g.cohomologyMap ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) n y)) =
      g'.cohomologyMap G n (TopCat.Sheaf.H.pushforwardEdge f.base G.toAb n y) := by
  rw [Hom.cohomologyMap_apply, Hom.cohomologyMap_apply, H.map,
    ← TopCat.Sheaf.H.map_comp_apply,
    toPullbackModules_comp_modulesToAb_map_pushforwardModulesBaseChange,
    TopCat.Sheaf.H.map_comp_apply]
  exact (TopCat.Sheaf.H.pushforwardEdge_map f'.base (g'.toPullbackModules G) _).trans
    (congrArg (TopCat.Sheaf.H.map (g'.toPullbackModules G) n)
      (TopCat.Sheaf.H.pushforwardEdge_pullback f.base (base_comm_of_comm h) G.toAb y))

/-- **`Hᵠ(Y, G) ≃+ Hᵠ(X, f_* G)` commutes with the comparison maps**: for a commutative square
`f' ≫ g = g' ≫ f` of locally ringed spaces, a sheaf of modules `G` on `Y` which is `f`-acyclic
with `g'^* G` `f'`-acyclic, and `x ∈ Hⁿ(Y, G)`, the image of `g'^*(x) ∈ Hⁿ(Y', g'^* G)` in
`Hⁿ(X', f'_* g'^* G)` is the image of `g^*(f_* x) ∈ Hⁿ(X', g^* f_* G)` under the base change
morphism. -/
theorem pushforwardModulesAcyclicAddEquiv_cohomologyMap (G : SheafOfModules.{u} Y.ringSheaf)
    (hG : TopCat.Sheaf.IsPushforwardAcyclic f.base G.toAb)
    (hG' : TopCat.Sheaf.IsPushforwardAcyclic f'.base (g'.pullbackModules.obj G).toAb) {n : ℕ}
    (x : H G n) :
    f'.pushforwardModulesAcyclicAddEquiv hG' n (g'.cohomologyMap G n x) =
      H.map (pushforwardModulesBaseChange h G) n
        (g.cohomologyMap ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) n
          (f.pushforwardModulesAcyclicAddEquiv hG n x)) := by
  apply (TopCat.Sheaf.H.bijective_pushforwardEdge f'.base hG' n).1
  rw [Hom.pushforwardEdge_pushforwardModulesAcyclicAddEquiv, pushforwardEdge_cohomologyMap,
    Hom.pushforwardEdge_pushforwardModulesAcyclicAddEquiv]

end AlgebraicGeometry.LocallyRingedSpace

end
