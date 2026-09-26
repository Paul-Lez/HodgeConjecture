/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-!
# Charts of `Y ×_K ℙⁿ_K` over affine opens of `Y`

Let `y : Y ⟶ Spec K` be a scheme over a ring `K` and `P = Y ×_K ℙₒ(n; K)`. For an affine open
`V ⊆ Y` with ring `A = Γ(Y, V)`, the preimage of `V` in `P` is `ℙₒ(n; A)`: the morphism
`ProjectiveSpace.affineChart y hV : ℙₒ(n; A) ⟶ P`, with components `ℙₒ(n; A) ⟶ Spec A ⟶ Y` and
`ProjectiveSpace.map : ℙₒ(n; A) ⟶ ℙₒ(n; K)`, is an open immersion
(`ProjectiveSpace.isOpenImmersion_affineChart`) with range `pr₁⁻¹ V`
(`ProjectiveSpace.opensRange_affineChart`), since the square

```
ℙₒ(n; A) --affineChart--> P
   |                      | pr₁
 Spec A ----fromSpec----> Y
```

is a pullback square (`ProjectiveSpace.isPullback_affineChart`), by base change of `ℙₒ(n; K)`
along `K → A` (`ProjectiveSpace.isPullback_map`). The preimage of a basic open `D(g)`, `g ∈ A`,
is the basic open of `g` on `ℙₒ(n; A)` (`ProjectiveSpace.affineChart_preimage_basicOpen`).
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {K : Type u} [CommRing K] {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K))
  {V : Y.Opens} (hV : IsAffineOpen V)

/-- The ring map `K → Γ(Y, V)` of the structure morphism, for an affine open `V`. -/
noncomputable def structureRingHom : K →+* Γ(Y, V) :=
  (Spec.preimage (hV.fromSpec ≫ y)).hom

lemma SpecMap_structureRingHom :
    Spec.map (CommRingCat.ofHom (structureRingHom y hV)) = hV.fromSpec ≫ y :=
  Spec.map_preimage _

variable (n) in
/-- The chart `ℙₒ(n; Γ(Y, V)) ⟶ Y ×_K ℙₒ(n; K)` over the affine open `V`. -/
noncomputable def affineChart : ℙₒ(n; Γ(Y, V)) ⟶ pullback y (toSpec n K) :=
  pullback.lift (toSpec n _ ≫ hV.fromSpec) (map (structureRingHom y hV)) (by
    rw [map_toSpec, Category.assoc, SpecMap_structureRingHom])

@[reassoc (attr := simp)]
lemma affineChart_fst :
    affineChart n y hV ≫ pullback.fst _ _ = toSpec n _ ≫ hV.fromSpec :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma affineChart_snd :
    affineChart n y hV ≫ pullback.snd _ _ = map (structureRingHom y hV) :=
  pullback.lift_snd _ _ _

/-- The chart square over the affine open `V` is a pullback square. -/
theorem isPullback_affineChart :
    IsPullback (affineChart n y hV) (toSpec n _) (pullback.fst y (toSpec n K)) hV.fromSpec := by
  refine IsPullback.of_right ?_ (affineChart_fst y hV) (IsPullback.of_hasPullback _ _).flip
  rw [affineChart_snd, ← SpecMap_structureRingHom]
  exact isPullback_map _

instance isOpenImmersion_affineChart : IsOpenImmersion (affineChart n y hV) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_affineChart y hV).flip
    inferInstance

lemma range_affineChart :
    Set.range (affineChart n y hV) = pullback.fst y (toSpec n K) ⁻¹' (V : Set Y) := by
  have h := (isPullback_affineChart (n := n) y hV).flip
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Set.range_eq_univ (f := h.isoPullback.hom)).2 h.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_snd, hV.range_fromSpec]

lemma opensRange_affineChart :
    (affineChart n y hV).opensRange = pullback.fst y (toSpec n K) ⁻¹ᵁ V :=
  TopologicalSpace.Opens.ext (range_affineChart y hV)

/-- The preimage under the chart of the preimage of a basic open `D(g) ⊆ V` is the basic open of
`g` on `ℙₒ(n; Γ(Y, V))`. -/
lemma affineChart_preimage_basicOpen (g : Γ(Y, V)) :
    affineChart n y hV ⁻¹ᵁ (pullback.fst y (toSpec n K) ⁻¹ᵁ Y.basicOpen g) =
      ℙₒ(n; Γ(Y, V)).basicOpen ((toSpec n _).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv g)) := by
  rw [← Scheme.Hom.comp_preimage, affineChart_fst, Scheme.Hom.comp_preimage,
    hV.fromSpec_preimage_basicOpen', Scheme.preimage_basicOpen_top]

end AlgebraicGeometry.ProjectiveSpace

end
