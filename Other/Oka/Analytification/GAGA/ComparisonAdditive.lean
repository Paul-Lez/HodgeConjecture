/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CohomologyComparison

/-!
# Additivity of the GAGA comparison map

For `X` a scheme locally of finite type over `ℂ`, the class of sheaves of modules `F` on `X` for
which the comparison map `gagaMap X F q : Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective is closed
under isomorphisms (`ComplexAnalytic.gagaMap_bijective_iff_of_iso`) and under finite direct sums
(`ComplexAnalytic.gagaMap_bijective_biproduct`, `ComplexAnalytic.gagaMap_bijective_sigma`).

The proof only uses naturality of `gagaMap`, additivity of `Hᵠ(X, -)` in the morphism and
additivity of the analytification functor: an element `x` of `Hᵠ(X, ⨁ Fᵢ)` is the sum of the
`ιᵢ (πᵢ x)`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace.H

variable {Y : LocallyRingedSpace.{u}} {M N : SheafOfModules.{u} Y.ringSheaf}

/-- The map on cohomology is additive in the morphism. -/
lemma map_add_apply (φ ψ : M ⟶ N) {q : ℕ} (x : H M q) :
    map (φ + ψ) q x = map φ q x + map ψ q x := by
  simp only [map, Functor.map_add, TopCat.Sheaf.H.map_add_apply]

/-- The map on cohomology induced by the zero morphism is zero. -/
lemma map_zero_apply {q : ℕ} (x : H M q) : map (0 : M ⟶ N) q x = 0 := by
  simp only [map, Functor.map_zero, TopCat.Sheaf.H.map_zero_apply]

/-- The map on cohomology commutes with finite sums of morphisms. -/
lemma map_sum_apply {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N)) {q : ℕ} (x : H M q) :
    map (∑ i ∈ s, φ i) q x = ∑ i ∈ s, map (φ i) q x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_zero_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, map_add_apply, ih]

end AlgebraicGeometry.LocallyRingedSpace.H

namespace ComplexAnalytic

variable {X : SchemeLFTℂ.{u}}

open LocallyRingedSpace

instance : (analytificationModules X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The map on cohomology induced by an isomorphism is bijective. -/
lemma bijective_H_map_hom {Y : LocallyRingedSpace.{u}} {M N : SheafOfModules.{u} Y.ringSheaf}
    (e : M ≅ N) (q : ℕ) : Function.Bijective (H.map e.hom q) := by
  refine Function.bijective_iff_has_inverse.2 ⟨H.map e.inv q, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← H.map_comp_apply, e.hom_inv_id, H.map_id_apply]
  · rw [← H.map_comp_apply, e.inv_hom_id, H.map_id_apply]

/-- Bijectivity of the GAGA comparison map is invariant under isomorphism of the sheaf. -/
lemma gagaMap_bijective_iff_of_iso
    {F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} (e : F ≅ G) (q : ℕ) :
    Function.Bijective (gagaMap X F q) ↔ Function.Bijective (gagaMap X G q) := by
  have key : ∀ {F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf}
      (e : F ≅ G), Function.Bijective (gagaMap X F q) → Function.Bijective (gagaMap X G q) := by
    intro F G e h
    have hc : ⇑(gagaMap X G q) ∘ ⇑(H.map e.hom q) =
        ⇑(H.map ((analytificationModules X).map e.hom) q) ∘ ⇑(gagaMap X F q) :=
      funext fun x ↦ gagaMap_map e.hom x
    have h' : Function.Bijective (⇑(gagaMap X G q) ∘ ⇑(H.map e.hom q)) := by
      rw [hc]
      exact (bijective_H_map_hom ((analytificationModules X).mapIso e) q).comp h
    exact (Function.Bijective.of_comp_iff _ (bijective_H_map_hom e q)).1 h'
  exact ⟨key e, key e.symm⟩

/-- **The GAGA comparison map is additive**: it is bijective on a finite direct sum `⨁ Fᵢ` if it
is bijective on every summand `Fᵢ`. -/
lemma gagaMap_bijective_biproduct {I : Type*} [Finite I]
    (F : I → SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [HasBiproduct F]
    (q : ℕ) (h : ∀ i, Function.Bijective (gagaMap X (F i) q)) :
    Function.Bijective (gagaMap X (⨁ F) q) := by
  have := Fintype.ofFinite I
  let an := analytificationModules X
  have htot : ∑ i, biproduct.π F i ≫ biproduct.ι F i = 𝟙 (⨁ F) :=
    IsBilimit.total (biproduct.isBilimit F)
  have hid : ∀ (x : H (⨁ F) q),
      x = ∑ i, H.map (biproduct.ι F i) q (H.map (biproduct.π F i) q x) := by
    intro x
    conv_lhs => rw [← H.map_id_apply x, ← htot, H.map_sum_apply]
    simp only [H.map_comp_apply]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · have hi : ∀ i, H.map (biproduct.π F i) q x = 0 := fun i ↦ (h i).1 <| by
      rw [gagaMap_map, hx, map_zero, map_zero]
    rw [hid x]
    simp [hi]
  · have hy : y = ∑ i, H.map (an.map (biproduct.ι F i)) q
        (H.map (an.map (biproduct.π F i)) q y) := by
      conv_lhs => rw [← H.map_id_apply y, ← an.map_id, ← htot, an.map_sum,
        H.map_sum_apply]
      simp only [an.map_comp, H.map_comp_apply]
    choose a ha using fun i ↦ (h i).2 (H.map (an.map (biproduct.π F i)) q y)
    refine ⟨∑ i, H.map (biproduct.ι F i) q (a i), ?_⟩
    rw [map_sum, hy]
    simp only [gagaMap_map, ha, an]

/-- **The GAGA comparison map is additive**: it is bijective on a finite coproduct `∐ Fᵢ` if it
is bijective on every summand `Fᵢ`. -/
lemma gagaMap_bijective_sigma {I : Type*} [Finite I]
    (F : I → SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [HasCoproduct F]
    (q : ℕ) (h : ∀ i, Function.Bijective (gagaMap X (F i) q)) :
    Function.Bijective (gagaMap X (∐ F) q) := by
  have := HasBiproduct.of_hasCoproduct F
  exact (gagaMap_bijective_iff_of_iso (biproduct.isoCoproduct F) q).1
    (gagaMap_bijective_biproduct F q h)

/-- **The GAGA comparison map is additive**: it is bijective on a binary direct sum `F ⊞ G` if it
is bijective on `F` and on `G`. -/
lemma gagaMap_bijective_biprod
    {F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} [HasBinaryBiproduct F G]
    (q : ℕ) (hF : Function.Bijective (gagaMap X F q)) (hG : Function.Bijective (gagaMap X G q)) :
    Function.Bijective (gagaMap X (F ⊞ G) q) := by
  let an := analytificationModules X
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · have h₁ : H.map (biprod.fst : F ⊞ G ⟶ F) q x = 0 := hF.1 <| by
      rw [gagaMap_map, hx, map_zero, map_zero]
    have h₂ : H.map (biprod.snd : F ⊞ G ⟶ G) q x = 0 := hG.1 <| by
      rw [gagaMap_map, hx, map_zero, map_zero]
    rw [← H.map_id_apply x, ← biprod.total, H.map_add_apply, H.map_comp_apply,
      H.map_comp_apply, h₁, h₂, map_zero, map_zero, add_zero]
  · obtain ⟨a, ha⟩ := hF.2 (H.map (an.map (biprod.fst : F ⊞ G ⟶ F)) q y)
    obtain ⟨b, hb⟩ := hG.2 (H.map (an.map (biprod.snd : F ⊞ G ⟶ G)) q y)
    refine ⟨H.map biprod.inl q a + H.map biprod.inr q b, ?_⟩
    rw [map_add, gagaMap_map, gagaMap_map, ha, hb, ← H.map_comp_apply, ← H.map_comp_apply,
      ← an.map_comp, ← an.map_comp, ← H.map_add_apply, ← an.map_add, biprod.total, an.map_id,
      H.map_id_apply]

end ComplexAnalytic

end
