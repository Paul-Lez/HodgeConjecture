/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietoris

/-!
# Cohomology of opens along open embeddings

Let `f : Y ⟶ X` be an open embedding, `F` an abelian sheaf on `X` and `U` an open of `Y`. The
cohomology of `F` on the open `f(U)` of `X` agrees with the cohomology of the restriction
`F|_Y` (`TopCat.Sheaf.restrictAb`) on `U`:

* `TopCat.Sheaf.H'ImageAddEquiv hf U F q : H'ᵠ(f(U), F) ≃+ H'ᵠ(U, F|_Y)` for Mathlib's cohomology
  of opens `CategoryTheory.Sheaf.H' F q U = Extᵠ(ℤ[U], F)`;
* `TopCat.Sheaf.H.restrictOpenImageAddEquiv hf U F q : Hᵠ(f(U), F|_{f(U)}) ≃+ Hᵠ(U, (F|_Y)|_U)`.

Both come from dimension shifting (`CategoryTheory.extComparison_bijective`) applied to the exact,
injectives preserving restriction functor and the canonical map `ℤ[U] ⟶ ℤ[f(U)]|_Y`: morphisms
out of `ℤ[f(U)]` and out of `ℤ[U]` into `B|_Y` are both the sections `B(f(U))`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenEmbedding f) (U : Opens Y)

/-- The canonical map `ℤ[U] ⟶ ℤ[f(U)]|_Y`, corresponding to the section
`1 ∈ ℤ[f(U)](f(U)) = (ℤ[f(U)]|_Y)(U)`. -/
noncomputable def freeYonedaImageUnit :
    freeYoneda U ⟶ (restrictAb hf).obj (freeYoneda (hf.isOpenMap.functor.obj U)) :=
  (freeYonedaHomEquiv U _).symm (freeYonedaHomEquiv (hf.isOpenMap.functor.obj U) _ (𝟙 _))

lemma freeYonedaImageUnit_comp_bijective (B : AbSheaf X) :
    Function.Bijective (fun x : freeYoneda (hf.isOpenMap.functor.obj U) ⟶ B =>
      freeYonedaImageUnit hf U ≫ (restrictAb hf).map x) := by
  have : (fun x : freeYoneda (hf.isOpenMap.functor.obj U) ⟶ B =>
      freeYonedaImageUnit hf U ≫ (restrictAb hf).map x) =
      (freeYonedaHomEquiv U _).symm ∘ freeYonedaHomEquiv _ B := by
    funext x
    apply (freeYonedaHomEquiv U _).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, freeYonedaHomEquiv_comp,
      freeYonedaImageUnit]
    have h := freeYonedaHomEquiv_comp (hf.isOpenMap.functor.obj U) (𝟙 _) x
    rw [Category.id_comp] at h
    rw [h]
    rfl
  rw [this]
  exact (freeYonedaHomEquiv U _).symm.bijective.comp (freeYonedaHomEquiv _ B).bijective

/-- **Cohomology of an open along an open embedding.** For an open embedding `f : Y ⟶ X`,
`H'ᵠ(f(U), F) ≃+ H'ᵠ(U, F|_Y)`. -/
noncomputable def H'ImageAddEquiv (F : AbSheaf X) (q : ℕ) :
    CategoryTheory.Sheaf.H'.{u} F q (hf.isOpenMap.functor.obj U) ≃+
      CategoryTheory.Sheaf.H'.{u} ((restrictAb hf).obj F) q U :=
  AddEquiv.ofBijective (extComparison (restrictAb hf) (freeYonedaImageUnit hf U) F q)
    (extComparison_bijective _ _ (freeYonedaImageUnit_comp_bijective hf U) F q)

/-- **Cohomology of an open along an open embedding**, for restricted sheaves:
`Hᵠ(f(U), F|_{f(U)}) ≃+ Hᵠ(U, (F|_Y)|_U)`. -/
noncomputable def H.restrictOpenImageAddEquiv (F : AbSheaf X) (q : ℕ) :
    H ((restrictOpen (hf.isOpenMap.functor.obj U)).obj F) q ≃+
      H ((restrictOpen U).obj ((restrictAb hf).obj F)) q :=
  (H'AddEquiv _ F q).symm.trans ((H'ImageAddEquiv hf U F q).trans (H'AddEquiv U _ q))

/-- The cohomology of `F` on `W` is that of `F|_Y` on `f⁻¹(W)` if `W` is the image of `f⁻¹(W)`
(e.g. `W ⊆ range f`), stated for the open `U` of `Y` with `f(U) = W`. -/
noncomputable def H.restrictOpenAddEquivOfEq (F : AbSheaf X) (q : ℕ) {W : Opens X}
    (hW : hf.isOpenMap.functor.obj U = W) :
    H ((restrictOpen W).obj F) q ≃+ H ((restrictOpen U).obj ((restrictAb hf).obj F)) q := by
  subst hW
  exact H.restrictOpenImageAddEquiv hf U F q

/-- Isomorphic sheaves have isomorphic cohomology on every open. -/
noncomputable def H.restrictOpenAddEquivOfIso {F G : AbSheaf Y} (e : F ≅ G) (q : ℕ) :
    H ((restrictOpen U).obj F) q ≃+ H ((restrictOpen U).obj G) q :=
  H.addEquivOfIso ((restrictOpen U).mapIso e) q

end TopCat.Sheaf

end
