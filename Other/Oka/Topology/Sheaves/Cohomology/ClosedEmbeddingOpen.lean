/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbedding

/-!
# Cohomology of opens along closed embeddings

Let `f : Y ⟶ X` be a closed embedding, `G` an abelian sheaf on `Y` and `W` an open of `X`. The
cohomology of `G` on `f⁻¹(W)` agrees with the cohomology of the pushforward `f_* G` on `W`:

* `TopCat.Sheaf.H'PushforwardClosedEmbeddingAddEquiv hf G W q :
  H'ᵠ(f⁻¹(W), G) ≃+ H'ᵠ(W, f_* G)` for Mathlib's cohomology of opens
  `CategoryTheory.Sheaf.H' F q W = Extᵠ(ℤ[W], F)`;
* `TopCat.Sheaf.H.restrictOpenPushforwardClosedEmbeddingAddEquiv hf G W q :
  Hᵠ(f⁻¹(W), G|_{f⁻¹(W)}) ≃+ Hᵠ(W, (f_* G)|_W)`.

Both come from dimension shifting (`CategoryTheory.extComparison_bijective`) applied to the exact,
injectives preserving functor `f_*` and the canonical map `ℤ[W] ⟶ f_* ℤ[f⁻¹(W)]`: morphisms
out of `ℤ[f⁻¹(W)]` into `B` and out of `ℤ[W]` into `f_* B` are both the sections `B(f⁻¹(W))`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

section

variable (f : Y ⟶ X) (W : Opens X)

/-- The canonical map `ℤ[W] ⟶ f_* ℤ[f⁻¹(W)]`, corresponding to the section
`1 ∈ ℤ[f⁻¹(W)](f⁻¹(W)) = (f_* ℤ[f⁻¹(W)])(W)`. -/
noncomputable def freeYonedaPushforwardUnit :
    freeYoneda W ⟶ (pushforwardAb f).obj (freeYoneda ((Opens.map f).obj W)) :=
  (freeYonedaHomEquiv W _).symm (freeYonedaHomEquiv ((Opens.map f).obj W) _ (𝟙 _))

/-- Precomposition with `ℤ[W] ⟶ f_* ℤ[f⁻¹(W)]` identifies morphisms `ℤ[f⁻¹(W)] ⟶ B` with
morphisms `ℤ[W] ⟶ f_* B`. -/
lemma freeYonedaPushforwardUnit_comp_bijective (B : AbSheaf Y) :
    Function.Bijective (fun x : freeYoneda ((Opens.map f).obj W) ⟶ B =>
      freeYonedaPushforwardUnit f W ≫ (pushforwardAb f).map x) := by
  have : (fun x : freeYoneda ((Opens.map f).obj W) ⟶ B =>
      freeYonedaPushforwardUnit f W ≫ (pushforwardAb f).map x) =
      (freeYonedaHomEquiv W _).symm ∘ freeYonedaHomEquiv _ B := by
    funext x
    apply (freeYonedaHomEquiv W _).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, freeYonedaHomEquiv_comp,
      freeYonedaPushforwardUnit]
    have h := freeYonedaHomEquiv_comp ((Opens.map f).obj W) (𝟙 _) x
    rw [Category.id_comp] at h
    rw [h]
    rfl
  rw [this]
  exact (freeYonedaHomEquiv W _).symm.bijective.comp (freeYonedaHomEquiv _ B).bijective

end

variable {f : Y ⟶ X}

/-- **Cohomology of an open along a closed embedding.** For a closed embedding `f : Y ⟶ X`,
`H'ᵠ(f⁻¹(W), G) ≃+ H'ᵠ(W, f_* G)`. -/
noncomputable def H'PushforwardClosedEmbeddingAddEquiv (hf : IsClosedEmbedding f)
    (G : AbSheaf Y) (W : Opens X) (q : ℕ) :
    CategoryTheory.Sheaf.H'.{u} G q ((Opens.map f).obj W) ≃+
      CategoryTheory.Sheaf.H'.{u} ((pushforwardAb f).obj G) q W :=
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).1
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).2
  AddEquiv.ofBijective (extComparison (pushforwardAb f) (freeYonedaPushforwardUnit f W) G q)
    (extComparison_bijective _ _ (freeYonedaPushforwardUnit_comp_bijective f W) G q)

/-- **Cohomology of an open along a closed embedding**, for restricted sheaves:
`Hᵠ(f⁻¹(W), G|_{f⁻¹(W)}) ≃+ Hᵠ(W, (f_* G)|_W)`. -/
noncomputable def H.restrictOpenPushforwardClosedEmbeddingAddEquiv (hf : IsClosedEmbedding f)
    (G : AbSheaf Y) (W : Opens X) (q : ℕ) :
    H ((restrictOpen ((Opens.map f).obj W)).obj G) q ≃+
      H ((restrictOpen W).obj ((pushforwardAb f).obj G)) q :=
  (H'AddEquiv _ G q).symm.trans
    ((H'PushforwardClosedEmbeddingAddEquiv hf G W q).trans (H'AddEquiv W _ q))

end TopCat.Sheaf

end
