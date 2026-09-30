/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbedding
public import Other.Oka.Topology.Sheaves.Cohomology.OpenEmbedding

/-!
# Cohomology of pushforwards along open embeddings

Let `f : Y ⟶ X` be an open embedding and `N` an abelian sheaf on `Y`. The restriction of `f_* N`
to `Y` is `N` (`TopCat.Sheaf.restrictAbPushforwardAbIso`), so for an open `U ⊆ Y` the cohomology of
`f_* N` on `f(U)` is the cohomology of `N` on `U`
(`TopCat.Sheaf.H.restrictOpenPushforwardOpenEmbeddingAddEquiv`).

We also record that a morphism of abelian sheaves which is bijective on sections over all opens
inside an open `W` induces isomorphisms on the cohomology on `W`
(`TopCat.Sheaf.H.restrictOpenAddEquivOfBijective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

/-- A morphism of abelian sheaves which is bijective on the sections over all opens inside `W`
restricts to an isomorphism over `W`. -/
lemma isIso_restrictOpen_map {A B : AbSheaf X} (φ : A ⟶ B) (W : Opens X)
    (h : ∀ V ≤ W, Function.Bijective (φ.hom.app (op V))) :
    IsIso ((restrictOpen W).map φ) := by
  haveI : ∀ V, IsIso (((sheafToPresheaf _ _).map ((restrictOpen W).map φ)).app V) := fun V ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (h _ (by rintro _ ⟨x, -, rfl⟩; exact x.2))
  haveI := NatIso.isIso_of_isIso_app ((sheafToPresheaf _ _).map ((restrictOpen W).map φ))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- A morphism of abelian sheaves which is bijective on the sections over all opens inside `W`
induces isomorphisms on the cohomology on `W`. -/
noncomputable def H.restrictOpenAddEquivOfBijective {A B : AbSheaf X} (φ : A ⟶ B) (W : Opens X)
    (h : ∀ V ≤ W, Function.Bijective (φ.hom.app (op V))) (q : ℕ) :
    H ((restrictOpen W).obj A) q ≃+ H ((restrictOpen W).obj B) q :=
  haveI := isIso_restrictOpen_map φ W h
  H.addEquivOfIso (asIso ((restrictOpen W).map φ)) q

variable {f : Y ⟶ X} (hf : IsOpenEmbedding f)

/-- **The restriction of a pushforward along an open embedding**: `(f_* N)|_Y ≅ N`. -/
noncomputable def restrictAbPushforwardAbIso (N : AbSheaf Y) :
    (restrictAb hf).obj ((pushforwardAb f).obj N) ≅ N :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun V ↦ N.obj.mapIso (eqToIso
      (TopologicalSpace.Opens.map_functor_eq' f hf V.unop).symm).op) fun {V V'} i ↦ by
        change N.obj.map _ ≫ N.obj.map _ = N.obj.map _ ≫ N.obj.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl)

/-- **Cohomology of a pushforward along an open embedding**: for an open `U ⊆ Y`,
`Hᵠ(f(U), f_* N) ≃+ Hᵠ(U, N)`. -/
noncomputable def H.restrictOpenPushforwardOpenEmbeddingAddEquiv (N : AbSheaf Y) (U : Opens Y)
    {W : Opens X} (hW : hf.isOpenMap.functor.obj U = W) (q : ℕ) :
    H ((restrictOpen W).obj ((pushforwardAb f).obj N)) q ≃+ H ((restrictOpen U).obj N) q :=
  (H.restrictOpenAddEquivOfEq hf U _ q hW).trans
    (H.restrictOpenAddEquivOfIso U (restrictAbPushforwardAbIso hf N) q)

end TopCat.Sheaf

end
