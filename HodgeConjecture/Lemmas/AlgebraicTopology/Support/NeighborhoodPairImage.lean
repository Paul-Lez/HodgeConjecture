/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPairImage
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NeighborhoodPair

/-!
# Maps and cohomology of neighborhood-support pairs

Topological consequences of the pair identifications induced by embeddings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicTopology.Singular

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- Pair-image isomorphisms commute with neighborhood inclusions. -/
@[simp]
theorem neighborhoodSupportPairImageIso_hom_naturality
    {f : M → N} (hf : IsEmbedding f) {U V B : Set M} {S : Set N}
    (hUV : U ⊆ V) (hS : ∀ w ∈ V, w ∈ B ↔ f w ∈ S) :
    neighborhoodSupportInclusionPairMap hUV B ≫
        (neighborhoodSupportPairImageIso hf hS).hom =
      (neighborhoodSupportPairImageIso hf (fun w hw => hS w (hUV hw))).hom ≫
        neighborhoodSupportInclusionPairMap (Set.image_mono hUV) S := rfl

/-- Relative cohomology vanishes for an embedded neighborhood-support pair exactly when
it vanishes for its image pair. -/
theorem neighborhoodSupportPairImageCohomology_isZero_iff
    (R : Type u) [CommRing R] {f : M → N} (hf : IsEmbedding f)
    {W B : Set M} {S : Set N} (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S) (n : ℕ) :
    IsZero (RelativeCohomology R (neighborhoodSupportComplementPair (f '' W) S) n) ↔
      IsZero (RelativeCohomology R (neighborhoodSupportComplementPair W B) n) :=
  (neighborhoodSupportPairImageCohomologyIso R hf hS n).isZero_iff

/-- The image-pair identification commutes with the maps to punctured-point pairs. -/
theorem neighborhoodSupportPairImageIso_inv_comp_toPoint
    {f : M → N} (hf : IsEmbedding f) {W B : Set M} {S : Set N}
    (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S) {x : M} (hxB : x ∈ B) (hxS : f x ∈ S) :
    (neighborhoodSupportPairImageIso hf hS).inv ≫
        neighborhoodSupportToPointPairMap W hxB ≫
          pointComplementPairMap (f := ⟨f, hf.continuous⟩) hf.injective x =
      neighborhoodSupportToPointPairMap (f '' W) hxS := by
  apply (cancel_epi (neighborhoodSupportPairImageIso hf hS).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

end AlgebraicTopology.Singular
