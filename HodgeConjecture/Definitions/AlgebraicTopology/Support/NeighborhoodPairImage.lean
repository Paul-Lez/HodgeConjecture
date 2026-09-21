/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Cohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPair
/-!
# Transporting actual neighborhood-support pairs through embeddings

An embedding identifies a neighborhood and its support complement with their actual
images. Only equality of support membership on that neighborhood is required.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicTopology.Singular

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- The literal pair isomorphism, with the embedding as ambient map. -/
def neighborhoodSupportPairImageIso {f : M → N} (hf : IsEmbedding f)
    {W B : Set M} {S : Set N} (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S) :
    neighborhoodSupportComplementPair W B ≅
      neighborhoodSupportComplementPair (f '' W) S :=
  let e := hf.homeomorphImage W
  let e₀ := e.subtype fun w => not_congr (hS w w.2)
  { hom := TopPair.ofHom
      (TopCat.ofHom ⟨e, e.continuous⟩)
      (TopCat.ofHom ⟨e₀, e₀.continuous⟩)
      (by ext w; rfl)
    inv := TopPair.ofHom
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
      (TopCat.ofHom ⟨e₀.symm, e₀.symm.continuous⟩)
      (by ext w; rfl)
    hom_inv_id := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext w
        exact e₀.left_inv w
      · ext w
        exact e.left_inv w
    inv_hom_id := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext w
        exact e₀.right_inv w
      · ext w
        exact e.right_inv w }

/-- Relative cohomology transport. -/
def neighborhoodSupportPairImageCohomologyIso
    (R : Type u) [CommRing R] {f : M → N} (hf : IsEmbedding f)
    {W B : Set M} {S : Set N} (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S) (n : ℕ) :
    RelativeCohomology R (neighborhoodSupportComplementPair (f '' W) S) n ≅
      RelativeCohomology R (neighborhoodSupportComplementPair W B) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (HomologicalComplex.linearDualIso
      ((relativeChainFunctor R).mapIso (neighborhoodSupportPairImageIso hf hS)))

end AlgebraicTopology.Singular
