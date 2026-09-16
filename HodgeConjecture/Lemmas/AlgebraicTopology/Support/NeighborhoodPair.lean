/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPair

/-!
# Neighborhood and point-complement pair maps

Basic identities for inclusions between neighborhood pairs.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicTopology.Singular

variable {M : Type u} [TopologicalSpace M]

@[simp] theorem neighborhoodSupportInclusionPairMap_id (W S : Set M) :
    neighborhoodSupportInclusionPairMap (show W ⊆ W from le_refl W) S =
      𝟙 (neighborhoodSupportComplementPair W S) := rfl

@[simp] theorem neighborhoodSupportInclusionPairMap_comp {U V W : Set M}
    (hUV : U ⊆ V) (hVW : V ⊆ W) (S : Set M) :
    neighborhoodSupportInclusionPairMap hUV S ≫ neighborhoodSupportInclusionPairMap hVW S =
      neighborhoodSupportInclusionPairMap (hUV.trans hVW) S := rfl

/-- Ambient inclusions factor through every nested neighborhood. -/
@[simp]
theorem neighborhoodSupportInclusionPairMap_toPoint {U V : Set M}
    (hUV : U ⊆ V) (S : Set M) (x : M) (hx : x ∈ S) :
    neighborhoodSupportInclusionPairMap hUV S ≫ neighborhoodSupportToPointPairMap V hx =
      neighborhoodSupportToPointPairMap U hx := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

end AlgebraicTopology.Singular
