/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FlattenedSupport

/-!
# Actual relative homology near a flattened support

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.FlattenedSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

variable (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (x : M) (hx : x ∈ e.source)

include hx

@[simp] theorem flattenedSupportEmbedding_zero : flattenedSupportEmbedding E c e x hx 0 = x := by
  change e.symm (OpenPartialHomeomorph.univBall (e x) _ 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero, e.left_inv hx]

theorem mem_flattenedSupportNeighborhood : x ∈ flattenedSupportNeighborhood E c e x hx := by
  have h := (flattenedSupportEmbedding E c e x hx).map_source
    (show 0 ∈ (flattenedSupportEmbedding E c e x hx).source by
      rw [flattenedSupportEmbedding_source]; trivial)
  change x ∈ (flattenedSupportEmbedding E c e x hx).target
  simpa only [flattenedSupportEmbedding_zero] using h

@[simp] theorem flattenedSupportHomeomorph_apply (v : E × (Fin c → ℂ)) :
    (flattenedSupportHomeomorph E c e x hx v : M) =
      flattenedSupportEmbedding E c e x hx v := rfl

variable (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (h0 : (e x).2 = 0)

include hS h0

theorem flattenedSupportRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeHomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n) :=
  (standardComplexLocalHomology_isZero_of_ne c n hn).of_iso
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 n)

@[simp] theorem flattenedSupportNormalClass_normalization :
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).hom.hom
      (flattenedSupportNormalClass E c e x hx S hS h0) = standardComplexLocalClass c :=
  ConcreteCategory.congr_hom
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).inv_hom_id _

theorem flattenedSupportRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n) :=
  relativeCohomology_isZero ℚ _ n
    (flattenedSupportRelativeHomology_isZero_of_ne E c e x hx S hS h0 n hn)

end AlgebraicTopology.Singular
