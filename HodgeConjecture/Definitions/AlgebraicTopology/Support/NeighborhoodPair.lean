/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Category.TopPair

/-!
# Neighborhood and point-complement pairs

Elementary pairs and maps used for local cohomology with support.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicTopology.Singular

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- The pair `(M, M ∖ {x})`. -/
abbrev pointComplementPair (x : M) : TopPair :=
  TopPair.ofSubset (X := TopCat.of M) ({x}ᶜ : Set M)

/-- A neighborhood paired with the complement of a support in it. -/
abbrev neighborhoodSupportComplementPair (W S : Set M) : TopPair :=
  TopPair.ofSubset (X := TopCat.of W) {w | w.1 ∉ S}

/-- Inclusion of neighborhood/support-complement pairs. -/
def neighborhoodSupportInclusionPairMap {W V : Set M} (hWV : W ⊆ V) (S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1.1, hWV w.1.2⟩, w.2⟩, by fun_prop⟩) (by ext w; rfl)

/-- The inclusion from a neighborhood/support pair into a punctured-point pair. -/
def neighborhoodSupportToPointPairMap (V : Set M) {S : Set M} {x : M} (hx : x ∈ S) :
    neighborhoodSupportComplementPair V S ⟶ pointComplementPair x :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w => ⟨w.1.1, fun h => w.2 (h ▸ hx)⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) rfl

/-- A continuous injection induces a map of punctured-point pairs. -/
def pointComplementPairMap {f : C(M, N)} (hf : Function.Injective f) (x : M) :
    pointComplementPair x ⟶ pointComplementPair (f x) :=
  TopPair.ofHom
    (TopCat.ofHom f)
    (TopCat.ofHom ⟨fun y => ⟨f y, fun h => y.2 (hf h)⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩) rfl

end AlgebraicTopology.Singular
