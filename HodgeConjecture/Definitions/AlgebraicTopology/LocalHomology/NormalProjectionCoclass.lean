/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FlattenedSupport
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.CenteredComplexOrientation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
/-!
# Normal projections and the local support coclass

The normal projection of a support-flattening chart is a map of pairs on every open subset of
its source, and pulling the fixed normal coclass back along it is compatible with restriction.
The radial-fiber factorization below identifies that coclass with the normalized local coclass.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

/-- Let `M` be a topological space and `W ⊆ V` and `S` subsets of `M`. This is the map of pairs `(W,
W \ S) → (V, V \ S)` given by inclusion on both subspaces. -/
def neighborhoodSupportInclusionPairMap {W V : Set M} (hWV : W ⊆ V) (S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1.1, hWV w.1.2⟩, w.2⟩, by fun_prop⟩) (by ext w; rfl)

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)

/-- Let `M` be a topological space, `E` a real normed vector space, and `e` a chart from an open
subset of `M` to `E × ℂ^c`. Suppose `S ⊆ M` agrees in this chart with the zero set of the second
coordinate. For `W` in the chart source, normal projection `w ↦ (e(w)).2` gives this map of
pairs `(W, W \ S) → (ℂ^c, ℂ^c \ {0})`. -/
def chartNormalProjectionPair (W : Set M) (hW : W ⊆ e.source) :
    neighborhoodSupportComplementPair W S ⟶ puncturedPair ℂ c :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => (e w.1).2, ((e.continuousOn.mono hW).domRestrict).snd⟩)
    (TopCat.ofHom ⟨fun w => ⟨(e w.1.1).2, fun h => w.2 ((hS _ (hW w.1.2)).mpr h)⟩,
      ((((e.continuousOn.mono hW).domRestrict).comp continuous_subtype_val).snd).subtype_mk _⟩)
    (by ext w; rfl)

/-- Let `M` be a topological space with a chart `e` into `E × ℂ^c`, where `E` is a real normed
vector space. Suppose `S ⊆ M` is the zero-normal-coordinate locus in the chart. For `W` in its
source, this class in `H^{2c}(W, W \ S; ℚ)` is the pullback under normal projection of the class
evaluating to `1` on the complex orientation class of `(ℂ^c, ℂ^c \ {0})`. -/
def chartNormalProjectionCoclass (W : Set M) (hW : W ⊆ e.source) :
    -- The pullback to `H^{2c}(W, W \ S; ℚ)` of the normalized class in `H^{2c}(ℂ^c, ℂ^c \ {0}; ℚ)`.
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W S) (2 * c) :=
  relativeCohomologyMap ℚ (2 * c) (chartNormalProjectionPair E c e S hS W hW)
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ c)
      (standardComplexLocalClass_ne_zero_for_chart c))

end AlgebraicTopology.Singular
