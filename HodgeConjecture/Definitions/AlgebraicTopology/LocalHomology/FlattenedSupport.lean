/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalSlicePurity
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Relative homology near a flattened support

Radial compression into a small product-norm ball preserves the zero-normal plane.
Composing with the inverse flattening chart gives a pair homeomorphism from the normal-slice
model to a small open neighborhood paired with its support complement, along which the
homology calculation and the normalized class are transported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

/-- The actual pair consisting of a neighborhood and the complement of a support in it. -/
abbrev neighborhoodSupportComplementPair (W S : Set M) : TopPair :=
  TopPair.ofSubset (X := TopCat.of W) {w | w.1 ∉ S}

variable (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (x : M) (hx : x ∈ e.source)

include hx

variable (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (h0 : (e x).2 = 0)

include hS h0

end AlgebraicTopology.Singular
