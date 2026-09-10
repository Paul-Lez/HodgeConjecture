/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.ChartLocalFundamentalClassDifferentiableInvariance

/-! # Exact transport of chart-local fundamental classes by homeomorphisms

The chart transported by an actual homeomorphism has the same target and the
same radial compression. Its literal punctured-pair map therefore factors through
the original chart pair map. This is topological naturality of the constructed
class, not an assumption that arbitrary homeomorphisms preserve orientations.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (H : M ≃ₜ N) (x : M)

/-- The actual homeomorphism map on point-complement pairs. -/
def pointComplementHomeomorphPairMap : pointComplementPair x ⟶ pointComplementPair (H x) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨H, H.continuous⟩)
    (TopCat.ofHom ⟨fun y => ⟨H y, fun he => y.2 (H.injective he)⟩,
      (H.continuous.comp continuous_subtype_val).subtype_mk _⟩) rfl

variable (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (hx : x ∈ e.source)

include hx in
/-- The transported chart contains the transported center. -/
theorem mem_homeomorphTransportedChart :
    H x ∈ (H.symm.transOpenPartialHomeomorph e).source := by
  change H.symm (H x) ∈ e.source
  simpa only [H.symm_apply_apply] using hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport does not change the chosen coordinate radius. -/
theorem chartRadius_homeomorphTransport :
    chartRadius d (H.symm.transOpenPartialHomeomorph e) (H x)
      (mem_homeomorphTransportedChart H x d e hx) = chartRadius d e x hx := by
  unfold chartRadius
  simp only [Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply, H.symm_apply_apply]

/-- The actual compressed-chart pair map factors through the homeomorphism. -/
theorem chartModelEmbeddingPair_homeomorphTransport :
    chartModelEmbeddingPair d e x hx ≫ pointComplementHomeomorphPairMap H x =
      chartModelEmbeddingPair d (H.symm.transOpenPartialHomeomorph e) (H x)
        (mem_homeomorphTransportedChart H x d e hx) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext y
    apply Subtype.ext
    change H (chartModelEmbedding d e x hx y.1) =
      chartModelEmbedding d (H.symm.transOpenPartialHomeomorph e) (H x)
        (mem_homeomorphTransportedChart H x d e hx) y.1
    dsimp only [chartModelEmbedding]
    rw [chartRadius_homeomorphTransport]
    simp only [OpenPartialHomeomorph.trans_apply,
      Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply, H.symm_apply_apply]
    rfl
  · ext y
    change H (chartModelEmbedding d e x hx y) =
      chartModelEmbedding d (H.symm.transOpenPartialHomeomorph e) (H x)
        (mem_homeomorphTransportedChart H x d e hx) y
    dsimp only [chartModelEmbedding]
    rw [chartRadius_homeomorphTransport]
    simp only [OpenPartialHomeomorph.trans_apply,
      Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_apply, H.symm_apply_apply]
    rfl

/-- Exact naturality for the transported chart, before imposing any orientation
comparison between this chart and a separately chosen target chart. -/
theorem localClassOfChart_homeomorphTransport :
    relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H x)
      (localClassOfChart d e x hx) =
    localClassOfChart d (H.symm.transOpenPartialHomeomorph e) (H x)
      (mem_homeomorphTransportedChart H x d e hx) := by
  rw [localClassOfChart, ← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    chartModelEmbeddingPair_homeomorphTransport]
  rfl

end AlgebraicTopology.Singular
