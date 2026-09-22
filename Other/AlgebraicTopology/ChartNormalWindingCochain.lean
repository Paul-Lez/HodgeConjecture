/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.StandardComplexWinding
public import HodgeConjecture.Definitions.AlgebraicTopology.NormalProjectionCoclass

/-!
# The explicit winding cocycle in a normal chart

For a codimension-one support flattened by an analytic chart, this file pulls the literal
standard cocycle `(0, windingIndex)` back along the chart's normal projection.  It is therefore
an actual degree-two relative singular cochain on the support-complement pair of the chart,
not a coclass postulated by a purity or Chern-class theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Topology AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M]
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) (S W : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (hW : W ⊆ e.source)

/-- The concrete degree-two cochain in the chart's support-complement pair. -/
def chartNormalWindingCochain :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ
      (neighborhoodSupportComplementPair W S))).X 1 :=
  rawRelativeWindingCochainPullback
    (chartNormalProjectionPair E 1 e S hS W hW)
    standardComplexNormalCoordinate standardComplexNormalCoordinate_ne_zero

omit [NormedSpace ℝ E] in
/-- The chart-level winding cochain is closed. -/
lemma chartNormalWindingCochain_closed :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ
      (neighborhoodSupportComplementPair W S))).d 1 2
      (chartNormalWindingCochain E e S W hS hW) = 0 :=
  rawRelativeWindingCochainPullback_closed
    (chartNormalProjectionPair E 1 e S hS W hW)
    standardComplexNormalCoordinate standardComplexNormalCoordinate_ne_zero

end ChernWinding
