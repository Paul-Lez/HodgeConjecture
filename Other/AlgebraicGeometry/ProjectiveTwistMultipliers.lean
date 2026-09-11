/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistAnalyticFrames
public import Other.AlgebraicGeometry.HolomorphicMultiplierTransition

/-!
# Chart multipliers of a twist endomorphism agree on overlaps

For a morphism between the *same* analytic twist on `ℙᴺ`, the two frames of source and target on
a chart are literally the same, so the frame changes on an overlap cancel and the chart
multipliers agree there.  This is the degree-zero case of the cocycle relation, and it is the
input to the maximum-modulus argument identifying such a morphism with a constant.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

variable (N a : ℕ)

/-- **Equal-degree cocycle.**  The chart multipliers of an endomorphism of `𝒪(−a)^an` agree on the
overlap of two standard charts. -/
theorem chartMultiplier_eq_on_overlap
    (φ : ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) a ⟶
      ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) a)
    (i j : Fin (N + 1))
    {hi : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N i))}
    {hj : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N j))}
    (hhi : φ.val.app (op (chartOpen N i)) (analyticChartFrame N a i) =
      hi • analyticChartFrame N a i)
    (hhj : φ.val.app (op (chartOpen N j)) (analyticChartFrame N a j) =
      hj • analyticChartFrame N a j) :
    ComplexPoint.holRingRes
        (inf_le_left : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N i) hi =
      ComplexPoint.holRingRes
        (inf_le_right : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N j) hj := by
  have hgi := (holomorphicGenerates_analyticChartFrame N a i).restrict
    (inf_le_left : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N i)
  have hgj := (holomorphicGenerates_analyticChartFrame N a j).restrict
    (inf_le_right : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N j)
  obtain ⟨u, huunit, hu⟩ := hgj.exists_isUnit_smul_eq hgi
  exact ComplexPoint.multiplier_eq_of_same_transition φ inf_le_left inf_le_right
    (holomorphicGenerates_analyticChartFrame N a j) huunit hu hu hhi hhj

end AlgebraicGeometry.ComplexProjectiveSpace
