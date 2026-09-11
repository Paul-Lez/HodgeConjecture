/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistComplexForm
public import Other.AlgebraicGeometry.ProjectiveChartOneChart

/-!
# Algebraization of twist morphisms in non-negative degree

For `b ≤ a` every morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ` is the analytification of an algebraic
one.  The chart multiplier on the `0`-th chart has polynomial growth of order `a − b`
(`chartMultiplierGrowth`), hence is the chart expression of a unique degree-`(a − b)` form `Q`
with complex coefficients (`existsUnique_isHomogeneous_of_growth`); `algMulC` realises `Q` by an
algebraic morphism with the same chart expression there
(`chartFun_formMultiplier`), and `hom_eq_zero_of_one_chart` upgrades that to equality of the two
morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000 in
/-- **Algebraization in non-negative degree.** -/
theorem twistRankOneAlgebraizesNonneg (N : ℕ) :
    Other.ProjectiveChart.TwistRankOneAlgebraizesNonneg N := by
  classical
  intro a b hba φ
  obtain ⟨k, rfl⟩ : ∃ k, a = b + k := ⟨a - b, by omega⟩
  have hex : ∀ i : Fin (N + 1), ∃ w,
      φ.val.app (op (chartOpen N i)) (anChartFrame N (b + k) i) = w • anChartFrame N b i :=
    fun i => (existsUnique_canonicalChartMultiplier N (b + k) b i φ).exists
  choose v hv using hex
  obtain ⟨C, hC⟩ := chartMultiplierGrowth N (b + k) b (Nat.le_add_right b k) φ 0 (v 0) (hv 0)
  have hC' : ∀ z : Fin N → ℂ, ‖chartFun N 0 (v 0) z‖ ≤ C * (1 + ‖z‖) ^ k := by
    intro z
    have := hC z
    rwa [Nat.add_sub_cancel_left] at this
  obtain ⟨Q, ⟨hQhom, hQeval⟩, -⟩ :=
    existsUnique_isHomogeneous_of_growth (m := k) 0 (analyticOnNhd_chartFun 0 (v 0)) hC'
  refine ⟨algMulC N b k Q hQhom, ?_⟩
  set g : analyticTwist N (b + k) ⟶ analyticTwist N b :=
    (moduleAnalytification (projectiveSpaceOver N) N).map (algMulC N b k Q hQhom) with hgdef
  have hgapp : ∀ i : Fin (N + 1),
      g.val.app (op (chartOpen N i)) (anChartFrame N (b + k) i) =
        formMultiplier N k i Q hQhom • anChartFrame N b i := by
    intro i
    rw [hgdef]
    exact analytified_algMulC_anChartFrame N b k i Q hQhom
  have hdiff : φ - g = 0 := by
    refine hom_eq_zero_of_one_chart _ 0 (fun i => v i - formMultiplier N k i Q hQhom) ?_ ?_
    · intro i
      show φ.val.app (op (chartOpen N i)) (anChartFrame N (b + k) i) -
          g.val.app (op (chartOpen N i)) (anChartFrame N (b + k) i) = _
      rw [hv i, hgapp i, sub_smul]
    · intro z
      show chartFun N 0 (v 0) z - chartFun N 0 (formMultiplier N k 0 Q hQhom) z = 0
      rw [chartFun_formMultiplier, ← hQeval z, sub_self]
  exact (sub_eq_zero.mp hdiff).symm

end AlgebraicGeometry.ComplexProjectiveSpace
