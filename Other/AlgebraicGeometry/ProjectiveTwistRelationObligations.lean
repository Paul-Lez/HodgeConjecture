/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistCanonicalMultipliers
public import Other.AlgebraicGeometry.TwistRelationsFromRankOne
public import Other.AlgebraicGeometry.ProjectiveTwistObligations

/-!
# What is left of the relation obligation on `ℙᴺ`

`TwistRelationsAlgebraizeProj N` is now reduced, by the matrix argument
(`TwistRelationsFromRankOne.lean`), to its **rank-one** case, and that case splits into

* `TwistRankOneAlgebraizesNonneg N` — the case `b ≤ a`, where the chart multipliers of a
  morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` have to be recognised as a degree-`(a − b)` form, and
* `TwistRankOneVanishesNeg N` — the case `a < b`, where they have to vanish.

Both are stated here, together with two finer intermediate obligations that the present
development reduces the first one to:

* `ChartRatioEvaluation N n` — the chart-coordinate formula for the transition unit
  `analyticSpaceRatio`, which is the evaluation of the regular function `Xⱼⁿ/Xᵢⁿ`;
* `ChartMultiplierGrowth N a b` — the polynomial growth bound for the chart expression of a
  multiplier, which follows from the cocycle
  `ComplexProjectiveSpace.canonicalChartMultiplier_transition`, the formula
  `ChartRatioEvaluation`, and compactness of `ℙᴺ(ℂ)`.

Everything else that the argument needs is already proved:
`ComplexProjectiveSpace.holomorphicGenerates_anChartFrame` (the frames),
`ComplexProjectiveSpace.existsUnique_canonicalChartMultiplier` (the multipliers),
`ComplexProjectiveSpace.canonicalChartMultiplier_transition` (the cocycle),
`ComplexProjectiveSpace.analyticOnNhd_comp_chartPointIn` (chart expressions are entire) and
`Other.ProjectiveChart.existsUnique_isHomogeneous_of_chart_growth` (growth ⇒ unique form).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace Other.ProjectiveChart

open AlgebraicGeometry.ComplexProjectiveSpace AlgebraicGeometry.ComplexPoint

/-! ### The two rank-one obligations -/

/-- **Rank one, non-negative degree.**  For `b ≤ a`, every morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` on
`ℙᴺ` is the analytification of an algebraic morphism `𝒪(−a) ⟶ 𝒪(−b)`. -/
def TwistRankOneAlgebraizesNonneg (N : ℕ) : Prop :=
  ∀ a b : ℕ, b ≤ a → ∀ φ : analyticTwist N a ⟶ analyticTwist N b,
    ∃ g : ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) a ⟶
        ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b,
      (moduleAnalytification (projectiveSpaceOver N) N).map g = φ

/-- **Rank one, negative degree.**  For `a < b` there is no nonzero morphism
`𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ`.  (A chart multiplier would be a global holomorphic section of a
negative twist; by compactness and the maximum principle it vanishes.) -/
def TwistRankOneVanishesNeg (N : ℕ) : Prop :=
  ∀ a b : ℕ, a < b → ∀ φ : analyticTwist N a ⟶ analyticTwist N b, φ = 0

/-! ### Two intermediate obligations for the non-negative case -/

/-- **The chart formula for the transition unit.**  On the `i`-th homogeneous chart, in the
coordinates `z ↦ [insertNth i 1 z]`, the transition unit `analyticSpaceRatio N n i j` — the
evaluation of the regular function `Xⱼⁿ / Xᵢⁿ` — is the monomial `z ↦ (insertNth i 1 z j)ⁿ`. -/
def ChartRatioEvaluation (N n : ℕ) : Prop :=
  ∀ (i j : Fin (N + 1)) (z : Fin N → ℂ),
    ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ≠ 0 →
      Point.evaluate
          (projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
            projectiveSpaceBasicOpen N (MvPolynomial.X j))
          (ComplexProjectiveSpace.spaceRatio N n i j)
          (ComplexProjectiveSpace.projectivizationToComplexPoint
            (ComplexProjectiveSpace.chartPoint i z)) =
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ n

/-- A section of the holomorphic structure sheaf of `ℙᴺ(ℂ)^an`, read as a function. -/
def holSectionFun {N : ℕ} {V : Opens (TopCat.of (ComplexPoint (projectiveSpaceOver N)))}
    (h : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op V)) : V → ℂ :=
  ⇑(id (α := C^ω⟮𝓘(ℂ, Fin N → ℂ), (V : Opens (ComplexPoint (projectiveSpaceOver N))); ℂ⟯) h)

/-- **The growth bound.**  For `b ≤ a`, the chart expression of a chart multiplier of a morphism
`𝒪(−a)^an ⟶ 𝒪(−b)^an` has polynomial growth of order `a − b`. -/
def ChartMultiplierGrowth (N a b : ℕ) : Prop :=
  b ≤ a → ∀ (φ : analyticTwist N a ⟶ analyticTwist N b) (i : Fin (N + 1))
    (h : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i))),
    φ.val.app (op (chartOpen N i)) (anChartFrame N a i) = h • anChartFrame N b i →
      ∃ C : ℝ, ∀ z : Fin N → ℂ,
        ‖holSectionFun h (ComplexProjectiveSpace.chartPointIn N i z)‖ ≤
          C * (1 + ‖z‖) ^ (a - b)

/-! ### The reduction -/

attribute [local instance] CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts

local instance projModuleAnalytification_additive (N : ℕ) :
    (moduleAnalytification (projectiveSpaceOver N) N).Additive :=
  CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

/-- The rank-one case of the relation obligation on `ℙᴺ`, in the form consumed by
`ProjectiveTwist.analyticTwistRelationsAlgebraize_of_rankOne`. -/
theorem analyticTwistRelationsAlgebraizeRankOne_of_parts (N : ℕ)
    (hnonneg : TwistRankOneAlgebraizesNonneg N) (hneg : TwistRankOneVanishesNeg N) :
    ProjectiveTwist.AnalyticTwistRelationsAlgebraizeRankOne (projectiveSpaceOver N) N
      (projPresentation N) := by
  intro a b φ
  rcases le_or_gt b a with hba | hab
  · exact hnonneg a b hba φ
  · refine ⟨0, ?_⟩
    rw [hneg a b hab φ]
    exact CategoryTheory.Functor.map_zero _ _ _

/-- **The relation obligation on `ℙᴺ` from the two rank-one obligations.** -/
theorem twistRelationsAlgebraizeProj_of_parts (N : ℕ)
    (hnonneg : TwistRankOneAlgebraizesNonneg N) (hneg : TwistRankOneVanishesNeg N) :
    TwistRelationsAlgebraizeProj N :=
  ProjectiveTwist.analyticTwistRelationsAlgebraize_of_rankOne (projectiveSpaceOver N) N
    (projPresentation N) (analyticTwistRelationsAlgebraizeRankOne_of_parts N hnonneg hneg)

end Other.ProjectiveChart
