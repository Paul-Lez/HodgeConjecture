/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistRatioPower
public import Other.AlgebraicGeometry.PointEvaluationApp

/-!
# The chart-coordinate formula for homogeneous ratios

The regular functions on the `i`-th standard chart `D₊(Xᵢ)` of `ℙᴺ` that the twist calculus
produces are the inverse images of the homogeneous ratios `G / Xᵢᵏ`, for `G` homogeneous of
degree `k`.  Everything that remains of the chart dictionary for the relation obligation is the
single evaluation formula

```
G / Xᵢᵏ  at the point  [v]   =   G(v) / (vᵢ)ᵏ,
```

isolated here as `HomogeneousRatioEvaluation N`.  From it the transition-unit formula
`ChartRatioEvaluation N n` follows for every `n`
(`chartRatioEvaluation_of_homogeneousRatioEvaluation`), and the same formula computes the chart
multiplier of the algebraic morphism "multiplication by a degree-`(a − b)` form".
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N k : ℕ) (G : UniversalGrading N k) (i j : Fin (N + 1))

/-- The homogeneous element `Xᵢᵏ` does not vanish on `D₊(Xᵢ)`. -/
theorem coordPower_notMem_basicOpen
    (x : (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
      (Proj (UniversalGrading N)).Opens)) :
    ((coordPower N k i : UniversalRing N)) ∉ x.1.asHomogeneousIdeal :=
  basicOpen_le_pow N k (MvPolynomial.X i) x.2

/-- The regular function `G / Xᵢᵏ` on the `i`-th coordinate basic open of `Proj ℤ[X]`. -/
def universalRatioBig :
    Γ(Proj (UniversalGrading N),
      (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
        (Proj (UniversalGrading N)).Opens)) :=
  projRatio (UniversalGrading N) G (coordPower N k i) _ (coordPower_notMem_basicOpen N k i)

/-- The regular function `G / Xᵢᵏ` on the `i`-th standard chart of `ℙᴺ`. -/
def spaceRatioBig :
    Γ((Other.ProjectiveChart.projectiveSpaceOver N).left,
      projectiveSpaceBasicOpen N (MvPolynomial.X i)) :=
  Scheme.Modules.pullbackFunction (Other.ProjectiveChart.projPresentation N).immersion _
    (Scheme.Modules.pullbackFunction (toUniversalProj N) _ (universalRatioBig N k G i))

/-- **Obligation: the chart-coordinate formula for homogeneous ratios.**  At the complex point
with homogeneous coordinates `v`, the regular function `G / Xᵢᵏ` takes the value
`G(v) / (vᵢ)ᵏ`. -/
def HomogeneousRatioEvaluation (N : ℕ) : Prop :=
  ∀ (k : ℕ) (G : UniversalGrading N k) (i : Fin (N + 1)) (v : CoordinateSpace N) (hv : v ≠ 0),
    v i ≠ 0 →
    Point.evaluate (projectiveSpaceBasicOpen N (MvPolynomial.X i)) (spaceRatioBig N k G i)
        (vectorToComplexPoint v hv) =
      coordinateEvaluationHom v (G : UniversalRing N) / (v i) ^ k

/-! ### The transition unit is a homogeneous ratio -/

theorem universalRatio_one_eq_res :
    universalRatio N 1 i j =
      Scheme.Modules.resRing
        (inf_le_left : universalOverlap N i j ≤
          (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
            (Proj (UniversalGrading N)).Opens))
        (universalRatioBig N 1 (coordPower N 1 j) i) := by
  apply Subtype.ext
  funext x
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem spaceRatio_one_eq_res :
    spaceRatio N 1 i j =
      Scheme.Modules.resRing
        (inf_le_left : projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
          projectiveSpaceBasicOpen N (MvPolynomial.X j) ≤
            projectiveSpaceBasicOpen N (MvPolynomial.X i))
        (spaceRatioBig N 1 (coordPower N 1 j) i) := by
  rw [spaceRatio, universalRatio_one_eq_res, Scheme.Modules.pullbackFunction_res,
    Scheme.Modules.pullbackFunction_res]
  rfl

/-! ### The reduction of the transition-unit formula -/

set_option backward.isDefEq.respectTransparency false in
/-- **`HomogeneousRatioEvaluation` gives the degree-one transition-unit formula.** -/
theorem chartRatioEvaluation_one_of_homogeneousRatioEvaluation (N : ℕ)
    (h : HomogeneousRatioEvaluation N) : Other.ProjectiveChart.ChartRatioEvaluation N 1 := by
  intro i j z hz
  have hvi : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) i) = 1 := Fin.insertNth_apply_same _ _ _
  have hv : (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) ≠ 0 := insertNth_one_ne_zero i z
  have hvine : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) i) ≠ 0 := by rw [hvi]; exact one_ne_zero
  have hmem : projectivizationToComplexPoint (chartPoint i z) ∈
      Point.overOpen (projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
        projectiveSpaceBasicOpen N (MvPolynomial.X j)) :=
    ⟨chartPoint_mem_overOpen_self N i z, chartPoint_mem_overOpen_of_ne_zero N i j z hz⟩
  calc Point.evaluate
        (projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
          projectiveSpaceBasicOpen N (MvPolynomial.X j)) (spaceRatio N 1 i j)
        (projectivizationToComplexPoint (chartPoint i z))
      = Point.evaluate (projectiveSpaceBasicOpen N (MvPolynomial.X i))
          (spaceRatioBig N 1 (coordPower N 1 j) i)
          (projectivizationToComplexPoint (chartPoint i z)) := by
        rw [spaceRatio_one_eq_res]
        exact (Point.evaluate_res inf_le_left _ _ hmem).symm
    _ = coordinateEvaluationHom (i.insertNth (1 : ℂ) z)
          ((coordPower N 1 j : UniversalRing N)) /
        ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) i) ^ 1 :=
        h 1 (coordPower N 1 j) i _ hv hvine
    _ = ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ 1 := by
        rw [hvi, one_pow, div_one]
        show coordinateEvaluationHom (i.insertNth (1 : ℂ) z)
          ((MvPolynomial.X j : UniversalRing N) ^ 1) = _
        rw [map_pow, coordinateEvaluationHom_X]

/-- **`HomogeneousRatioEvaluation` gives the transition-unit formula in every degree.** -/
theorem chartRatioEvaluation_of_homogeneousRatioEvaluation (N : ℕ)
    (h : HomogeneousRatioEvaluation N) (n : ℕ) :
    Other.ProjectiveChart.ChartRatioEvaluation N n :=
  chartRatioEvaluation_of_one N (chartRatioEvaluation_one_of_homogeneousRatioEvaluation N h) n

end AlgebraicGeometry.ComplexProjectiveSpace
