/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistCanonicalFrames
public import Other.AlgebraicGeometry.HolomorphicMultiplierTransition

/-!
# The chart cocycle of a morphism of analytic twists on `ℙᴺ`

With the canonical chart frames of `ProjectiveTwistCanonicalFrames.lean`, a morphism
`𝒪(−a)^an ⟶ 𝒪(−b)^an` on `ℙᴺ` is, on each standard homogeneous chart, multiplication by a
unique holomorphic function `hᵢ`, and on the overlap of two charts

```
hᵢ · (Xⱼ/Xᵢ)ᵇ = (Xⱼ/Xᵢ)ᵃ · hⱼ,
```

the transition units being the *evaluations of explicit regular functions*.  This is the
identity that produces the polynomial growth bound of degree `a − b` for the chart expression of
`hᵢ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

variable (N a b : ℕ) (i j : Fin (N + 1))

/-- The analytic twist `𝒪(−n)^an` on `ℙᴺ`, abbreviated. -/
abbrev analyticTwist (N n : ℕ) : SheafOfModules.{0}
    (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N) :=
  ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
    (Other.ProjectiveChart.projPresentation N) n

/-- **Chart multipliers for the canonical frames.**  A morphism of analytified twists on `ℙᴺ` is,
on each standard chart, multiplication by a unique holomorphic function. -/
theorem existsUnique_canonicalChartMultiplier
    (φ : analyticTwist N a ⟶ analyticTwist N b) :
    ∃! h : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
        (op (chartOpen N i)),
      φ.val.app (op (chartOpen N i)) (anChartFrame N a i) = h • anChartFrame N b i := by
  have hb := holomorphicGenerates_anChartFrame N b i
  obtain ⟨h, hh⟩ := hb.bijective.surjective
    (φ.val.app (op (chartOpen N i)) (anChartFrame N a i))
  refine ⟨h, hh.symm, fun h' hh' ↦ hb.bijective.injective ?_⟩
  exact hh'.symm.trans hh.symm

/-- The evaluation of the regular transition function `Xⱼⁿ/Xᵢⁿ` on the chart overlap. -/
def analyticSpaceRatio (N n : ℕ) (i j : Fin (N + 1)) :
    (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N i ⊓ chartOpen N j)) :=
  ComplexPoint.analyticFunction (Other.ProjectiveChart.projectiveSpaceOver N) N
    (projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
      projectiveSpaceBasicOpen N (MvPolynomial.X j)) (spaceRatio N n i j)

/-- The canonical frames of `𝒪(−n)^an` differ on the overlap by `analyticSpaceRatio`. -/
theorem analyticSpaceRatio_smul_anChartFrame (n : ℕ) :
    analyticSpaceRatio N n i j •
        ComplexPoint.holRes (analyticTwist N n)
          (inf_le_right : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N j) (anChartFrame N n j) =
      ComplexPoint.holRes (analyticTwist N n)
        (inf_le_left : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N i) (anChartFrame N n i) :=
  analyticFunction_spaceRatio_smul_anChartFrame N n i j

/-- **The chart cocycle.**  The chart multipliers of a morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` satisfy
`hᵢ · (Xⱼ/Xᵢ)ᵇ = (Xⱼ/Xᵢ)ᵃ · hⱼ` on the overlap of the `i`-th and `j`-th standard charts. -/
theorem canonicalChartMultiplier_transition
    (φ : analyticTwist N a ⟶ analyticTwist N b)
    {hi : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N i))}
    {hj : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N j))}
    (hhi : φ.val.app (op (chartOpen N i)) (anChartFrame N a i) = hi • anChartFrame N b i)
    (hhj : φ.val.app (op (chartOpen N j)) (anChartFrame N a j) = hj • anChartFrame N b j) :
    ComplexPoint.holRingRes
        (inf_le_left : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N i) hi *
        analyticSpaceRatio N b i j =
      analyticSpaceRatio N a i j *
        ComplexPoint.holRingRes
          (inf_le_right : chartOpen N i ⊓ chartOpen N j ≤ chartOpen N j) hj :=
  ComplexPoint.multiplier_transition φ inf_le_left inf_le_right
    (holomorphicGenerates_anChartFrame N b j)
    (analyticSpaceRatio_smul_anChartFrame N i j a)
    (analyticSpaceRatio_smul_anChartFrame N i j b) hhi hhj

end AlgebraicGeometry.ComplexProjectiveSpace
