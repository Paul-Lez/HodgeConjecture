/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumTwistDivide
public import Other.AlgebraicGeometry.ProjectiveTwistNonnegAlgebraize

/-!
# The zero-dimensional case

On `ℙ⁰` the single coordinate basic open is everything (`D₊(X₀) = ⊤`), so division by `X₀ᵏ` is a
*global* morphism of twists and all twists are trivial.  Hence the negative-degree obligation,
which is false in the vanishing form, holds in the algebraization form: `ℙ⁰(ℂ)` is a point and
every chart multiplier is a constant, realised by `divideShiftHom` followed by multiplication by
that constant.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On `Proj ℤ[X₀]` the coordinate basic open is everything. -/
theorem basicOpen_X_zero_eq_top :
    (ProjectiveSpectrum.basicOpen (UniversalGrading 0) (MvPolynomial.X 0) :
      (Proj (UniversalGrading 0)).Opens) = ⊤ := by
  refine top_unique fun x _ => ?_
  have h := iSup_coordinateBasicOpen_eq_top 0
  have hx : x ∈ (⊤ : (Proj (UniversalGrading 0)).Opens) := trivial
  rw [← h] at hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi0 : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
  rw [hi0] at hi
  exact hi

/-- `X₀ᵏ` vanishes nowhere on `Proj ℤ[X₀]`. -/
theorem coordPower_zero_notMem (k : ℕ) (x : ProjectiveSpectrum.top (UniversalGrading 0)) :
    ((coordPower 0 k 0 : UniversalGrading 0 k) : UniversalRing 0) ∉ x.asHomogeneousIdeal := by
  have hx : x ∈ (ProjectiveSpectrum.basicOpen (UniversalGrading 0) (MvPolynomial.X 0) :
      (Proj (UniversalGrading 0)).Opens) := by
    rw [basicOpen_X_zero_eq_top]
    trivial
  exact basicOpen_le_pow 0 k (MvPolynomial.X 0) hx

variable (a k : ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- Division by `X₀ᵏ` on the universal frames over `D₊(X₀)`. -/
theorem divideShiftHom_universalChartFrame :
    (schemeDivideShiftHom (UniversalGrading 0) (coordPower 0 k 0) a
          (coordPower_zero_notMem k)).app
        (ProjectiveSpectrum.basicOpen (UniversalGrading 0) (MvPolynomial.X 0) :
          (Proj (UniversalGrading 0)).Opens)
        (Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading 0) a)
          (basicOpen_le_pow 0 a (MvPolynomial.X 0)) (universalChartFrame 0 a 0)) =
      Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading 0) (a + k))
        (basicOpen_le_pow 0 (a + k) (MvPolynomial.X 0)) (universalChartFrame 0 (a + k) 0) := by
  refine divideShiftHom_projFrame (UniversalGrading 0) (coordPower 0 k 0) (coordPower 0 a 0)
    (coordPower 0 (a + k) 0) (coordPower_zero_notMem k) ?_ _ _ _
  show (MvPolynomial.X 0 : UniversalRing 0) ^ (a + k) =
    (MvPolynomial.X 0 : UniversalRing 0) ^ k * (MvPolynomial.X 0 : UniversalRing 0) ^ a
  rw [← pow_add]
  congr 1
  omega

/-- **Division by `X₀ᵏ`, transported to `ℙ⁰`.** -/
def algDivHom :
    ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver 0) (projPresentation 0) a ⟶
      ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver 0) (projPresentation 0)
        (a + k) :=
  (Scheme.Modules.pullback (projPresentation 0).immersion).map
    ((Scheme.Modules.pullback (toUniversalProj 0)).map
      (schemeDivideShiftHom (UniversalGrading 0) (coordPower 0 k 0) a (coordPower_zero_notMem k)))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The algebraic frame identity for `algDivHom`. -/
theorem algDivHom_algChartFrame :
    (algDivHom a k).app (projectiveSpaceBasicOpen 0 (MvPolynomial.X 0)) (algChartFrame 0 a 0) =
      algChartFrame 0 (a + k) 0 := by
  have h1 := congrArg
    (Scheme.Modules.pullbackSection (toUniversalProj 0)
      (schemeSheafOfModules (UniversalGrading 0) (a + k))
      (ProjectiveSpectrum.basicOpen (UniversalGrading 0) (MvPolynomial.X 0) :
        (Proj (UniversalGrading 0)).Opens))
    (divideShiftHom_universalChartFrame a k)
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.pullbackSection_res,
    Scheme.Modules.pullbackSection_res] at h1
  have h2 := congrArg
    (Scheme.Modules.pullbackSection (projPresentation 0).immersion
      ((Scheme.Modules.pullback (toUniversalProj 0)).obj
        (schemeSheafOfModules (UniversalGrading 0) (a + k)))
      (toUniversalProj 0 ⁻¹ᵁ (ProjectiveSpectrum.basicOpen (UniversalGrading 0)
        (MvPolynomial.X 0) : (Proj (UniversalGrading 0)).Opens)))
    h1
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.pullbackSection_res,
    Scheme.Modules.pullbackSection_res] at h2
  exact h2

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The analytic chart multiplier of `algDivHom` is `1`. -/
theorem analytified_algDivHom_anChartFrame :
    ((moduleAnalytification (projectiveSpaceOver 0) 0).map (algDivHom a k)).val.app
        (op (chartOpen 0 0)) (anChartFrame 0 a 0) = anChartFrame 0 (a + k) 0 := by
  have h := congrArg
    (ComplexPoint.analyticSection (projectiveSpaceOver 0) 0
      (ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver 0) (projPresentation 0)
        (a + k))
      (projectiveSpaceBasicOpen 0 (MvPolynomial.X 0)))
    (algDivHom_algChartFrame a k)
  rw [ComplexPoint.analyticSection_map] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The negative-degree obligation on `ℙ⁰`.** -/
theorem twistRankOneAlgebraizesNeg_zero :
    Other.ProjectiveChart.TwistRankOneAlgebraizesNeg 0 := by
  classical
  intro a b hab φ
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have hex : ∀ i : Fin (0 + 1), ∃ w,
      φ.val.app (op (chartOpen 0 i)) (anChartFrame 0 a i) = w • anChartFrame 0 (a + k) i :=
    fun i => (existsUnique_canonicalChartMultiplier 0 a (a + k) i φ).exists
  choose v hv using hex
  set c : ℂ := chartFun 0 0 (v 0) (fun _ => 0) with hc
  refine ⟨algDivHom a k ≫ constMulHom 0 (a + k) c, ?_⟩
  set g : analyticTwist 0 a ⟶ analyticTwist 0 (a + k) :=
    (moduleAnalytification (projectiveSpaceOver 0) 0).map
      (algDivHom a k ≫ constMulHom 0 (a + k) c) with hgdef
  have hgapp : ∀ i : Fin (0 + 1),
      g.val.app (op (chartOpen 0 i)) (anChartFrame 0 a i) =
        constAnalyticFun 0 i c • anChartFrame 0 (a + k) i := by
    intro i
    have hi0 : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi0
    rw [hgdef, (moduleAnalytification (projectiveSpaceOver 0) 0).map_comp]
    show ((moduleAnalytification (projectiveSpaceOver 0) 0).map
          (constMulHom 0 (a + k) c)).val.app (op (chartOpen 0 0))
        (((moduleAnalytification (projectiveSpaceOver 0) 0).map (algDivHom a k)).val.app
          (op (chartOpen 0 0)) (anChartFrame 0 a 0)) = _
    rw [analytified_algDivHom_anChartFrame, analytified_constMulHom_anChartFrame]
  have hdiff : φ - g = 0 := by
    refine hom_eq_zero_of_one_chart _ 0 (fun i => v i - constAnalyticFun 0 i c) ?_ ?_
    · intro i
      show φ.val.app (op (chartOpen 0 i)) (anChartFrame 0 a i) -
          g.val.app (op (chartOpen 0 i)) (anChartFrame 0 a i) = _
      rw [hv i, hgapp i, sub_smul]
    · intro z
      show chartFun 0 0 (v 0) z - chartFun 0 0 (constAnalyticFun 0 0 c) z = 0
      rw [chartFun_constAnalyticFun, hc, Subsingleton.elim z (fun _ => 0), sub_self]
  exact (sub_eq_zero.mp hdiff).symm

/-- **The negative-degree obligation, in every dimension.** -/
theorem twistRankOneAlgebraizesNeg (N : ℕ) :
    Other.ProjectiveChart.TwistRankOneAlgebraizesNeg N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact twistRankOneAlgebraizesNeg_zero
  · exact twistRankOneAlgebraizesNeg_of_pos hN

/-- **The relation obligation (iii) on `ℙᴺ`, for every `N`.** -/
theorem twistRelationsAlgebraizeProj (N : ℕ) :
    Other.ProjectiveChart.TwistRelationsAlgebraizeProj N :=
  Other.ProjectiveChart.twistRelationsAlgebraizeProj_of_parts N
    (twistRankOneAlgebraizesNonneg N) (twistRankOneAlgebraizesNeg N)

end AlgebraicGeometry.ComplexProjectiveSpace
