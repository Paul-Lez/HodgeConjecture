/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistRelationObligations

/-!
# The transition units are powers of the degree-one one

The transition unit `Xⱼⁿ / Xᵢⁿ` of the canonical chart frames of `𝒪(−n)` is the `n`-th power of
the degree-one transition unit `Xⱼ / Xᵢ`, at every stage of the construction: as a regular
function on `Proj ℤ[X]`, on `ℙᴺ`, and after analytification.  Consequently the chart-coordinate
formula `ChartRatioEvaluation N n` follows from its degree-one case
(`chartRatioEvaluation_of_one`), which is the only evaluation that has to be computed by hand.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.NegativeTwist

set_option backward.isDefEq.respectTransparency.types false in
/-- The homogeneous ratio of the `m`-th powers is the `m`-th power of the homogeneous ratio. -/
theorem homogeneousRatio_pow {k l m : ℕ} (num den : 𝒜 k) (num' den' : 𝒜 l)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h : ∀ x : U, (den : A) ∉ x.1.asHomogeneousIdeal)
    (h' : ∀ x : U, (den' : A) ∉ x.1.asHomogeneousIdeal)
    (hn : (num' : A) = (num : A) ^ m) (hd : (den' : A) = (den : A) ^ m) :
    homogeneousRatio 𝒜 num' den' U h' = (homogeneousRatio 𝒜 num den U h) ^ m := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  have hx : ((homogeneousRatio 𝒜 num den U h) ^ m).1 x =
      ((homogeneousRatio 𝒜 num den U h).1 x) ^ m := rfl
  rw [homogeneousRatio_val, hx, HomogeneousLocalization.val_pow, homogeneousRatio_val,
    Localization.mk_pow, hn,
    show ProjectiveSpectrum.ambientDenominator 𝒜 x.1 den' (h' x) =
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 den (h x)) ^ m from
      Subtype.ext (by simpa [ProjectiveSpectrum.ambientDenominator] using hd)]

end ProjectiveSpectrum.NegativeTwist

namespace ComplexProjectiveSpace

open ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N n : ℕ) (i j : Fin (N + 1))

/-- The universal transition unit in degree `n` is the `n`-th power of the degree-one one. -/
theorem universalRatio_pow :
    universalRatio N n i j = (universalRatio N 1 i j) ^ n := by
  refine homogeneousRatio_pow (UniversalGrading N) (coordPower N 1 j) (coordPower N 1 i)
    (coordPower N n j) (coordPower N n i) _ _ _ ?_ ?_
  · show (MvPolynomial.X j : UniversalRing N) ^ n = ((MvPolynomial.X j : UniversalRing N) ^ 1) ^ n
    rw [pow_one]
  · show (MvPolynomial.X i : UniversalRing N) ^ n = ((MvPolynomial.X i : UniversalRing N) ^ 1) ^ n
    rw [pow_one]

set_option backward.isDefEq.respectTransparency false in
/-- The transition unit on `ℙᴺ` in degree `n` is the `n`-th power of the degree-one one. -/
theorem spaceRatio_pow : spaceRatio N n i j = (spaceRatio N 1 i j) ^ n := by
  rw [spaceRatio, spaceRatio, universalRatio_pow, Scheme.Modules.pullbackFunction_pow,
    Scheme.Modules.pullbackFunction_pow]

end ComplexProjectiveSpace

namespace ComplexPoint

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- Analytification of regular functions preserves powers. -/
lemma analyticFunction_pow (U : X.left.Opens) (r : Γ(X.left, U)) (m : ℕ) :
    analyticFunction X d U (r ^ m) = analyticFunction X d U r ^ m :=
  map_pow ((regularToHolomorphicRingSheaf X d).hom.app (op U)).hom r m

end ComplexPoint

namespace ComplexProjectiveSpace

open ComplexPoint

variable (N n : ℕ) (i j : Fin (N + 1))

/-- The analytic transition unit in degree `n` is the `n`-th power of the degree-one one. -/
theorem analyticSpaceRatio_pow :
    analyticSpaceRatio N n i j = (analyticSpaceRatio N 1 i j) ^ n := by
  rw [analyticSpaceRatio, analyticSpaceRatio, spaceRatio_pow, ComplexPoint.analyticFunction_pow]
  rfl

/-! ### Reduction of the chart formula to degree one -/

/-- The chart point `[insertNth i 1 z]` lies over the `i`-th coordinate basic open. -/
theorem chartPoint_mem_overOpen_self (z : Fin N → ℂ) :
    projectivizationToComplexPoint (chartPoint i z) ∈
      Point.overOpen (projectiveSpaceBasicOpen N (MvPolynomial.X i)) := by
  rw [chartPoint, projectivizationToComplexPoint_mk]
  refine (vectorToComplexPoint_mem_projectiveSpaceBasicOpen_iff _ _ _ Nat.one_pos
    (MvPolynomial.isHomogeneous_X _ i)).mpr ?_
  rw [coordinateEvaluationHom_X]
  simp

/-- The chart point `[insertNth i 1 z]` lies over the `j`-th coordinate basic open exactly when
its `j`-th homogeneous coordinate is nonzero. -/
theorem chartPoint_mem_overOpen_of_ne_zero (z : Fin N → ℂ)
    (hz : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ≠ 0) :
    projectivizationToComplexPoint (chartPoint i z) ∈
      Point.overOpen (projectiveSpaceBasicOpen N (MvPolynomial.X j)) := by
  rw [chartPoint, projectivizationToComplexPoint_mk]
  refine (vectorToComplexPoint_mem_projectiveSpaceBasicOpen_iff _ _ _ Nat.one_pos
    (MvPolynomial.isHomogeneous_X _ j)).mpr ?_
  rw [coordinateEvaluationHom_X]
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- **The chart formula in degree `n` follows from the one in degree one.** -/
theorem chartRatioEvaluation_of_one (N : ℕ)
    (h1 : Other.ProjectiveChart.ChartRatioEvaluation N 1) (n : ℕ) :
    Other.ProjectiveChart.ChartRatioEvaluation N n := by
  intro i j z hz
  set U : (Other.ProjectiveChart.projectiveSpaceOver N).left.Opens :=
    projectiveSpaceBasicOpen N (MvPolynomial.X i) ⊓
      projectiveSpaceBasicOpen N (MvPolynomial.X j) with hU
  set pt := projectivizationToComplexPoint (chartPoint i z) with hpt
  have hmem : pt ∈ Point.overOpen U :=
    ⟨chartPoint_mem_overOpen_self N i z, chartPoint_mem_overOpen_of_ne_zero N i j z hz⟩
  calc Point.evaluate U (spaceRatio N n i j) pt
      = Point.evaluate U ((spaceRatio N 1 i j) ^ n) pt := by rw [spaceRatio_pow]
    _ = (Point.evaluationHom U ⟨pt, hmem⟩).hom ((spaceRatio N 1 i j) ^ n) :=
        (Point.evaluationHom_hom_apply U ⟨pt, hmem⟩ _).symm
    _ = ((Point.evaluationHom U ⟨pt, hmem⟩).hom (spaceRatio N 1 i j)) ^ n := map_pow _ _ _
    _ = (Point.evaluate U (spaceRatio N 1 i j) pt) ^ n := by
        rw [Point.evaluationHom_hom_apply]
    _ = (((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ 1) ^ n := by rw [h1 i j z hz]
    _ = ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) j) ^ n := by rw [pow_one]

end ComplexProjectiveSpace

end AlgebraicGeometry
