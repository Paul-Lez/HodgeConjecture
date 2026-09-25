/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartRatioEvaluation
public import Other.AlgebraicGeometry.ProjAwayEvaluation

/-!
# The chart-coordinate formula for homogeneous ratios on `ℙᴺ`

`HomogeneousRatioEvaluation N` is proved here: at the complex point with homogeneous coordinates
`v`, the regular function `G / Xᵢᵏ` on the `i`-th standard chart takes the value `G(v) / (vᵢ)ᵏ`.

The point `[v]` factors through the affine chart `Spec (A⁰_{Xᵢ}) ⟶ Proj ℤ[X]` by evaluation of
homogeneous coordinates (`chartIntegralProjAt`), and `Proj.awayι` factors through
`IsAffineOpen.fromSpec`, so the value is read off by applying `awayCoordinateEvaluation`
(`ProjAwayEvaluation.lean`).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N k : ℕ) (G : UniversalGrading N k) (i : Fin (N + 1))

/-- The element `G / Xᵢᵏ` of the degree-zero away localisation. -/
def awayElt : HomogeneousLocalization.Away (UniversalGrading N) (MvPolynomial.X i) :=
  HomogeneousLocalization.mk ⟨k, G, coordPower N k i, ⟨k, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The away element `G / Xᵢᵏ` in Mathlib's normal form. -/
theorem awayElt_eq_mk :
    awayElt N k G i =
      HomogeneousLocalization.Away.mk (UniversalGrading N)
        (MvPolynomial.isHomogeneous_X _ i) k (G : UniversalRing N)
        (by simpa only [smul_eq_mul, mul_one] using G.2) := by
  apply HomogeneousLocalization.val_injective
  rw [awayElt, HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
  rfl

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The regular function `G / Xᵢᵏ` is the section attached to the away element `G / Xᵢᵏ`. -/
theorem universalRatioBig_eq_awayToSection :
    universalRatioBig N k G i =
      Proj.awayToSection (UniversalGrading N) (MvPolynomial.X i) (awayElt N k G i) := by
  apply Subtype.ext
  funext x
  show HomogeneousLocalization.mk
      ⟨k, G, coordPower N k i, coordPower_notMem_basicOpen N k i x⟩ =
    HomogeneousLocalization.mapId (UniversalGrading N) (Submonoid.powers_le.mpr x.2)
      (awayElt N k G i)
  rw [awayElt, HomogeneousLocalization.map_mk]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The regular function `G / Xᵢᵏ` on `ℙᴺ` is the inverse image of the universal one. -/
theorem spaceRatioBig_eq_app :
    spaceRatioBig N k G i =
      (toUniversalProj N).app
        (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
          (Proj (UniversalGrading N)).Opens) (universalRatioBig N k G i) := rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The chart-coordinate formula for homogeneous ratios.** -/
theorem homogeneousRatioEvaluation (N : ℕ) : HomogeneousRatioEvaluation N := by
  intro k G i v hv hvi
  have hp : (vectorToComplexPoint v hv).left ≫ toUniversalProj N =
      Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hvi)) ≫
        Proj.awayι (UniversalGrading N) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X _ i) zero_lt_one := by
    have hleft : (vectorToComplexPoint v hv).left = vectorToProjectiveSpace v hv := rfl
    rw [hleft, toUniversalProj, vectorToProjectiveSpace_toProj,
      chartIntegralProj_eq_chartIntegralProjAt v hv i hvi]
    rfl
  have h := Proj.top_le_preimage_basicOpen_of_awayι (UniversalGrading N) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ i) zero_lt_one _ _ hp
  have step1 := ComplexPoint.evaluate_app_eq_appLE_top (X := Other.ProjectiveChart.projectiveSpaceOver N)
    (toUniversalProj N)
    (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
      (Proj (UniversalGrading N)).Opens)
    (universalRatioBig N k G i) (vectorToComplexPoint v hv) h
  rw [spaceRatioBig_eq_app]
  refine step1.trans ?_
  rw [universalRatioBig_eq_awayToSection]
  refine Eq.trans (Proj.ΓSpecIso_appLE_top_awayToSection (UniversalGrading N) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ i) zero_lt_one _ _ hp h (awayElt N k G i)) ?_
  rw [awayElt_eq_mk, CommRingCat.hom_ofHom,
    awayCoordinateEvaluation_mk v i hvi k (G : UniversalRing N) G.2,
    div_eq_mul_inv, inv_pow]

/-- **The transition-unit formula in every degree.** -/
theorem chartRatioEvaluation (N n : ℕ) : Other.ProjectiveChart.ChartRatioEvaluation N n :=
  chartRatioEvaluation_of_homogeneousRatioEvaluation N (homogeneousRatioEvaluation N) n

end AlgebraicGeometry.ComplexProjectiveSpace
