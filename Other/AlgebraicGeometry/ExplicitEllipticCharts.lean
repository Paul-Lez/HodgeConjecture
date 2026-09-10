/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCandidate
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff

/-!
# Affine charts of the explicit projective cubic

The two standard charts `Y ≠ 0` and `Z ≠ 0` cover the actual cubic scheme. This file
also constructs its complex points directly from homogeneous solutions of the cubic equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open ComplexProjectiveSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The composite map from the cubic into the integral projective plane. -/
def curveToIntegerPlane : curve ⟶ integerPlane := curveToPlane ≫ planeToIntegerPlane

/-- The standard affine open on the cubic on which the indicated homogeneous coordinate
is nonzero. -/
def chart (i : Fin 3) : curve.Opens :=
  curveToIntegerPlane ⁻¹ᵁ Proj.basicOpen (UniversalGrading 2) (X i)

instance : IsAffineHom planeToIntegerPlane := by
  have : IsAffine base := inferInstanceAs (IsAffine (Spec (CommRingCat.of ℂ)))
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have : IsAffine (⊤_ Scheme) :=
    (IsAffine.iff_of_isIso (terminal.from (Spec (CommRingCat.of (ULift ℤ))))).1 inferInstance
  exact MorphismProperty.pullback_snd (terminal.from base) (terminal.from integerPlane)
    (inferInstanceAs (IsAffineHom (terminal.from base)))

instance : IsAffineHom curveToIntegerPlane := by
  exact inferInstanceAs (IsAffineHom (curveToPlane ≫ planeToIntegerPlane))

/-- Each of the standard coordinate opens is affine as an open of the actual cubic scheme. -/
theorem chart_isAffineOpen (i : Fin 3) : IsAffineOpen (chart i) := by
  exact (Proj.isAffineOpen_basicOpen (UniversalGrading 2) (X i)
    (isHomogeneous_X _ i) zero_lt_one).preimage curveToIntegerPlane

/-- The defining cubic belongs to the homogeneous prime of every point of the cubic scheme. -/
theorem cubic_mem_point (x : curve) :
    cubic ∈ (curveToIntegerPlane x).asHomogeneousIdeal := by
  have hx : curveToPlane x ∈ (cubicIdeal.support : Set plane) := by
    rw [← cubicIdeal.range_subschemeι]
    exact ⟨x, rfl⟩
  have hx' : curveToPlane x ∈ (cubicLocus : Set plane) := by
    simpa only [cubicIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hx
  exact hx' (Set.mem_singleton cubic)

/-- On this cubic, the `Y` and `Z` charts already cover the whole scheme. -/
theorem chart_one_sup_chart_two : chart 1 ⊔ chart 2 = ⊤ := by
  apply top_unique
  intro x _
  change X 1 ∉ (curveToIntegerPlane x).asHomogeneousIdeal ∨
    X 2 ∉ (curveToIntegerPlane x).asHomogeneousIdeal
  by_contra h
  push Not at h
  let p := curveToIntegerPlane x
  let I : Ideal (UniversalRing 2) := p.asHomogeneousIdeal.toIdeal
  have hY : X 1 ∈ I := h.1
  have hZ : X 2 ∈ I := h.2
  have hc : X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2 ∈ I := cubic_mem_point x
  have hY2Z : X 1 ^ 2 * X 2 ∈ I := I.mul_mem_left _ hZ
  have hXZ2 : X 0 * X 2 ^ 2 ∈ I :=
    I.mul_mem_left _ (Ideal.pow_mem_of_mem I hZ 2 (by decide))
  have hX3 : X 0 ^ 3 ∈ I := by
    convert I.sub_mem (I.add_mem hY2Z hXZ2) hc using 1
    ring
  have hX : X 0 ∈ I := p.isPrime.mem_of_pow_mem 3 hX3
  apply p.not_irrelevant_le
  apply (irrelevant_le_span_coordinates 2).trans
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hX
  · exact hY
  · exact hZ

/-- Homogeneous coordinates define a complex point of the ambient scheme-theoretic plane. -/
def homogeneousPlanePoint (P : Fin 3 → ℂ) (hP : P ≠ 0) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin 3) base)) :=
  vectorToComplexPoint P hP

@[reassoc]
theorem homogeneousPlanePoint_toChartIntegralProj (P : Fin 3 → ℂ) (hP : P ≠ 0) :
    (homogeneousPlanePoint P hP).left ≫ planeToIntegerPlane = chartIntegralProj P hP := by
  exact vectorToProjectiveSpace_toProj P hP

/-- Evaluating the integral cubic in complex coordinates gives the displayed Weierstrass
equation. -/
theorem coordinateEvaluationHom_cubic (P : Fin 3 → ℂ) :
    coordinateEvaluationHom P cubic = eval P equation.toProjective.polynomial := by
  simp [cubic, equation, WeierstrassCurve.Projective.eval_polynomial]
  ring

/-- The constructed plane point belongs to the actual cubic locus exactly when its coordinates
satisfy the Weierstrass equation. -/
theorem homogeneousPlanePoint_mem_cubicLocus_iff (P : Fin 3 → ℂ) (hP : P ≠ 0) :
    (homogeneousPlanePoint P hP).underlying ∈ (cubicLocus : Set plane) ↔
      equation.toProjective.Equation P := by
  classical
  change planeToIntegerPlane ((homogeneousPlanePoint P hP).left (IsLocalRing.closedPoint ℂ)) ∈
    ProjectiveSpectrum.zeroLocus (UniversalGrading 2) {cubic} ↔ _
  change ((homogeneousPlanePoint P hP).left ≫ planeToIntegerPlane)
    (IsLocalRing.closedPoint ℂ) ∈ ProjectiveSpectrum.zeroLocus (UniversalGrading 2) {cubic} ↔ _
  rw [homogeneousPlanePoint_toChartIntegralProj]
  change ({cubic} : Set (UniversalRing 2)) ⊆
    (chartIntegralProj P hP (IsLocalRing.closedPoint ℂ)).asHomogeneousIdeal ↔ _
  rw [Set.singleton_subset_iff]
  rw [← not_iff_not]
  change IsLocalRing.closedPoint ℂ ∈
    chartIntegralProj P hP ⁻¹ᵁ Proj.basicOpen (UniversalGrading 2) cubic ↔ _
  rw [chartIntegralProj_preimage_basicOpen P hP cubic (by decide : 0 < 3) cubic_homogeneous]
  rw [coordinateEvaluationHom_cubic]
  change IsLocalRing.closedPoint ℂ ∈
    (if equation.toProjective.Equation P then ⊥ else ⊤) ↔ _
  split_ifs <;> simp_all

/-- Every nonzero homogeneous solution gives an actual complex point of the cubic scheme. -/
theorem exists_curvePoint_of_equation (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) :
    ∃ z : ComplexPoint (Over.mk curveToBase),
      Point.map (Over.homMk curveToPlane rfl) z = homogeneousPlanePoint P hP := by
  let i : Over.mk curveToBase ⟶ Over.mk (ProjectiveSpace.toBase (Fin 3) base) :=
    Over.homMk curveToPlane rfl
  let : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion curveToPlane)
  change homogeneousPlanePoint P hP ∈ Set.range (Point.map i)
  erw [ComplexPoint.range_map_of_closedImmersion i]
  change (homogeneousPlanePoint P hP).underlying ∈ Set.range curveToPlane
  change (homogeneousPlanePoint P hP).underlying ∈ Set.range cubicIdeal.subschemeι
  rw [cubicIdeal.range_subschemeι, cubicIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (homogeneousPlanePoint_mem_cubicLocus_iff P hP).2 heq

/-- An actual complex point of the cubic, obtained from the given homogeneous coordinates. -/
def curvePoint (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) : ComplexPoint (Over.mk curveToBase) :=
  (exists_curvePoint_of_equation P hP heq).choose

@[simp]
theorem curvePoint_map (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) :
    Point.map (Over.homMk curveToPlane rfl) (curvePoint P hP heq) = homogeneousPlanePoint P hP :=
  (exists_curvePoint_of_equation P hP heq).choose_spec

/-- Under the projective embedding, the point constructed from homogeneous coordinates is the
analytic coordinate point used by `ProjectiveAnalytification`. -/
@[simp]
theorem curvePoint_map_vectorToComplexPoint (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) :
    Point.map (Over.homMk curveToPlane rfl) (curvePoint P hP heq) =
      vectorToComplexPoint P hP := by
  rw [curvePoint_map]
  unfold homogeneousPlanePoint
  congr

/-- Membership in the actual affine chart is detected by the corresponding homogeneous
coordinate. -/
theorem curvePoint_mem_chart_iff (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) (i : Fin 3) :
    (curvePoint P hP heq).underlying ∈ chart i ↔ P i ≠ 0 := by
  have hmap := congrArg Point.underlying (curvePoint_map P hP heq)
  simp only [Point.underlying_map, Over.homMk_left] at hmap
  change curveToPlane (curvePoint P hP heq).underlying ∈
    planeToIntegerPlane ⁻¹ᵁ Proj.basicOpen (UniversalGrading 2) (X i) ↔ _
  erw [hmap]
  change IsLocalRing.closedPoint ℂ ∈
    ((homogeneousPlanePoint P hP).left ≫ planeToIntegerPlane) ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading 2) (X i) ↔ _
  rw [homogeneousPlanePoint_toChartIntegralProj,
    chartIntegralProj_preimage_basicOpen P hP (X i) zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i), coordinateEvaluationHom_X]
  split_ifs <;> simp_all

/-- The point at infinity `[0:1:0]`, as a point of the actual cubic scheme. -/
def infinity : ComplexPoint (Over.mk curveToBase) :=
  curvePoint ![0, 1, 0]
    (by intro h; have := congrFun h 1; simp at this)
    WeierstrassCurve.Projective.equation_zero

instance : Nonempty (ComplexPoint (Over.mk curveToBase)) := ⟨infinity⟩

instance : Nonempty curve := ⟨infinity.underlying⟩

/-- The complex point `[i:1-i:1]` lies in both affine charts. -/
def overlapPoint : ComplexPoint (Over.mk curveToBase) :=
  curvePoint ![Complex.I, 1 - Complex.I, 1]
    (by intro h; have := congrFun h 2; simp at this)
    (by
      simp [equation, WeierstrassCurve.Projective.equation_iff]
      ring_nf
      simp [Complex.I_sq])

/-- The two displayed affine opens have a nonempty intersection in the actual scheme. -/
theorem chart_inter_nonempty : ((chart 1 ⊓ chart 2 : curve.Opens) : Set curve).Nonempty := by
  refine ⟨overlapPoint.underlying, ?_, ?_⟩
  · apply (curvePoint_mem_chart_iff _ _ _ 1).2
    intro h
    have := congrArg Complex.re h
    norm_num at this
  · apply (curvePoint_mem_chart_iff _ _ _ 2).2
    exact one_ne_zero

end AlgebraicGeometry.ExplicitEllipticCandidate
