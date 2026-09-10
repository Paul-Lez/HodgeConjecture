/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCurveConnectivity
public import Other.AlgebraicGeometry.ExplicitEllipticSegre
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Connectedness of the explicit elliptic cubic

This file proves that the complex points of the cubic `Y²Z = X³ - XZ²` are connected.
The proof uses homogeneous coordinates, paths in the complement of the three branch values,
and path lifting for the squaring covering of `ℂ \ {0}`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint ComplexProjectiveSpace

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem curvePointProjectiveEmbedding_injective :
    Function.Injective (Point.map curvePointProjectiveEmbedding) := by
  intro z w h
  apply Over.OverMorphism.ext
  apply (cancel_mono curveToPlane).mp
  exact congrArg Over.Hom.left h

lemma vectorToComplexPoint_congr {n : ℕ} {v w : CoordinateSpace n}
    (hv : v ≠ 0) (hw : w ≠ 0) (h : v = w) :
    vectorToComplexPoint v hv = vectorToComplexPoint w hw := by
  subst w
  exact vectorToComplexPoint_proof_irrel v hv hw

lemma curvePoint_congr {P Q : Fin 3 → ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (heqP : equation.toProjective.Equation P)
    (heqQ : equation.toProjective.Equation Q) (h : P = Q) :
    curvePoint P hP heqP = curvePoint Q hQ heqQ := by
  apply curvePointProjectiveEmbedding_injective
  rw [curvePointProjectiveEmbedding_apply, curvePointProjectiveEmbedding_apply]
  exact vectorToComplexPoint_congr hP hQ h

/-- Every complex point of the cubic is represented by homogeneous coordinates satisfying the
displayed cubic equation. -/
theorem exists_homogeneous_coordinates (z : ComplexPoint curveComplexSpace) :
    ∃ (P : Fin 3 → ℂ) (hP : P ≠ 0) (heq : equation.toProjective.Equation P),
      z = curvePoint P hP heq := by
  obtain ⟨P, hP⟩ :=
    surjective_vectorToComplexPoint (Point.map curvePointProjectiveEmbedding z)
  have hP_underlying := congrArg Point.underlying hP
  change (vectorToComplexPoint P.1 P.2).underlying =
    curveToPlane z.underlying at hP_underlying
  have hmem : (vectorToComplexPoint P.1 P.2).underlying ∈ (cubicLocus : Set plane) := by
    rw [hP_underlying]
    have hz : curveToPlane z.underlying ∈ (cubicIdeal.support : Set plane) := by
      rw [← cubicIdeal.range_subschemeι]
      exact ⟨z.underlying, rfl⟩
    simpa only [cubicIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hz
  have heq : equation.toProjective.Equation P.1 :=
    (homogeneousPlanePoint_mem_cubicLocus_iff P.1 P.2).mp hmem
  refine ⟨P.1, P.2, heq, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono curveToPlane).mp
  have hm : Point.map curvePointProjectiveEmbedding z =
      Point.map curvePointProjectiveEmbedding (curvePoint P.1 P.2 heq) := by
    rw [curvePointProjectiveEmbedding_apply]
    exact hP.symm
  exact congrArg Over.Hom.left hm

/-- Every point is either the point at infinity or has affine coordinates satisfying
`y² = x³ - x`. -/
theorem eq_infinity_or_eq_affine (z : ComplexPoint curveComplexSpace) :
    z = infinity ∨
      ∃ (x y : ℂ) (heq : equation.toAffine.Equation x y),
        z = curvePoint ![x, y, 1]
          (by intro h; have := congrFun h 2; simp at this)
          ((WeierstrassCurve.Projective.equation_some x y).2 heq) := by
  obtain ⟨P, hP, heq, rfl⟩ := exists_homogeneous_coordinates z
  by_cases hZ : P 2 = 0
  · left
    have hX : P 0 = 0 :=
      WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero heq hZ
    have hY : P 1 ≠ 0 := by
      intro hY
      apply hP
      funext i
      fin_cases i <;> simp_all
    apply curvePointProjectiveEmbedding_injective
    rw [curvePointProjectiveEmbedding_apply]
    unfold infinity
    rw [curvePointProjectiveEmbedding_apply]
    have hvec : P = P 1 • ![0, 1, 0] := by
      funext i
      fin_cases i <;> simp [hX, hZ]
    let hN : (![0, 1, 0] : Fin 3 → ℂ) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    exact (vectorToComplexPoint_congr hP (smul_ne_zero hY hN) hvec).trans
      ((vectorToComplexPoint_smul ![0, 1, 0] hN (P 1) hY).trans
        (vectorToComplexPoint_proof_irrel _ _ _))
  · right
    let x : ℂ := P 0 / P 2
    let y : ℂ := P 1 / P 2
    have hAff : equation.toAffine.Equation x y :=
      (WeierstrassCurve.Projective.equation_of_Z_ne_zero hZ).mp heq
    refine ⟨x, y, hAff, ?_⟩
    apply curvePointProjectiveEmbedding_injective
    rw [curvePointProjectiveEmbedding_apply, curvePointProjectiveEmbedding_apply]
    have hN : (![x, y, 1] : Fin 3 → ℂ) ≠ 0 := by
      intro h
      have := congrFun h 2
      simp at this
    have hvec : P 2 • ![x, y, 1] = P := by
      funext i
      fin_cases i <;> simp [x, y] <;> field_simp
    have hs := vectorToComplexPoint_smul ![x, y, 1] hN (P 2) hZ
    exact (vectorToComplexPoint_congr hP (smul_ne_zero hZ hN) hvec.symm).trans hs

/-- The branch point `[-1:0:1]`. -/
def branchPointMinusOne : ComplexPoint curveComplexSpace :=
  curvePoint ![-1, 0, 1]
    (by intro h; have := congrFun h 2; simp at this)
    (by simp [equation, WeierstrassCurve.Projective.equation_iff]; ring)

/-- The second lift of the real interval from `x = 0` to `x = 1`. -/
def negativeZeroToOneVector (s : Set.Icc (0 : ℝ) 1) : Fin 3 → ℂ :=
  ![(s.1 : ℂ), -(Complex.I * (Real.sqrt (s.1 - s.1 ^ 3) : ℂ)), 1]

lemma negativeZeroToOneVector_ne_zero (s : Set.Icc (0 : ℝ) 1) :
    negativeZeroToOneVector s ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [negativeZeroToOneVector] at h2

lemma negativeZeroToOneVector_equation (s : Set.Icc (0 : ℝ) 1) :
    equation.toProjective.Equation (negativeZeroToOneVector s) := by
  have h := zeroToOneVector_equation s
  simpa [negativeZeroToOneVector, zeroToOneVector, equation,
    WeierstrassCurve.Projective.equation_iff] using h

def negativeZeroToOnePath (s : Set.Icc (0 : ℝ) 1) :
    ComplexPoint curveComplexSpace :=
  curvePoint (negativeZeroToOneVector s)
    (negativeZeroToOneVector_ne_zero s) (negativeZeroToOneVector_equation s)

lemma continuous_negativeZeroToOnePath :
    @Continuous (Set.Icc (0 : ℝ) 1) (ComplexPoint curveComplexSpace)
      inferInstance Point.analyticTopology negativeZeroToOnePath := by
  apply continuous_curvePoint_family negativeZeroToOneVector
    negativeZeroToOneVector_ne_zero negativeZeroToOneVector_equation
  unfold negativeZeroToOneVector
  fun_prop

@[simp] lemma negativeZeroToOnePath_zero :
    negativeZeroToOnePath ⟨0, by constructor <;> norm_num⟩ = branchPointZero := by
  simp [negativeZeroToOnePath, negativeZeroToOneVector, branchPointZero]

/-- A path in the negative real half of the cubic, from `x = -1` to `x = 0`. -/
def minusOneToZeroVector (s : Set.Icc (0 : ℝ) 1) : Fin 3 → ℂ :=
  ![-(s.1 : ℂ), (Real.sqrt (s.1 - s.1 ^ 3) : ℂ), 1]

lemma minusOneToZeroVector_ne_zero (s : Set.Icc (0 : ℝ) 1) :
    minusOneToZeroVector s ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [minusOneToZeroVector] at h2

lemma minusOneToZeroVector_equation (s : Set.Icc (0 : ℝ) 1) :
    equation.toProjective.Equation (minusOneToZeroVector s) := by
  have hs0 : 0 ≤ s.1 := s.2.1
  have hs1 : s.1 ≤ 1 := s.2.2
  have hs2 : s.1 ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  have hnonneg : 0 ≤ s.1 - s.1 ^ 3 := by
    have hmul : 0 ≤ s.1 * (1 - s.1 ^ 2) :=
      mul_nonneg hs0 (sub_nonneg.mpr hs2)
    nlinarith
  have hsqrt : Real.sqrt (s.1 - s.1 ^ 3) ^ 2 = s.1 - s.1 ^ 3 :=
    Real.sq_sqrt hnonneg
  simp [minusOneToZeroVector, equation, WeierstrassCurve.Projective.equation_iff]
  have hsqrtC : ((Real.sqrt (s.1 - s.1 ^ 3) : ℂ) ^ 2) =
      ((s.1 - s.1 ^ 3 : ℝ) : ℂ) := by exact_mod_cast hsqrt
  rw [hsqrtC]
  push_cast
  ring

def minusOneToZeroPath (s : Set.Icc (0 : ℝ) 1) :
    ComplexPoint curveComplexSpace :=
  curvePoint (minusOneToZeroVector s)
    (minusOneToZeroVector_ne_zero s) (minusOneToZeroVector_equation s)

lemma continuous_minusOneToZeroPath :
    @Continuous (Set.Icc (0 : ℝ) 1) (ComplexPoint curveComplexSpace)
      inferInstance Point.analyticTopology minusOneToZeroPath := by
  apply continuous_curvePoint_family minusOneToZeroVector
    minusOneToZeroVector_ne_zero minusOneToZeroVector_equation
  unfold minusOneToZeroVector
  fun_prop

@[simp] lemma minusOneToZeroPath_zero :
    minusOneToZeroPath ⟨0, by constructor <;> norm_num⟩ = branchPointZero := by
  simp [minusOneToZeroPath, minusOneToZeroVector, branchPointZero]

@[simp] lemma minusOneToZeroPath_one :
    minusOneToZeroPath ⟨1, by constructor <;> norm_num⟩ = branchPointMinusOne := by
  simp [minusOneToZeroPath, minusOneToZeroVector, branchPointMinusOne]

theorem branchPointMinusOne_mem_connectedComponent_infinity :
    branchPointMinusOne ∈ connectedComponent infinity := by
  have hc : IsConnected (Set.range minusOneToZeroPath) :=
    isConnected_range continuous_minusOneToZeroPath
  have hminus : branchPointMinusOne ∈ connectedComponent branchPointZero :=
    hc.subset_connectedComponent
      ⟨⟨0, by constructor <;> norm_num⟩, minusOneToZeroPath_zero⟩
      ⟨⟨1, by constructor <;> norm_num⟩, minusOneToZeroPath_one⟩
  rw [connectedComponent_eq branchPointZero_mem_connectedComponent_infinity]
  exact hminus

def cubicRightHandSide (x : ℂ) : ℂ := x ^ 3 - x

def curveBranchValues : Set ℂ := {-1, 0, 1}

lemma cubicRightHandSide_eq_zero_iff (x : ℂ) :
    cubicRightHandSide x = 0 ↔ x ∈ curveBranchValues := by
  change x ^ 3 - x = 0 ↔ x = -1 ∨ x = 0 ∨ x = 1
  constructor
  · intro h
    have hfac : (x + 1) * x * (x - 1) = 0 := by
      calc
        (x + 1) * x * (x - 1) = x ^ 3 - x := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfac with hfac | hfac
    · rcases mul_eq_zero.mp hfac with hx | hx
      · left
        linear_combination hx
      · exact Or.inr (Or.inl hx)
    · right; right
      linear_combination hfac
  · rintro (rfl | rfl | rfl) <;> norm_num

lemma cubicRightHandSide_ne_zero_iff (x : ℂ) :
    cubicRightHandSide x ≠ 0 ↔ x ∈ curveBranchValuesᶜ := by
  rw [Set.mem_compl_iff, ← not_congr (cubicRightHandSide_eq_zero_iff x)]

lemma curveBranchValues_countable : curveBranchValues.Countable := by
  simp [curveBranchValues]

lemma curveBranchValues_compl_isPathConnected :
    IsPathConnected curveBranchValuesᶜ := by
  apply curveBranchValues_countable.isPathConnected_compl_of_one_lt_rank
  rw [Complex.rank_real_complex]
  norm_num

def curveHalf : ℂ := (1 : ℂ) / 2

def curveHalfInterval : Set.Icc (0 : ℝ) 1 :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

def curveHalfPositiveY : ℂ :=
  Complex.I * (Real.sqrt ((3 : ℝ) / 8) : ℂ)

lemma curveHalf_not_branch : curveHalf ∈ curveBranchValuesᶜ := by
  rw [← cubicRightHandSide_ne_zero_iff]
  norm_num [curveHalf, cubicRightHandSide]

lemma curveHalfPositiveY_sq :
    curveHalfPositiveY ^ 2 = cubicRightHandSide curveHalf := by
  have hsqrt : Real.sqrt ((3 : ℝ) / 8) ^ 2 = (3 : ℝ) / 8 :=
    Real.sq_sqrt (by norm_num)
  simp only [curveHalfPositiveY, mul_pow, Complex.I_sq]
  rw [show ((Real.sqrt ((3 : ℝ) / 8) : ℂ) ^ 2) = ((3 : ℝ) / 8 : ℂ) by
    exact_mod_cast hsqrt]
  norm_num [curveHalf, cubicRightHandSide]

lemma zeroToOneVector_curveHalfInterval :
    zeroToOneVector curveHalfInterval = ![curveHalf, curveHalfPositiveY, 1] := by
  funext i
  fin_cases i <;> simp [zeroToOneVector, curveHalfInterval, curveHalf,
    curveHalfPositiveY] <;> congr 2 <;> norm_num

lemma negativeZeroToOneVector_curveHalfInterval :
    negativeZeroToOneVector curveHalfInterval = ![curveHalf, -curveHalfPositiveY, 1] := by
  funext i
  fin_cases i <;> simp [negativeZeroToOneVector, curveHalfInterval, curveHalf,
    curveHalfPositiveY] <;> congr 2 <;> norm_num

theorem zeroToOnePath_mem_connectedComponent_infinity (s : Set.Icc (0 : ℝ) 1) :
    zeroToOnePath s ∈ connectedComponent infinity := by
  have hc : IsConnected (Set.range zeroToOnePath) :=
    isConnected_range continuous_zeroToOnePath
  have hs : zeroToOnePath s ∈ connectedComponent branchPointZero :=
    hc.subset_connectedComponent
      ⟨⟨0, by constructor <;> norm_num⟩, zeroToOnePath_zero⟩ ⟨s, rfl⟩
  rw [connectedComponent_eq branchPointZero_mem_connectedComponent_infinity]
  exact hs

theorem negativeZeroToOnePath_mem_connectedComponent_infinity
    (s : Set.Icc (0 : ℝ) 1) :
    negativeZeroToOnePath s ∈ connectedComponent infinity := by
  have hc : IsConnected (Set.range negativeZeroToOnePath) :=
    isConnected_range continuous_negativeZeroToOnePath
  have hs : negativeZeroToOnePath s ∈ connectedComponent branchPointZero :=
    hc.subset_connectedComponent
      ⟨⟨0, by constructor <;> norm_num⟩, negativeZeroToOnePath_zero⟩ ⟨s, rfl⟩
  rw [connectedComponent_eq branchPointZero_mem_connectedComponent_infinity]
  exact hs

lemma affineEquation_iff_sq (x y : ℂ) :
    equation.toAffine.Equation x y ↔ y ^ 2 = cubicRightHandSide x := by
  simpa [equation, WeierstrassCurve.Affine.equation_iff, cubicRightHandSide,
    sub_eq_add_neg]

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}
abbrev NonbranchComplex := {z : ℂ // z ∉ curveBranchValues}

def cubicRightHandSideOnNonbranch : NonbranchComplex → NonzeroComplex :=
  fun x ↦ ⟨cubicRightHandSide x.1,
    (cubicRightHandSide_ne_zero_iff x.1).2 x.2⟩

lemma continuous_cubicRightHandSideOnNonbranch :
    Continuous cubicRightHandSideOnNonbranch := by
  apply Continuous.subtype_mk
  change Continuous (fun x : NonbranchComplex ↦ x.1 ^ 3 - x.1)
  fun_prop

def squareNonzeroComplex (z : NonzeroComplex) : NonzeroComplex :=
  ⟨z.1 ^ 2, pow_ne_zero 2 z.2⟩

lemma isCoveringMap_squareNonzeroComplex :
    IsCoveringMap squareNonzeroComplex := by
  exact isCoveringMap_npow 2 (by norm_num : (2 : ℂ) ≠ 0)

theorem affineBranchPoint_mem_connectedComponent_infinity
    (x y : ℂ) (heq : equation.toAffine.Equation x y) (hy : y = 0) :
    curvePoint ![x, y, 1]
        (by intro h; have := congrFun h 2; simp at this)
        ((WeierstrassCurve.Projective.equation_some x y).2 heq) ∈
      connectedComponent infinity := by
  have hrs : cubicRightHandSide x = 0 := by
    rw [← (affineEquation_iff_sq x y).mp heq, hy]
    norm_num
  have hx := (cubicRightHandSide_eq_zero_iff x).mp hrs
  change x = -1 ∨ x = 0 ∨ x = 1 at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [hy, branchPointMinusOne] using
      branchPointMinusOne_mem_connectedComponent_infinity
  · simpa only [hy, branchPointZero] using
      branchPointZero_mem_connectedComponent_infinity
  · simpa only [hy, branchPointOne] using
      branchPointOne_mem_connectedComponent_infinity

theorem affineNonbranchPoint_mem_connectedComponent_infinity
    (x y : ℂ) (heq : equation.toAffine.Equation x y) (hy : y ≠ 0) :
    curvePoint ![x, y, 1]
        (by intro h; have := congrFun h 2; simp at this)
        ((WeierstrassCurve.Projective.equation_some x y).2 heq) ∈
      connectedComponent infinity := by
  have hy_sq : y ^ 2 = cubicRightHandSide x :=
    (affineEquation_iff_sq x y).mp heq
  have hrs : cubicRightHandSide x ≠ 0 := by
    rw [← hy_sq]
    exact pow_ne_zero 2 hy
  have hx : x ∉ curveBranchValues :=
    (cubicRightHandSide_ne_zero_iff x).mp hrs
  have hjoined : JoinedIn curveBranchValuesᶜ x curveHalf :=
    curveBranchValues_compl_isPathConnected.joinedIn x hx curveHalf curveHalf_not_branch
  let basePath : Path (⟨x, hx⟩ : NonbranchComplex)
      (⟨curveHalf, curveHalf_not_branch⟩ : NonbranchComplex) :=
    hjoined.joined_subtype.somePath
  let rhsPath : Path
      (cubicRightHandSideOnNonbranch ⟨x, hx⟩)
      (cubicRightHandSideOnNonbranch ⟨curveHalf, curveHalf_not_branch⟩) :=
    basePath.map continuous_cubicRightHandSideOnNonbranch
  have hsource : rhsPath 0 = squareNonzeroComplex ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa [cubicRightHandSideOnNonbranch, squareNonzeroComplex] using hy_sq.symm
  let liftedY : C(Set.Icc (0 : ℝ) 1, NonzeroComplex) :=
    isCoveringMap_squareNonzeroComplex.liftPath rhsPath ⟨y, hy⟩ hsource
  have hlift (t : Set.Icc (0 : ℝ) 1) :
      (liftedY t).1 ^ 2 = cubicRightHandSide (basePath t).1 := by
    have h := congrFun
      (isCoveringMap_squareNonzeroComplex.liftPath_lifts rhsPath ⟨y, hy⟩ hsource) t
    have h' := congrArg Subtype.val h
    change (liftedY t).1 ^ 2 = cubicRightHandSide (basePath t).1 at h'
    exact h'
  let P : Set.Icc (0 : ℝ) 1 → Fin 3 → ℂ :=
    fun t ↦ ![(basePath t).1, (liftedY t).1, 1]
  have hP (t : Set.Icc (0 : ℝ) 1) : P t ≠ 0 := by
    intro h
    have := congrFun h 2
    simp [P] at this
  have hPeq (t : Set.Icc (0 : ℝ) 1) :
      equation.toProjective.Equation (P t) := by
    apply (WeierstrassCurve.Projective.equation_some _ _).2
    apply (affineEquation_iff_sq _ _).2
    exact hlift t
  let curveLiftPath (t : Set.Icc (0 : ℝ) 1) : ComplexPoint curveComplexSpace :=
    curvePoint (P t) (hP t) (hPeq t)
  have hcontinuous :
      @Continuous (Set.Icc (0 : ℝ) 1) (ComplexPoint curveComplexSpace)
        inferInstance Point.analyticTopology curveLiftPath := by
    apply continuous_curvePoint_family P hP hPeq
    unfold P
    fun_prop
  have hstart : curveLiftPath ⟨0, by constructor <;> norm_num⟩ =
      curvePoint ![x, y, 1]
        (by intro h; have := congrFun h 2; simp at this)
        ((WeierstrassCurve.Projective.equation_some x y).2 heq) := by
    apply curvePoint_congr
    funext i
    fin_cases i
    · change (basePath 0).1 = x
      exact congrArg Subtype.val basePath.source
    · have hzero := isCoveringMap_squareNonzeroComplex.liftPath_zero
          rhsPath ⟨y, hy⟩ hsource
      have hzero' := congrArg Subtype.val hzero
      change (liftedY 0).1 = y
      exact hzero'
    · rfl
  have hend_sq : (liftedY ⟨1, by constructor <;> norm_num⟩).1 ^ 2 =
      curveHalfPositiveY ^ 2 := by
    calc
      (liftedY ⟨1, by constructor <;> norm_num⟩).1 ^ 2 =
          cubicRightHandSide curveHalf := by simpa using hlift ⟨1, by constructor <;> norm_num⟩
      _ = curveHalfPositiveY ^ 2 := curveHalfPositiveY_sq.symm
  have hend_cases :
      (liftedY ⟨1, by constructor <;> norm_num⟩).1 = curveHalfPositiveY ∨
        (liftedY ⟨1, by constructor <;> norm_num⟩).1 = -curveHalfPositiveY :=
    eq_or_eq_neg_of_sq_eq_sq _ _ hend_sq
  have hend_mem : curveLiftPath ⟨1, by constructor <;> norm_num⟩ ∈
      connectedComponent infinity := by
    rcases hend_cases with hend | hend
    · have hvec : P ⟨1, by constructor <;> norm_num⟩ =
          zeroToOneVector curveHalfInterval := by
        rw [zeroToOneVector_curveHalfInterval]
        funext i
        fin_cases i
        · change (basePath 1).1 = curveHalf
          exact congrArg Subtype.val basePath.target
        · change (liftedY ⟨1, by constructor <;> norm_num⟩).1 = curveHalfPositiveY
          exact hend
        · rfl
      have hpoint : curveLiftPath ⟨1, by constructor <;> norm_num⟩ =
          zeroToOnePath curveHalfInterval := by
        apply curvePoint_congr
        exact hvec
      rw [hpoint]
      exact zeroToOnePath_mem_connectedComponent_infinity curveHalfInterval
    · have hvec : P ⟨1, by constructor <;> norm_num⟩ =
          negativeZeroToOneVector curveHalfInterval := by
        rw [negativeZeroToOneVector_curveHalfInterval]
        funext i
        fin_cases i
        · change (basePath 1).1 = curveHalf
          exact congrArg Subtype.val basePath.target
        · change (liftedY ⟨1, by constructor <;> norm_num⟩).1 = -curveHalfPositiveY
          exact hend
        · rfl
      have hpoint : curveLiftPath ⟨1, by constructor <;> norm_num⟩ =
          negativeZeroToOnePath curveHalfInterval := by
        apply curvePoint_congr
        exact hvec
      rw [hpoint]
      exact negativeZeroToOnePath_mem_connectedComponent_infinity curveHalfInterval
  have hc : IsConnected (Set.range curveLiftPath) :=
    isConnected_range hcontinuous
  have hsource_mem :
      curvePoint ![x, y, 1]
          (by intro h; have := congrFun h 2; simp at this)
          ((WeierstrassCurve.Projective.equation_some x y).2 heq) ∈
        connectedComponent (curveLiftPath ⟨1, by constructor <;> norm_num⟩) :=
    hc.subset_connectedComponent
      ⟨⟨1, by constructor <;> norm_num⟩, rfl⟩
      ⟨⟨0, by constructor <;> norm_num⟩, hstart⟩
  rw [← connectedComponent_eq hend_mem] at hsource_mem
  exact hsource_mem

theorem affinePoint_mem_connectedComponent_infinity
    (x y : ℂ) (heq : equation.toAffine.Equation x y) :
    curvePoint ![x, y, 1]
        (by intro h; have := congrFun h 2; simp at this)
        ((WeierstrassCurve.Projective.equation_some x y).2 heq) ∈
      connectedComponent infinity := by
  by_cases hy : y = 0
  · exact affineBranchPoint_mem_connectedComponent_infinity x y heq hy
  · exact affineNonbranchPoint_mem_connectedComponent_infinity x y heq hy

/-- Every complex point of the cubic belongs to the component of the point at infinity. -/
theorem mem_connectedComponent_infinity (z : ComplexPoint curveComplexSpace) :
    z ∈ connectedComponent infinity := by
  rcases eq_infinity_or_eq_affine z with h | ⟨x, y, heq, h⟩
  · rw [h]
    exact mem_connectedComponent
  · rw [h]
    exact affinePoint_mem_connectedComponent_infinity x y heq

theorem connectedComponent_infinity_eq_univ :
    connectedComponent infinity = Set.univ := by
  exact Set.eq_univ_of_forall mem_connectedComponent_infinity

/-- The analytification of the explicit elliptic cubic is connected. -/
noncomputable instance curveComplexPointConnectedSpace :
    ConnectedSpace (ComplexPoint curveComplexSpace) := by
  rw [connectedSpace_iff_connectedComponent]
  exact ⟨infinity, connectedComponent_infinity_eq_univ⟩

noncomputable instance curveVarietyComplexPointConnectedSpace :
    ConnectedSpace (ComplexPoint curveVariety) := by
  change ConnectedSpace (ComplexPoint curveComplexSpace)
  exact curveComplexPointConnectedSpace

end AlgebraicGeometry.ExplicitEllipticCandidate
