import Other.AlgebraicGeometry.ExplicitEllipticCharts

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint ComplexProjectiveSpace

noncomputable section

set_option maxHeartbeats 600000

abbrev testCurveSpace : Over (Spec (CommRingCat.of ℂ)) := Over.mk curveToBase

abbrev testPlaneSpace : Over (Spec (CommRingCat.of ℂ)) :=
  Over.mk (ProjectiveSpace.toBase (Fin 3) base)

def testClosedMap : testCurveSpace ⟶ testPlaneSpace := Over.homMk curveToPlane rfl

instance : IsClosedImmersion testClosedMap.left :=
  inferInstanceAs (IsClosedImmersion curveToPlane)

lemma vectorToComplexPoint_proof_irrel {n : ℕ} (v : CoordinateSpace n)
    (h h' : v ≠ 0) : vectorToComplexPoint v h = vectorToComplexPoint v h' := by
  rw [Subsingleton.elim h h']

set_option backward.isDefEq.respectTransparency.types false in
lemma testClosedMap_curvePoint (P : Fin 3 → ℂ) (hP : P ≠ 0)
    (heq : equation.toProjective.Equation P) :
    Point.map testClosedMap (curvePoint P hP heq) = vectorToComplexPoint P hP := by
  simpa only [testClosedMap] using curvePoint_map_vectorToComplexPoint P hP heq

lemma continuous_curvePoint_family {T : Type*} [TopologicalSpace T]
    (P : T → Fin 3 → ℂ) (hP : ∀ t, P t ≠ 0)
    (heq : ∀ t, equation.toProjective.Equation (P t))
    (hcontinuous : Continuous P) :
    @Continuous T (ComplexPoint testCurveSpace) inferInstance Point.analyticTopology
      (fun t ↦ curvePoint (P t) (hP t) (heq t)) := by
  apply (@IsInducing.continuous_iff T (ComplexPoint testCurveSpace)
    (ComplexPoint testPlaneSpace) (fun t ↦ curvePoint (P t) (hP t) (heq t))
    (Point.map testClosedMap) Point.analyticTopology inferInstance Point.analyticTopology
    (isInducing_map_of_closedImmersion testClosedMap)).mpr
  rw [show (Point.map testClosedMap ∘ fun t ↦ curvePoint (P t) (hP t) (heq t)) =
      fun t ↦ vectorToComplexPoint (P t) (hP t) by
    funext t
    exact testClosedMap_curvePoint (P t) (hP t) (heq t)]
  change @Continuous T
    (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin 3) (Spec (CommRingCat.of ℂ)))))
    inferInstance Point.analyticTopology (fun t ↦ vectorToComplexPoint (P t) (hP t))
  have hv : Continuous (fun t ↦ (⟨P t, hP t⟩ : {v : Fin 3 → ℂ // v ≠ 0})) :=
    hcontinuous.subtype_mk hP
  have hc := continuous_vectorToComplexPoint.comp hv
  exact hc.congr fun t ↦ vectorToComplexPoint_proof_irrel _ _ _

def branchPointOne : ComplexPoint testCurveSpace :=
  curvePoint ![1, 0, 1]
    (by intro h; have := congrFun h 2; simp at this)
    (by simp [equation, WeierstrassCurve.Projective.equation_iff])

def branchPointZero : ComplexPoint testCurveSpace :=
  curvePoint ![0, 0, 1]
    (by intro h; have := congrFun h 2; simp at this)
    (by simp [equation, WeierstrassCurve.Projective.equation_iff])

def infinityToOneVector (t : Set.Icc (0 : ℝ) 1) : Fin 3 → ℂ :=
  ![(t.1 : ℂ), (Real.sqrt (1 - t.1 ^ 4) : ℂ), (t.1 ^ 3 : ℂ)]

lemma infinityToOneVector_ne_zero (t : Set.Icc (0 : ℝ) 1) :
    infinityToOneVector t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [infinityToOneVector] at h0 h1
  have hsqrt : Real.sqrt 1 = 0 := by simpa [h0] using h1
  norm_num at hsqrt

lemma infinityToOneVector_equation (t : Set.Icc (0 : ℝ) 1) :
    equation.toProjective.Equation (infinityToOneVector t) := by
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have ht4 : t.1 ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have hnonneg : 0 ≤ 1 - t.1 ^ 4 := sub_nonneg.mpr ht4
  have hsqrt : Real.sqrt (1 - t.1 ^ 4) ^ 2 = 1 - t.1 ^ 4 :=
    Real.sq_sqrt hnonneg
  simp [infinityToOneVector, equation,
    WeierstrassCurve.Projective.equation_iff]
  have hsqrtC : ((Real.sqrt (1 - t.1 ^ 4) : ℂ) ^ 2) =
      ((1 - t.1 ^ 4 : ℝ) : ℂ) := by exact_mod_cast hsqrt
  rw [hsqrtC]
  push_cast
  ring

def infinityToOnePath (t : Set.Icc (0 : ℝ) 1) : ComplexPoint testCurveSpace :=
  curvePoint (infinityToOneVector t)
    (infinityToOneVector_ne_zero t) (infinityToOneVector_equation t)

lemma continuous_infinityToOneVector : Continuous infinityToOneVector := by
  unfold infinityToOneVector
  fun_prop

lemma continuous_infinityToOnePath :
    @Continuous (Set.Icc (0 : ℝ) 1) (ComplexPoint testCurveSpace)
      inferInstance Point.analyticTopology infinityToOnePath :=
  continuous_curvePoint_family infinityToOneVector infinityToOneVector_ne_zero
    infinityToOneVector_equation continuous_infinityToOneVector

@[simp]
lemma infinityToOnePath_zero :
    infinityToOnePath ⟨0, by constructor <;> norm_num⟩ = infinity := by
  simp [infinityToOnePath, infinityToOneVector, infinity]

@[simp]
lemma infinityToOnePath_one :
    infinityToOnePath ⟨1, by constructor <;> norm_num⟩ = branchPointOne := by
  simp [infinityToOnePath, infinityToOneVector, branchPointOne]

def zeroToOneVector (s : Set.Icc (0 : ℝ) 1) : Fin 3 → ℂ :=
  ![(s.1 : ℂ), Complex.I * (Real.sqrt (s.1 - s.1 ^ 3) : ℂ), 1]

lemma zeroToOneVector_ne_zero (s : Set.Icc (0 : ℝ) 1) :
    zeroToOneVector s ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [zeroToOneVector] at h2

lemma zeroToOneVector_equation (s : Set.Icc (0 : ℝ) 1) :
    equation.toProjective.Equation (zeroToOneVector s) := by
  have hs0 : 0 ≤ s.1 := s.2.1
  have hs1 : s.1 ≤ 1 := s.2.2
  have hs2 : s.1 ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  have hnonneg : 0 ≤ s.1 - s.1 ^ 3 := by
    have hmul : 0 ≤ s.1 * (1 - s.1 ^ 2) :=
      mul_nonneg hs0 (sub_nonneg.mpr hs2)
    nlinarith
  have hsqrt : Real.sqrt (s.1 - s.1 ^ 3) ^ 2 = s.1 - s.1 ^ 3 :=
    Real.sq_sqrt hnonneg
  simp [zeroToOneVector, equation, WeierstrassCurve.Projective.equation_iff]
  have hsqrtC : ((Real.sqrt (s.1 - s.1 ^ 3) : ℂ) ^ 2) =
      ((s.1 - s.1 ^ 3 : ℝ) : ℂ) := by exact_mod_cast hsqrt
  rw [mul_pow, hsqrtC, Complex.I_sq]
  push_cast
  ring

def zeroToOnePath (s : Set.Icc (0 : ℝ) 1) : ComplexPoint testCurveSpace :=
  curvePoint (zeroToOneVector s)
    (zeroToOneVector_ne_zero s) (zeroToOneVector_equation s)

lemma continuous_zeroToOneVector : Continuous zeroToOneVector := by
  unfold zeroToOneVector
  fun_prop

lemma continuous_zeroToOnePath :
    @Continuous (Set.Icc (0 : ℝ) 1) (ComplexPoint testCurveSpace)
      inferInstance Point.analyticTopology zeroToOnePath :=
  continuous_curvePoint_family zeroToOneVector zeroToOneVector_ne_zero
    zeroToOneVector_equation continuous_zeroToOneVector

@[simp]
lemma zeroToOnePath_zero :
    zeroToOnePath ⟨0, by constructor <;> norm_num⟩ = branchPointZero := by
  simp [zeroToOnePath, zeroToOneVector, branchPointZero]

@[simp]
lemma zeroToOnePath_one :
    zeroToOnePath ⟨1, by constructor <;> norm_num⟩ = branchPointOne := by
  simp [zeroToOnePath, zeroToOneVector, branchPointOne]

theorem branchPointOne_mem_connectedComponent_infinity :
    branchPointOne ∈ connectedComponent infinity := by
  have hc : IsConnected (Set.range infinityToOnePath) :=
    isConnected_range continuous_infinityToOnePath
  exact hc.subset_connectedComponent
    ⟨⟨0, by constructor <;> norm_num⟩, infinityToOnePath_zero⟩
    ⟨⟨1, by constructor <;> norm_num⟩, infinityToOnePath_one⟩

theorem branchPointZero_mem_connectedComponent_branchPointOne :
    branchPointZero ∈ connectedComponent branchPointOne := by
  have hc : IsConnected (Set.range zeroToOnePath) :=
    isConnected_range continuous_zeroToOnePath
  exact hc.subset_connectedComponent
    ⟨⟨1, by constructor <;> norm_num⟩, zeroToOnePath_one⟩
    ⟨⟨0, by constructor <;> norm_num⟩, zeroToOnePath_zero⟩

theorem branchPointZero_mem_connectedComponent_infinity :
    branchPointZero ∈ connectedComponent infinity := by
  rw [connectedComponent_eq branchPointOne_mem_connectedComponent_infinity]
  exact branchPointZero_mem_connectedComponent_branchPointOne

def curvePointToTop (x : ComplexPoint testCurveSpace) :
    (⊤ : Opens (TopCat.of (ComplexPoint testCurveSpace))) := ⟨x, trivial⟩

lemma continuous_curvePointToTop : Continuous curvePointToTop :=
  continuous_id.subtype_mk _

theorem branchPointZeroTop_mem_connectedComponent_infinityTop :
    curvePointToTop branchPointZero ∈ connectedComponent (curvePointToTop infinity) :=
  continuous_curvePointToTop.mapsTo_connectedComponent infinity
    branchPointZero_mem_connectedComponent_infinity

end

end AlgebraicGeometry.ExplicitEllipticCandidate
