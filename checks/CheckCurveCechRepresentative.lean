import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
import Other.AlgebraicGeometry.ExplicitEllipticInfinityCoordinates
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

#check Point.evaluate_res
#check Point.evaluationHom
#check Point.evaluationHom_apply
#check Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
#check regularToHolomorphicAlgHom

theorem check_curveCMOverlap_eq :
    curveCMOverlap = curveZOpen ⊓ curveYOpen := by
  exact curveZOverlapCoordinate_basicOpen

theorem check_regularAnalyticOpen_curveCMOverlap :
    regularAnalyticOpen curveVariety curveCMOverlap = curveCechOverlap := by
  rw [check_curveCMOverlap_eq]
  rfl

/-- The standard algebraic Cech representative `x²/y = x²v` on the overlap. -/
def check_curveCechRegularRepresentative : Γ(curve, curveCMOverlap) :=
  curveCMOverlapZX ^ 2 * curveCMOverlapYV

theorem check_curveCechRegularRepresentative_cm :
    curveYCMOverlapRingEnd check_curveCechRegularRepresentative =
      -(Complex.I • check_curveCechRegularRepresentative) := by
  simp only [check_curveCechRegularRepresentative, map_mul, map_pow,
    curveYCMOverlapRingEnd_ZX, curveYCMOverlapRingEnd_YV]
  simp [Algebra.smul_def]
  ring

theorem check_overlapPoint_mem_curveCMOverlap :
    overlapPoint.underlying ∈ curveCMOverlap := by
  rw [check_curveCMOverlap_eq]
  constructor
  · exact (curvePoint_mem_chart_iff _ _ _ 2).2 one_ne_zero
  · apply (curvePoint_mem_chart_iff _ _ _ 1).2
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem check_overlapPoint_mem_overOpen_curveCMOverlap :
    overlapPoint ∈ Point.overOpen curveCMOverlap := by
  exact check_overlapPoint_mem_curveCMOverlap

theorem check_evaluate_curveCMOverlapZX_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap curveCMOverlapZX overlapPoint ≠ 0 := by
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    curveCMOverlapZX overlapPoint
      check_overlapPoint_mem_overOpen_curveCMOverlap]
  rw [curveCMOverlapZX, curveSectionRestriction_coordinate,
    ProjectiveRatioSections.basicOpen_pullRatio]
  exact ⟨check_overlapPoint_mem_curveCMOverlap,
    (curvePoint_mem_chart_iff _ _ _ 0).2 Complex.I_ne_zero⟩

theorem check_evaluate_curveCMOverlapYV_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap curveCMOverlapYV overlapPoint ≠ 0 := by
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    curveCMOverlapYV overlapPoint
      check_overlapPoint_mem_overOpen_curveCMOverlap]
  rw [curveCMOverlapYV, curveSectionRestriction_coordinate,
    ProjectiveRatioSections.basicOpen_pullRatio]
  exact ⟨check_overlapPoint_mem_curveCMOverlap,
    (curvePoint_mem_chart_iff _ _ _ 2).2 one_ne_zero⟩

theorem check_curveCechRegularRepresentative_ne_zero :
    check_curveCechRegularRepresentative ≠ 0 := by
  intro h
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩
  have he := congrArg
    (fun s : Γ(curve, curveCMOverlap) => ev s) h
  change ev (curveCMOverlapZX ^ 2 * curveCMOverlapYV) = ev 0 at he
  simp only [map_mul, map_pow, map_zero] at he
  have hx : ev curveCMOverlapZX ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapZX ≠ 0
    rw [Point.evaluationHom_apply]
    exact check_evaluate_curveCMOverlapZX_overlapPoint_ne_zero
  have hv : ev curveCMOverlapYV ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapYV ≠ 0
    rw [Point.evaluationHom_apply]
    exact check_evaluate_curveCMOverlapYV_overlapPoint_ne_zero
  exact mul_ne_zero (pow_ne_zero 2 hx) hv he

theorem check_evaluate_curveCechRegularRepresentative_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap check_curveCechRegularRepresentative overlapPoint ≠ 0 := by
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩
  have hx : ev curveCMOverlapZX ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapZX ≠ 0
    rw [Point.evaluationHom_apply]
    exact check_evaluate_curveCMOverlapZX_overlapPoint_ne_zero
  have hv : ev curveCMOverlapYV ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapYV ≠ 0
    rw [Point.evaluationHom_apply]
    exact check_evaluate_curveCMOverlapYV_overlapPoint_ne_zero
  rw [← Point.evaluationHom_apply (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩
    check_curveCechRegularRepresentative]
  change ev check_curveCechRegularRepresentative ≠ 0
  change ev (curveCMOverlapZX ^ 2 * curveCMOverlapYV) ≠ 0
  rw [map_mul, map_pow]
  exact mul_ne_zero (pow_ne_zero 2 hx) hv

/-- The regular representative as a holomorphic function before identifying overlap opens. -/
def check_curveCMOverlapHolomorphicRepresentative :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) :=
  regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
    check_curveCechRegularRepresentative

theorem check_curveCMOverlapHolomorphicRepresentative_ne_zero :
    check_curveCMOverlapHolomorphicRepresentative ≠ 0 := by
  intro h
  have he := congrArg (fun f => f.1
    ⟨overlapPoint, check_overlapPoint_mem_overOpen_curveCMOverlap⟩) h
  change Point.evaluate curveCMOverlap check_curveCechRegularRepresentative overlapPoint = 0 at he
  exact check_evaluate_curveCechRegularRepresentative_overlapPoint_ne_zero he

/-- Transport holomorphic functions across the equality of the two descriptions of the overlap. -/
def check_curveCechOpenFunctionAddEquiv :
    OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveCMOverlap)) ≃+
      OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) := by
  rw [check_regularAnalyticOpen_curveCMOverlap]

/-- The actual holomorphic overlap function obtained from `x²/y`. -/
def check_curveCechRepresentative :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) := by
  exact check_curveCechOpenFunctionAddEquiv
    check_curveCMOverlapHolomorphicRepresentative

theorem check_curveCechRepresentative_ne_zero :
    check_curveCechRepresentative ≠ 0 := by
  intro h
  apply check_curveCMOverlapHolomorphicRepresentative_ne_zero
  apply check_curveCechOpenFunctionAddEquiv.injective
  change check_curveCechOpenFunctionAddEquiv
      check_curveCMOverlapHolomorphicRepresentative = 0 at h
  exact h.trans check_curveCechOpenFunctionAddEquiv.map_zero.symm

end
end AlgebraicGeometry.ExplicitEllipticCandidate
