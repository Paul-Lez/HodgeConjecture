import Other.AlgebraicGeometry.ExplicitEllipticBranchDivision

#check ContinuousLinearEquiv.funUnique
#check ContinuousLinearEquiv.funUnique_apply
#check ContinuousLinearEquiv.funUnique_symm_apply
#check Complex.isROrC
#check AnalyticAt.comp
#check AnalyticAt.cl
#check AnalyticAt.continuousAt
#check ContDiffAt.analyticAt
#check analyticAt_iff_eventually
#check ContMDiff.contDiff
#check ContMDiffOn.div
#check ContMDiff.div
#check ContMDiffAt.div
#check contMDiff_of_locally_contMDiffOn
#check ContMDiffAt.contMDiffOn
#check ContMDiffAt.contMDiffWithinAt
#check ContMDiffMap
#check TopCat.Sheaf.existsUnique_gluing'
#check ContinuousLinearMap.analytic
#check ContinuousLinearMap.analyticAt
#check ContinuousLinearEquiv.analytic
#check ContinuousLinearEquiv.analyticAt
#check AnalyticAt.exists_mem_nhds_analyticOnNhd
#check AnalyticAt.exists_ball_analyticOnNhd
#check AnalyticAt.div
#check AnalyticAt.inv
#check AnalyticOnNhd.comp
#check AnalyticOnNhd.div
#check IsOpen.isOpenMap_subtype_val
#check LocalHomeomorph.injOn
#check LocalHomeomorph.injOn_source
#check LocalHomeomorph.left_inv
#check LocalHomeomorph.eq_iff_eq
#check ContMDiffMap.ext
#check AlgebraicGeometry.ComplexPoint.chartSection_holomorphicSectionOfChart
#check AlgebraicGeometry.ComplexPoint.chartSection_apply_of_mem
#check AlgebraicGeometry.ComplexPoint.holomorphicRestrictionAlgHom
#check fderiv_comp
#check HasFDerivAt.comp
#check Metric.mem_nhds_iff
#check Metric.ball_subset_ball
#check Metric.mem_ball
#check min_pos
#check AnalyticAt.eventually_ne
#check mem_nhds_iff
#check mem_nhds_iff_exists_mem_nhds_inter
#check Filter.Eventually.exists_mem
#check Metric.isOpen_ball
#check IsOpen.mem_nhds
#check AlgebraicGeometry.ComplexPoint.curveOneForm_coefficient_ne_zero
#check AlgebraicGeometry.ComplexPoint.regularKaehlerFormEvaluation_D_apply
#check AlgebraicGeometry.ComplexPoint.chartSectionDifferential_regularToHolomorphic
#print AlgebraicGeometry.ExplicitEllipticCandidate.curveZOpen
#reduce AlgebraicGeometry.ExplicitEllipticCandidate.curveZOpen

open AlgebraicGeometry AlgebraicGeometry.ExplicitEllipticCandidate
example : curveZOpen = chart 2 := rfl

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.Point
example (z : ComplexPoint (Over.mk curveToBase))
    (hz : z.underlying ∈ curveZOpen) :
    regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) curveZOpen z hz
      curveZDifferentialCM ≠ 0 := by
  rw [curveZDifferentialCM_eq_curveZDifferential]
  convert curveZDifferential_evaluation_ne_zero z
      (show z.underlying ∈ chart 2 by simpa only [show curveZOpen = chart 2 from rfl] using hz) using 1 <;>
    unfold regularKaehlerFormEvaluation <;> rfl
