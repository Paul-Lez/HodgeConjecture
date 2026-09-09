/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RegularHolomorphicForms
public import Other.Algebra.DeRham.KaehlerWedge
import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare

import all Mathlib.Data.Complex.Basic

/-!
# Analytic detection of regular differentials

On a positive-dimensional smooth affine neighborhood, the derivatives of regular functions
cannot all vanish. Local fractions express the algebraically constructed analytic coordinate
functions in terms of regular functions on the affine neighborhood.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Topology Filter
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance (priority := 10000) regularDerivativeComplexAddCommGroup : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
local instance (priority := 10000) regularDerivativeComplexModule : Module ℂ ℂ := (inferInstance : NormedSpace ℂ ℂ).toModule
local instance (priority := 10000) regularDerivativePiAddCommGroup : AddCommGroup (Fin d → ℂ) :=
  (inferInstance : NormedAddCommGroup (Fin d → ℂ)).toAddCommGroup
local instance (priority := 10000) regularDerivativePiModule : Module ℂ (Fin d → ℂ) :=
  (inferInstance : NormedSpace ℂ (Fin d → ℂ)).toModule
local instance (priority := 10000) regularDerivativePiTopology : TopologicalSpace (Fin d → ℂ) :=
  (inferInstance : PseudoMetricSpace (Fin d → ℂ)).toUniformSpace.toTopologicalSpace

/-- A regular section written in the canonical analytic chart at a complex point. -/
def regularInLocalChart (U : X.left.Opens) (s : Γ(X.left, U)) (z : ComplexPoint X) :
    (Fin d → ℂ) → ℂ :=
  fun v => Point.evaluate U s ((localChart X d z).symm v)

theorem analyticAt_regularInLocalChart (U : X.left.Opens) (s : Γ(X.left, U))
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) :
    AnalyticAt ℂ (regularInLocalChart X d U s z) (localChart X d z z) := by
  apply analyticAt_localChart_symm_evaluate X d z
    ((localChart X d z).map_source (mem_localChart_source X d z)) U s
  rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
  exact hz

theorem regularInLocalChart_add (U : X.left.Opens) (s t : Γ(X.left, U))
    (z : ComplexPoint X) :
    regularInLocalChart X d U (s + t) z =
      fun v => regularInLocalChart X d U s z v + regularInLocalChart X d U t z v := by
  funext v
  by_cases hv : ((localChart X d z).symm v).underlying ∈ U
  · simp only [regularInLocalChart, Point.evaluate, dif_pos hv, map_add]
  · simp only [regularInLocalChart, Point.evaluate, dif_neg hv, zero_add]

theorem regularInLocalChart_mul (U : X.left.Opens) (s t : Γ(X.left, U))
    (z : ComplexPoint X) :
    regularInLocalChart X d U (s * t) z =
      fun v => regularInLocalChart X d U s z v * regularInLocalChart X d U t z v := by
  funext v
  by_cases hv : ((localChart X d z).symm v).underlying ∈ U
  · simp only [regularInLocalChart, Point.evaluate, dif_pos hv, map_mul]
  · simp only [regularInLocalChart, Point.evaluate, dif_neg hv, zero_mul]

theorem regularInLocalChart_scalar_eventually (U : X.left.Opens) (c : ℂ)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) :
    regularInLocalChart X d U (regularSectionScalar X U c) z =ᶠ[
      𝓝 (localChart X d z z)] (fun _ => c) := by
  have htarget := (localChart X d z).map_source (mem_localChart_source X d z)
  have hmem : ∀ᶠ v in 𝓝 (localChart X d z z),
      (localChart X d z).symm v ∈ Point.overOpen U := by
    apply (localChart X d z).continuousAt_symm htarget
      ((Point.isOpen_overOpen U).mem_nhds _)
    rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
    exact hz
  filter_upwards [hmem] with v hv
  exact evaluate_regularSectionScalar X U c ((localChart X d z).symm v) hv

/-- An affine neighborhood of a smooth point of positive dimension has a regular function
whose actual analytic differential at that point is nonzero. -/
theorem exists_regularInLocalChart_fderiv_ne_zero (U : X.left.Opens) (hU : IsAffineOpen U)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) (hd : 0 < d) :
    ∃ s : Γ(X.left, U), fderiv ℂ (regularInLocalChart X d U s z)
      (localChart X d z z) ≠ 0 := by
  by_contra! hzero
  let D := localEtaleCoordinates X d z
  let e := localChart X d z
  let w := e z
  let j : Fin d := ⟨0, hd⟩
  have hzsource : z ∈ e.source := mem_localChart_source X d z
  have hztarget : w ∈ e.target := e.map_source hzsource
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using mem_localEtaleCoordinates X d z
  obtain ⟨f, hfD, hzf⟩ := hU.exists_basicOpen_le ⟨z.underlying, hzD⟩ hz
  let t := X.left.presheaf.map (homOfLE hfD).op (D.ambientCoordinateSection j)
  obtain ⟨k, a, ha⟩ := Point.exists_evaluate_basicOpen_eq_div (X := X) hU f t
  have hnonzero : regularInLocalChart X d U f z w ≠ 0 := by
    change Point.evaluate U f (e.symm (e z)) ≠ 0
    rw [e.left_inv hzsource]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f z hz).mp hzf
  have hderiv (s : Γ(X.left, U)) :
      HasFDerivAt (regularInLocalChart X d U s z) (0 : (Fin d → ℂ) →L[ℂ] ℂ) w := by
    simpa only [hzero s] using
      (analyticAt_regularInLocalChart X d U s z hz).differentiableAt.hasFDerivAt
  have hquotient : HasFDerivAt
      (fun v => regularInLocalChart X d U a z v / regularInLocalChart X d U f z v ^ k)
      (0 : (Fin d → ℂ) →L[ℂ] ℂ) w := by
    have hinv : HasFDerivAt (fun v => (regularInLocalChart X d U f z v ^ k)⁻¹)
        (0 : (Fin d → ℂ) →L[ℂ] ℂ) w := by
      convert (hasFDerivAt_inv' (𝕜 := ℂ) (pow_ne_zero k hnonzero)).comp w
        ((hderiv f).pow k) using 1 <;> first | rfl | simp
    convert (hderiv a).mul hinv using 1 <;>
      first | rfl | simp [div_eq_mul_inv] | (ext v; simp)
  have hmem : ∀ᶠ v in 𝓝 w, e.symm v ∈ Point.overOpen (X.left.basicOpen f) := by
    apply e.continuousAt_symm hztarget
      ((Point.isOpen_overOpen (X.left.basicOpen f)).mem_nhds _)
    rw [e.left_inv hzsource]
    exact hzf
  have hcoord : (fun v => regularInLocalChart X d U a z v /
      regularInLocalChart X d U f z v ^ k) =ᶠ[𝓝 w] (fun v => v j) := by
    filter_upwards [hmem, e.open_target.mem_nhds hztarget] with v hv hvt
    change Point.evaluate U a (e.symm v) / Point.evaluate U f (e.symm v) ^ k = v j
    rw [← ha (e.symm v) hv]
    rw [← Point.evaluate_res hfD (D.ambientCoordinateSection j) (e.symm v) hv]
    rw [← localChart_apply_component_eq_evaluate X d z (e.symm v) (e.map_target hvt) j]
    exact congrFun (e.right_inv hvt) j
  have hderivCoord := hquotient.congr_of_eventuallyEq hcoord.symm
  have hprojection : HasFDerivAt (fun v : Fin d → ℂ => v j)
      (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ) w :=
    (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have heq : (0 : (Fin d → ℂ) →L[ℂ] ℂ) = ContinuousLinearMap.proj j :=
    hderivCoord.unique hprojection
  have := congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L (fun _ => 1)) heq
  simp at this

attribute [local instance] regularSectionAlgebra

/-- Algebra generators of the section ring detect some nonzero analytic derivative at a
smooth point of positive dimension. -/
theorem exists_generator_fderiv_ne_zero (U : X.left.Opens) (hU : IsAffineOpen U)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) (hd : 0 < d)
    {n : ℕ} (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, U))
    (hφ : Function.Surjective φ) :
    ∃ j : Fin n, fderiv ℂ (regularInLocalChart X d U (φ (MvPolynomial.X j)) z)
      (localChart X d z z) ≠ 0 := by
  by_contra! hzero
  have hpolynomial (p : MvPolynomial (Fin n) ℂ) :
      HasFDerivAt (regularInLocalChart X d U (φ p) z)
        (0 : (Fin d → ℂ) →L[ℂ] ℂ) (localChart X d z z) := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        have hconstant : HasFDerivAt (fun _ : Fin d → ℂ => c)
            (0 : (Fin d → ℂ) →L[ℂ] ℂ) (localChart X d z z) :=
          hasFDerivAt_const c _
        apply hconstant.congr_of_eventuallyEq
        simpa only [show φ (MvPolynomial.C c) = regularSectionScalar X U c from φ.commutes c]
          using regularInLocalChart_scalar_eventually X d U c z hz
    | add p q hp hq =>
        rw [map_add, regularInLocalChart_add]
        convert hp.add hq using 1 <;> first | rfl | simp
    | mul_X p j hp =>
        have hj : HasFDerivAt (regularInLocalChart X d U (φ (MvPolynomial.X j)) z)
            (0 : (Fin d → ℂ) →L[ℂ] ℂ) (localChart X d z z) := by
          simpa only [hzero j] using
            (analyticAt_regularInLocalChart X d U (φ (MvPolynomial.X j)) z hz).differentiableAt.hasFDerivAt
        rw [map_mul, regularInLocalChart_mul]
        convert hp.mul hj using 1 <;> first | rfl | simp | (ext v; simp)
  obtain ⟨s, hs⟩ := exists_regularInLocalChart_fderiv_ne_zero X d U hU z hz hd
  obtain ⟨p, rfl⟩ := hφ s
  exact hs (hpolynomial p).fderiv

/-- Evaluation of an actual holomorphic form in a fixed analytic chart. The quotient
relations vanish under this evaluation by their defining restriction-stable kernel. -/
def holomorphicFormEvaluation
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (y : Fin d → ℂ) (hy : y ∈ chartSectionDomain X d U z) :
    HolomorphicForm X d U p →ₗ[ℂ] (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  (holomorphicFormRelations X d U p).liftQ (chartEvaluationAt X d U z p y) (by
    intro a ha
    rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
      restrictionStableAnalyticKernel] at ha
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha
    specialize ha U (𝟙 U)
    rw [rawRestriction_id, LinearMap.id_apply] at ha
    exact (mem_chartEvaluationKernel_iff X d U p a).mp ha z y hy)

theorem holomorphicFormEvaluation_mk
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (y : Fin d → ℂ) (hy : y ∈ chartSectionDomain X d U z)
    (a : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U) :
    holomorphicFormEvaluation X d U z p y hy
        (algebraicFormToHolomorphicForm X d U p (Algebra.DeRham.mk ℂ _ p a v)) =
      chartGeneratorEvaluation X d U z p (a, v) y := by
  simp [holomorphicFormEvaluation, algebraicFormToHolomorphicForm, Algebra.DeRham.mk,
    chartEvaluationAt, chartRawEvaluation_single]

theorem localChart_center_mem_regularChartSectionDomain
    (U : X.left.Opens) (z : ComplexPoint X) (hz : z.underlying ∈ U) :
    localChart X d z z ∈ chartSectionDomain X d (.op (regularAnalyticOpen X U)) z := by
  simp only [chartSectionDomain, extChartAt_target, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_def, id_eq,
    chartAt_eq_localChart, Set.range_id, Set.preimage_id, Set.inter_univ]
  exact ⟨(localChart X d z).map_source (mem_localChart_source X d z), by
    change ((localChart X d z).symm (localChart X d z z)).underlying ∈ U
    rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
    exact hz⟩

theorem chartSection_regularToHolomorphic
    (U : X.left.Opens) (s : Γ(X.left, U)) (z : ComplexPoint X)
    {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d (.op (regularAnalyticOpen X U)) z) :
    chartSection X d (.op (regularAnalyticOpen X U)) z
        (regularToHolomorphicAlgHom X d U s) y = regularInLocalChart X d U s z y := by
  rw [chartSection_apply_of_mem X d _ z _ hy]
  change Point.evaluate U s ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) = _
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_def,
    id_eq, chartAt_eq_localChart, regularInLocalChart]

theorem chartSectionDifferential_regularToHolomorphic
    (U : X.left.Opens) (s : Γ(X.left, U)) (z : ComplexPoint X)
    {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d (.op (regularAnalyticOpen X U)) z) :
    chartSectionDifferential X d (.op (regularAnalyticOpen X U)) z
        (regularToHolomorphicAlgHom X d U s) y =
      fderiv ℂ (regularInLocalChart X d U s z) y := by
  rw [chartSectionDifferential, fderivWithin_congr'
    (fun _ hw => chartSection_regularToHolomorphic X d U s z hw) hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d _ z) hy]

theorem holomorphicFormEvaluation_regular_mk_one
    (U : X.left.Opens) (a b : Γ(X.left, U)) (z : ComplexPoint X)
    (hz : z.underlying ∈ U) (v : Fin d → ℂ) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z 1
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U 1
          (Algebra.DeRham.mk ℂ _ 1 a (fun _ => b))) (fun _ => v) =
      Point.evaluate U a z * fderiv ℂ (regularInLocalChart X d U b z)
        (localChart X d z z) v := by
  simp only [regularFormToHolomorphicForm, LinearMap.comp_apply, Algebra.DeRham.map_mk,
    holomorphicFormEvaluation_mk, chartGeneratorEvaluation,
    ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_eq_det, Matrix.det_fin_one,
    smul_eq_mul]
  rw [chartSection_regularToHolomorphic X d U a z
    (localChart_center_mem_regularChartSectionDomain X d U z hz),
    chartSectionDifferential_regularToHolomorphic X d U b z
      (localChart_center_mem_regularChartSectionDomain X d U z hz)]
  simp only [regularInLocalChart, (localChart X d z).left_inv (mem_localChart_source X d z),
    Matrix.of_apply]

/-- Evaluation of an actual regular symbol is its coefficient times the analytic wedge of
the derivatives of its regular entries. -/
theorem holomorphicFormEvaluation_regular_mk
    (U : X.left.Opens) (p : ℕ) (a : Γ(X.left, U)) (b : Fin p → Γ(X.left, U))
    (z : ComplexPoint X) (hz : z.underlying ∈ U) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z p
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U p (Algebra.DeRham.mk ℂ _ p a b)) =
      Point.evaluate U a z • wedgeCovectors (Fin d → ℂ) p
        (fun i => fderiv ℂ (regularInLocalChart X d U (b i) z) (localChart X d z z)) := by
  simp only [regularFormToHolomorphicForm, LinearMap.comp_apply, Algebra.DeRham.map_mk,
    holomorphicFormEvaluation_mk, chartGeneratorEvaluation]
  rw [chartSection_regularToHolomorphic X d U a z
    (localChart_center_mem_regularChartSectionDomain X d U z hz)]
  simp only [regularInLocalChart, (localChart X d z).left_inv (mem_localChart_source X d z)]
  congr 2
  funext i
  exact chartSectionDifferential_regularToHolomorphic X d U (b i) z
    (localChart_center_mem_regularChartSectionDomain X d U z hz)

/-- The determinant formula in every degree for the regular-to-holomorphic comparison. -/
theorem holomorphicFormEvaluation_regular_mk_apply
    (U : X.left.Opens) (p : ℕ) (a : Γ(X.left, U)) (b : Fin p → Γ(X.left, U))
    (z : ComplexPoint X) (hz : z.underlying ∈ U) (v : Fin p → Fin d → ℂ) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z p
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U p (Algebra.DeRham.mk ℂ _ p a b)) v =
      Point.evaluate U a z * Matrix.det (Matrix.of (fun i j =>
        fderiv ℂ (regularInLocalChart X d U (b i) z) (localChart X d z z) (v j))) := by
  rw [holomorphicFormEvaluation_regular_mk X d U p a b z hz]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, wedgeCovectors_apply_eq_det]

/-- The degree-two determinant formula, with two explicit regular entries. -/
theorem holomorphicFormEvaluation_regular_mk_two
    (U : X.left.Opens) (a b c : Γ(X.left, U))
    (z : ComplexPoint X) (hz : z.underlying ∈ U) (v w : Fin d → ℂ) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z 2
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U 2 (Algebra.DeRham.mk ℂ _ 2 a ![b, c])) ![v, w] =
      Point.evaluate U a z *
        (fderiv ℂ (regularInLocalChart X d U b z) (localChart X d z z) v *
            fderiv ℂ (regularInLocalChart X d U c z) (localChart X d z z) w -
          fderiv ℂ (regularInLocalChart X d U b z) (localChart X d z z) w *
            fderiv ℂ (regularInLocalChart X d U c z) (localChart X d z z) v) := by
  rw [holomorphicFormEvaluation_regular_mk_apply X d U 2 a ![b, c] z hz ![v, w]]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- Evaluation of a weighted Kähler wedge agrees with the wedge of the actual analytic
coordinate derivatives, including the product of the two regular coefficients. -/
theorem holomorphicFormEvaluation_regular_kaehlerWedge_smul_D
    (U : X.left.Opens) (a b c e : Γ(X.left, U))
    (z : ComplexPoint X) (hz : z.underlying ∈ U) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z 2
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U 2
          (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U)
            (a • KaehlerDifferential.D ℂ Γ(X.left, U) b)
            (c • KaehlerDifferential.D ℂ Γ(X.left, U) e))) =
      (Point.evaluate U a z * Point.evaluate U c z) • wedgeCovectors (Fin d → ℂ) 2
        (fun i => fderiv ℂ (regularInLocalChart X d U (![b, e] i) z)
          (localChart X d z z)) := by
  rw [Algebra.DeRham.kaehlerWedge_smul_D_smul_D,
    holomorphicFormEvaluation_regular_mk X d U 2 (a * c) ![b, e] z hz]
  congr 1
  simp [Point.evaluate, hz]

/-- If the two regular one-forms have normalized leading coefficients and vanishing
remaining coefficients at a point, their actual holomorphic wedge evaluates to the wedge
of their leading coordinate derivatives there. -/
theorem holomorphicFormEvaluation_regular_kaehlerWedge_normalized
    (U : X.left.Opens) (a b u v : Fin 2 → Γ(X.left, U))
    (z : ComplexPoint X) (hz : z.underlying ∈ U)
    (ha : ∀ i, Point.evaluate U (a i) z = 1) (hb : ∀ i, Point.evaluate U (b i) z = 0) :
    holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z 2
        (localChart X d z z) (localChart_center_mem_regularChartSectionDomain X d U z hz)
        (regularFormToHolomorphicForm X d U 2
          (Algebra.DeRham.kaehlerWedge ℂ Γ(X.left, U)
            (-(a 0 • KaehlerDifferential.D ℂ Γ(X.left, U) (u 0) -
              b 0 • KaehlerDifferential.D ℂ Γ(X.left, U) (v 0)))
            (-(a 1 • KaehlerDifferential.D ℂ Γ(X.left, U) (u 1) -
              b 1 • KaehlerDifferential.D ℂ Γ(X.left, U) (v 1))))) =
      wedgeCovectors (Fin d → ℂ) 2
        (fun i => fderiv ℂ (regularInLocalChart X d U (u i) z) (localChart X d z z)) := by
  have he (a b c e : Γ(X.left, U)) :=
    holomorphicFormEvaluation_regular_kaehlerWedge_smul_D X d U a b c e z hz
  simp only [map_neg, LinearMap.neg_apply, map_sub, LinearMap.sub_apply,
    he, ha, hb, mul_one, mul_zero, one_smul]
  ext w
  simp only [ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, zero_mul, sub_zero, neg_zero, neg_neg]
  have hu : ![u 0, u 1] = u := by
    funext i
    fin_cases i <;> rfl
  rw [hu]

end AlgebraicGeometry.ComplexPoint
