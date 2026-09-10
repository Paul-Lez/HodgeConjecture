/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicFormFunctionMultiplication

/-!
# Local division of one-forms on a complex curve

On a one-dimensional complex manifold, a one-form with nonzero value at a point generates all
one-forms on a smaller neighborhood.  The coefficient is the quotient of the two coordinate
coefficients.  This file proves the statement for the repository's actual analytic-form quotient,
including its compatibility with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : Over (Spec (CommRingCat.of ℂ)))
  [SmoothOfRelativeDimension 1 X.hom]

/-- The standard tangent vector used to read the coefficient of a one-form in dimension one. -/
def curveOneFormTestVector : Fin 1 → Fin 1 → ℂ :=
  fun _ => Pi.single (0 : Fin 1) 1

/-- A one-form on a one-dimensional vector space is determined by its value on the standard
tangent vector. -/
theorem curveOneForm_eq_coefficient_smul_volume
    (A : ContinuousAlternatingMap ℂ (Fin 1 → ℂ) ℂ (Fin 1)) :
    A = A curveOneFormTestVector •
      wedgeCovectors (Fin 1 → ℂ) 1 (fun _ => ContinuousLinearMap.proj 0) := by
  have h := alternating_eq_sum_wedgeCovectors 1 1 A
  change A = A (fun _ => Pi.single (0 : Fin 1) 1) •
    wedgeCovectors (Fin 1 → ℂ) 1 (fun _ => ContinuousLinearMap.proj 0)
  simpa using h

/-- Division of the standard coefficient divides one nonzero one-form by another. -/
theorem curveOneForm_eq_ratio_smul
    (A B : ContinuousAlternatingMap ℂ (Fin 1 → ℂ) ℂ (Fin 1))
    (hB : B curveOneFormTestVector ≠ 0) :
    A = (A curveOneFormTestVector / B curveOneFormTestVector) • B := by
  let V := wedgeCovectors (Fin 1 → ℂ) 1 (fun _ => ContinuousLinearMap.proj 0)
  have hA : A = A curveOneFormTestVector • V :=
    curveOneForm_eq_coefficient_smul_volume A
  have hBV : B = B curveOneFormTestVector • V :=
    curveOneForm_eq_coefficient_smul_volume B
  calc
    A = A curveOneFormTestVector • V := hA
    _ = (A curveOneFormTestVector / B curveOneFormTestVector) •
        (B curveOneFormTestVector • V) := by
      rw [smul_smul]
      congr 1
      exact (div_mul_cancel₀ _ hB).symm
    _ = (A curveOneFormTestVector / B curveOneFormTestVector) • B := by rw [← hBV]

/-- If a one-form is nonzero, its standard coordinate coefficient is nonzero. -/
theorem curveOneForm_coefficient_ne_zero
    {A : ContinuousAlternatingMap ℂ (Fin 1 → ℂ) ℂ (Fin 1)} (hA : A ≠ 0) :
    A curveOneFormTestVector ≠ 0 := by
  intro h
  apply hA
  rw [curveOneForm_eq_coefficient_smul_volume A, h]
  ext v
  simp [ContinuousAlternatingMap.smul_apply]

/-- The center of the chosen chart belongs to the coordinate domain of every open containing
the center. -/
theorem localChart_center_mem_chartSectionDomain
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U) :
    localChart X 1 x x ∈ chartSectionDomain X 1 U x := by
  simp only [chartSectionDomain, extChartAt_target, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Function.comp_def, id_eq,
    chartAt_eq_localChart, Set.range_id, Set.preimage_id, Set.inter_univ]
  exact ⟨(localChart X 1 x).map_source (mem_localChart_source X 1 x), by
    change (localChart X 1 x).symm (localChart X 1 x x) ∈ Opposite.unop U
    rw [(localChart X 1 x).left_inv (mem_localChart_source X 1 x)]
    exact hxU⟩

/-- Evaluation of a quotient holomorphic form commutes with restriction. -/
theorem holomorphicFormEvaluation_restriction
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X) (p : ℕ) (w : HolomorphicForm X 1 U p)
    (y : Fin 1 → ℂ) (hy : y ∈ chartSectionDomain X 1 V z) :
    holomorphicFormEvaluation X 1 V z p y hy
        (holomorphicFormRestriction X 1 i p w) =
      holomorphicFormEvaluation X 1 U z p y
        ⟨hy.1, leOfHom i.unop hy.2⟩ w := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X 1 U p) w
  change chartRawEvaluation X 1 V z p (rawRestriction X 1 i p r) y =
    chartRawEvaluation X 1 U z p r y
  exact chartRawEvaluation_rawRestriction X 1 i z p r hy

/-- Multiplication by a one-form which is nonzero at every point is injective on holomorphic
functions. -/
theorem holomorphicFormFunctionMul_injective_of_pointwise_ne_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (beta : HolomorphicForm X 1 U 1)
    (hbeta : ∀ (z : ComplexPoint X) (hz : z ∈ Opposite.unop U),
      holomorphicFormEvaluation X 1 U z 1 (localChart X 1 z z)
        (localChart_center_mem_chartSectionDomain X U z hz) beta ≠ 0) :
    Function.Injective (fun q : OpenHolomorphicFunctions X 1 U =>
      holomorphicFormFunctionMul X 1 U 1 q beta) := by
  intro a b hab
  apply Subtype.ext
  funext z
  let x : ComplexPoint X := z.1
  have hx : x ∈ Opposite.unop U := z.2
  let hc := localChart_center_mem_chartSectionDomain X U x hx
  have he := congrArg
    (fun w : HolomorphicForm X 1 U 1 =>
      holomorphicFormEvaluation X 1 U x 1 (localChart X 1 x x) hc w) hab
  rw [holomorphicFormEvaluation_functionMul,
    holomorphicFormEvaluation_functionMul] at he
  have hchart : chartSection X 1 U x a (localChart X 1 x x) =
      chartSection X 1 U x b (localChart X 1 x x) :=
    smul_left_injective ℂ (hbeta x hx) he
  simpa only [chartSection_apply_of_mem X 1 U x a hc,
    chartSection_apply_of_mem X 1 U x b hc,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq,
    chartAt_eq_localChart,
    (localChart X 1 x).left_inv (mem_localChart_source X 1 x)] using hchart

/-- A nonzero analytic one-form locally divides every other analytic one-form.  Both forms are
given by raw representatives on `U`; the conclusion lives in the actual analytic quotient on a
smaller open neighborhood. -/
theorem exists_local_holomorphicOneForm_eq_functionMul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U)
    (α beta : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X 1 U) 1)
    (hbeta : chartRawEvaluation X 1 U x 1 beta
      (localChart X 1 x x) ≠ 0) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (k : U ⟶ W)
      (q : OpenHolomorphicFunctions X 1 W),
      x ∈ Opposite.unop W ∧
      holomorphicFormRestriction X 1 k 1
          ((holomorphicFormRelations X 1 U 1).mkQ α) =
        holomorphicFormFunctionMul X 1 W 1 q
          (holomorphicFormRestriction X 1 k 1
            ((holomorphicFormRelations X 1 U 1).mkQ beta)) := by
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    exists_chartBall_le X 1 U x hxU
  let αV := rawRestriction X 1 i 1 α
  let betaV := rawRestriction X 1 i 1 beta
  let e := localChart X 1 x
  let center : Fin 1 → ℂ := localChart X 1 x x
  have hcenterV : center ∈ chartSectionDomain X 1 V x := by
    rw [hdomV]
    exact Metric.mem_ball_self hr
  have hbetaV : chartRawEvaluation X 1 V x 1 betaV center ≠ 0 := by
    rw [chartRawEvaluation_rawRestriction X 1 i x 1 beta hcenterV]
    exact hbeta
  let numerator : (Fin 1 → ℂ) → ℂ :=
    fun y => chartRawEvaluation X 1 V x 1 αV y curveOneFormTestVector
  let denominator : (Fin 1 → ℂ) → ℂ :=
    fun y => chartRawEvaluation X 1 V x 1 betaV y curveOneFormTestVector
  have hdenCenter : denominator center ≠ 0 :=
    curveOneForm_coefficient_ne_zero hbetaV
  have hnumAnalytic : AnalyticOnNhd ℂ numerator (chartSectionDomain X 1 V x) :=
    analyticOnNhd_chartRawEvaluation_apply X 1 V x 1 αV curveOneFormTestVector
  have hdenAnalytic : AnalyticOnNhd ℂ denominator (chartSectionDomain X 1 V x) :=
    analyticOnNhd_chartRawEvaluation_apply X 1 V x 1 betaV curveOneFormTestVector
  let D : Set (Fin 1 → ℂ) :=
    chartSectionDomain X 1 V x ∩ {y | denominator y ≠ 0}
  have hDopen : IsOpen D := by
    exact hdenAnalytic.continuousOn.isOpen_inter_preimage
      (isOpen_chartSectionDomain X 1 V x) isOpen_ne
  let Wo : Opens (ComplexPoint X) :=
    ⟨e.source ∩ e ⁻¹' D, e.isOpen_inter_preimage hDopen⟩
  have hxsource : x ∈ e.source := mem_localChart_source X 1 x
  have hcenterD : center ∈ D := ⟨hcenterV, hdenCenter⟩
  have hxWo : x ∈ Wo := by
    refine ⟨hxsource, ?_⟩
    change e x ∈ D
    exact hcenterD
  have hWoV : Wo ≤ Opposite.unop V := by
    intro z hz
    have hezD : e z ∈ D := hz.2
    have hezDom : e z ∈ chartSectionDomain X 1 V x := hezD.1
    have hzV : e.symm (e z) ∈ Opposite.unop V := hezDom.2
    rw [e.left_inv hz.1] at hzV
    exact hzV
  let W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ := Opposite.op Wo
  let j : V ⟶ W := (homOfLE hWoV).op
  have hxW : x ∈ Opposite.unop W := hxWo
  have hsourceW : ((Opposite.unop W : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin 1 → ℂ)) x).source := by
    intro z hz
    simpa only [e, extChartAt_source, chartAt_eq_localChart X 1] using hz.1
  have hWD (y : Fin 1 → ℂ) (hy : y ∈ chartSectionDomain X 1 W x) : y ∈ D := by
    have hpre : e (e.symm y) ∈ D := hy.2.2
    have hytarget : y ∈ e.target := by
      change y ∈ (localChart X 1 x).target
      simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
        ModelWithCorners.range_eq_univ, Set.inter_univ,
        chartAt_eq_localChart X 1] using hy.1
    rwa [e.right_inv hytarget] at hpre
  have hWDom (y : Fin 1 → ℂ) (hy : y ∈ chartSectionDomain X 1 W x) :
      y ∈ chartSectionDomain X 1 V x := (hWD y hy).1
  have hWDen (y : Fin 1 → ℂ) (hy : y ∈ chartSectionDomain X 1 W x) :
      denominator y ≠ 0 := (hWD y hy).2
  let quotient : (Fin 1 → ℂ) → ℂ := fun y => numerator y / denominator y
  have hquotient : AnalyticOnNhd ℂ quotient (chartSectionDomain X 1 W x) :=
    (hnumAnalytic.mono (fun y hy => hWDom y hy)).div
      (hdenAnalytic.mono (fun y hy => hWDom y hy)) hWDen
  let q : OpenHolomorphicFunctions X 1 W :=
    holomorphicSectionOfChart X 1 W x hsourceW quotient hquotient
  refine ⟨W, i ≫ j, q, hxW, ?_⟩
  change (holomorphicFormRelations X 1 W 1).mkQ
      (rawRestriction X 1 (i ≫ j) 1 α) =
    holomorphicFormFunctionMul X 1 W 1 q
      ((holomorphicFormRelations X 1 W 1).mkQ
        (rawRestriction X 1 (i ≫ j) 1 beta))
  rw [holomorphicFormFunctionMul_mk]
  apply (Submodule.Quotient.eq (holomorphicFormRelations X 1 W 1)).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply mem_restrictionStableAnalyticKernel_of_chartRawEvaluation_eq_zero
    X 1 W x 1 hsourceW
  intro y hy
  rw [map_sub, Pi.sub_apply,
    chartRawEvaluation_rawHolomorphicFormFunctionMul X 1 W x 1 q
      (rawRestriction X 1 (i ≫ j) 1 beta) hy,
    chartSection_holomorphicSectionOfChart X 1 W x hsourceW quotient hquotient hy,
    rawRestriction_comp, LinearMap.comp_apply]
  change chartRawEvaluation X 1 W x 1 (rawRestriction X 1 j 1 αV) y -
      quotient y • chartRawEvaluation X 1 W x 1 (rawRestriction X 1 j 1 betaV) y = 0
  rw [chartRawEvaluation_rawRestriction X 1 j x 1 αV hy,
    chartRawEvaluation_rawRestriction X 1 j x 1 betaV hy]
  have hratio := curveOneForm_eq_ratio_smul
    (chartRawEvaluation X 1 V x 1 αV y)
    (chartRawEvaluation X 1 V x 1 betaV y)
    (hWDen y hy)
  exact sub_eq_zero.mpr hratio

/-- Quotient-level version of local division.  If `beta` has nonzero value at `x`, then on a
smaller neighborhood every holomorphic one-form is a holomorphic-function multiple of `beta`. -/
theorem exists_local_holomorphicOneForm_eq_functionMul_of_ne_zero
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U)
    (alpha beta : HolomorphicForm X 1 U 1)
    (hbeta : holomorphicFormEvaluation X 1 U x 1
      (localChart X 1 x x) (localChart_center_mem_chartSectionDomain X U x hxU) beta ≠ 0) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (k : U ⟶ W)
      (q : OpenHolomorphicFunctions X 1 W),
      x ∈ Opposite.unop W ∧
      holomorphicFormRestriction X 1 k 1 alpha =
        holomorphicFormFunctionMul X 1 W 1 q
          (holomorphicFormRestriction X 1 k 1 beta) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X 1 U 1) alpha
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X 1 U 1) beta
  apply exists_local_holomorphicOneForm_eq_functionMul X U x hxU a b
  exact hbeta

end AlgebraicGeometry.ComplexPoint
