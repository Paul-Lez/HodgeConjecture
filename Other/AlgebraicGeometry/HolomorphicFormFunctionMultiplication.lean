/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicFormSheafification
public import Other.AlgebraicGeometry.RegularHolomorphicFormEvaluation

/-!
# Multiplication of holomorphic forms by holomorphic functions

The analytic de Rham quotient is naturally a module over holomorphic functions.  This file
constructs the operation directly on raw symbols and proves its evaluation and restriction
laws.  Only complex linearity is packaged in the ambient category; the function coefficient is
an additional parameter.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Multiply the coefficient of every raw de Rham symbol by a holomorphic function. -/
def rawHolomorphicFormFunctionMul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p :=
  Finsupp.lsum ℂ fun g =>
    Finsupp.lsingle (a * g.1, g.2)

@[simp] theorem rawHolomorphicFormFunctionMul_single
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p) (c : ℂ) :
    rawHolomorphicFormFunctionMul X d U p a (Finsupp.single g c) =
      Finsupp.single (a * g.1, g.2) c := by
  simp [rawHolomorphicFormFunctionMul]

/-- Fixed-chart evaluation turns function multiplication into pointwise scalar multiplication. -/
theorem chartRawEvaluation_rawHolomorphicFormFunctionMul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U)
    (w : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartRawEvaluation X d U z p (rawHolomorphicFormFunctionMul X d U p a w) y =
      chartSection X d U z a y • chartRawEvaluation X d U z p w y := by
  classical
  induction w using Finsupp.induction with
  | zero =>
      rw [map_zero, map_zero]
      ext v
      simp [ContinuousAlternatingMap.smul_apply]
  | single_add g c w hg hc ih =>
      simp only [map_add, rawHolomorphicFormFunctionMul_single,
        chartRawEvaluation_single]
      ext v
      simp only [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
        ContinuousAlternatingMap.smul_apply, chartGeneratorEvaluation, smul_eq_mul]
      rw [show chartSection X d U z (a * g.1) y =
          chartSection X d U z a y * chartSection X d U z g.1 y by
        simp only [chartSection_apply_of_mem X d U z _ hy]
        rfl]
      rw [ih, ContinuousAlternatingMap.smul_apply]
      ring

/-- Analytic form relations are stable under multiplication by a holomorphic function. -/
theorem rawHolomorphicFormFunctionMul_mem_relations
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U)
    {w : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hw : w ∈ holomorphicFormRelations X d U p) :
    rawHolomorphicFormFunctionMul X d U p a w ∈
      holomorphicFormRelations X d U p := by
  rw [holomorphicFormRelations_eq_chartEvaluationKernel] at hw ⊢
  apply (mem_chartEvaluationKernel_iff X d U p _).2
  intro z y hy
  rw [chartRawEvaluation_rawHolomorphicFormFunctionMul X d U z p a w hy,
    (mem_chartEvaluationKernel_iff X d U p w).1 hw z y hy]
  ext v
  simp [ContinuousAlternatingMap.smul_apply]

/-- Multiplication by one fixed holomorphic function on the analytic form quotient. -/
def holomorphicFormFunctionMul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U p :=
  (holomorphicFormRelations X d U p).liftQ
    ((holomorphicFormRelations X d U p).mkQ.comp
      (rawHolomorphicFormFunctionMul X d U p a)) (by
        intro w hw
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact rawHolomorphicFormFunctionMul_mem_relations X d U p a hw)

@[simp] theorem holomorphicFormFunctionMul_mk
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U)
    (w : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p) :
    holomorphicFormFunctionMul X d U p a
        ((holomorphicFormRelations X d U p).mkQ w) =
      (holomorphicFormRelations X d U p).mkQ
        (rawHolomorphicFormFunctionMul X d U p a w) := by
  rfl

/-- Evaluation of a function multiple is pointwise scalar multiplication. -/
theorem holomorphicFormEvaluation_functionMul
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (y : Fin d → ℂ) (hy : y ∈ chartSectionDomain X d U z)
    (a : OpenHolomorphicFunctions X d U) (w : HolomorphicForm X d U p) :
    holomorphicFormEvaluation X d U z p y hy
        (holomorphicFormFunctionMul X d U p a w) =
      chartSection X d U z a y • holomorphicFormEvaluation X d U z p y hy w := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) w
  simp only [holomorphicFormFunctionMul_mk]
  change chartRawEvaluation X d U z p
      (rawHolomorphicFormFunctionMul X d U p a r) y =
    chartSection X d U z a y • chartRawEvaluation X d U z p r y
  exact chartRawEvaluation_rawHolomorphicFormFunctionMul X d U z p a r hy

/-- Multiplication by a constant holomorphic function agrees with the ordinary complex scalar
action on holomorphic forms. -/
theorem holomorphicFormFunctionMul_algebraMap
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (c : ℂ) (w : HolomorphicForm X d U p) :
    holomorphicFormFunctionMul X d U p
        (algebraMap ℂ (OpenHolomorphicFunctions X d U) c) w = c • w := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) w
  rw [holomorphicFormFunctionMul_mk]
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d U p)).2
  rw [holomorphicFormRelations_eq_chartEvaluationKernel]
  apply (mem_chartEvaluationKernel_iff X d U p _).2
  intro z y hy
  rw [map_sub]
  change chartRawEvaluation X d U z p
      (rawHolomorphicFormFunctionMul X d U p
        (algebraMap ℂ (OpenHolomorphicFunctions X d U) c) r) y -
      chartRawEvaluation X d U z p (c • r) y = 0
  rw [chartRawEvaluation_rawHolomorphicFormFunctionMul X d U z p _ r hy,
    map_smul]
  have hc : chartSection X d U z
      (algebraMap ℂ (OpenHolomorphicFunctions X d U) c) y = c := by
    rw [chartSection_apply_of_mem X d U z _ hy]
    rfl
  rw [hc]
  exact sub_self _

/-- Raw function multiplication commutes with restriction. -/
theorem rawRestriction_rawHolomorphicFormFunctionMul
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U)
    (w : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p) :
    rawRestriction X d i p (rawHolomorphicFormFunctionMul X d U p a w) =
      rawHolomorphicFormFunctionMul X d V p
        (holomorphicRestrictionAlgHom X d i a) (rawRestriction X d i p w) := by
  classical
  induction w using Finsupp.induction with
  | zero => simp
  | single_add g c w hg hc ih =>
      simp only [map_add, rawHolomorphicFormFunctionMul_single, ih]
      congr 1
      simp only [rawRestriction, Algebra.DeRham.rawMap_single,
        Algebra.DeRham.generatorMap, map_mul]
      rw [rawHolomorphicFormFunctionMul_single]

/-- Function multiplication on holomorphic forms commutes with restriction. -/
theorem holomorphicFormRestriction_functionMul
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (a : OpenHolomorphicFunctions X d U) (w : HolomorphicForm X d U p) :
    holomorphicFormRestriction X d i p
        (holomorphicFormFunctionMul X d U p a w) =
      holomorphicFormFunctionMul X d V p
        (holomorphicRestrictionAlgHom X d i a)
        (holomorphicFormRestriction X d i p w) := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) w
  change (holomorphicFormRelations X d V p).mkQ
      (rawRestriction X d i p (rawHolomorphicFormFunctionMul X d U p a r)) =
    (holomorphicFormRelations X d V p).mkQ
      (rawHolomorphicFormFunctionMul X d V p
        (holomorphicRestrictionAlgHom X d i a) (rawRestriction X d i p r))
  rw [rawRestriction_rawHolomorphicFormFunctionMul]

end AlgebraicGeometry.ComplexPoint
