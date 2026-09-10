/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponential

/-!
# Holomorphic zero-forms are holomorphic functions

The analytic quotient in degree zero is identified with actual holomorphic functions. In
particular the function-to-zero-form comparison used in the exponential resolution is an
isomorphism of sheaves, not an additional comparison hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- Regard a holomorphic function as an analytic zero-form. -/
def holomorphicFormOfFunction (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    OpenHolomorphicFunctions s d U →ₗ[ℂ] HolomorphicForm s d U 0 :=
  (algebraicFormToHolomorphicForm s d U 0).comp
    (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions s d U))

/-- The degree-zero quotient retains all values of a holomorphic function. -/
theorem holomorphicFormOfFunction_injective
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    Function.Injective (holomorphicFormOfFunction s d U) := by
  intro f g h
  have hzero : holomorphicFormOfFunction s d U (f - g) = 0 := by
    rw [map_sub, h, sub_self]
  let a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions s d U) 0 :=
    Finsupp.single (f - g, Fin.elim0) 1
  have ha : a ∈ holomorphicFormRelations s d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero _).mp hzero
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
    restrictionStableAnalyticKernel] at ha
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha
  specialize ha U (𝟙 U)
  rw [rawRestriction_id, LinearMap.id_apply] at ha
  apply ContMDiffMap.ext
  intro x
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ chartSectionDomain s d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (mem_chartEvaluationKernel_iff s d U 0 a).1 ha x.1 (e x.1) hxe
  have hcoeff := congrArg
    (fun v : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ => v Fin.elim0) heval
  simp only [a, chartRawEvaluation_single, one_smul, chartGeneratorEvaluation,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, wedgeCovectors] at hcoeff
  rw [chartSection_apply_of_mem s d U x.1 (f - g) hxe] at hcoeff
  have hz : (f - g).1 x = 0 := by simpa [e] using hcoeff
  exact sub_eq_zero.mp hz

/-- Every analytic zero-form is represented by a holomorphic function. -/
theorem holomorphicFormOfFunction_surjective
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    Function.Surjective (holomorphicFormOfFunction s d U) := by
  intro form
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations s d U 0) form
  classical
  induction a using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add v c a hv hc ih =>
      obtain ⟨f, hf⟩ := ih
      refine ⟨c • v.1 + f, ?_⟩
      rw [map_add, map_smul, hf, map_add]
      congr 1
      change c • (holomorphicFormRelations s d U 0).mkQ
        (Finsupp.single (v.1, Fin.elim0) 1) =
          (holomorphicFormRelations s d U 0).mkQ (Finsupp.single v c)
      rw [← map_smul]
      congr 1
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      congr 1
      exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The actual analytic zero-forms and holomorphic functions are complex-linearly equivalent. -/
def holomorphicZeroFormEquiv (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    OpenHolomorphicFunctions s d U ≃ₗ[ℂ] HolomorphicForm s d U 0 :=
  LinearEquiv.ofBijective (holomorphicFormOfFunction s d U)
    ⟨holomorphicFormOfFunction_injective s d U, holomorphicFormOfFunction_surjective s d U⟩

instance holomorphicFunctionToZeroFormPresheaf_isIso :
    IsIso (holomorphicFunctionToZeroFormPresheaf s d) := by
  let (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
      IsIso ((holomorphicFunctionToZeroFormPresheaf s d).app U) :=
    by
      let : Mono ((holomorphicFunctionToZeroFormPresheaf s d).app U) :=
        (AddCommGrpCat.mono_iff_injective _).2 (holomorphicFormOfFunction_injective s d U)
      let : Epi ((holomorphicFunctionToZeroFormPresheaf s d).app U) :=
        (AddCommGrpCat.epi_iff_surjective _).2 (holomorphicFormOfFunction_surjective s d U)
      exact isIso_of_mono_of_epi _
  exact NatIso.isIso_of_isIso_app _

instance holomorphicFunctionToZeroFormSheaf_isIso :
    IsIso (holomorphicFunctionToZeroFormSheaf s d) := by
  let := holomorphicFunctionToZeroFormPresheaf_isIso s d
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))
  have h : Presheaf.IsSheaf J (holomorphicDeRhamPresheaf s d 0) :=
    (Presheaf.isSheaf_of_iso_iff (asIso (holomorphicFunctionToZeroFormPresheaf s d))).mp
      (holomorphicAdditiveFunctionSheaf s d).property
  let := isIso_toSheafify J h
  let : IsIso ((sheafToPresheaf J AddCommGrpCat).map
      (holomorphicFunctionToZeroFormSheaf s d)) := by
    change IsIso (holomorphicFunctionToZeroFormPresheaf s d ≫ toSheafify J _)
    infer_instance
  refine ⟨⟨inv ((sheafToPresheaf J AddCommGrpCat).map
    (holomorphicFunctionToZeroFormSheaf s d))⟩, ?_, ?_⟩
  · apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    exact IsIso.hom_inv_id ((sheafToPresheaf J AddCommGrpCat).map
      (holomorphicFunctionToZeroFormSheaf s d))
  · apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    exact IsIso.inv_hom_id ((sheafToPresheaf J AddCommGrpCat).map
      (holomorphicFunctionToZeroFormSheaf s d))

end AlgebraicGeometry.ComplexPoint
