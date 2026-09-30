/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import Other.AlgebraicGeometry.HolomorphicExponential

/-!
# Holomorphic zero-forms as functions

Evaluation of degree-zero forms gives a morphism to the holomorphic-function sheaf.
This supplies the projection used to send the first Hodge filtration to zero in `H²(𝒪)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

local instance holomorphicZeroFormsTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The degree-zero exterior power gives the coefficient function of a Kähler zero-form. -/
def algebraicZeroFormToFunction (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0 →ₗ[ℂ]
      OpenHolomorphicFunctions X d U :=
  (exteriorPower.zeroEquiv (OpenHolomorphicFunctions X d U)
    Ω[OpenHolomorphicFunctions X d U⁄ℂ]).toLinearMap.restrictScalars ℂ

@[simp]
lemma algebraicZeroFormToFunction_mk (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (a : OpenHolomorphicFunctions X d U) (v : Fin 0 → OpenHolomorphicFunctions X d U) :
    algebraicZeroFormToFunction X d U (Algebra.DeRham.mk ℂ _ 0 a v) = a := by
  simp [algebraicZeroFormToFunction, Algebra.DeRham.mk, Algebra.DeRham.exact]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a zero-form in a chart gives its coefficient function. -/
lemma chartEvaluation_zero_apply (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartEvaluation X d U z 0 a y Fin.elim0 =
      (algebraicZeroFormToFunction X d U a).1
        ⟨(extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y, hy.2⟩ := by
  induction a using Algebra.DeRham.mk_induction with
  | mk a v =>
      rw [chartEvaluation_mk X d U z 0 a v hy, algebraicZeroFormToFunction_mk]
      simp [chartGeneratorEvaluation, chartSection_apply_of_mem X d U z a hy]
  | zero => rw [chartEvaluation_zero, map_zero]; rfl
  | add a b ha hb =>
      rw [chartEvaluation_add, map_add]
      exact congrArg₂ (· + ·) ha hb
  | smul c a ha =>
      rw [chartEvaluation_smul, map_smul]
      exact congrArg (c • ·) ha

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A zero-form which vanishes in all charts has zero coefficient function. -/
lemma chartEvaluationKernel_zero_le_ker (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    chartEvaluationKernel X d U 0 ≤ LinearMap.ker (algebraicZeroFormToFunction X d U) := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext x
  let e := extChartAt 𝓘(ℂ, Fin d → ℂ) (x : ComplexPoint X)
  have hx : (x : ComplexPoint X) ∈ e.source := mem_extChartAt_source (x : ComplexPoint X)
  have hy : e x ∈ chartSectionDomain X d U x :=
    ⟨e.map_source hx, by change e.symm (e x) ∈ U.unop; rw [e.left_inv hx]; exact x.2⟩
  have heval := congrArg (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0)
    ((mem_chartEvaluationKernel_iff X d U 0 a).mp ha x (e x) hy)
  rw [chartEvaluation_zero_apply X d U x a hy] at heval
  have hpoint : (⟨e.symm (e x), hy.2⟩ : U.unop) = x := Subtype.ext (e.left_inv hx)
  change (algebraicZeroFormToFunction X d U a).1 ⟨e.symm (e x), hy.2⟩ = 0 at heval
  rw [hpoint] at heval
  exact heval

/-- The holomorphic function represented by an analytic zero-form. -/
def holomorphicZeroFormToFunction (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    HolomorphicForm X d U 0 →ₗ[ℂ] OpenHolomorphicFunctions X d U :=
  (chartEvaluationKernel X d U 0).liftQ (algebraicZeroFormToFunction X d U)
    (chartEvaluationKernel_zero_le_ker X d U)

/-- Evaluation of algebraic zero-forms commutes with restriction. -/
lemma algebraicZeroFormToFunction_restriction
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0) :
    algebraicZeroFormToFunction X d V (formRestriction X d i 0 a) =
      holomorphicRestrictionAlgHom X d i (algebraicZeroFormToFunction X d U a) := by
  induction a using Algebra.DeRham.mk_induction with
  | mk a v => simp [formRestriction]
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul c a ha => simp [ha]

/-- Evaluation of analytic zero-forms commutes with restriction. -/
lemma holomorphicZeroFormToFunction_restriction
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (a : HolomorphicForm X d U 0) :
    holomorphicZeroFormToFunction X d V (holomorphicFormRestriction X d i 0 a) =
      holomorphicRestrictionAlgHom X d i (holomorphicZeroFormToFunction X d U a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (chartEvaluationKernel X d U 0) a
  exact algebraicZeroFormToFunction_restriction X d i a

/-- Evaluation on the presheaf of holomorphic zero-forms. -/
def holomorphicZeroFormToFunctionPresheaf :
    holomorphicDeRhamPresheaf X d 0 ⟶ (holomorphicAdditiveSheaf X d).obj where
  app U := AddCommGrpCat.ofHom (holomorphicZeroFormToFunction X d U).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact holomorphicZeroFormToFunction_restriction X d i a

/-- Evaluation on the sheaf of holomorphic zero-forms. -/
def holomorphicZeroFormToFunctionSheaf :
    holomorphicDeRhamSheaf X d 0 ⟶ holomorphicAdditiveSheaf X d :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicZeroFormToFunctionPresheaf X d) (holomorphicAdditiveSheaf X d).property⟩

/-- Evaluation sends constant zero-forms to the corresponding constant functions. -/
@[simp]
lemma holomorphicZeroFormToFunction_ofConstant
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (c : ℂ) :
    holomorphicZeroFormToFunction X d U (holomorphicFormOfConstant X d U c) =
      algebraMap ℂ (OpenHolomorphicFunctions X d U) c := by
  change algebraicZeroFormToFunction X d U
    (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) c) = _
  simp [Algebra.DeRham.ofConstant_apply, Algebra.DeRham.ofFunction_apply]

/-- Complex constants as holomorphic functions, before sheafification. -/
def complexConstantsToHolomorphicPresheaf :
    𝓒ᵖ(↧(ComplexPoint X); ℂ) ⟶ (holomorphicAdditiveSheaf X d).obj where
  app U := AddCommGrpCat.ofHom ContMDiffMap.C.toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    rfl

/-- The inclusion of the constant complex sheaf into holomorphic functions. -/
def complexConstantsToHolomorphicSheaf :
    𝓒(↧(ComplexPoint X); ℂ) ⟶ holomorphicAdditiveSheaf X d :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (complexConstantsToHolomorphicPresheaf X d) (holomorphicAdditiveSheaf X d).property⟩

lemma constantsToHolomorphicDeRhamZero_comp_toFunction :
    constantsToHolomorphicDeRhamZero X d ≫ holomorphicZeroFormToFunctionPresheaf X d =
      complexConstantsToHolomorphicPresheaf X d := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact holomorphicZeroFormToFunction_ofConstant X d U c

set_option backward.isDefEq.respectTransparency false in
lemma constantsToHolomorphicDeRhamZeroSheaf_comp_toFunction :
    constantsToHolomorphicDeRhamZeroSheaf X d ≫ holomorphicZeroFormToFunctionSheaf X d =
      complexConstantsToHolomorphicSheaf X d := by
  apply Sheaf.hom_ext
  change sheafifyMap _ (constantsToHolomorphicDeRhamZero X d) ≫
    sheafifyLift _ (holomorphicZeroFormToFunctionPresheaf X d) _ =
      sheafifyLift _ (complexConstantsToHolomorphicPresheaf X d) _
  rw [sheafifyMap_sheafifyLift, constantsToHolomorphicDeRhamZero_comp_toFunction]

end AlgebraicGeometry.ComplexPoint
