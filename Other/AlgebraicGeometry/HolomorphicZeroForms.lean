/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HolomorphicDeRham
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

/-- A raw zero-form is evaluated by summing its holomorphic coefficients. -/
def rawZeroFormToFunction (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) 0 →ₗ[ℂ]
      OpenHolomorphicFunctions X d U :=
  Finsupp.linearCombination ℂ Prod.fst

@[simp]
lemma rawZeroFormToFunction_single (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) 0) (c : ℂ) :
    rawZeroFormToFunction X d U (Finsupp.single g c) = c • g.1 :=
  Finsupp.linearCombination_single ..

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a zero-form in a chart agrees with its underlying holomorphic function. -/
lemma chartRawEvaluation_zero_apply (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) 0)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartRawEvaluation X d U z 0 a y Fin.elim0 =
      (rawZeroFormToFunction X d U a).1
        ⟨(extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y, hy.2⟩ := by
  classical
  induction a using Finsupp.induction with
  | zero => rw [map_zero, map_zero]; rfl
  | single_add g c a hg hc ih =>
      rw [map_add, map_add]
      change _ + _ = (rawZeroFormToFunction X d U (Finsupp.single g c)).1 _ +
        (rawZeroFormToFunction X d U a).1 _
      refine congrArg₂ (· + ·) ?_ ih
      rw [chartRawEvaluation_single, rawZeroFormToFunction_single]
      change c * (chartSection X d U z g.1 y * 1) =
        c * g.1.1 ⟨(extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y, hy.2⟩
      rw [chartSection_apply_of_mem X d U z _ hy, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Analytic zero-form relations evaluate to the zero holomorphic function. -/
lemma holomorphicFormRelations_zero_le_ker (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    holomorphicFormRelations X d U 0 ≤ LinearMap.ker (rawZeroFormToFunction X d U) := by
  intro a ha
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
    restrictionStableAnalyticKernel] at ha
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha
  specialize ha U (𝟙 U)
  rw [rawRestriction_id, LinearMap.id_apply] at ha
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  funext x
  let e := extChartAt 𝓘(ℂ, Fin d → ℂ) (x : ComplexPoint X)
  have hx : (x : ComplexPoint X) ∈ e.source :=
    mem_extChartAt_source (x : ComplexPoint X)
  have hy : e x ∈ chartSectionDomain X d U x :=
    ⟨e.map_source hx, by change e.symm (e x) ∈ U.unop; rw [e.left_inv hx]; exact x.2⟩
  have heval := congrArg (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0)
    ((mem_chartEvaluationKernel_iff X d U 0 a).mp ha x (e x) hy)
  rw [chartRawEvaluation_zero_apply X d U x a hy] at heval
  have hpoint : (⟨e.symm (e x), hy.2⟩ : U.unop) = x := Subtype.ext (e.left_inv hx)
  change (rawZeroFormToFunction X d U a).1 ⟨e.symm (e x), hy.2⟩ = 0 at heval
  rw [hpoint] at heval
  exact heval

/-- The holomorphic function represented by an analytic zero-form. -/
def holomorphicZeroFormToFunction (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    HolomorphicForm X d U 0 →ₗ[ℂ] OpenHolomorphicFunctions X d U :=
  (holomorphicFormRelations X d U 0).liftQ (rawZeroFormToFunction X d U)
    (holomorphicFormRelations_zero_le_ker X d U)

/-- Evaluation of raw zero-forms commutes with restriction. -/
lemma rawZeroFormToFunction_restriction
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) 0) :
    rawZeroFormToFunction X d V (rawRestriction X d i 0 a) =
      holomorphicRestrictionAlgHom X d i (rawZeroFormToFunction X d U a) := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | single_add g c a hg hc ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      simp [rawZeroFormToFunction, rawRestriction, Algebra.DeRham.generatorMap]

/-- Evaluation of analytic zero-forms commutes with restriction. -/
lemma holomorphicZeroFormToFunction_restriction
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (a : HolomorphicForm X d U 0) :
    holomorphicZeroFormToFunction X d V (holomorphicFormRestriction X d i 0 a) =
      holomorphicRestrictionAlgHom X d i (holomorphicZeroFormToFunction X d U a) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U 0) a
  exact rawZeroFormToFunction_restriction X d i a

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
  change rawZeroFormToFunction X d U
    (Finsupp.single (algebraMap ℂ (OpenHolomorphicFunctions X d U) c, Fin.elim0) 1) = _
  rw [rawZeroFormToFunction_single, one_smul]

/-- Complex constants as holomorphic functions, before sheafification. -/
def complexConstantsToHolomorphicPresheaf :
    constantComplexAddCommGrpPresheaf X ⟶ (holomorphicAdditiveSheaf X d).obj where
  app U := AddCommGrpCat.ofHom ContMDiffMap.C.toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    rfl

/-- The inclusion of the constant complex sheaf into holomorphic functions. -/
def complexConstantsToHolomorphicSheaf :
    constantComplexSheaf X ⟶ holomorphicAdditiveSheaf X d :=
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
