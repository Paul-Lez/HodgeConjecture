/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLogarithmicForms
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare

/-!
# The holomorphic exponential and logarithmic derivative

This file constructs the exponential of a holomorphic function as an actual holomorphic unit.
It proves restriction compatibility and the analytic chain rule needed to compare logarithmic
classes with the exponential sequence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The pointwise complex exponential of a holomorphic function is holomorphic. -/
def holomorphicExp (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U) : OpenHolomorphicFunctions s d U := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X s)); ℂ⟯
  exact ⟨fun x => Complex.exp (f.1 x),
    Complex.contDiff_exp.contMDiff.comp (holomorphicFunctionSheaf_section_analytic s d f)⟩

@[simp]
theorem holomorphicExp_apply (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U)
    (x : (Opposite.unop U : Opens (ComplexPoint X s))) :
    (holomorphicExp s d U f).1 x = Complex.exp (f.1 x) := rfl

@[simp]
theorem holomorphicExp_zero (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    holomorphicExp s d U 0 = 1 := by
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_zero

@[simp]
theorem holomorphicExp_add (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions s d U) :
    holomorphicExp s d U (f + g) = holomorphicExp s d U f * holomorphicExp s d U g := by
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_add _ _

/-- The exponential is invertible, with inverse the exponential of the negative function. -/
def holomorphicExpUnit (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U) : (OpenHolomorphicFunctions s d U)ˣ where
  val := holomorphicExp s d U f
  inv := holomorphicExp s d U (-f)
  val_inv := by rw [← holomorphicExp_add, add_neg_cancel, holomorphicExp_zero]
  inv_val := by rw [← holomorphicExp_add, neg_add_cancel, holomorphicExp_zero]

@[simp]
theorem holomorphicExpUnit_zero (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) :
    holomorphicExpUnit s d U 0 = 1 := Units.ext (holomorphicExp_zero s d U)

@[simp]
theorem holomorphicExpUnit_add (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f g : OpenHolomorphicFunctions s d U) :
    holomorphicExpUnit s d U (f + g) = holomorphicExpUnit s d U f * holomorphicExpUnit s d U g :=
  Units.ext (holomorphicExp_add s d U f g)

@[simp]
theorem holomorphicRestrictionAlgHom_exp
    {U V : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ} (i : U ⟶ V)
    (f : OpenHolomorphicFunctions s d U) :
    holomorphicRestrictionAlgHom s d i (holomorphicExp s d U f) =
      holomorphicExp s d V (holomorphicRestrictionAlgHom s d i f) := rfl

@[simp]
theorem holomorphicRestrictionAlgHom_expUnit
    {U V : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ} (i : U ⟶ V)
    (f : OpenHolomorphicFunctions s d U) :
    Units.map (holomorphicRestrictionAlgHom s d i).toMonoidHom (holomorphicExpUnit s d U f) =
      holomorphicExpUnit s d V (holomorphicRestrictionAlgHom s d i f) := rfl

/-- The exponential chain rule in any fixed algebraically constructed analytic chart. -/
theorem chartSectionDifferential_exp
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) (z : ComplexPoint X s)
    (f : OpenHolomorphicFunctions s d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain s d U z) :
    chartSectionDifferential s d U z (holomorphicExp s d U f) y =
      Complex.exp (chartSection s d U z f y) • chartSectionDifferential s d U z f y := by
  have hEq : Set.EqOn (chartSection s d U z (holomorphicExp s d U f))
      (fun y => Complex.exp (chartSection s d U z f y)) (chartSectionDomain s d U z) := by
    intro w hw
    simp only [chartSection_apply_of_mem s d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact ((chartSection_contDiffWithinAt s d U z f hy).differentiableWithinAt
    (by simp)).hasFDerivWithinAt.cexp.fderivWithin
      ((isOpen_chartSectionDomain s d U z).uniqueDiffWithinAt hy)

/-- Equality of raw forms in every chart gives equality in the analytic quotient. -/
theorem holomorphicForm_mkQ_eq_of_chartEvaluation_eq
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) (p : ℕ)
    (a b : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions s d U) p)
    (h : ∀ z y, y ∈ chartSectionDomain s d U z →
      chartRawEvaluation s d U z p a y = chartRawEvaluation s d U z p b y) :
    (holomorphicFormRelations s d U p).mkQ a =
      (holomorphicFormRelations s d U p).mkQ b := by
  apply (Submodule.Quotient.eq (holomorphicFormRelations s d U p)).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
    restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  apply (mem_chartEvaluationKernel_iff s d V p _).2
  intro z y hy
  rw [chartRawEvaluation_rawRestriction s d i z p (a - b) hy,
    map_sub, Pi.sub_apply, sub_eq_zero]
  exact h z y ⟨hy.1, leOfHom i.unop hy.2⟩

/-- The analytic identity `dlog(exp f) = df` in the actual holomorphic-form quotient. -/
theorem holomorphicDlog_exp
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ)
    (f : OpenHolomorphicFunctions s d U) :
    holomorphicLogarithmicForm s d U 1 (fun _ => holomorphicExpUnit s d U f) =
      algebraicFormToHolomorphicForm s d U 1
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions s d U) 1 1 (fun _ => f)) := by
  simp only [holomorphicLogarithmicForm, Algebra.DeRham.logarithmicForm,
    Fin.prod_univ_one]
  change (holomorphicFormRelations s d U 1).mkQ
      (Finsupp.single (holomorphicExp s d U (-f), fun _ => holomorphicExp s d U f) 1) =
    (holomorphicFormRelations s d U 1).mkQ (Finsupp.single (1, fun _ => f) 1)
  apply holomorphicForm_mkQ_eq_of_chartEvaluation_eq
  intro z y hy
  simp only [chartRawEvaluation_single, one_smul, chartGeneratorEvaluation]
  rw [chartSectionDifferential_exp s d U z f hy]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_eq_det,
    Matrix.det_fin_one, Matrix.of_apply, smul_apply,
    smul_eq_mul, chartSection_apply_of_mem s d U z _ hy]
  change Complex.exp (-f.1 _) * (Complex.exp (f.1 _) * _) = 1 * _
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Holomorphic functions with only their additive group retained. -/
def holomorphicAdditiveFunctionPresheaf :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  holomorphicFunctionPresheaf s d ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat

/-- The additive sheaf underlying holomorphic functions. -/
def holomorphicAdditiveFunctionSheaf :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
      (holomorphicFunctionSheaf s d)

/-- Pointwise exponential as a morphism to the additive presentation of holomorphic units. -/
def holomorphicExpPresheaf :
    holomorphicAdditiveFunctionPresheaf s d ⟶ holomorphicUnitsPresheaf s d where
  app U := AddCommGrpCat.ofHom {
    toFun f := Additive.ofMul (holomorphicExpUnit s d U f)
    map_zero' := holomorphicExpUnit_zero s d U
    map_add' f g := holomorphicExpUnit_add s d U f g }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    exact (holomorphicRestrictionAlgHom_expUnit s d i f).symm

/-- The exponential morphism of actual analytic sheaves. -/
def holomorphicExpSheaf :
    holomorphicAdditiveFunctionSheaf s d ⟶ holomorphicUnitsSheaf s d :=
  ⟨holomorphicExpPresheaf s d⟩

/-- A holomorphic function regarded as a holomorphic zero-form. -/
def holomorphicFunctionToZeroFormPresheaf :
    holomorphicAdditiveFunctionPresheaf s d ⟶ holomorphicDeRhamPresheaf s d 0 where
  app U := AddCommGrpCat.ofHom {
    toFun f := algebraicFormToHolomorphicForm s d U 0
      (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions s d U) 0 f Fin.elim0)
    map_zero' := by rw [Algebra.DeRham.mk_coeff_zero, map_zero]
    map_add' f g := by rw [Algebra.DeRham.mk_coeff_add, map_add] }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    change algebraicFormToHolomorphicForm s d V 0
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions s d V) 0
          (holomorphicRestrictionAlgHom s d i f) Fin.elim0) =
      holomorphicFormRestriction s d i 0
        (algebraicFormToHolomorphicForm s d U 0
          (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions s d U) 0 f Fin.elim0))
    rw [holomorphicFormRestriction_algebraicFormToHolomorphicForm, Algebra.DeRham.map_mk]
    congr 2
    exact funext fun j => Fin.elim0 j

/-- The analytic identity `dlog ∘ exp = d`, now as an equality of presheaf morphisms. -/
theorem holomorphicExpPresheaf_comp_dlog :
    holomorphicExpPresheaf s d ≫ holomorphicDlogPresheaf s d =
      holomorphicFunctionToZeroFormPresheaf s d ≫ holomorphicDeRhamDifferential s d 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  change holomorphicLogarithmicForm s d U 1 (fun _ => holomorphicExpUnit s d U f) =
    holomorphicFormDifferential s d U 0
      (algebraicFormToHolomorphicForm s d U 0
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions s d U) 0 f Fin.elim0))
  rw [holomorphicDlog_exp, holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.differential_mk]
  congr 2
  funext j
  exact Fin.cases rfl (fun i => Fin.elim0 i) j

/-- Functions as sections of the sheafified zero-forms. -/
def holomorphicFunctionToZeroFormSheaf :
    holomorphicAdditiveFunctionSheaf s d ⟶ holomorphicDeRhamSheaf s d 0 :=
  ⟨holomorphicFunctionToZeroFormPresheaf s d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
      (holomorphicDeRhamPresheaf s d 0)⟩

/-- The exponential and de Rham differentials form a commutative square of actual sheaves. -/
@[reassoc]
theorem holomorphicExpSheaf_comp_dlog :
    holomorphicExpSheaf s d ≫ holomorphicDlogSheaf s d =
      holomorphicFunctionToZeroFormSheaf s d ≫ holomorphicDeRhamSheafDifferential s d 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  change holomorphicExpPresheaf s d ≫ holomorphicDlogPresheaf s d ≫
      toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) _ =
    holomorphicFunctionToZeroFormPresheaf s d ≫ toSheafify _ _ ≫
      sheafifyMap _ (holomorphicDeRhamDifferential s d 0)
  rw [← toSheafify_naturality, ← Category.assoc, ← Category.assoc,
    holomorphicExpPresheaf_comp_dlog]

end AlgebraicGeometry.ComplexPoint
