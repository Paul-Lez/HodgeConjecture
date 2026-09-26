/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Other.AlgebraicTopology.Sheaf.ConstantDegreeZero
public import Other.AlgebraicGeometry.Hodge.Filtration

/-!
# Degree-zero rational constant-sheaf cohomology

This file computes degree-zero rational constant-sheaf cohomology as the ordinary morphism
group from the constant integer sheaf to the constant rational sheaf. The computation first
undoes the extension from natural to integer degrees and then uses the theorem
`Abelian.Ext.homEquiv₀` that degree-zero Ext is ordinary Hom.

The explicit comparison sends the constant cohomology class of `q : ℚ` to the sheafification
of the additive map `n ↦ n q`. Thus later arguments about the cohomological unit can be reduced
to honest statements about the constant-sheaf functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- The source object of Mathlib's sheaf cohomology is the constant integer sheaf. -/
def uliftIntegerConstantSheafIso :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ)) ≅ 𝓒(↧(ComplexPoint X); ℤ) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).mapIso
    (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso

/-- Degree-zero rational constant-sheaf cohomology is ordinary Hom from integer constants to
rational constants. -/
def rationalCohomologyZeroEquivSheafHom :
    H^0(X; ℚ) ≃
      (𝓒(↧(ComplexPoint X); ℤ) ⟶ 𝓒(↧(ComplexPoint X); ℚ)) :=
  Abelian.Ext.homEquiv₀.trans ((uliftIntegerConstantSheafIso X).homCongr (Iso.refl _))

/-- The degree-zero comparison sends the constant class of `q` to the constant-sheaf morphism
induced by `n ↦ n q`. -/
@[simp] theorem rationalCohomologyZeroEquivSheafHom_class (q : ℚ) :
    rationalCohomologyZeroEquivSheafHom X
        (fieldCohomologyClass ℚ X q) =
      integerToFieldConstantSheaf ℚ X q := by
  have h : Abelian.Ext.homEquiv₀ (Abelian.Ext.mk₀
      (uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf ℚ X q)) =
      uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf ℚ X q :=
    (Abelian.Ext.mk₀_bijective _ _).injective (Abelian.Ext.mk₀_homEquiv₀_apply _)
  rw [rationalCohomologyZeroEquivSheafHom, Equiv.trans_apply, fieldCohomologyClass, h,
    Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  change (uliftIntegerConstantSheafIso X).inv ≫ (uliftIntegerConstantSheafIso X).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

/-- If the constant-sheaf functor is faithful, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective_of_constantSheaf_faithful
    [(TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).Faithful] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  intro a b hab
  have hs : integerToFieldConstantSheaf ℚ X a =
      integerToFieldConstantSheaf ℚ X b := by
    rw [← rationalCohomologyZeroEquivSheafHom_class,
      ← rationalCohomologyZeroEquivSheafHom_class, hab]
  unfold integerToFieldConstantSheaf at hs
  have hm := (TopCat.Sheaf.constantFunctor
    ↧(ComplexPoint X)).map_injective hs
  simpa using ConcreteCategory.congr_hom hm (1 : ℤ)

/-- On a nonempty analytic complex-point space, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective
    [Nonempty (ComplexPoint X)] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  let : (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).Faithful :=
    TopCat.constantSheaf_faithful_of_nonempty _
  exact rationalCohomologyClass_injective_of_constantSheaf_faithful X

/-- On a connected analytic complex-point space, every degree-zero rational cohomology class is
a constant class. -/
theorem rationalCohomologyClass_surjective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Surjective (fieldCohomologyClass ℚ X) := by
  intro α
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  let ff := TopCat.constantSheafFullyFaithfulOfConnected
    (TopCat.of (ComplexPoint X))
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  let e := rationalCohomologyZeroEquivSheafHom X
  obtain ⟨f, hf⟩ := F.map_surjective (e α)
  let q : ℚ := f (1 : ℤ)
  refine ⟨q, e.injective ?_⟩
  rw [rationalCohomologyZeroEquivSheafHom_class, ← hf]
  unfold integerToFieldConstantSheaf
  change F.map (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ q)) = F.map f
  congr 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n ↦ ?_)
  change n • q = f n
  rw [show n = n • (1 : ℤ) by simp, map_zsmul]
  simp [q]

/-- Constant rational classes give a bijection onto degree-zero cohomology of a connected
analytic complex-point space. -/
theorem rationalCohomologyClass_bijective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Bijective (fieldCohomologyClass ℚ X) := by
  let : Nonempty (ComplexPoint X) := inferInstance
  exact ⟨rationalCohomologyClass_injective X,
    rationalCohomologyClass_surjective X⟩

/-- On a connected analytic complex-point space, rational constants are linearly equivalent to
degree-zero rational cohomology. -/
def rationalCohomologyClassLinearEquiv
    [ConnectedSpace (ComplexPoint X)] :
    ℚ ≃ₗ[ℚ] H^0(X; ℚ) :=
  LinearEquiv.ofBijective (fieldCohomologyClassLinear ℚ X)
    (rationalCohomologyClass_bijective X)

/-- On a connected analytic complex-point space, the rational cohomology unit spans all of
degree-zero rational cohomology. -/
theorem span_rationalCohomologyUnit_eq_top
    [ConnectedSpace (ComplexPoint X)] :
    Submodule.span ℚ {fieldCohomologyUnit ℚ X} = ⊤ := by
  apply le_antisymm le_top
  intro α _
  obtain ⟨q, rfl⟩ := rationalCohomologyClass_surjective X α
  have hq : fieldCohomologyClass ℚ X q =
      q • fieldCohomologyUnit ℚ X := by
    simpa [fieldCohomologyUnit] using
      fieldCohomologyClass_mul ℚ X q 1
  rw [hq]
  exact Submodule.smul_mem _ q (Submodule.subset_span (Set.mem_singleton _))

/-- The degree-zero rational cohomology unit is nonzero on a nonempty analytic complex-point
space. -/
theorem rationalCohomologyUnit_ne_zero
    [Nonempty (ComplexPoint X)] :
    fieldCohomologyUnit ℚ X ≠ 0 := by
  intro h
  have h10 : fieldCohomologyClass ℚ X 1 =
      fieldCohomologyClass ℚ X 0 := by
    simpa [fieldCohomologyUnit] using h
  exact one_ne_zero (rationalCohomologyClass_injective X h10)

end AlgebraicGeometry.ComplexPoint
