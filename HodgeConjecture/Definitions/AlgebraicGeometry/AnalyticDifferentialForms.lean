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

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic
public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Analytic differential forms

This file constructs analytic differential forms from holomorphic functions and their actual
manifold derivatives. A raw form is evaluated pointwise as an alternating continuous multilinear
map. We quotient raw forms by the identities detected after every restriction and close those
identities under the exterior derivative. This enforces analytic identities such as the chain
rule, rather than only the algebraic identities of Kahler differentials.

In degrees above the complex dimension the evaluation target is zero, so the resulting forms
vanish.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

def wedgeCovectors (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (p : ℕ) → (Fin p → E →L[ℂ] ℂ) → E [⋀^Fin p]→L[ℂ] ℂ
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) 1
  | p + 1, L => ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousLinearMap.smulRight (L 0) (wedgeCovectors E p (fun i => L i.succ)))

/-- Evaluation of a wedge of covectors is the determinant of their pairing matrix. -/
lemma wedgeCovectors_apply_eq_det (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (v : Fin p → E),
      wedgeCovectors E p L v = Matrix.det
        (Matrix.of (fun i j ↦ L i (v j))) := by
  intro p
  induction p with
  | zero =>
      intro L v
      simp [wedgeCovectors]
  | succ p ih =>
      intro L v
      rw [wedgeCovectors, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ContinuousLinearMap.smulRight_apply, Matrix.of_apply,
        zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [ih, mul_assoc]
      congr 2

/-- The wedge construction is additive in each covector. -/
lemma wedgeCovectors_update_add (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (a b : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (a + b)) =
      wedgeCovectors E p (Function.update L i a) +
        wedgeCovectors E p (Function.update L i b) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousAlternatingMap.add_apply]
  simp only [wedgeCovectors_apply_eq_det]
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.of (fun k j ↦ L k (v j))
  have hAdd : Matrix.of (fun k j ↦ (Function.update L i (a + b)) k (v j)) =
      A.updateRow i (fun j ↦ a (v j) + b (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have ha : Matrix.of (fun k j ↦ (Function.update L i a) k (v j)) =
      A.updateRow i (fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have hb : Matrix.of (fun k j ↦ (Function.update L i b) k (v j)) =
      A.updateRow i (fun j ↦ b (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  rw [hAdd, ha, hb]
  exact Matrix.det_updateRow_add A i _ _

/-- The wedge construction is homogeneous in each covector. -/
lemma wedgeCovectors_update_smul (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (c : ℂ) (a : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (c • a)) =
      c • wedgeCovectors E p (Function.update L i a) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousAlternatingMap.smul_apply]
  simp only [wedgeCovectors_apply_eq_det]
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.of (fun k j ↦ L k (v j))
  have hsmul : Matrix.of (fun k j ↦ (Function.update L i (c • a)) k (v j)) =
      A.updateRow i (c • fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  have ha : Matrix.of (fun k j ↦ (Function.update L i a) k (v j)) =
      A.updateRow i (fun j ↦ a (v j)) := by
    ext k j
    by_cases h : k = i <;> simp [A, h]
  rw [hsmul, ha, Matrix.det_updateRow_smul]
  simp

/-- A wedge with two equal covectors vanishes. -/
lemma wedgeCovectors_eq_zero_of_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i j : Fin p)
    (h : L i = L j) (hne : i ≠ j) :
    wedgeCovectors E p L = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det]
  apply Matrix.det_zero_of_row_eq hne
  ext k
  simp [h]

/-- A wedge containing the zero covector vanishes. -/
lemma wedgeCovectors_update_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) :
    wedgeCovectors E p (Function.update L i 0) = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det]
  refine Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ ?_
  simp

/-- The standard constant volume form on `ℂ^p`. -/
def standardVolumeForm (p : ℕ) :
    (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  wedgeCovectors (Fin p → ℂ) p
    (fun i ↦ ContinuousLinearMap.proj i)

/-- A wedge of derivatives is the pullback of the standard constant volume form. -/
lemma wedgeFDerivWithin_eq_standardVolumeForm_comp
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hf : ∀ i, DifferentiableWithinAt ℂ (f i) s x)
    (hs : UniqueDiffWithinAt ℂ s x) :
    wedgeCovectors E p (fun i ↦ fderivWithin ℂ (f i) s x) =
      (standardVolumeForm p).compContinuousLinearMap
        (fderivWithin ℂ (fun y i ↦ f i y) s x) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    standardVolumeForm, wedgeCovectors_apply_eq_det]
  congr 1
  ext i j
  rw [fderivWithin_pi hf hs]
  simp

/-- A wedge of differentials of scalar functions, all differentiated within the same set. -/
def exactWedgeWithin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) :
    E → E [⋀^Fin p]→L[ℂ] ℂ :=
  fun x ↦ wedgeCovectors E p (fun i ↦ fderivWithin ℂ (f i) s x)

/-- A wedge of exact one-forms is closed. The proof identifies it with the pullback of the
constant volume form and applies naturality of the exterior derivative. -/
lemma extDerivWithin_exactWedgeWithin_eq_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    extDerivWithin (exactWedgeWithin E p f s) s x = 0 := by
  let F : E → (Fin p → ℂ) := fun y i ↦ f i y
  let η : (Fin p → ℂ) → (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
    fun _ ↦ standardVolumeForm p
  have hF : ContDiffWithinAt ℂ ω F s x := contDiffWithinAt_pi.2 fun i ↦ hf i x hx
  have hEq : Set.EqOn (exactWedgeWithin E p f s)
      (fun y ↦ (η (F y)).compContinuousLinearMap
        (fderivWithin ℂ F s y)) s := by
    intro y hy
    exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s y
      (fun i ↦ (hf i y hy).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hy)
  rw [extDerivWithin_congr' hEq hx]
  rw [extDerivWithin_pullback
    (hω := differentiableAt_const (x := F x) (standardVolumeForm p) |>.differentiableWithinAt)
    (hf := hF) (hr := by simp) (hs := hs.uniqueDiffOn)
    (hxc := by simpa [hs.interior_eq] using (show x ∈ closure s from subset_closure hx))
    (hxs := hx) (hst := Set.mapsTo_univ F s)]
  have hη : extDerivWithin η Set.univ (F x) = 0 := by
    rw [extDerivWithin, show fderivWithin ℂ η Set.univ (F x) = 0 from
      congrFun (fderivWithin_const (𝕜 := ℂ) (E := Fin p → ℂ)
        (s := Set.univ) (standardVolumeForm p)) (F x)]
    exact map_zero _
  rw [hη]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma exactWedgeWithin_differentiableWithinAt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    DifferentiableWithinAt ℂ (exactWedgeWithin E p f s) s x := by
  let F : E → (Fin p → ℂ) := fun y i ↦ f i y
  let η : (Fin p → ℂ) → (Fin p → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
    fun _ ↦ standardVolumeForm p
  have hF : ContDiffWithinAt ℂ ω F s x := contDiffWithinAt_pi.2 fun i ↦ hf i x hx
  have hDF : DifferentiableWithinAt ℂ (fderivWithin ℂ F s) s x :=
    (hF.fderivWithin_right (m := 1) hs.uniqueDiffOn (by simp) hx).differentiableWithinAt
      one_ne_zero
  have hPull : DifferentiableWithinAt ℂ
      (fun y ↦ (η (F y)).compContinuousLinearMap (fderivWithin ℂ F s y)) s x :=
    DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
      (differentiableWithinAt_const (c := standardVolumeForm p)) hDF
  apply hPull.congr
  · intro y hy
    exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s y
      (fun i ↦ (hf i y hy).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hy)
  · exact wedgeFDerivWithin_eq_standardVolumeForm_comp E p f s x
      (fun i ↦ (hf i x hx).differentiableWithinAt (by simp))
      (hs.uniqueDiffWithinAt hx)

/-- Exterior differentiation of `a · df₁ ∧ ⋯ ∧ dfₚ` gives
`da ∧ df₁ ∧ ⋯ ∧ dfₚ`. -/
lemma extDerivWithin_smul_exactWedgeWithin
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (a : E → ℂ) (f : Fin p → E → ℂ) (s : Set E) (x : E)
    (hs : IsOpen s) (hx : x ∈ s) (ha : ContDiffOn ℂ ω a s)
    (hf : ∀ i, ContDiffOn ℂ ω (f i) s) :
    extDerivWithin (fun y ↦ a y • exactWedgeWithin E p f s y) s x =
      wedgeCovectors E (p + 1)
        (Fin.cases (fderivWithin ℂ a s x)
          (fun i ↦ fderivWithin ℂ (f i) s x)) := by
  rw [extDerivWithin, fderivWithin_fun_smul
    (hs.uniqueDiffWithinAt hx)
    ((ha x hx).differentiableWithinAt (by simp))
    (exactWedgeWithin_differentiableWithinAt E p f s x hs hx hf),
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  change a x • extDerivWithin (exactWedgeWithin E p f s) s x + _ = _
  rw [extDerivWithin_exactWedgeWithin_eq_zero E p f s x hs hx hf, smul_zero, zero_add]
  simp [exactWedgeWithin, wedgeCovectors]

noncomputable instance holomorphicFunctionPresheafAlgebra
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Algebra ℂ ((holomorphicFunctionPresheaf X d).obj U) := by
  change Algebra ℂ
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯
  infer_instance

/-- Restriction of holomorphic functions as an algebra homomorphism over the constants. -/
def holomorphicRestrictionAlgHom [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) :
    ((holomorphicFunctionPresheaf X d).obj U : Type) →ₐ[ℂ]
      ((holomorphicFunctionPresheaf X d).obj V : Type) where
  toRingHom := ((holomorphicFunctionSheaf X d).presheaf.map i).hom
  commutes' _ := rfl

@[simp] lemma holomorphicRestrictionAlgHom_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    holomorphicRestrictionAlgHom X d (𝟙 U) = AlgHom.id ℂ _ := by
  ext f
  rfl

@[simp] lemma holomorphicRestrictionAlgHom_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    holomorphicRestrictionAlgHom X d (i ≫ j) =
      (holomorphicRestrictionAlgHom X d j).comp
        (holomorphicRestrictionAlgHom X d i) := by
  ext f
  rfl

abbrev OpenHolomorphicFunctions [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :=
  ((holomorphicFunctionPresheaf X d).obj U : Type)

/-- The part of a fixed chart target whose inverse image belongs to `U`. -/
def chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    Set (Fin d → ℂ) :=
  (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target ∩
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm ⁻¹'
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X))

lemma isOpen_chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    IsOpen (chartSectionDomain X d U z) := by
  simpa [chartSectionDomain, extChartAt_target, extChartAt_coe_symm] using
    (chartAt (Fin d → ℂ) z).isOpen_inter_preimage_symm
      (Opposite.unop U).isOpen

/-- An arbitrary total extension of a section from its open domain. Its values outside the
domain play no role in derivatives taken within that domain. -/
def extendedSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f : OpenHolomorphicFunctions X d U) :
    ComplexPoint X → ℂ :=
  Function.extend Subtype.val f.1 0

lemma extendedSection_contMDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f : OpenHolomorphicFunctions X d U) {x : ComplexPoint X}
    (hx : x ∈ (Opposite.unop U : Opens (ComplexPoint X))) :
    ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection X d U f)
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X)) x := by
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff
    (U := (Opposite.unop U : Opens (ComplexPoint X)))
    (x := ⟨x, hx⟩)).mp
  simpa only [extendedSection, Subtype.val_injective.extend_apply] using
    (holomorphicFunctionSheaf_section_analytic X d f).contMDiffAt
      (x := ⟨x, hx⟩)

/-- The expression of a holomorphic section in one fixed chart. -/
def chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) : (Fin d → ℂ) → ℂ :=
  extendedSection X d U f ∘
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm

lemma chartSection_contDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    ContDiffWithinAt ℂ ω (chartSection X d U z f)
      (chartSectionDomain X d U z) y := by
  have hsymm : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (chartSectionDomain X d U z) y := by
    exact (contMDiffOn_extChartAt_symm
      (I := modelWithCornersSelf ℂ (Fin d → ℂ)) z y hy.1).mono Set.inter_subset_left
  have hext : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection X d U f)
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X))
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) :=
    extendedSection_contMDiffWithinAt X d U f hy.2
  exact (hext.comp y hsymm (fun _ h ↦ h.2)).contDiffWithinAt

lemma chartSection_contDiffOn [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    ContDiffOn ℂ ω (chartSection X d U z f)
      (chartSectionDomain X d U z) :=
  fun _ hy ↦ chartSection_contDiffWithinAt X d U z f hy

@[simp] lemma chartSection_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z f y =
      f.1 ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y, hy.2⟩ := by
  change Function.extend Subtype.val f.1 0
      (Subtype.val ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y,
        hy.2⟩) = _
  rw [Subtype.val_injective.extend_apply]

/-- The derivative of a section in one fixed chart. -/
def chartSectionDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) (y : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  fderivWithin ℂ (chartSection X d U z f)
    (chartSectionDomain X d U z) y

lemma chartSectionDifferential_add [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f g : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (f + g) y =
      chartSectionDifferential X d U z f y +
        chartSectionDifferential X d U z g y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (f + g))
      (chartSection X d U z f + chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.add_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_add ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_smul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (c : ℂ)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (c • f) y =
      c • chartSectionDifferential X d U z f y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (c • f))
      (c • chartSection X d U z f) S := by
    intro w hw
    simp only [Pi.smul_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_const_smul_field c
    ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)

lemma chartSectionDifferential_mul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f g : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (f * g) y =
      chartSection X d U z f y • chartSectionDifferential X d U z g y +
        chartSection X d U z g y •
          chartSectionDifferential X d U z f y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (f * g))
      (chartSection X d U z f * chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.mul_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_mul ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_algebraMap [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
      (algebraMap ℂ (OpenHolomorphicFunctions X d U) c) y = 0 := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn
      (chartSection X d U z
        (algebraMap ℂ (OpenHolomorphicFunctions X d U) c))
      (fun _ ↦ c) S := by
    intro w hw
    simp only [chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact congrFun
    (fderivWithin_const (𝕜 := ℂ) (E := Fin d → ℂ) (s := S) c) y

/-- Evaluation of a generator in one fixed coordinate chart. -/
def chartGeneratorEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ) :
    Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p →
      (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  fun g y ↦ chartSection X d U z g.1 y •
    wedgeCovectors (Fin d → ℂ) p
      (fun i ↦ chartSectionDifferential X d U z (g.2 i) y)

/-- Evaluation of a raw form in one fixed coordinate chart. -/
def chartRawEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      ((Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  Finsupp.linearCombination ℂ (chartGeneratorEvaluation X d U z p)

@[simp] lemma chartRawEvaluation_single [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p)
    (c : ℂ) :
    chartRawEvaluation X d U z p (Finsupp.single g c) =
      c • chartGeneratorEvaluation X d U z p g := by
  simp [chartRawEvaluation]

/-- Every defining Kähler relation evaluates to zero in each fixed chart, at every point of the
coordinate domain. -/
lemma chartRawEvaluation_relationValue [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (r : Algebra.DeRham.Relation ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartRawEvaluation X d U z p
      (Algebra.DeRham.relationValue ℂ _ p r) y = 0 := by
  have hupdate (v : Fin p → OpenHolomorphicFunctions X d U) (i : Fin p)
      (q : OpenHolomorphicFunctions X d U) :
      (fun j ↦ chartSectionDifferential X d U z (Function.update v i q j) y) =
        Function.update (fun j ↦ chartSectionDifferential X d U z (v j) y) i
          (chartSectionDifferential X d U z q y) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  cases r with
  | coeffAdd a b v =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      rw [show chartSection X d U z (a + b) y =
        chartSection X d U z a y + chartSection X d U z b y by
          simp only [chartSection_apply_of_mem X d U z _ hy]
          rfl]
      module
  | coeffSMul c a v =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, map_smul, Pi.sub_apply, Pi.smul_apply,
        chartGeneratorEvaluation]
      rw [show chartSection X d U z (c • a) y =
        c * chartSection X d U z a y by
          simp only [chartSection_apply_of_mem X d U z _ hy]
          rfl]
      simp [mul_smul]
  | diffAdd a₀ v i a b =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      rw [hupdate, hupdate, hupdate,
        chartSectionDifferential_add X d U z a b hy,
        wedgeCovectors_update_add]
      module
  | diffSMul a₀ v i c a =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, map_smul, Pi.sub_apply, Pi.smul_apply,
        chartGeneratorEvaluation]
      rw [hupdate, hupdate,
        chartSectionDifferential_smul X d U z c a hy,
        wedgeCovectors_update_smul]
      module
  | diffMul a₀ v i a b =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      rw [hupdate, hupdate, hupdate]
      rw [show chartSection X d U z (a₀ * a) y =
          chartSection X d U z a₀ y * chartSection X d U z a y by
            simp only [chartSection_apply_of_mem X d U z _ hy]
            rfl,
        show chartSection X d U z (a₀ * b) y =
          chartSection X d U z a₀ y * chartSection X d U z b y by
            simp only [chartSection_apply_of_mem X d U z _ hy]
            rfl]
      change chartSection X d U z a₀ y • _ -
        (chartSection X d U z a₀ y *
          chartSection X d U z a y) • _ -
        (chartSection X d U z a₀ y *
          chartSection X d U z b y) • _ =
        (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
      rw [chartSectionDifferential_mul X d U z a b hy,
        wedgeCovectors_update_add, wedgeCovectors_update_smul,
        wedgeCovectors_update_smul]
      module
  | diffConst a₀ v i c =>
      simp only [Algebra.DeRham.relationValue, chartRawEvaluation_single, one_smul,
        chartGeneratorEvaluation]
      rw [hupdate, chartSectionDifferential_algebraMap X d U z c hy,
        wedgeCovectors_update_zero]
      refine ContinuousAlternatingMap.ext fun w ↦ ?_
      simp
  | alt a₀ v i j h hne =>
      simp only [Algebra.DeRham.relationValue, chartRawEvaluation_single, one_smul,
        chartGeneratorEvaluation]
      have heq : chartSectionDifferential X d U z (v i) y =
          chartSectionDifferential X d U z (v j) y := by rw [h]
      rw [wedgeCovectors_eq_zero_of_eq (Fin d → ℂ) p _ i j heq hne]
      refine ContinuousAlternatingMap.ext fun w ↦ ?_
      simp

/-- Exterior differentiation of a generator in fixed coordinates agrees with the syntactic de
Rham differential. -/
lemma extDerivWithin_chartGeneratorEvaluation
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    extDerivWithin (chartGeneratorEvaluation X d U z p g)
        (chartSectionDomain X d U z) y =
      chartGeneratorEvaluation X d U z (p + 1)
        (Algebra.DeRham.nextGenerator _ g) y := by
  have h := extDerivWithin_smul_exactWedgeWithin (Fin d → ℂ) p
    (chartSection X d U z g.1)
    (fun i ↦ chartSection X d U z (g.2 i))
    (chartSectionDomain X d U z) y
    (isOpen_chartSectionDomain X d U z) hy
    (chartSection_contDiffOn X d U z g.1)
    (fun i ↦ chartSection_contDiffOn X d U z (g.2 i))
  rw [show chartGeneratorEvaluation X d U z p g =
      (fun w ↦ chartSection X d U z g.1 w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection X d U z (g.2 i))
          (chartSectionDomain X d U z) w) by
        rfl]
  rw [h]
  simp only [chartGeneratorEvaluation, Algebra.DeRham.nextGenerator,
    chartSectionDifferential]
  rw [show chartSection X d U z (1 : OpenHolomorphicFunctions X d U) y =
      1 by
        simp only [chartSection_apply_of_mem X d U z _ hy]
        rfl, one_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

lemma chartGeneratorEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (chartGeneratorEvaluation X d U z p g)
      (chartSectionDomain X d U z) y := by
  rw [show chartGeneratorEvaluation X d U z p g =
      (fun w ↦ chartSection X d U z g.1 w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection X d U z (g.2 i))
          (chartSectionDomain X d U z) w) by
        rfl]
  exact DifferentiableWithinAt.smul
    ((chartSection_contDiffWithinAt X d U z g.1 hy).differentiableWithinAt (by simp))
    (exactWedgeWithin_differentiableWithinAt (Fin d → ℂ) p
      (fun i ↦ chartSection X d U z (g.2 i))
      (chartSectionDomain X d U z) y
      (isOpen_chartSectionDomain X d U z) hy
      (fun i ↦ chartSection_contDiffOn X d U z (g.2 i)))

lemma chartRawEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (chartRawEvaluation X d U z p x)
      (chartSectionDomain X d U z) y := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [map_zero]
      exact differentiableWithinAt_const (c :=
        (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ))
  | single_add g c x hg hc ih =>
      rw [map_add, chartRawEvaluation_single]
      exact ((chartGeneratorEvaluation_differentiableWithinAt X d U z p g hy).const_smul
        c).add ih

/-- Fixed-chart evaluation intertwines the syntactic and analytic exterior derivatives. -/
lemma chartRawEvaluation_rawDifferential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartRawEvaluation X d U z (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions X d U) p x) y =
      extDerivWithin (chartRawEvaluation X d U z p x)
        (chartSectionDomain X d U z) y := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [map_zero, map_zero]
      symm
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        fderivWithin_zero]
  | single_add g c x hg hc ih =>
      rw [map_add, Algebra.DeRham.rawDifferential_single, map_add,
        chartRawEvaluation_single]
      have hEval : chartRawEvaluation X d U z p (Finsupp.single g c + x) =
          c • chartGeneratorEvaluation X d U z p g +
            chartRawEvaluation X d U z p x := by
        rw [map_add, chartRawEvaluation_single]
      rw [hEval, Pi.add_apply,
        extDerivWithin_add
          ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
          ((chartGeneratorEvaluation_differentiableWithinAt X d U z p g hy).const_smul c)
          (chartRawEvaluation_differentiableWithinAt X d U z p x hy),
        extDerivWithin_smul c _
          ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy),
        extDerivWithin_chartGeneratorEvaluation X d U z p g hy,
        ih]
      simp only [Pi.smul_apply]

/-- Evaluation at one point of one fixed coordinate chart. -/
def chartEvaluationAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ) (y : Fin d → ℂ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ where
  toFun x := chartRawEvaluation X d U z p x y
  map_add' a b := by rw [map_add, Pi.add_apply]
  map_smul' c a := by
    rw [map_smul, Pi.smul_apply]
    rfl

/-- Raw forms that vanish in every fixed chart at every point of its coordinate domain. -/
def chartEvaluationKernel [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions X d U) p) :=
  ⨅ (z : ComplexPoint X), ⨅ (y : Fin d → ℂ),
    ⨅ (_ : y ∈ chartSectionDomain X d U z),
      LinearMap.ker (chartEvaluationAt X d U z p y)

lemma mem_chartEvaluationKernel_iff [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p) :
    x ∈ chartEvaluationKernel X d U p ↔
      ∀ z y, y ∈ chartSectionDomain X d U z →
        chartRawEvaluation X d U z p x y = 0 := by
  simp only [chartEvaluationKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    chartEvaluationAt]
  rfl

/-- The ordinary Kähler relations are genuine coordinate identities. -/
lemma standardRelations_le_chartEvaluationKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.standardRelations ℂ (OpenHolomorphicFunctions X d U) p ≤
      chartEvaluationKernel X d U p := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨r, rfl⟩
  exact (mem_chartEvaluationKernel_iff X d U p _).2 fun z y hy ↦
    chartRawEvaluation_relationValue X d U z p r hy

/-- Coordinate-zero identities remain coordinate-zero after exterior differentiation. -/
lemma rawDifferential_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ chartEvaluationKernel X d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p x ∈
      chartEvaluationKernel X d U (p + 1) := by
  have hx' := (mem_chartEvaluationKernel_iff X d U p x).1 hx
  refine (mem_chartEvaluationKernel_iff X d U (p + 1) _).2 fun z y hy ↦ ?_
  rw [chartRawEvaluation_rawDifferential X d U z p x hy]
  have hEq : Set.EqOn (chartRawEvaluation X d U z p x) 0
      (chartSectionDomain X d U z) := fun w hw ↦ hx' z w hw
  rw [extDerivWithin_congr' hEq hy, extDerivWithin]
  have hzero := congrFun
    (fderivWithin_zero (𝕜 := ℂ) (E := Fin d → ℂ)
      (F := (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
      (s := chartSectionDomain X d U z)) y
  rw [hzero]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]

lemma chartEvaluationKernel_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : chartEvaluationKernel X d U p = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  refine (mem_chartEvaluationKernel_iff X d U p x).2 fun z y hy ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_
  refine (chartRawEvaluation X d U z p x y).toAlternatingMap.map_linearDependent _ fun hli ↦ ?_
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  lia


def rawRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d V) p :=
  Algebra.DeRham.rawMap ℂ (holomorphicRestrictionAlgHom X d i) p

@[simp] lemma rawRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    rawRestriction X d (𝟙 U) p = LinearMap.id := by
  rw [rawRestriction, holomorphicRestrictionAlgHom_id,
    Algebra.DeRham.rawMap_id]

@[simp] lemma rawRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    rawRestriction X d (i ≫ j) p =
      (rawRestriction X d j p).comp (rawRestriction X d i p) := by
  rw [rawRestriction, rawRestriction, rawRestriction,
    holomorphicRestrictionAlgHom_comp, Algebra.DeRham.rawMap_comp]

def restrictionStableAnalyticKernel [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions X d U) p) :=
  ⨅ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ),
    ⨅ (i : U ⟶ V),
      (chartEvaluationKernel X d V p).comap
        (rawRestriction X d i p)

/-- Every standard Kähler relation remains evaluation-zero after every restriction. -/
lemma standardRelations_le_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.standardRelations ℂ (OpenHolomorphicFunctions X d U) p ≤
      restrictionStableAnalyticKernel X d U p := by
  intro x hx
  rw [restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  exact standardRelations_le_chartEvaluationKernel X d V p
    (Algebra.DeRham.rawMap_standardRelations ℂ (holomorphicRestrictionAlgHom X d i) p hx)

lemma rawRestriction_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ restrictionStableAnalyticKernel X d U p) :
    rawRestriction X d i p x ∈
      restrictionStableAnalyticKernel X d V p := by
  rw [restrictionStableAnalyticKernel] at hx ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  intro W j
  specialize hx W (i ≫ j)
  rwa [rawRestriction_comp, LinearMap.comp_apply] at hx

/-- Restriction-stable coordinate identities remain so after exterior differentiation. -/
lemma rawDifferential_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ restrictionStableAnalyticKernel X d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p x ∈
      restrictionStableAnalyticKernel X d U (p + 1) := by
  rw [restrictionStableAnalyticKernel] at hx ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  intro V i
  specialize hx V i
  rw [rawRestriction, Algebra.DeRham.rawMap_rawDifferential]
  exact rawDifferential_mem_chartEvaluationKernel X d V p hx

/-- Analytic identities and all their exterior derivatives. -/
def analyticRelations [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    (p : ℕ) → Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions X d U) p)
  | 0 => restrictionStableAnalyticKernel X d U 0
  | p + 1 => restrictionStableAnalyticKernel X d U (p + 1) ⊔
      (analyticRelations U p).map
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions X d U) p)

/-- Because analytic exterior differentiation preserves the fixed-chart evaluation kernel, the
recursive differential closure adds no extra relations. -/
lemma analyticRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) : ∀ p : ℕ,
    analyticRelations X d U p =
      restrictionStableAnalyticKernel X d U p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [analyticRelations, ih]
      refine sup_eq_left.mpr ?_
      rintro y ⟨x, hx, rfl⟩
      exact rawDifferential_mem_restrictionStableAnalyticKernel X d U p hx

/-- The differential closure of the standard Kähler relations is contained in the analytic
relations. -/
lemma algebraicRelations_le_analyticRelations [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) : ∀ p : ℕ,
    Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions X d U) p ≤
      analyticRelations X d U p := by
  intro p
  induction p with
  | zero =>
      exact standardRelations_le_restrictionStableAnalyticKernel X d U 0
  | succ p ih =>
      rw [Algebra.DeRham.relations, analyticRelations]
      apply sup_le
      · exact (standardRelations_le_restrictionStableAnalyticKernel X d U (p + 1)).trans
          le_sup_left
      · exact (Submodule.map_mono ih).trans le_sup_right

lemma rawDifferential_mem_analyticRelations [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ analyticRelations X d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p x ∈
      analyticRelations X d U (p + 1) := by
  rw [analyticRelations]
  exact (le_sup_right : (analyticRelations X d U p).map
    (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) p) ≤ _) ⟨x, hx, rfl⟩

lemma rawRestriction_mem_analyticRelations [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ analyticRelations X d U p) :
    rawRestriction X d i p x ∈ analyticRelations X d V p := by
  induction p with
  | zero =>
      exact rawRestriction_mem_restrictionStableAnalyticKernel X d i 0 hx
  | succ p ih =>
      rw [analyticRelations] at hx ⊢
      rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
      rw [map_add]
      apply Submodule.add_mem
      · exact (le_sup_left : restrictionStableAnalyticKernel X d V (p + 1) ≤ _)
          (rawRestriction_mem_restrictionStableAnalyticKernel X d i (p + 1) hy)
      · rcases hz with ⟨w, hw, rfl⟩
        rw [rawRestriction, Algebra.DeRham.rawMap_rawDifferential]
        apply (le_sup_right : (analyticRelations X d V p).map
          (Algebra.DeRham.rawDifferential ℂ
            (OpenHolomorphicFunctions X d V) p) ≤ _)
        exact ⟨rawRestriction X d i p w, ih hw, rfl⟩

/-- Relations for analytic de Rham forms: algebraic differential-form identities together with
all restriction-stable identities detected by actual complex derivatives. -/
def holomorphicFormRelations [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions X d U) p) :=
  Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions X d U) p ⊔
    analyticRelations X d U p

/-- Algebraic relations are already among the restriction-stable analytic relations and their
exterior derivatives. -/
lemma holomorphicFormRelations_eq_analyticRelations
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations X d U p =
      analyticRelations X d U p :=
  sup_eq_right.mpr (algebraicRelations_le_analyticRelations X d U p)

/-- Holomorphic forms are quotiented by exactly the identities that vanish in every fixed chart
after every restriction. -/
lemma holomorphicFormRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations X d U p =
      restrictionStableAnalyticKernel X d U p := by
  rw [holomorphicFormRelations_eq_analyticRelations,
    analyticRelations_eq_restrictionStableAnalyticKernel]

lemma holomorphicFormRelations_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : holomorphicFormRelations X d U p = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  apply (le_sup_right : analyticRelations X d U p ≤ _)
  induction p with
  | zero => lia
  | succ p ih =>
      rw [analyticRelations]
      apply (le_sup_left : restrictionStableAnalyticKernel X d U (p + 1) ≤ _)
      rw [restrictionStableAnalyticKernel]
      simp only [Submodule.mem_iInf, Submodule.mem_comap]
      intro V i
      rw [chartEvaluationKernel_eq_top_of_lt X d V hp]
      trivial

lemma rawDifferential_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ holomorphicFormRelations X d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p x ∈
      holomorphicFormRelations X d U (p + 1) := by
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
  rw [map_add]
  apply Submodule.add_mem
  · exact (le_sup_left : Algebra.DeRham.relations ℂ
      (OpenHolomorphicFunctions X d U) (p + 1) ≤ _)
      (Algebra.DeRham.rawDifferential_mem_relations ℂ
        (OpenHolomorphicFunctions X d U) p hy)
  · exact (le_sup_right : analyticRelations X d U (p + 1) ≤ _)
      (rawDifferential_mem_analyticRelations X d U p hz)

lemma rawRestriction_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p}
    (hx : x ∈ holomorphicFormRelations X d U p) :
    rawRestriction X d i p x ∈ holomorphicFormRelations X d V p := by
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
  rw [map_add]
  apply Submodule.add_mem
  · exact (le_sup_left : Algebra.DeRham.relations ℂ
      (OpenHolomorphicFunctions X d V) p ≤ _)
      (Algebra.DeRham.rawMap_relations ℂ
        (holomorphicRestrictionAlgHom X d i) p hy)
  · exact (le_sup_right : analyticRelations X d V p ≤ _)
      (rawRestriction_mem_analyticRelations X d i p hz)

abbrev HolomorphicForm [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :=
  Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p ⧸
    holomorphicFormRelations X d U p

lemma holomorphicForm_eq_zero_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) (x : HolomorphicForm X d U p) : x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U p) x
  change Submodule.Quotient.mk x = 0
  rw [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_top_of_lt X d U hp]
  trivial

/-- The quotient map from algebraic Kähler forms to analytic differential forms. -/
def algebraicFormToHolomorphicForm [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      HolomorphicForm X d U p :=
  (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions X d U) p).liftQ
    (holomorphicFormRelations X d U p).mkQ (by
      intro x hx
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (le_sup_left : Algebra.DeRham.relations ℂ
        (OpenHolomorphicFunctions X d U) p ≤ _) hx)

/-- A complex constant regarded as an analytic differential zero-form. -/
def holomorphicFormOfConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    ℂ →ₗ[ℂ] HolomorphicForm X d U 0 :=
  (algebraicFormToHolomorphicForm X d U 0).comp
    (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U))

def holomorphicFormDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U (p + 1) :=
  (holomorphicFormRelations X d U p).liftQ
    ((holomorphicFormRelations X d U (p + 1)).mkQ.comp
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p)) (by
          intro x hx
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          exact rawDifferential_mem_holomorphicFormRelations X d U p hx)

def holomorphicFormRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d V p :=
  (holomorphicFormRelations X d U p).liftQ
    ((holomorphicFormRelations X d V p).mkQ.comp
      (rawRestriction X d i p)) (by
        intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact rawRestriction_mem_holomorphicFormRelations X d i p hx)

lemma holomorphicFormRestriction_algebraicFormToHolomorphicForm
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (x : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    holomorphicFormRestriction X d i p
        (algebraicFormToHolomorphicForm X d U p x) =
      algebraicFormToHolomorphicForm X d V p
        (Algebra.DeRham.map ℂ (holomorphicRestrictionAlgHom X d i) p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions X d U) p) x
  rfl

lemma holomorphicFormDifferential_algebraicFormToHolomorphicForm
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (x : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    holomorphicFormDifferential X d U p
        (algebraicFormToHolomorphicForm X d U p x) =
      algebraicFormToHolomorphicForm X d U (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions X d U) p) x
  rfl

@[simp] lemma holomorphicFormRestriction_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (c : ℂ) :
    holomorphicFormRestriction X d i 0
        (holomorphicFormOfConstant X d U c) =
      holomorphicFormOfConstant X d V c := by
  rw [holomorphicFormOfConstant, holomorphicFormOfConstant, LinearMap.comp_apply,
    holomorphicFormRestriction_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_ofConstant]
  rfl

@[simp] lemma holomorphicFormDifferential_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (c : ℂ) :
    holomorphicFormDifferential X d U 0
        (holomorphicFormOfConstant X d U c) = 0 := by
  rw [holomorphicFormOfConstant, LinearMap.comp_apply,
    holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.differential_ofConstant, map_zero]

lemma holomorphicFormDifferential_squared [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (x : HolomorphicForm X d U p) :
    holomorphicFormDifferential X d U (p + 1)
      (holomorphicFormDifferential X d U p x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U p) x
  change Submodule.Quotient.mk
    (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) (p + 1)
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d U) p x)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (le_sup_left : Algebra.DeRham.relations ℂ
    (OpenHolomorphicFunctions X d U) (p + 2) ≤ _)
  exact Algebra.DeRham.standardRelations_le_relations ℂ
    (OpenHolomorphicFunctions X d U) (p + 2)
    (Algebra.DeRham.rawDifferential_squared_mem_standardRelations ℂ
      (OpenHolomorphicFunctions X d U) p x)

lemma holomorphicFormRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (x : HolomorphicForm X d U p) :
    holomorphicFormRestriction X d i (p + 1)
        (holomorphicFormDifferential X d U p x) =
      holomorphicFormDifferential X d V p
        (holomorphicFormRestriction X d i p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U p) x
  change Submodule.Quotient.mk
      (rawRestriction X d i (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions X d U) p x)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d V) p
        (rawRestriction X d i p x))
  simp only [rawRestriction, Algebra.DeRham.rawMap_rawDifferential]

@[simp] lemma holomorphicFormRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRestriction X d (𝟙 U) p = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U p) x
  change Submodule.Quotient.mk (rawRestriction X d (𝟙 U) p x) =
    Submodule.Quotient.mk x
  rw [rawRestriction_id, LinearMap.id_apply]

@[simp] lemma holomorphicFormRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    holomorphicFormRestriction X d (i ≫ j) p =
      (holomorphicFormRestriction X d j p).comp
        (holomorphicFormRestriction X d i p) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U p) x
  change Submodule.Quotient.mk (rawRestriction X d (i ≫ j) p x) =
    Submodule.Quotient.mk
      (rawRestriction X d j p (rawRestriction X d i p x))
  rw [rawRestriction_comp, LinearMap.comp_apply]

end AlgebraicGeometry.ComplexPoint
