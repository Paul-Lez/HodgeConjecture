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
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Analytic differential forms

This file constructs analytic differential forms from holomorphic functions and their actual
manifold derivatives. A raw form is evaluated pointwise as an alternating continuous multilinear
map. We quotient raw forms by the kernel of evaluation in every coordinate chart. These
identities are preserved by restriction and exterior differentiation. They include analytic
identities such as the chain rule.

In degrees above the complex dimension the evaluation target is zero, so the resulting forms
vanish.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

local instance analyticEvalTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

local instance analyticEvalChartedSpace [SmoothOfRelativeDimension d structureMap] :
    ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
  analyticChartedSpace structureMap d

local instance analyticEvalIsManifold [SmoothOfRelativeDimension d structureMap] :
    IsManifold (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (ComplexPoint X structureMap) :=
  isManifold_omega structureMap d

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
      apply Finset.sum_congr rfl
      intro j hj
      simp only [ContinuousLinearMap.smulRight_apply, Matrix.of_apply,
        zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [ih]
      rw [mul_assoc]
      congr 2

/-- The wedge construction is additive in each covector. -/
lemma wedgeCovectors_update_add (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (a b : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (a + b)) =
      wedgeCovectors E p (Function.update L i a) +
        wedgeCovectors E p (Function.update L i b) := by
  apply ContinuousAlternatingMap.ext
  intro v
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
  have hfun : (fun j ↦ a (v j) + b (v j)) =
      (fun j ↦ a (v j)) + (fun j ↦ b (v j)) := by
    funext j
    rfl
  rw [hfun]
  exact Matrix.det_updateRow_add A i _ _

/-- The wedge construction is homogeneous in each covector. -/
lemma wedgeCovectors_update_smul (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) (c : ℂ) (a : E →L[ℂ] ℂ) :
    wedgeCovectors E p (Function.update L i (c • a)) =
      c • wedgeCovectors E p (Function.update L i a) := by
  apply ContinuousAlternatingMap.ext
  intro v
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
  apply ContinuousAlternatingMap.ext
  intro v
  rw [wedgeCovectors_apply_eq_det]
  apply Matrix.det_zero_of_row_eq hne
  ext k
  simp [h]

/-- A wedge containing the zero covector vanishes. -/
lemma wedgeCovectors_update_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (L : Fin p → E →L[ℂ] ℂ) (i : Fin p) :
    wedgeCovectors E p (Function.update L i 0) = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [wedgeCovectors_apply_eq_det]
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
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
  apply ContinuousAlternatingMap.ext
  intro v
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
  have hF : ContDiffWithinAt ℂ ω F s x := by
    rw [contDiffWithinAt_pi]
    exact fun i ↦ hf i x hx
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
    rw [extDerivWithin]
    have hconst := congrFun
      (fderivWithin_const (𝕜 := ℂ) (E := Fin p → ℂ)
        (s := Set.univ) (standardVolumeForm p)) (F x)
    rw [show fderivWithin ℂ η Set.univ (F x) = 0 from hconst]
    exact map_zero _
  rw [hη]
  apply ContinuousAlternatingMap.ext
  intro v
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
  have hF : ContDiffWithinAt ℂ ω F s x := by
    rw [contDiffWithinAt_pi]
    exact fun i ↦ hf i x hx
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
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) :
    Algebra ℂ ((holomorphicFunctionPresheaf structureMap d).obj U) := by
  change Algebra ℂ
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X structureMap)); ℂ⟯
  infer_instance

/-- Restriction of holomorphic functions as an algebra homomorphism over the constants. -/
def holomorphicRestrictionAlgHom [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) :
    ((holomorphicFunctionPresheaf structureMap d).obj U : Type) →ₐ[ℂ]
      ((holomorphicFunctionPresheaf structureMap d).obj V : Type) where
  toRingHom := ((holomorphicFunctionSheaf structureMap d).presheaf.map i).hom
  commutes' _ := rfl

@[simp] lemma holomorphicRestrictionAlgHom_id [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) :
    holomorphicRestrictionAlgHom structureMap d (𝟙 U) = AlgHom.id ℂ _ := by
  ext f
  rfl

@[simp] lemma holomorphicRestrictionAlgHom_comp [SmoothOfRelativeDimension d structureMap]
    {U V W : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    holomorphicRestrictionAlgHom structureMap d (i ≫ j) =
      (holomorphicRestrictionAlgHom structureMap d j).comp
        (holomorphicRestrictionAlgHom structureMap d i) := by
  ext f
  rfl

abbrev OpenHolomorphicFunctions [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) :=
  ((holomorphicFunctionPresheaf structureMap d).obj U : Type)

/-- The part of a fixed chart target whose inverse image belongs to `U`. -/
def chartSectionDomain [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (z : ComplexPoint X structureMap) :
    Set (Fin d → ℂ) :=
  (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target ∩
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm ⁻¹'
      ((Opposite.unop U : Opens (ComplexPoint X structureMap)) :
        Set (ComplexPoint X structureMap))

lemma isOpen_chartSectionDomain [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (z : ComplexPoint X structureMap) :
    IsOpen (chartSectionDomain structureMap d U z) := by
  simpa [chartSectionDomain, extChartAt_target, extChartAt_coe_symm,
    analyticEvalChartedSpace, analyticChartedSpace] using
    (chartAt (Fin d → ℂ) z).isOpen_inter_preimage_symm
      (Opposite.unop U).isOpen

/-- An arbitrary total extension of a section from its open domain. Its values outside the
domain play no role in derivatives taken within that domain. -/
def extendedSection [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (f : OpenHolomorphicFunctions structureMap d U) :
    ComplexPoint X structureMap → ℂ :=
  Function.extend Subtype.val f.1 0

lemma extendedSection_contMDiffWithinAt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (f : OpenHolomorphicFunctions structureMap d U) {x : ComplexPoint X structureMap}
    (hx : x ∈ (Opposite.unop U : Opens (ComplexPoint X structureMap))) :
    ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection structureMap d U f)
      ((Opposite.unop U : Opens (ComplexPoint X structureMap)) :
        Set (ComplexPoint X structureMap)) x := by
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff
    (U := (Opposite.unop U : Opens (ComplexPoint X structureMap)))
    (x := ⟨x, hx⟩)).mp
  simpa only [extendedSection, Subtype.val_injective.extend_apply] using
    (holomorphicFunctionSheaf_section_analytic structureMap d f).contMDiffAt
      (x := ⟨x, hx⟩)

/-- The expression of a holomorphic section in one fixed chart. -/
def chartSection [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) : (Fin d → ℂ) → ℂ :=
  extendedSection structureMap d U f ∘
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm

lemma chartSection_contDiffWithinAt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    ContDiffWithinAt ℂ ω (chartSection structureMap d U z f)
      (chartSectionDomain structureMap d U z) y := by
  have hsymm : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (chartSectionDomain structureMap d U z) y := by
    apply (contMDiffOn_extChartAt_symm
      (I := modelWithCornersSelf ℂ (Fin d → ℂ)) z y hy.1).mono
    exact Set.inter_subset_left
  have hext : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection structureMap d U f)
      ((Opposite.unop U : Opens (ComplexPoint X structureMap)) :
        Set (ComplexPoint X structureMap))
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) :=
    extendedSection_contMDiffWithinAt structureMap d U f hy.2
  exact (hext.comp y hsymm (fun _ h ↦ h.2)).contDiffWithinAt

lemma chartSection_contDiffOn [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) :
    ContDiffOn ℂ ω (chartSection structureMap d U z f)
      (chartSectionDomain structureMap d U z) :=
  fun _ hy ↦ chartSection_contDiffWithinAt structureMap d U z f hy

@[simp] lemma chartSection_apply_of_mem [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartSection structureMap d U z f y =
      f.1 ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y, hy.2⟩ := by
  change Function.extend Subtype.val f.1 0
      (Subtype.val ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y,
        hy.2⟩) = _
  rw [Subtype.val_injective.extend_apply]

/-- The derivative of a section in one fixed chart. -/
def chartSectionDifferential [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) (y : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  fderivWithin ℂ (chartSection structureMap d U z f)
    (chartSectionDomain structureMap d U z) y

lemma chartSectionDifferential_add [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f g : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartSectionDifferential structureMap d U z (f + g) y =
      chartSectionDifferential structureMap d U z f y +
        chartSectionDifferential structureMap d U z g y := by
  let S := chartSectionDomain structureMap d U z
  have hEq : Set.EqOn (chartSection structureMap d U z (f + g))
      (chartSection structureMap d U z f + chartSection structureMap d U z g) S := by
    intro w hw
    simp only [Pi.add_apply, chartSection_apply_of_mem structureMap d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_add ((isOpen_chartSectionDomain structureMap d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt structureMap d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt structureMap d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_smul [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (c : ℂ)
    (f : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartSectionDifferential structureMap d U z (c • f) y =
      c • chartSectionDifferential structureMap d U z f y := by
  let S := chartSectionDomain structureMap d U z
  have hEq : Set.EqOn (chartSection structureMap d U z (c • f))
      (c • chartSection structureMap d U z f) S := by
    intro w hw
    simp only [Pi.smul_apply, chartSection_apply_of_mem structureMap d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_const_smul_field c
    ((isOpen_chartSectionDomain structureMap d U z).uniqueDiffWithinAt hy)

lemma chartSectionDifferential_mul [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap)
    (f g : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartSectionDifferential structureMap d U z (f * g) y =
      chartSection structureMap d U z f y • chartSectionDifferential structureMap d U z g y +
        chartSection structureMap d U z g y •
          chartSectionDifferential structureMap d U z f y := by
  let S := chartSectionDomain structureMap d U z
  have hEq : Set.EqOn (chartSection structureMap d U z (f * g))
      (chartSection structureMap d U z f * chartSection structureMap d U z g) S := by
    intro w hw
    simp only [Pi.mul_apply, chartSection_apply_of_mem structureMap d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_mul ((isOpen_chartSectionDomain structureMap d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt structureMap d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt structureMap d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_algebraMap [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartSectionDifferential structureMap d U z
      (algebraMap ℂ (OpenHolomorphicFunctions structureMap d U) c) y = 0 := by
  let S := chartSectionDomain structureMap d U z
  have hEq : Set.EqOn
      (chartSection structureMap d U z
        (algebraMap ℂ (OpenHolomorphicFunctions structureMap d U) c))
      (fun _ ↦ c) S := by
    intro w hw
    simp only [chartSection_apply_of_mem structureMap d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact congrFun
    (fderivWithin_const (𝕜 := ℂ) (E := Fin d → ℂ) (s := S) c) y

/-- Evaluation of a generator in one fixed coordinate chart. -/
def chartGeneratorEvaluation [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ) :
    Algebra.DeRham.Generator (OpenHolomorphicFunctions structureMap d U) p →
      (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  fun g y ↦ chartSection structureMap d U z g.1 y •
    wedgeCovectors (Fin d → ℂ) p
      (fun i ↦ chartSectionDifferential structureMap d U z (g.2 i) y)

/-- Evaluation of a raw form in one fixed coordinate chart. -/
def chartRawEvaluation [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p →ₗ[ℂ]
      ((Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  Finsupp.linearCombination ℂ (chartGeneratorEvaluation structureMap d U z p)

@[simp] lemma chartRawEvaluation_single [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions structureMap d U) p)
    (c : ℂ) :
    chartRawEvaluation structureMap d U z p (Finsupp.single g c) =
      c • chartGeneratorEvaluation structureMap d U z p g := by
  simp [chartRawEvaluation]

/-- Every defining Kähler relation evaluates to zero in each fixed chart, at every point of the
coordinate domain. -/
lemma chartRawEvaluation_relationValue [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (r : Algebra.DeRham.Relation ℂ (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartRawEvaluation structureMap d U z p
      (Algebra.DeRham.relationValue ℂ _ p r) y = 0 := by
  cases r with
  | coeffAdd a b v =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      rw [show chartSection structureMap d U z (a + b) y =
        chartSection structureMap d U z a y + chartSection structureMap d U z b y by
          simp only [chartSection_apply_of_mem structureMap d U z _ hy]
          rfl]
      module
  | coeffSMul c a v =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, map_smul, Pi.sub_apply, Pi.smul_apply,
        chartGeneratorEvaluation]
      rw [show chartSection structureMap d U z (c • a) y =
        c * chartSection structureMap d U z a y by
          simp only [chartSection_apply_of_mem structureMap d U z _ hy]
          rfl]
      simp [mul_smul]
  | diffAdd a₀ v i a b =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      have hupdate (q : OpenHolomorphicFunctions structureMap d U) :
          (fun j ↦ chartSectionDifferential structureMap d U z (Function.update v i q j) y) =
            Function.update
              (fun j ↦ chartSectionDifferential structureMap d U z (v j) y) i
              (chartSectionDifferential structureMap d U z q y) := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [hupdate, hupdate, hupdate,
        chartSectionDifferential_add structureMap d U z a b hy,
        wedgeCovectors_update_add]
      module
  | diffSMul a₀ v i c a =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, map_smul, Pi.sub_apply, Pi.smul_apply,
        chartGeneratorEvaluation]
      have hupdate (q : OpenHolomorphicFunctions structureMap d U) :
          (fun j ↦ chartSectionDifferential structureMap d U z (Function.update v i q j) y) =
            Function.update
              (fun j ↦ chartSectionDifferential structureMap d U z (v j) y) i
              (chartSectionDifferential structureMap d U z q y) := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [hupdate, hupdate,
        chartSectionDifferential_smul structureMap d U z c a hy,
        wedgeCovectors_update_smul]
      module
  | diffMul a₀ v i a b =>
      simp only [Algebra.DeRham.relationValue, map_sub, chartRawEvaluation_single,
        one_smul, Pi.sub_apply, chartGeneratorEvaluation]
      have hupdate (q : OpenHolomorphicFunctions structureMap d U) :
          (fun j ↦ chartSectionDifferential structureMap d U z (Function.update v i q j) y) =
            Function.update
              (fun j ↦ chartSectionDifferential structureMap d U z (v j) y) i
              (chartSectionDifferential structureMap d U z q y) := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [hupdate, hupdate, hupdate]
      rw [show chartSection structureMap d U z (a₀ * a) y =
          chartSection structureMap d U z a₀ y * chartSection structureMap d U z a y by
            simp only [chartSection_apply_of_mem structureMap d U z _ hy]
            rfl,
        show chartSection structureMap d U z (a₀ * b) y =
          chartSection structureMap d U z a₀ y * chartSection structureMap d U z b y by
            simp only [chartSection_apply_of_mem structureMap d U z _ hy]
            rfl]
      change chartSection structureMap d U z a₀ y • _ -
        (chartSection structureMap d U z a₀ y *
          chartSection structureMap d U z a y) • _ -
        (chartSection structureMap d U z a₀ y *
          chartSection structureMap d U z b y) • _ =
        (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
      rw [chartSectionDifferential_mul structureMap d U z a b hy,
        wedgeCovectors_update_add, wedgeCovectors_update_smul,
        wedgeCovectors_update_smul]
      module
  | diffConst a₀ v i c =>
      simp only [Algebra.DeRham.relationValue, chartRawEvaluation_single, one_smul,
        chartGeneratorEvaluation]
      have hupdate (q : OpenHolomorphicFunctions structureMap d U) :
          (fun j ↦ chartSectionDifferential structureMap d U z (Function.update v i q j) y) =
            Function.update
              (fun j ↦ chartSectionDifferential structureMap d U z (v j) y) i
              (chartSectionDifferential structureMap d U z q y) := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [hupdate, chartSectionDifferential_algebraMap structureMap d U z c hy,
        wedgeCovectors_update_zero]
      apply ContinuousAlternatingMap.ext
      intro w
      simp
  | alt a₀ v i j h hne =>
      simp only [Algebra.DeRham.relationValue, chartRawEvaluation_single, one_smul,
        chartGeneratorEvaluation]
      have heq : chartSectionDifferential structureMap d U z (v i) y =
          chartSectionDifferential structureMap d U z (v j) y := by rw [h]
      rw [wedgeCovectors_eq_zero_of_eq (Fin d → ℂ) p _ i j heq hne]
      apply ContinuousAlternatingMap.ext
      intro w
      simp

/-- Exterior differentiation of a generator in fixed coordinates agrees with the syntactic de
Rham differential. -/
lemma extDerivWithin_chartGeneratorEvaluation
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d U z) :
    extDerivWithin (chartGeneratorEvaluation structureMap d U z p g)
        (chartSectionDomain structureMap d U z) y =
      chartGeneratorEvaluation structureMap d U z (p + 1)
        (Algebra.DeRham.nextGenerator _ g) y := by
  have h := extDerivWithin_smul_exactWedgeWithin (Fin d → ℂ) p
    (chartSection structureMap d U z g.1)
    (fun i ↦ chartSection structureMap d U z (g.2 i))
    (chartSectionDomain structureMap d U z) y
    (isOpen_chartSectionDomain structureMap d U z) hy
    (chartSection_contDiffOn structureMap d U z g.1)
    (fun i ↦ chartSection_contDiffOn structureMap d U z (g.2 i))
  rw [show chartGeneratorEvaluation structureMap d U z p g =
      (fun w ↦ chartSection structureMap d U z g.1 w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection structureMap d U z (g.2 i))
          (chartSectionDomain structureMap d U z) w) by
        funext w
        rfl]
  rw [h]
  simp only [chartGeneratorEvaluation, Algebra.DeRham.nextGenerator,
    chartSectionDifferential]
  rw [show chartSection structureMap d U z (1 : OpenHolomorphicFunctions structureMap d U) y =
      1 by
        simp only [chartSection_apply_of_mem structureMap d U z _ hy]
        rfl, one_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

lemma chartGeneratorEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d U z) :
    DifferentiableWithinAt ℂ (chartGeneratorEvaluation structureMap d U z p g)
      (chartSectionDomain structureMap d U z) y := by
  rw [show chartGeneratorEvaluation structureMap d U z p g =
      (fun w ↦ chartSection structureMap d U z g.1 w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection structureMap d U z (g.2 i))
          (chartSectionDomain structureMap d U z) w) by
        funext w
        rfl]
  exact DifferentiableWithinAt.smul
    ((chartSection_contDiffWithinAt structureMap d U z g.1 hy).differentiableWithinAt (by simp))
    (exactWedgeWithin_differentiableWithinAt (Fin d → ℂ) p
      (fun i ↦ chartSection structureMap d U z (g.2 i))
      (chartSectionDomain structureMap d U z) y
      (isOpen_chartSectionDomain structureMap d U z) hy
      (fun i ↦ chartSection_contDiffOn structureMap d U z (g.2 i)))

lemma chartRawEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d U z) :
    DifferentiableWithinAt ℂ (chartRawEvaluation structureMap d U z p x)
      (chartSectionDomain structureMap d U z) y := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [map_zero]
      exact differentiableWithinAt_const (c :=
        (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ))
  | single_add g c x hg hc ih =>
      rw [map_add, chartRawEvaluation_single]
      exact ((chartGeneratorEvaluation_differentiableWithinAt structureMap d U z p g hy).const_smul
        c).add ih

/-- Fixed-chart evaluation intertwines the syntactic and analytic exterior derivatives. -/
lemma chartRawEvaluation_rawDifferential
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d U z) :
    chartRawEvaluation structureMap d U z (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions structureMap d U) p x) y =
      extDerivWithin (chartRawEvaluation structureMap d U z p x)
        (chartSectionDomain structureMap d U z) y := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [map_zero, map_zero]
      symm
      apply ContinuousAlternatingMap.ext
      intro v
      simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        fderivWithin_zero]
  | single_add g c x hg hc ih =>
      rw [map_add, Algebra.DeRham.rawDifferential_single, map_add,
        chartRawEvaluation_single]
      have hEval : chartRawEvaluation structureMap d U z p (Finsupp.single g c + x) =
          c • chartGeneratorEvaluation structureMap d U z p g +
            chartRawEvaluation structureMap d U z p x := by
        rw [map_add, chartRawEvaluation_single]
      rw [hEval, Pi.add_apply,
        extDerivWithin_add
          ((isOpen_chartSectionDomain structureMap d U z).uniqueDiffWithinAt hy)
          ((chartGeneratorEvaluation_differentiableWithinAt structureMap d U z p g hy).const_smul c)
          (chartRawEvaluation_differentiableWithinAt structureMap d U z p x hy),
        extDerivWithin_smul c _
          ((isOpen_chartSectionDomain structureMap d U z).uniqueDiffWithinAt hy),
        extDerivWithin_chartGeneratorEvaluation structureMap d U z p g hy,
        ih]
      simp only [Pi.smul_apply]

/-- Evaluation at one point of one fixed coordinate chart. -/
def chartEvaluationAt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (z : ComplexPoint X structureMap) (p : ℕ) (y : Fin d → ℂ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p →ₗ[ℂ]
      (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ where
  toFun x := chartRawEvaluation structureMap d U z p x y
  map_add' a b := by rw [map_add, Pi.add_apply]
  map_smul' c a := by
    rw [map_smul, Pi.smul_apply]
    rfl

/-- Raw forms that vanish in every fixed chart at every point of its coordinate domain. -/
def chartEvaluationKernel [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions structureMap d U) p) :=
  ⨅ (z : ComplexPoint X structureMap), ⨅ (y : Fin d → ℂ),
    ⨅ (_ : y ∈ chartSectionDomain structureMap d U z),
      LinearMap.ker (chartEvaluationAt structureMap d U z p y)

lemma mem_chartEvaluationKernel_iff [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p) :
    x ∈ chartEvaluationKernel structureMap d U p ↔
      ∀ z y, y ∈ chartSectionDomain structureMap d U z →
        chartRawEvaluation structureMap d U z p x y = 0 := by
  simp only [chartEvaluationKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    chartEvaluationAt]
  exact forall_congr' fun z ↦ forall_congr' fun y ↦
    ⟨fun h hy ↦ h hy, fun h hy ↦ h hy⟩

/-- The ordinary Kähler relations are genuine coordinate identities. -/
lemma standardRelations_le_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.standardRelations ℂ (OpenHolomorphicFunctions structureMap d U) p ≤
      chartEvaluationKernel structureMap d U p := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply (mem_chartEvaluationKernel_iff structureMap d U p _).2
  intro z y hy
  exact chartRawEvaluation_relationValue structureMap d U z p r hy

/-- Coordinate-zero identities remain coordinate-zero after exterior differentiation. -/
lemma rawDifferential_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ chartEvaluationKernel structureMap d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p x ∈
      chartEvaluationKernel structureMap d U (p + 1) := by
  have hx' := (mem_chartEvaluationKernel_iff structureMap d U p x).1 hx
  apply (mem_chartEvaluationKernel_iff structureMap d U (p + 1) _).2
  intro z y hy
  rw [chartRawEvaluation_rawDifferential structureMap d U z p x hy]
  have hEq : Set.EqOn (chartRawEvaluation structureMap d U z p x) 0
      (chartSectionDomain structureMap d U z) := fun w hw ↦ hx' z w hw
  rw [extDerivWithin_congr' hEq hy, extDerivWithin]
  have hzero := congrFun
    (fderivWithin_zero (𝕜 := ℂ) (E := Fin d → ℂ)
      (F := (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
      (s := chartSectionDomain structureMap d U z)) y
  rw [hzero]
  apply ContinuousAlternatingMap.ext
  intro v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply]

lemma chartEvaluationKernel_eq_top_of_lt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : chartEvaluationKernel structureMap d U p = ⊤ := by
  apply top_unique
  intro x hx
  apply (mem_chartEvaluationKernel_iff structureMap d U p x).2
  intro z y hy
  apply ContinuousAlternatingMap.ext
  intro v
  apply (chartRawEvaluation structureMap d U z p x y).toAlternatingMap.map_linearDependent
  intro hli
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  lia


def rawRestriction [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p →ₗ[ℂ]
      Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d V) p :=
  Algebra.DeRham.rawMap ℂ (holomorphicRestrictionAlgHom structureMap d i) p

@[simp] lemma rawRestriction_id [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    rawRestriction structureMap d (𝟙 U) p = LinearMap.id := by
  rw [rawRestriction, holomorphicRestrictionAlgHom_id,
    Algebra.DeRham.rawMap_id]

@[simp] lemma rawRestriction_comp [SmoothOfRelativeDimension d structureMap]
    {U V W : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    rawRestriction structureMap d (i ≫ j) p =
      (rawRestriction structureMap d j p).comp (rawRestriction structureMap d i p) := by
  rw [rawRestriction, rawRestriction, rawRestriction,
    holomorphicRestrictionAlgHom_comp, Algebra.DeRham.rawMap_comp]

/-- Restricting a holomorphic function does not change its value in a fixed chart. -/
lemma chartSection_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d V z) :
    chartSection structureMap d V z (holomorphicRestrictionAlgHom structureMap d i f) y =
      chartSection structureMap d U z f y := by
  have hyU : y ∈ chartSectionDomain structureMap d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  rw [chartSection_apply_of_mem structureMap d V z _ hy,
    chartSection_apply_of_mem structureMap d U z _ hyU]
  rfl

/-- Restricting a holomorphic function does not change its derivative in a fixed chart. -/
lemma chartSectionDifferential_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X structureMap)
    (f : OpenHolomorphicFunctions structureMap d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain structureMap d V z) :
    chartSectionDifferential structureMap d V z
        (holomorphicRestrictionAlgHom structureMap d i f) y =
      chartSectionDifferential structureMap d U z f y := by
  have hyU : y ∈ chartSectionDomain structureMap d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  have heq : Filter.EventuallyEq (nhds y)
      (chartSection structureMap d V z
        (holomorphicRestrictionAlgHom structureMap d i f))
      (chartSection structureMap d U z f) := by
    filter_upwards [(isOpen_chartSectionDomain structureMap d V z).mem_nhds hy] with w hw
    exact chartSection_holomorphicRestrictionAlgHom structureMap d i z f hw
  rw [chartSectionDifferential, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain structureMap d V z) hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain structureMap d U z) hyU]
  exact heq.fderiv_eq

/-- Fixed-chart evaluation of a raw form commutes with restriction. -/
lemma chartRawEvaluation_rawRestriction
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X structureMap) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain structureMap d V z) :
    chartRawEvaluation structureMap d V z p
        (rawRestriction structureMap d i p x) y =
      chartRawEvaluation structureMap d U z p x y := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g c x hg hc ih =>
      rw [map_add, map_add, Pi.add_apply, map_add, Pi.add_apply, ih]
      simp only [rawRestriction, Algebra.DeRham.rawMap_single,
        chartRawEvaluation_single, Pi.smul_apply]
      simp only [chartGeneratorEvaluation, Algebra.DeRham.generatorMap]
      rw [chartSection_holomorphicRestrictionAlgHom structureMap d i z g.1 hy]
      have hd :
          (fun j ↦ chartSectionDifferential structureMap d V z
            (holomorphicRestrictionAlgHom structureMap d i (g.2 j)) y) =
          (fun j ↦ chartSectionDifferential structureMap d U z (g.2 j) y) := by
        funext j
        exact chartSectionDifferential_holomorphicRestrictionAlgHom
          structureMap d i z (g.2 j) hy
      rw [hd]

/-- Coordinate-zero identities remain so after restriction. -/
lemma rawRestriction_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ chartEvaluationKernel structureMap d U p) :
    rawRestriction structureMap d i p x ∈ chartEvaluationKernel structureMap d V p := by
  apply (mem_chartEvaluationKernel_iff structureMap d V p _).2
  intro z y hy
  rw [chartRawEvaluation_rawRestriction structureMap d i z p x hy]
  exact (mem_chartEvaluationKernel_iff structureMap d U p x).1 hx z y
    ⟨hy.1, leOfHom i.unop hy.2⟩

/-- Raw forms whose restrictions vanish in every coordinate chart. -/
def restrictionStableAnalyticKernel [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions structureMap d U) p) :=
  ⨅ (V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ),
    ⨅ (i : U ⟶ V),
      (chartEvaluationKernel structureMap d V p).comap
        (rawRestriction structureMap d i p)

/-- Vanishing in every coordinate chart already implies vanishing after every restriction. -/
lemma restrictionStableAnalyticKernel_eq_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    restrictionStableAnalyticKernel structureMap d U p =
      chartEvaluationKernel structureMap d U p := by
  apply le_antisymm
  · intro x hx
    simp only [restrictionStableAnalyticKernel, Submodule.mem_iInf, Submodule.mem_comap] at hx
    have h := hx U (𝟙 U)
    rw [rawRestriction_id structureMap d U p] at h
    exact h
  · intro x hx
    simp only [restrictionStableAnalyticKernel, Submodule.mem_iInf, Submodule.mem_comap]
    intro V i
    exact rawRestriction_mem_chartEvaluationKernel structureMap d i p hx

/-- Every standard Kähler relation remains evaluation-zero after every restriction. -/
lemma standardRelations_le_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.standardRelations ℂ (OpenHolomorphicFunctions structureMap d U) p ≤
      restrictionStableAnalyticKernel structureMap d U p := by
  rw [restrictionStableAnalyticKernel_eq_chartEvaluationKernel]
  exact standardRelations_le_chartEvaluationKernel structureMap d U p

lemma rawRestriction_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ restrictionStableAnalyticKernel structureMap d U p) :
    rawRestriction structureMap d i p x ∈
      restrictionStableAnalyticKernel structureMap d V p := by
  rw [restrictionStableAnalyticKernel_eq_chartEvaluationKernel] at hx ⊢
  exact rawRestriction_mem_chartEvaluationKernel structureMap d i p hx

/-- Restriction-stable coordinate identities remain so after exterior differentiation. -/
lemma rawDifferential_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ restrictionStableAnalyticKernel structureMap d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p x ∈
      restrictionStableAnalyticKernel structureMap d U (p + 1) := by
  rw [restrictionStableAnalyticKernel_eq_chartEvaluationKernel] at hx ⊢
  exact rawDifferential_mem_chartEvaluationKernel structureMap d U p hx

/-- Analytic identities detected by evaluation in every coordinate chart. -/
def analyticRelations [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions structureMap d U) p) :=
  chartEvaluationKernel structureMap d U p

lemma analyticRelations_eq_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    analyticRelations structureMap d U p = chartEvaluationKernel structureMap d U p := rfl

/-- Analytic identities remain evaluation-zero after every restriction. -/
lemma analyticRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    analyticRelations structureMap d U p =
      restrictionStableAnalyticKernel structureMap d U p :=
  (restrictionStableAnalyticKernel_eq_chartEvaluationKernel structureMap d U p).symm

/-- The differential closure of the standard Kähler relations is contained in the analytic
relations. -/
lemma algebraicRelations_le_analyticRelations [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) : ∀ p : ℕ,
    Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions structureMap d U) p ≤
      analyticRelations structureMap d U p := by
  intro p
  induction p with
  | zero =>
      exact standardRelations_le_chartEvaluationKernel structureMap d U 0
  | succ p ih =>
      rw [Algebra.DeRham.relations]
      refine sup_le (standardRelations_le_chartEvaluationKernel structureMap d U (p + 1)) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact rawDifferential_mem_chartEvaluationKernel structureMap d U p (ih hx)

lemma rawDifferential_mem_analyticRelations [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ analyticRelations structureMap d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p x ∈
      analyticRelations structureMap d U (p + 1) :=
  rawDifferential_mem_chartEvaluationKernel structureMap d U p hx

lemma rawRestriction_mem_analyticRelations [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ analyticRelations structureMap d U p) :
    rawRestriction structureMap d i p x ∈ analyticRelations structureMap d V p :=
  rawRestriction_mem_chartEvaluationKernel structureMap d i p hx

/-- Relations for holomorphic forms: raw forms that vanish in every coordinate chart. -/
def holomorphicFormRelations [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.RawForm ℂ
      (OpenHolomorphicFunctions structureMap d U) p) :=
  chartEvaluationKernel structureMap d U p

lemma holomorphicFormRelations_eq_chartEvaluationKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations structureMap d U p = chartEvaluationKernel structureMap d U p := rfl

/-- Holomorphic form relations are exactly the analytic identities. -/
lemma holomorphicFormRelations_eq_analyticRelations
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations structureMap d U p = analyticRelations structureMap d U p := rfl

/-- Holomorphic form relations vanish in every coordinate chart after every restriction. -/
lemma holomorphicFormRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations structureMap d U p =
      restrictionStableAnalyticKernel structureMap d U p :=
  (restrictionStableAnalyticKernel_eq_chartEvaluationKernel structureMap d U p).symm

lemma holomorphicFormRelations_eq_top_of_lt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : holomorphicFormRelations structureMap d U p = ⊤ :=
  chartEvaluationKernel_eq_top_of_lt structureMap d U hp

lemma rawDifferential_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ holomorphicFormRelations structureMap d U p) :
    Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p x ∈
      holomorphicFormRelations structureMap d U (p + 1) :=
  rawDifferential_mem_chartEvaluationKernel structureMap d U p hx

lemma rawRestriction_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p}
    (hx : x ∈ holomorphicFormRelations structureMap d U p) :
    rawRestriction structureMap d i p x ∈ holomorphicFormRelations structureMap d V p :=
  rawRestriction_mem_chartEvaluationKernel structureMap d i p hx

abbrev HolomorphicForm [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :=
  Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) p ⧸
    holomorphicFormRelations structureMap d U p

lemma holomorphicForm_eq_zero_of_lt [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    {p : ℕ} (hp : d < p) (x : HolomorphicForm structureMap d U p) : x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations structureMap d U p) x
  change Submodule.Quotient.mk x = 0
  rw [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_top_of_lt structureMap d U hp]
  trivial

/-- The quotient map from algebraic Kähler forms to analytic differential forms. -/
def algebraicFormToHolomorphicForm [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions structureMap d U) p →ₗ[ℂ]
      HolomorphicForm structureMap d U p :=
  (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions structureMap d U) p).liftQ
    (holomorphicFormRelations structureMap d U p).mkQ (by
      intro x hx
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact algebraicRelations_le_analyticRelations structureMap d U p hx)

/-- A complex constant regarded as an analytic differential zero-form. -/
def holomorphicFormOfConstant [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) :
    ℂ →ₗ[ℂ] HolomorphicForm structureMap d U 0 :=
  (algebraicFormToHolomorphicForm structureMap d U 0).comp
    (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions structureMap d U))

def holomorphicFormDifferential [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    HolomorphicForm structureMap d U p →ₗ[ℂ] HolomorphicForm structureMap d U (p + 1) :=
  (holomorphicFormRelations structureMap d U p).liftQ
    ((holomorphicFormRelations structureMap d U (p + 1)).mkQ.comp
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p)) (by
          intro x hx
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          exact rawDifferential_mem_holomorphicFormRelations structureMap d U p hx)

def holomorphicFormRestriction [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    HolomorphicForm structureMap d U p →ₗ[ℂ] HolomorphicForm structureMap d V p :=
  (holomorphicFormRelations structureMap d U p).liftQ
    ((holomorphicFormRelations structureMap d V p).mkQ.comp
      (rawRestriction structureMap d i p)) (by
        intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact rawRestriction_mem_holomorphicFormRelations structureMap d i p hx)

lemma holomorphicFormRestriction_algebraicFormToHolomorphicForm
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (x : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions structureMap d U) p) :
    holomorphicFormRestriction structureMap d i p
        (algebraicFormToHolomorphicForm structureMap d U p x) =
      algebraicFormToHolomorphicForm structureMap d V p
        (Algebra.DeRham.map ℂ (holomorphicRestrictionAlgHom structureMap d i) p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions structureMap d U) p) x
  rfl

lemma holomorphicFormDifferential_algebraicFormToHolomorphicForm
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    (x : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions structureMap d U) p) :
    holomorphicFormDifferential structureMap d U p
        (algebraicFormToHolomorphicForm structureMap d U p x) =
      algebraicFormToHolomorphicForm structureMap d U (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions structureMap d U) p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (Algebra.DeRham.relations ℂ (OpenHolomorphicFunctions structureMap d U) p) x
  rfl

@[simp] lemma holomorphicFormRestriction_ofConstant
    [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (c : ℂ) :
    holomorphicFormRestriction structureMap d i 0
        (holomorphicFormOfConstant structureMap d U c) =
      holomorphicFormOfConstant structureMap d V c := by
  rw [holomorphicFormOfConstant, holomorphicFormOfConstant, LinearMap.comp_apply,
    holomorphicFormRestriction_algebraicFormToHolomorphicForm,
    Algebra.DeRham.map_ofConstant]
  rfl

@[simp] lemma holomorphicFormDifferential_ofConstant
    [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (c : ℂ) :
    holomorphicFormDifferential structureMap d U 0
        (holomorphicFormOfConstant structureMap d U c) = 0 := by
  rw [holomorphicFormOfConstant, LinearMap.comp_apply,
    holomorphicFormDifferential_algebraicFormToHolomorphicForm,
    Algebra.DeRham.differential_ofConstant, map_zero]

lemma holomorphicFormDifferential_squared [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ)
    (x : HolomorphicForm structureMap d U p) :
    holomorphicFormDifferential structureMap d U (p + 1)
      (holomorphicFormDifferential structureMap d U p x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations structureMap d U p) x
  change Submodule.Quotient.mk
    (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions structureMap d U) (p + 1)
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d U) p x)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact standardRelations_le_chartEvaluationKernel structureMap d U (p + 2)
    (Algebra.DeRham.rawDifferential_squared_mem_standardRelations ℂ
      (OpenHolomorphicFunctions structureMap d U) p x)

lemma holomorphicFormRestriction_differential [SmoothOfRelativeDimension d structureMap]
    {U V : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (x : HolomorphicForm structureMap d U p) :
    holomorphicFormRestriction structureMap d i (p + 1)
        (holomorphicFormDifferential structureMap d U p x) =
      holomorphicFormDifferential structureMap d V p
        (holomorphicFormRestriction structureMap d i p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations structureMap d U p) x
  change Submodule.Quotient.mk
      (rawRestriction structureMap d i (p + 1)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions structureMap d U) p x)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions structureMap d V) p
        (rawRestriction structureMap d i p x))
  simp only [rawRestriction, Algebra.DeRham.rawMap_rawDifferential]

@[simp] lemma holomorphicFormRestriction_id [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRestriction structureMap d (𝟙 U) p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations structureMap d U p) x
  change Submodule.Quotient.mk (rawRestriction structureMap d (𝟙 U) p x) =
    Submodule.Quotient.mk x
  rw [rawRestriction_id, LinearMap.id_apply]

@[simp] lemma holomorphicFormRestriction_comp [SmoothOfRelativeDimension d structureMap]
    {U V W : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    holomorphicFormRestriction structureMap d (i ≫ j) p =
      (holomorphicFormRestriction structureMap d j p).comp
        (holomorphicFormRestriction structureMap d i p) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations structureMap d U p) x
  change Submodule.Quotient.mk (rawRestriction structureMap d (i ≫ j) p x) =
    Submodule.Quotient.mk
      (rawRestriction structureMap d j p (rawRestriction structureMap d i p x))
  rw [rawRestriction_comp, LinearMap.comp_apply]

end AlgebraicGeometry.ComplexPoint
