/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.Algebra.Homology.ShiftedExact

/-!
# Exactness of the support sequence in the middle

For a subset `Z` of the analytic complex-point space, this file defines the restriction of
rational cohomology to the complement of `Z`, in the derived presentation used by
`RationalCohomologyWithSupport`, and proves exactness of

`H^n_Z(X, ℚ) → H^n(X, ℚ) → H^n(Zᶜ, ℚ)`

at the middle term. Both statements come from the distinguished triangle of the mapping cone of
the restriction morphism together with the long exact sequence obtained by applying
`Hom_D(ℤ_X, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance analyticSupportExactHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The image in the derived category of the mapping-cone triangle of the restriction to the
complement of `Z`. -/
abbrev restrictionDerivedTriangle (Z : Set (ComplexPoint X)) :
    Triangle (DerivedCategory (AnalyticAdditiveSheaf X)) :=
  DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z))

/-- The restriction triangle is distinguished. -/
lemma restrictionDerivedTriangle_distinguished (Z : Set (ComplexPoint X)) :
    restrictionDerivedTriangle X Z ∈ distTriang (DerivedCategory (AnalyticAdditiveSheaf X)) :=
  DerivedCategory.mappingCone_triangle_distinguished _

/-- The support-forgetting shifted morphism is, in the derived category, the connecting morphism
of the restriction triangle. -/
lemma equiv_forgetSupportShiftedHom (Z : Set (ComplexPoint X)) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (forgetSupportShiftedHom X Z) = (restrictionDerivedTriangle X Z).mor₃ := by
  unfold forgetSupportShiftedHom
  erw [Localization.SmallShiftedHom.equiv_mk]
  rfl

/-- Restriction of rational cohomology to the complement of `Z`, in the same derived
presentation. -/
def restrictToComplementHypercohomology (Z : Set (ComplexPoint X)) (n : ℤ) :
    Hypercohomology X (constantFieldSheafComplexInt ℚ X) n →+
      Hypercohomology X
        (derivedPushforwardComplementConstantRationalComplexInt X Z) n :=
  hypercohomologyMap X (rationalRestrictionComplexInt X Z) n

/-- Restriction of ordinary rational cohomology to the derived pushforward from the complement.

This is the current cohomology interface; the underlying map is the hypercohomology map above,
transported along the canonical constant-sheaf cohomology equivalence. -/
def restrictToComplement (Z : Set (ComplexPoint X)) (n : ℕ) :
    H^n(X; ℚ) →+
      Hypercohomology X
        (derivedPushforwardComplementConstantRationalComplexInt X Z) n :=
  (restrictToComplementHypercohomology X Z n).comp
    (hypercohomologyAddEquivConstantCohomology ℚ X n).symm.toAddMonoidHom

/-- In the derived category, restriction to the complement is postcomposition with the first
morphism of the restriction triangle. -/
lemma equiv_restrictToComplementHypercohomology (Z : Set (ComplexPoint X)) (n : ℤ)
    (α : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (restrictToComplementHypercohomology X Z n α) =
      ((Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) α).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (restrictionDerivedTriangle X Z).mor₁)
        (zero_add n) := by
  change (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q)
      (α.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (rationalRestrictionComplexInt X Z)) (zero_add n)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀]
  rfl

/-- In the derived category, forgetting support is postcomposition with the connecting morphism
of the restriction triangle. -/
lemma equiv_forgetSupport (Z : Set (ComplexPoint X)) (n : ℤ)
    (β : RationalCohomologyWithSupport X Z n) :
    (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) (forgetSupportHypercohomology X Z n β) =
      ((Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) β).comp
        (restrictionDerivedTriangle X Z).mor₃
        (show (1 : ℤ) + (n - 1) = n by lia) := by
  change (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q)
      (β.comp (forgetSupportShiftedHom X Z) (show (1 : ℤ) + (n - 1) = n by lia)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, equiv_forgetSupportShiftedHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A class coming from cohomology with support in `Z` restricts to zero on the complement. -/
theorem restrictToComplementHypercohomology_forgetSupport (Z : Set (ComplexPoint X)) (n : ℤ)
    (β : RationalCohomologyWithSupport X Z n) :
    restrictToComplementHypercohomology X Z n (forgetSupportHypercohomology X Z n β) = 0 := by
  have hzero : ShiftedHom.comp (restrictionDerivedTriangle X Z).mor₃
      (ShiftedHom.mk₀ (0 : ℤ) rfl (restrictionDerivedTriangle X Z).mor₁)
      (zero_add (1 : ℤ)) = 0 := by
    rw [ShiftedHom.comp_mk₀]
    exact comp_distTriang_mor_zero₃₁ _ (restrictionDerivedTriangle_distinguished X Z)
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [equiv_restrictToComplementHypercohomology, equiv_forgetSupport, hypercohomologyEquiv_zero,
    ShiftedHom.comp_assoc _ _ _ (show (1 : ℤ) + (n - 1) = n by lia) (zero_add (1 : ℤ))
      (show (0 : ℤ) + 1 + (n - 1) = n by lia), hzero, ShiftedHom.comp_zero]

/-- Exactness in the middle: a rational class restricting to zero on the complement of `Z` comes
from rational cohomology with support in `Z`. -/
theorem exists_forgetSupportHypercohomology_eq_of_restrictToComplementHypercohomology_eq_zero
    (Z : Set (ComplexPoint X)) (n : ℤ)
    (α : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n)
    (hα : restrictToComplementHypercohomology X Z n α = 0) :
    ∃ β : RationalCohomologyWithSupport X Z n, forgetSupportHypercohomology X Z n β = α := by
  let eTarget : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let eSource : RationalCohomologyWithSupport X Z n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Z)) (n - 1) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  have hα' : (eTarget α).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (restrictionDerivedTriangle X Z).mor₁)
      (show (0 : ℤ) + n = n by lia) = 0 := by
    rw [show eTarget α = (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) α from rfl,
      ← equiv_restrictToComplementHypercohomology, hα, hypercohomologyEquiv_zero]
    rfl
  obtain ⟨b, hb⟩ := Triangle.shifted_coyoneda_exact₁ (restrictionDerivedTriangle X Z)
    (restrictionDerivedTriangle_distinguished X Z)
    (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)) n (eTarget α) hα'
  refine ⟨eSource.symm b, ?_⟩
  apply eTarget.injective
  have hsymm : (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q) (eSource.symm b) = b :=
    eSource.apply_symm_apply b
  rw [show eTarget (forgetSupportHypercohomology X Z n (eSource.symm b)) =
      (Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q)
          (forgetSupportHypercohomology X Z n (eSource.symm b)) from rfl,
    equiv_forgetSupport, hsymm]
  exact hb

/-- The support sequence `H^n_Z(X, ℚ) → H^n(X, ℚ) → H^n(Zᶜ, ℚ)` is exact at the middle term. -/
theorem exact_forgetSupportHypercohomology_restrictToComplementHypercohomology
    (Z : Set (ComplexPoint X)) (n : ℤ) :
    Function.Exact (forgetSupportHypercohomology X Z n)
      (restrictToComplementHypercohomology X Z n) := fun α ↦
    ⟨fun hα ↦ exists_forgetSupportHypercohomology_eq_of_restrictToComplementHypercohomology_eq_zero
      X Z n α hα,
    fun ⟨β, hβ⟩ ↦ hβ ▸ restrictToComplementHypercohomology_forgetSupport X Z n β⟩

/-- A class coming from cohomology with support in `Z` restricts to zero on the complement. -/
theorem restrictToComplement_forgetSupport (Z : Set (ComplexPoint X)) (n : ℕ)
    (β : RationalCohomologyWithSupport X Z n) :
    restrictToComplement X Z n (forgetSupport X Z n β) = 0 := by
  change restrictToComplementHypercohomology X Z (n : ℤ)
    ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm
      ((hypercohomologyAddEquivConstantCohomology ℚ X n)
        (forgetSupportHypercohomology X Z (n : ℤ) β))) = 0
  rw [AddEquiv.symm_apply_apply]
  exact restrictToComplementHypercohomology_forgetSupport X Z (n : ℤ) β

/-- A rational cohomology class restricting to zero on the complement comes from support in `Z`. -/
theorem exists_forgetSupport_eq_of_restrictToComplement_eq_zero
    (Z : Set (ComplexPoint X)) (n : ℕ)
    (α : H^n(X; ℚ))
    (hα : restrictToComplement X Z n α = 0) :
    ∃ β : RationalCohomologyWithSupport X Z n, forgetSupport X Z n β = α := by
  let e : Hypercohomology X (constantFieldSheafComplexInt ℚ X) (n : ℤ) ≃ H^n(X; ℚ) :=
    hypercohomologyAddEquivConstantCohomology ℚ X n
  have hα' : restrictToComplementHypercohomology X Z (n : ℤ) (e.symm α) = 0 := by
    change restrictToComplement X Z n α = 0 at hα
    simpa [restrictToComplement, e] using hα
  obtain ⟨β, hβ⟩ :=
    exists_forgetSupportHypercohomology_eq_of_restrictToComplementHypercohomology_eq_zero
      X Z (n : ℤ) (e.symm α) hα'
  refine ⟨β, ?_⟩
  change e (forgetSupportHypercohomology X Z (n : ℤ) β) = α
  rw [hβ, e.apply_symm_apply]

/-- The support sequence is exact at ordinary rational cohomology in degree `n`. -/
theorem exact_forgetSupport_restrictToComplement (Z : Set (ComplexPoint X)) (n : ℕ) :
    Function.Exact (forgetSupport X Z n) (restrictToComplement X Z n) := fun α ↦
  ⟨fun hα ↦ exists_forgetSupport_eq_of_restrictToComplement_eq_zero X Z n α hα,
    fun ⟨β, hβ⟩ ↦ hβ ▸ restrictToComplement_forgetSupport X Z n β⟩

end AlgebraicGeometry.ComplexPoint
