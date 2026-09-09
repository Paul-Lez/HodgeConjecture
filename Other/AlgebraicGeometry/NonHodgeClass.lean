/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Detecting non-Hodge classes in the cohomology of a variety

The cohomology and filtration in this file are the ones constructed from the analytic space of
an actual scheme. No independently supplied pure Hodge structure is used. A non-Hodge rational
class exists exactly when the pulled-back complex Hodge filtration is proper. The key point is
that the rational vectors span their complexification over `ℂ`.

This criterion does not construct a variety for which the filtration is proper. Such a geometric
example still requires a computation of its cohomology and its holomorphic de Rham filtration.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ)

/-- All rational classes of a variety are Hodge exactly when the pulled-back complex Hodge
filtration is the whole complexification of rational cohomology. -/
theorem hodgeClasses_eq_top_iff_complexifiedFieldHodgeFiltration_eq_top :
    Hdg^p(ℚ; X) = ⊤ ↔ complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ)) = ⊤ := by
  rw [← hodgeClassesViaComplexification_eq]
  constructor
  · intro h
    apply top_unique
    intro x hx
    clear hx
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul z v =>
        have hv : HodgeStructure.ofBase ℚ _ v ∈
            complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ)) := by
          change v ∈ hodgeClassesViaComplexification ℚ X p
          rw [h]
          trivial
        simpa [TensorProduct.smul_tmul'] using
          (complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ))).smul_mem z hv
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  · intro h
    apply top_unique
    intro x _
    change HodgeStructure.ofBase ℚ _ x ∈
      complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ))
    rw [h]
    trivial

/-- A proper Hodge filtration on the actual complexified cohomology gives a rational class
which is not Hodge, and conversely. -/
theorem exists_not_isHodgeClass_iff :
    (∃ α : FieldCohomology ℚ X (2 * (p : ℤ)), ¬ IsHodgeClass ℚ X p α) ↔
      complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ)) ≠ ⊤ := by
  change (∃ α : FieldCohomology ℚ X (2 * (p : ℤ)), ¬ IsHodgeClass ℚ X p α) ↔
    ¬ complexifiedFieldHodgeFiltration ℚ X p (2 * (p : ℤ)) = ⊤
  rw [← hodgeClasses_eq_top_iff_complexifiedFieldHodgeFiltration_eq_top]
  constructor
  · rintro ⟨α, hα⟩ h
    apply hα
    change α ∈ Hdg^p(ℚ; X)
    rw [h]
    trivial
  · intro h
    by_contra h'
    apply h
    apply top_unique
    intro α _
    by_contra hα
    exact h' ⟨α, hα⟩

end AlgebraicGeometry.ComplexPoint
