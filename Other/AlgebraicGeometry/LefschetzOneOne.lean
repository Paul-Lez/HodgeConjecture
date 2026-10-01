/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Statement
public import Other.AlgebraicGeometry.ChernRelativeFinalAssembly
public import Other.AlgebraicGeometry.DivisorObligations
public import Other.AlgebraicGeometry.GAGAProper
public import Other.AlgebraicGeometry.GAGAtoLefschetz
public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveFiniteHomology

/-!
# Rational Lefschetz (1, 1)

This file states and proves the rational Lefschetz `(1, 1)` theorem for smooth projective
integral schemes over `ℂ`. The canonical statement says that every rational degree-two Hodge
class lies in the span of codimension-one algebraic cycle classes. The stronger intermediate
statement produces an explicit rational codimension-one cycle with the prescribed class.

The proof combines finite generation of integral homology, the divisor--Chern comparison, and
proper GAGA for line bundles. It does not assert the stronger integral identification with the
image of the first Chern class map from the Picard group, the reverse inclusion, or the theorem
for compact Kähler manifolds.

## Reference

* [P. Deligne, *The Hodge Conjecture*, §2(iii)]
  (https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open scoped TensorProduct

/-- The rational Lefschetz `(1, 1)` statement proved in this repository.

For every smooth projective integral scheme `X` over `ℂ`, each rational degree-two Hodge class is
in the rational span of the classes of codimension-one algebraic subvarieties. -/
def LefschetzOneOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
    Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1

/-- The explicit-cycle rational Lefschetz `(1, 1)` statement for smooth projective integral
complex schemes. -/
def RationalLefschetzOneOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α : H^2(X; ℚ)),
    α ∈ Hdg^1(X; ℚ) →
      ∃ D : TensorProduct ℤ ℚ (codimensionCycleSubgroup X.left 1),
        rationalSheafCycleClassOnCycles
          { scheme := X.left, structureMap := X.hom } 1 D = α

/-- The concrete rational-cycle formulation implies the canonical Lefschetz `(1, 1)`
statement. -/
theorem RationalLefschetzOneOne.to_lefschetzOneOne
    (h : RationalLefschetzOneOne) : LefschetzOneOne := by
  intro X _ _ _ α hα
  obtain ⟨D, rfl⟩ := h X α hα
  exact rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan X 1 D

/-- The Hodge conjecture implies the explicit-cycle rational Lefschetz `(1, 1)` statement. -/
theorem HodgeConjecture.rationalLefschetzOneOne
    (hodge : HodgeConjecture) : RationalLefschetzOneOne := by
  intro X _ _ _ α hα
  have hspan : algebraicCycleClassSpan X 1 ≤
      LinearMap.range (rationalSheafCycleClassOnCycles
        { scheme := X.left, structureMap := X.hom } 1) := by
    refine sSup_le ?_
    rintro S ⟨x, hx, hS⟩
    subst S
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨1 ⊗ₜ[ℤ] codimensionCycleSubgroup.single x hx 1, ?_⟩
    refine (rationalSheafCycleClassOnCycles_tmul_single
      { scheme := X.left, structureMap := X.hom } 1 1 x hx).trans ?_
    rw [one_smul]
    rfl
  exact hspan (hodge X 1 hα)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A direct proof of the same implication that checks each divisor generator. -/
theorem HodgeConjecture.rationalLefschetzOneOne_direct :
    type_of% HodgeConjecture.rationalLefschetzOneOne := by
  intro hodge X _ _ _ α hα
  have hspan : algebraicCycleClassSpan X 1 ≤
      LinearMap.range (rationalSheafCycleClassOnCycles
        { scheme := X.left, structureMap := X.hom } 1) := by
    refine sSup_le ?_
    rintro S ⟨x, hx, hS⟩
    subst S
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨1 ⊗ₜ[ℤ] codimensionCycleSubgroup.single x hx 1, ?_⟩
    refine (rationalSheafCycleClassOnCycles_tmul_single
      { scheme := X.left, structureMap := X.hom } 1 1 x hx).trans ?_
    rw [one_smul]
    rfl
  exact hspan (hodge X 1 hα)

/-- Denominator clearing and divisors for unit-sheaf extensions imply the explicit-cycle
statement. -/
theorem RationalLefschetzOneOne.of_obligations
    (hclear : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasIntegralDenominatorClearing X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne := by
  intro X _ _ _ α hα
  exact exists_rationalSheafCycleClassOnCycles_eq_of_obligations
    X (hclear X) (hdivisor X) α hα

/-- Finite generation of second integral homology and divisors for unit-sheaf extensions imply
the explicit-cycle statement. -/
theorem RationalLefschetzOneOne.of_finiteSecondHomology_of_divisor
    (hfin : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteSecondHomology X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteSecondHomology X (hfin X)) hdivisor

/-- Finite good covers and divisors for unit-sheaf extensions imply the explicit-cycle
statement. -/
theorem RationalLefschetzOneOne.of_finiteGoodCover_of_divisor
    (hcover : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteGoodCover X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteGoodCover X (hcover X)) hdivisor

/-- Divisors for unit-sheaf extensions imply the explicit-cycle statement. -/
theorem RationalLefschetzOneOne.of_divisor
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing X) hdivisor

/-- Algebraic models for the analytic line bundles imply the explicit-cycle statement. -/
theorem RationalLefschetzOneOne.of_algebraicModel
    (h : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasAlgebraicModel X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_divisor fun X _ _ _ ↦
    hasDivisorOfUnitExtension_of_algebraicModel X (h X)
      (hasDivisorOfAlgebraicModel_of_divisorClass X
        (hasDivisorClassOfSomeCartierData_of_cartierData X
          (hasDivisorClassOfCartierData (X := X))))

/-- Line-bundle GAGA implies the explicit-cycle statement. -/
theorem RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize
    (h : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      AnalyticLineBundlesAlgebraize X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_algebraicModel fun X _ _ _ ↦
    hasAlgebraicModel_of_analyticLineBundlesAlgebraize X (h X)

/-- The rational Lefschetz `(1, 1)` theorem in explicit-cycle form. -/
theorem rationalLefschetzOneOne : RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize
    analyticLineBundlesAlgebraize

/-- The rational Lefschetz `(1, 1)` theorem in its canonical formulation. -/
theorem lefschetzOneOne : LefschetzOneOne :=
  rationalLefschetzOneOne.to_lefschetzOneOne

end
