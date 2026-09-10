/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOne
public import Other.AlgebraicGeometry.HolomorphicUnitExtension
public import Other.AlgebraicGeometry.HolomorphicLineBundleInvertible
public import Other.AlgebraicGeometry.AnalytificationModules

/-!
# Reduction of the rational Lefschetz `(1, 1)` theorem to its remaining obligations

This file does **not** prove `RationalLefschetzOneOne`. It isolates, as explicit propositions
about a single smooth projective integral complex variety, exactly what is still missing after
the analytic construction in `HolomorphicUnitExtension`, and proves that these propositions
suffice. Each obligation is stated using only the definitions already in the repository, so
that progress on any one of them can be checked independently.

* `HasIntegralDenominatorClearing X`: every rational degree-two class becomes integral after
  multiplication by a nonzero integer. Mathematically this is finite generation of `H²(X, ℤ)`.
* `HasAlgebraicModel X`: the invertible holomorphic section sheaf constructed from a unit-sheaf
  extension is the analytification of an algebraic invertible sheaf. This is the projective
  GAGA statement for line bundles.
* `HasDivisorOfAlgebraicModel X`: an algebraic invertible sheaf analytifying to that section
  sheaf is represented by a codimension-one cycle whose constructed cycle class is the rational
  image of the extension's first Chern class. This combines the divisor/line-bundle dictionary
  with the comparison of the constructed cycle class and the exponential connecting map.

`HasDivisorOfUnitExtension X` is the conjunction of the last two, stated without reference to
an algebraic model; `rationalLefschetzOneOne_of_obligations` derives the theorem from the first
obligation and this conjunction. What is proved unconditionally here is only the bookkeeping:
Hodge classes are stable under scaling, the analytic lift exists for integral Hodge classes,
and rational divisors may be divided by the integer denominator.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every rational degree-two class is a rational multiple of an integral class. -/
def HasIntegralDenominatorClearing : Prop :=
  ∀ α : FieldCohomology ℚ X 2, ∃ (m : ℤ) (β : IntegralCohomology X 2),
    m ≠ 0 ∧ integralToRationalCohomology X 2 β = m • α

/-- The holomorphic section sheaf of every unit-sheaf extension is the analytification of an
algebraic invertible sheaf. -/
def HasAlgebraicModel : Prop :=
  ∀ E : HolomorphicUnitExtension X (dim X.left),
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)

/-- An algebraic invertible sheaf analytifying to the section sheaf of a unit-sheaf extension
is represented by an integral codimension-one cycle whose constructed class is the rational
image of the extension's first Chern class. -/
def HasDivisorOfAlgebraicModel : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ D : CodimensionCycle X.left 1,
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
        integralToRationalCohomology X 2 E.firstChernClass

/-- The first Chern class of every unit-sheaf extension is the constructed class of an integral
codimension-one cycle. -/
def HasDivisorOfUnitExtension : Prop :=
  ∀ E : HolomorphicUnitExtension X (dim X.left),
    ∃ D : CodimensionCycle X.left 1,
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
        integralToRationalCohomology X 2 E.firstChernClass

/-- An algebraic model together with its divisor representation gives the divisor of the
extension directly. -/
theorem hasDivisorOfUnitExtension_of_algebraicModel
    (hmodel : HasAlgebraicModel X) (hdivisor : HasDivisorOfAlgebraicModel X) :
    HasDivisorOfUnitExtension X := by
  intro E
  obtain ⟨L, hL, ⟨e⟩⟩ := hmodel E
  exact hdivisor E L hL e

omit [IsProjective X.hom] in
/-- Scaling by an integer preserves rational Hodge classes. -/
theorem zsmul_mem_hodgeClasses {p : ℕ} (m : ℤ)
    {α : FieldCohomology ℚ X (2 * p)} (hα : α ∈ Hdg^p(ℚ; X)) :
    m • α ∈ Hdg^p(ℚ; X) := by
  rw [← Int.cast_smul_eq_zsmul ℚ]
  exact Submodule.smul_mem _ _ hα

set_option backward.isDefEq.respectTransparency false in
/-- Given denominator clearing and divisors for extensions on `X`, every rational Hodge class
of degree two on `X` is the class of a rational divisor. -/
theorem exists_rationalSheafCycleClassOnCycles_eq_of_obligations
    (hclear : HasIntegralDenominatorClearing X) (hdivisor : HasDivisorOfUnitExtension X)
    (α : FieldCohomology ℚ X 2) (hα : α ∈ Hdg^1(ℚ; X)) :
    ∃ D : TensorProduct ℤ ℚ (CodimensionCycle X.left 1),
      rationalSheafCycleClassOnCycles
        (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D = α := by
  obtain ⟨m, β, hm, hβ⟩ := hclear α
  have hβHodge : integralToRationalCohomology X 2 β ∈ Hdg^1(ℚ; X) := by
    rw [hβ]
    exact zsmul_mem_hodgeClasses X m hα
  obtain ⟨E, hE⟩ := exists_holomorphicUnitExtension_of_integral_hodgeClass X β hβHodge
  obtain ⟨D, hD⟩ := hdivisor E
  refine ⟨(1 / (m : ℚ)) ⊗ₜ[ℤ] D, ?_⟩
  rw [rationalSheafCycleClassOnCycles_tmul, hD, hE, hβ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    one_div, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hm), one_smul]

/-- The rational Lefschetz `(1, 1)` theorem follows from denominator clearing and the divisor
representation of unit-sheaf extensions on every smooth projective integral complex variety.
This is a reduction, not a proof of `RationalLefschetzOneOne`. -/
theorem _root_.RationalLefschetzOneOne.of_obligations
    (hclear : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasIntegralDenominatorClearing X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne := by
  intro X _ _ _ α hα
  exact exists_rationalSheafCycleClassOnCycles_eq_of_obligations X (hclear X) (hdivisor X) α hα

end AlgebraicGeometry.ComplexPoint
