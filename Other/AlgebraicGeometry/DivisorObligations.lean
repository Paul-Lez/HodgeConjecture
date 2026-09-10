/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.CartierDataOfTrivializingCover

/-!
# Decomposition of `HasDivisorOfAlgebraicModel`

`HasDivisorOfAlgebraicModel X` (`Other/AlgebraicGeometry/LefschetzOneOneReduction.lean`) is the
third remaining obligation of the unconditional rational Lefschetz `(1, 1)` theorem: an algebraic
invertible sheaf `L` whose analytification is the section sheaf of a unit-sheaf extension `E` is
represented by a codimension-one cycle whose constructed cycle class is the rational first Chern
class of `E`.

This file cuts it along the divisor of a rational section, into an algebraic half and a
geometric half, and proves the algebraic half:

* **Proved.** Every invertible `L : X.left.Modules` is represented by Cartier data
  (`exists_cartierData_represents`): an invertible sheaf has a trivializing cover by nonempty
  opens with a generating section on each member
  (`Scheme.Modules.nonempty_trivializingCover_of_isInvertible`), and the transition functions
  between the members and a fixed reference member are units of the structure sheaf, hence
  nonzero rational functions with equal orders of vanishing on overlaps
  (`Scheme.Modules.TrivializingCover.cartierData_represents`). Its Weil divisor is
  `Scheme.CartierData.divisor`, the divisor of the corresponding rational section of `L`.
* **Remaining.** `HasDivisorClassOfSomeCartierData X`: the constructed cycle class of that
  divisor is the rational first Chern class of `E`. This is the geometric comparison, where the
  exponential sequence meets the normal-chart coclass of `CycleComponentSheafClass.lean`. Its
  uniform variant `HasDivisorClassOfCartierData X`, which asserts the same for *every*
  representing Cartier datum, is strictly stronger — it contains the vanishing of the
  constructed class of a principal divisor — and is not needed.

`Scheme.CartierData.Represents` is the relation that keeps the decomposition faithful: without
it the remaining obligation would be false, since an arbitrary divisor has no reason to have the
right class.

See `docs/DIVISOR_HANDOFF.md` for the mathematics and for how the remaining obligation may be
attacked.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

omit [Smooth X.hom] in
/-- Every invertible sheaf of modules on `X.left` is represented by Cartier data: the local
equations of a nonzero rational section of it. -/
theorem exists_cartierData_represents (L : X.left.Modules)
    (hL : TauCeti.SheafOfModules.IsInvertible L) :
    ∃ c : Scheme.CartierData X.left, c.Represents L := by
  obtain ⟨t⟩ := Scheme.Modules.nonempty_trivializingCover_of_isInvertible L hL
  exact t.exists_cartierData_represents

/-- Some Cartier data representing an algebraic model of a unit-sheaf extension has the
extension's rational first Chern class as its constructed cycle class.

This is what remains of `HasDivisorOfAlgebraicModel X` after the divisor of a rational section
has been constructed, and it is the weakest sufficient form: the Cartier data may be chosen. -/
def HasDivisorClassOfSomeCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∃ c : Scheme.CartierData X.left, c.Represents L ∧
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass

/-- The uniform form of the same comparison: *every* Cartier datum representing an algebraic
model has the extension's rational first Chern class as its constructed cycle class.

This is the natural statement, but it is strictly stronger than
`HasDivisorClassOfSomeCartierData`: two Cartier data representing the same sheaf are the local
equations of two rational sections, whose divisors differ by a principal divisor, so the uniform
form contains the vanishing of the constructed class of a principal divisor. Only the weaker
form is needed. -/
def HasDivisorClassOfCartierData : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 c.divisor =
        integralToRationalCohomology X 2 E.firstChernClass

/-- The uniform comparison implies the existential one, the Cartier data being supplied by
`exists_cartierData_represents`. -/
theorem hasDivisorClassOfSomeCartierData_of_cartierData
    (h : HasDivisorClassOfCartierData X) : HasDivisorClassOfSomeCartierData X := by
  intro E L hL e
  obtain ⟨c, hc⟩ := exists_cartierData_represents X L hL
  exact ⟨c, hc, h E L hL e c hc⟩

/-- The third obligation of the Lefschetz `(1, 1)` reduction follows from the cycle-class
comparison for the divisor of a rational section alone: the existence of that divisor is
proved. -/
theorem hasDivisorOfAlgebraicModel_of_divisorClass
    (hclass : HasDivisorClassOfSomeCartierData X) : HasDivisorOfAlgebraicModel X := by
  intro E L hL e
  obtain ⟨c, _, hc⟩ := hclass E L hL e
  exact ⟨c.divisor, hc⟩

end AlgebraicGeometry.ComplexPoint
