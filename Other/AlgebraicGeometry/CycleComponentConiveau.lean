/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSheafClass

/-!
# The support property of constructed cycle-component classes

This file records the first coniveau property of the constructed rational
cycle class.  A class obtained by forgetting support restricts to zero on the
complement of that support.  The proof is the consecutive-morphisms relation
in the distinguished triangle defining cohomology with support.

In particular, the class of an integral component restricts to zero away
from its analytic support.  This is the topological support condition that a
future filtered residue representative has to satisfy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance cycleComponentConiveauHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- Restriction of rational cohomology to the derived constant-sheaf complex
on the complement of a set. -/
def restrictFieldCohomologyAway (Z : Set (ComplexPoint X)) (n : ℤ) :
    FieldCohomology ℚ X n →+ Hypercohomology X
      (derivedPushforwardComplementConstantRationalComplexInt X Z) n :=
  hypercohomologyMap X (rationalRestrictionComplexInt X Z) n

/-- Forgetting support and then restricting to the complementary open gives
zero.  This is proved directly from the mapping-cone triangle used in the
definition of rational cohomology with support. -/
theorem restrictFieldCohomologyAway_forgetSupport (Z : Set (ComplexPoint X)) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    restrictFieldCohomologyAway X Z n (forgetSupport X Z n x) = 0 := by
  let e : Hypercohomology X
      (derivedPushforwardComplementConstantRationalComplexInt X Z) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj
          (derivedPushforwardComplementConstantRationalComplexInt X Z)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  apply e.injective
  let f := forgetSupportShiftedHom X Z
  let g := Localization.SmallShiftedHom.mk₀
    (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (rationalRestrictionComplexInt X Z)
  change e ((x.comp f (by omega)).comp g (by omega)) = e 0
  rw [Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_comp]
  rw [show e 0 = 0 from hypercohomologyEquiv_zero X
    (derivedPushforwardComplementConstantRationalComplexInt X Z) n]
  dsimp only [f, g]
  rw [Localization.SmallShiftedHom.equiv_mk₀]
  unfold forgetSupportShiftedHom
  erw [Localization.SmallShiftedHom.equiv_mk]
  let α : ShiftedHom
      (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
      (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Z))
      (n - 1) := Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q x
  let β : ShiftedHom
      (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Z))
      (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) (1 : ℤ) :=
    ShiftedHom.map (CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt X Z)).mor₃ DerivedCategory.Q
  let γ : ShiftedHom
      (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X))
      (DerivedCategory.Q.obj
        (derivedPushforwardComplementConstantRationalComplexInt X Z)) (0 : ℤ) :=
    ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map
      (rationalRestrictionComplexInt X Z))
  change (α.comp β (show (1 : ℤ) + (n - 1) = n by omega)).comp γ
      (show (0 : ℤ) + n = n by omega) = 0
  have hβγ : β.comp γ (show (0 : ℤ) + 1 = 1 by omega) =
      (0 : ShiftedHom
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Z))
        (DerivedCategory.Q.obj
          (derivedPushforwardComplementConstantRationalComplexInt X Z)) (1 : ℤ)) := by
    rw [ShiftedHom.comp_mk₀]
    exact Pretriangulated.comp_distTriang_mor_zero₃₁ _
      (DerivedCategory.mappingCone_triangle_distinguished
        (rationalRestrictionComplexInt X Z))
  rw [ShiftedHom.comp_assoc α β γ
    (show (1 : ℤ) + (n - 1) = n by omega)
    (show (0 : ℤ) + 1 = 1 by omega)
    (show (0 : ℤ) + 1 + (n - 1) = n by omega),
    hβγ, ShiftedHom.comp_zero]

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The constructed class of an integral component vanishes after
restriction to the complement of that component. -/
theorem cycleComponentSheafClass_restrict_complement
    (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    restrictFieldCohomologyAway X (cycleComponentSupport X x) (2 * (p : ℤ))
        (cycleComponentSheafClass X x (d := d) hx) = 0 := by
  rw [cycleComponentSheafClass_eq_forgetSupport]
  exact restrictFieldCohomologyAway_forgetSupport X
    (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x (d := d) hx)

end AlgebraicGeometry.ComplexPoint

