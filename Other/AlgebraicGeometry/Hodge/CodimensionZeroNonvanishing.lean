/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
module

public import Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison
public import Other.AlgebraicGeometry.Cycle.Component.CoclassNonzero
public import Other.AlgebraicGeometry.Cycle.SmoothPair.CoclassNonzero

/-!
# Nonvanishing of the codimension-zero cycle class

The generic component is supported on the whole analytification. Forgetting support is therefore
injective, so nonvanishing of its normalized coclass implies nonvanishing of its ordinary cycle
class and proves the codimension-zero Hodge conjecture.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every component's normalized coclass section is nonzero, as detected on its smooth locus. -/
theorem cycleComponentSmoothSupportCoclassSection_ne_zero
    (x : X.left) {p : ℕ}
    (hx : coheight x = p) :
    cycleComponentSmoothSupportCoclassSection X x hx ≠ 0 := by
  apply cycleComponentSmoothSupportCoclassSection_ne_zero_of_lift_ne_zero X x hx
  apply (cycleComponentSmoothClosedLiftCoclassSection_ne_zero_iff X x hx).mpr
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  obtain ⟨z⟩ := cycleComponentSmoothLocusOver_nonempty X x
  exact smoothClosedSupportCoclassSection_ne_zero _ _ _ (dim X.left - p) (dim X.left) z

/-- The generic component's normalized coclass section is nonzero in every dimension. -/
theorem cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero :
    cycleComponentSmoothSupportCoclassSection X (genericPoint X.left)
      (coheight_genericPoint_eq_zero X) ≠ 0 :=
  cycleComponentSmoothSupportCoclassSection_ne_zero X _
    (coheight_genericPoint_eq_zero X)

/-- The constructed ordinary cycle class of the whole variety is nonzero. -/
theorem cycleComponentSheafClass_genericPoint_ne_zero :
    cycleComponentSheafClass X (genericPoint X.left)
        (coheight_genericPoint_eq_zero X) ≠ 0 :=
  fun h ↦ cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero X
    ((cycleComponentSheafClass_genericPoint_eq_zero_iff X).mp h)

/-- The constructed codimension-zero classes span degree-zero rational cohomology. -/
theorem algebraicCycleClassSpan_zero_eq_top :
    algebraicCycleClassSpan X 0 = ⊤ :=
  (algebraicCycleClassSpan_zero_eq_top_iff X).mpr
    (cycleComponentSheafClass_genericPoint_ne_zero X)

/-- The codimension-zero Hodge conjecture. -/
theorem rationalHodgeClasses_zero_eq_algebraicCycleClassSpan :
    Hdg^0(ℚ; X) = algebraicCycleClassSpan X 0 := by
  rw [hodgeClasses_zero_eq_top, algebraicCycleClassSpan_zero_eq_top]

end AlgebraicGeometry.ComplexPoint
