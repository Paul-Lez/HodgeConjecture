/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
module

public import Other.AlgebraicGeometry.Hodge.CodimensionZeroComparison
public import Other.AlgebraicGeometry.Cycle.Component.CoclassNonzero
public import Other.AlgebraicGeometry.Cycle.SmoothPair.CoclassNonzero

/-!
# Nonvanishing of component coclasses

The representation-independent coclass nonvanishing results are retained. Their former
application to ordinary hypercohomology awaits a derived-global-sections comparison.
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

end AlgebraicGeometry.ComplexPoint
