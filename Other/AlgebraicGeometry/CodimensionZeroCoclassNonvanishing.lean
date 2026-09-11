/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CodimensionZeroClassComparison
public import Other.AlgebraicGeometry.CycleComponentCoclassNonzeroTransfer
public import Other.AlgebraicGeometry.SmoothClosedSupportCoclassNonzero

/-!
# Nonvanishing of component coclasses and the codimension-zero cycle class

A complex point of the component's smooth locus detects its nonzero normal coclass germ.
For the generic component, forgetting support is injective, so the ordinary cycle class
is nonzero in every dimension. Analytic connectedness now follows from smoothness and integrality,
which gives the codimension-zero Hodge conjecture.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Every component's normalized coclass section is nonzero, as detected on its smooth locus. -/
theorem cycleComponentSmoothSupportCoclassSection_ne_zero
    (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
    (hx : coheight x = p) :
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx ≠ 0 := by
  apply cycleComponentSmoothSupportCoclassSection_ne_zero_of_lift_ne_zero X x hx
  apply (cycleComponentSmoothClosedLiftCoclassSection_ne_zero_iff X x hx).mpr
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x
    (d := d) hx
  obtain ⟨z⟩ := cycleComponentSmoothLocusOver_nonempty X x
  exact smoothClosedSupportCoclassSection_ne_zero _ _ _ (d - p) d z

/-- The generic component's normalized coclass section is nonzero in every dimension. -/
theorem cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    cycleComponentSmoothSupportCoclassSection X (genericPoint X.left)
      (d := d) (coheight_genericPoint_eq_zero X) ≠ 0 :=
  cycleComponentSmoothSupportCoclassSection_ne_zero X _ (coheight_genericPoint_eq_zero X)

/-- The constructed ordinary cycle class of the whole variety is nonzero in every dimension. -/
theorem cycleComponentSheafClass_genericPoint_ne_zero
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    cycleComponentSheafClass X (genericPoint X.left)
      (d := d) (coheight_genericPoint_eq_zero X) ≠ 0 :=
  fun h ↦ cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero X d
    ((cycleComponentSheafClass_genericPoint_eq_zero_iff X d).mp h)

/-- The constructed codimension-zero span agrees with the span of the cohomological unit. -/
theorem algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan :
    algebraicCycleClassSpan X 0 = codimensionZeroCycleClassSpan X :=
  (algebraicCycleClassSpan_zero_eq_codimensionZeroCycleClassSpan_iff X).mpr
    (cycleComponentSheafClass_genericPoint_ne_zero X (dim X.left))

/-- The constructed codimension-zero classes span degree-zero cohomology. -/
theorem algebraicCycleClassSpan_zero_eq_top :
    algebraicCycleClassSpan X 0 = ⊤ :=
  algebraicCycleClassSpan_zero_eq_top_of_coclassSection_ne_zero X
    (cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero X (dim X.left))

/-- The codimension-zero Hodge conjecture in every dimension. -/
theorem rationalHodgeClasses_zero_eq_algebraicCycleClassSpan :
    Hdg^0(ℚ; X) = algebraicCycleClassSpan X 0 :=
  rationalHodgeClasses_zero_eq_algebraicCycleClassSpan_of_coclassSection_ne_zero X
    (cycleComponentSmoothSupportCoclassSection_genericPoint_ne_zero X (dim X.left))

end AlgebraicGeometry.ComplexPoint
