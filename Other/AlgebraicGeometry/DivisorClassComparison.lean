/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DivisorClassCompatibility
public import Other.AlgebraicGeometry.CartierDataOfTrivializingCover

/-!
# From uniform divisor–Chern compatibility to existence
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

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

/-- The uniform comparison implies the existential one, the Cartier data being supplied by
`exists_cartierData_represents`. -/
theorem hasDivisorClassOfSomeCartierData_of_cartierData
    (h : HasDivisorClassOfCartierData X) : HasDivisorClassOfSomeCartierData X := by
  intro E L hL e
  obtain ⟨c, hc⟩ := exists_cartierData_represents X L hL
  exact ⟨c, hc, h E L hL e c hc⟩

end AlgebraicGeometry.ComplexPoint
