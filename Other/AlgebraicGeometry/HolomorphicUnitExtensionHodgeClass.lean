/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitExtension
public import Other.AlgebraicGeometry.HolomorphicIntegralHodgeClass
public import Other.CategoryTheory.Abelian.ExtOneRepresentative

/-!
# Unit-sheaf extensions representing integral Hodge classes
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance holomorphicUnitExtensionHodgeTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

namespace HolomorphicUnitExtension

/-- Every degree-one class of the holomorphic-unit sheaf is represented by an extension. -/
theorem exists_cohomologyClass
    (β : Abelian.Ext.{1} (𝓒(↧(ComplexPoint X); ℤ)) (holomorphicUnitSheaf X d) 1) :
    ∃ E : HolomorphicUnitExtension X d, E.cohomologyClass = β := by
  obtain ⟨M, i, p, w, h, hβ⟩ := Abelian.Ext.exists_shortExact β
  exact ⟨⟨M, i, p, w, h⟩, hβ⟩


end HolomorphicUnitExtension

/-- Integral Hodge classes are first Chern classes of extensions by holomorphic units. -/
theorem exists_holomorphicUnitExtension_of_integral_hodgeClass [IsIntegral X.left] [Smooth X.hom]
    (α : H^2(X; ℤ))
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    ∃ E : HolomorphicUnitExtension X (dim X.left), E.firstChernClass = α := by
  obtain ⟨β, hβ⟩ := exists_holomorphicFirstChernClass_of_integral_hodgeClass X α hα
  obtain ⟨E, hE⟩ := HolomorphicUnitExtension.exists_cohomologyClass X (dim X.left) β
  refine ⟨E, ?_⟩
  apply (sheafCohomologyEquivExt X (𝓒(↧(ComplexPoint X); ℤ)) 2).injective
  rw [HolomorphicUnitExtension.firstChernClass, AddEquiv.apply_symm_apply, hE, hβ]

end AlgebraicGeometry.ComplexPoint
