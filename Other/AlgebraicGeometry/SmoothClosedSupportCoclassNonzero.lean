/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothSupport.CoclassSection
public import Other.AlgebraicGeometry.SmoothClosedSupportCoclassRestrictionNonzero
public import Other.AlgebraicTopology.SupportRelativeCohomologyGermNonzero

/-!
# Nonvanishing of smooth closed-support coclass sections

The normal coclass remains nonzero on every neighborhood of its center, so its germ
is nonzero. The globally glued coclass section has this germ and hence is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The normalized normal coclass has nonzero germ at its center. -/
theorem smoothClosedSupportNormalCoclassGerm_ne_zero
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (Point.map i z) (mem_smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) ≠ 0 :=
  supportRelativeCohomologyGerm_ne_zero_of_restrict_ne_zero _ _ _ _ _ _ _
    (smoothClosedSupportNormalCoclass_restrict_ne_zero X Y i m d z V hzV)

/-- A point of the smooth support witnesses nonvanishing of its global coclass section. -/
theorem smoothClosedSupportCoclassSection_ne_zero (z : ComplexPoint Y) :
    smoothClosedSupportCoclassSection X Y i m d ≠ 0 := by
  intro hzero
  have hg := smoothClosedSupportCoclassSection_germ_eq_normalCoclass
    X Y i m d z ⊤ (show Point.map i z ∈ (⊤ : Opens (ComplexPoint X)) from trivial)
  rw [hzero, map_zero] at hg
  exact smoothClosedSupportNormalCoclassGerm_ne_zero X Y i m d z ⊤ trivial hg.symm

end AlgebraicGeometry.ComplexPoint
