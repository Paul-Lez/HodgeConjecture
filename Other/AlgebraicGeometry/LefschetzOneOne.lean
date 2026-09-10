/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Statement

/-!
# The rational Lefschetz (1, 1) theorem assuming the Hodge conjecture

On a smooth projective integral complex variety, every rational cohomology class of degree two
and Hodge type `(1, 1)` is the class of a rational divisor. Here a rational divisor is an element
of `ℚ ⊗[ℤ] CodimensionCycle X 1`, and its class is given by the constructed cycle-class map.

The proof specializes `HodgeConjecture` to codimension one and realizes the resulting span
membership by a rational cycle. It uses the conjecture as an explicit hypothesis.
`HodgeConjecture.rationalLefschetzOneOne_direct` copies the type of that implication with Lean's
`type_of%` elaborator and gives a second proof by checking the divisor generators directly.
The copied type retains the Hodge-conjecture hypothesis.

This is the rational algebraicity statement. The classical integral Lefschetz `(1, 1)` theorem
asserts that every integral `(1, 1)` class is the first Chern class of a line bundle. Specializing
the rational Hodge conjecture does not establish that stronger integral statement, nor does this
file prove that divisor classes have Hodge type `(1, 1)` or descend the map to the Chow group.

## References

[P. Deligne, *The Hodge Conjecture*, §2(iii)]
(https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open CategoryTheory AlgebraicGeometry ComplexPoint

/-- The rational Lefschetz `(1, 1)` statement for smooth projective integral complex varieties:
every rational Hodge class in degree two is the class of a rational divisor. -/
@[expose] public def RationalLefschetzOneOne : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (α : FieldCohomology ℚ X 2),
    α ∈ Hdg^1(ℚ; X) →
      ∃ D : TensorProduct ℤ ℚ (CodimensionCycle X.left 1),
        rationalSheafCycleClassOnCycles
          (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D = α

/-- The Hodge conjecture implies the rational Lefschetz `(1, 1)` theorem. -/
public theorem HodgeConjecture.rationalLefschetzOneOne
    (hodge : HodgeConjecture) : RationalLefschetzOneOne := by
  intro X _ _ _ α hα
  exact algebraicCycleClassSpan_le_range_rationalSheafCycleClassOnCycles X 1 (hodge X 1 hα)

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A second direct proof of the same implication, with its statement copied using `type_of%`.
This still assumes the Hodge conjecture. The proof checks each divisor generator without using
`HodgeConjecture.rationalLefschetzOneOne` or the general span-to-cycle lemma. -/
public theorem HodgeConjecture.rationalLefschetzOneOne_direct :
    type_of% HodgeConjecture.rationalLefschetzOneOne := by
  intro hodge X _ _ _ α hα
  have hspan : algebraicCycleClassSpan X 1 ≤
      LinearMap.range (rationalSheafCycleClassOnCycles
        (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1) := by
    refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨1 ⊗ₜ[ℤ] CodimensionCycle.single x hx 1, ?_⟩
    refine (rationalSheafCycleClassOnCycles_tmul_single
      (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 1 x hx).trans ?_
    rw [one_smul]
    rfl
  exact hspan (hodge X 1 hα)
