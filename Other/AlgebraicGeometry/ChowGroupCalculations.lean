/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ChowGroup

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Sanity checks on Chow groups

Two boundary computations on the empty scheme and two computations of the codimension-zero Chow
group of the spectrum of a field, with integer and with rational coefficients.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace ChowGroup

/-- A concrete boundary computation: every Chow group of `Spec PUnit` is trivial. -/
example (p : ℕ) : Subsingleton (ChowGroup (Spec ↧PUnit) p) := by
  let := spec_punit_isEmpty
  infer_instance

/-- A rational-coefficient version of the same boundary computation. -/
example (p : ℕ) : Subsingleton (RationalChowGroup (Spec ↧PUnit) p) := by
  let := spec_punit_isEmpty
  infer_instance

/-- A nonempty calculation: `CH⁰(Spec ℚ) ≃ ℤ`, including its distinguished generator. -/
example : specFieldEquiv ℚ
    (mk (CodimensionCycle.single default
      (CodimensionCycle.specField_coheight ℚ default) 1)) = 1 := by
  simp

/-- The rational-coefficient calculation sends the same generator to `1 : ℚ`. -/
example : rationalSpecFieldEquiv ℚ
    (toRational (mk (CodimensionCycle.single default
      (CodimensionCycle.specField_coheight ℚ default) 1))) = 1 :=
  rationalSpecFieldEquiv_toRational_single ℚ 1

end ChowGroup

end AlgebraicGeometry
