/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Algebraic.Basic

/-!
# A nonvanishing obstruction for algebraic elements

Mathlib supplies a polynomial relation with nonzero constant coefficient for every nonzero
algebraic element. Here we record its consequence for specialization.
-/

open Polynomial

namespace Polynomial

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

/-- If an element satisfies a polynomial relation with nonzero constant coefficient, a compatible
specialization sending that element to zero must kill the constant coefficient. -/
theorem algebraMap_coeff_zero_eq_zero_of_map_eq_zero {b : B} {p : R[X]}
    (hb : aeval b p = 0) (f : B →ₐ[R] C) (hfb : f b = 0) :
    algebraMap R C (p.coeff 0) = 0 := by
  calc
    algebraMap R C (p.coeff 0) = aeval (0 : C) p := coeff_zero_eq_aeval_zero' p
    _ = aeval (f b) p := by rw [hfb]
    _ = f (aeval b p) := aeval_algHom_apply f b p
    _ = 0 := by rw [hb, map_zero]

end Polynomial
