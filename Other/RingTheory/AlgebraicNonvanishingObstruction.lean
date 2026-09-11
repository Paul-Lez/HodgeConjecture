/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.RingTheory.Algebraic.Basic

/-!
# A nonvanishing obstruction for algebraic elements

Mathlib supplies a polynomial relation with nonzero constant coefficient for every nonzero
algebraic element. Here we record its consequence for specialization.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B]

/-- If an element satisfies a polynomial relation, compatible ring maps which send that element
to zero must send the constant coefficient to zero. -/
theorem map_coeff_zero_eq_zero_of_map_eq_zero {b : B} {p : R[X]}
    (hb : aeval b p = 0) (f : R →+* C) (g : B →+* C)
    (hfg : f = g.comp (algebraMap R B)) (hgb : g b = 0) :
    f (p.coeff 0) = 0 := by
  have hcompat : (algebraMap C C).comp f = g.comp (algebraMap R B) := by
    simpa using hfg
  calc
    f (p.coeff 0) = (p.map f).coeff 0 := by rw [coeff_map]
    _ = aeval (0 : C) (p.map f) := coeff_zero_eq_aeval_zero _
    _ = aeval (g b) (p.map f) := by rw [hgb]
    _ = g (aeval b p) := (map_aeval_eq_aeval_map hcompat p b).symm
    _ = 0 := by rw [hb, map_zero]

end Polynomial
