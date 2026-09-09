/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Integer multiples in a ring

The map sending an integer `n` to `n * q` is additive for every ring.  Keeping
this elementary construction separate makes it reusable by the constant-sheaf
and cohomology developments without imposing field or scalar-algebra hypotheses.
-/

@[expose] public noncomputable section

/-- The additive map `n ↦ n q` from the integers to a ring. -/
def integerMultipleAddHom (R : Type*) [Ring R] (q : R) : ℤ →+ R where
  toFun n := (n : R) * q
  map_zero' := by simp
  map_add' a b := by simp [Int.cast_add, add_mul]

@[simp]
lemma integerMultipleAddHom_zero (R : Type*) [Ring R] :
    integerMultipleAddHom R 0 = 0 := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom]

@[simp]
lemma integerMultipleAddHom_add (R : Type*) [Ring R] (a b : R) :
    integerMultipleAddHom R (a + b) =
      integerMultipleAddHom R a + integerMultipleAddHom R b := by
  apply AddMonoidHom.ext
  intro n
  simp [integerMultipleAddHom, mul_add]
