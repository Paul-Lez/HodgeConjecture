/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Ring.Basic

/-!
# Left multiplication as an additive endomorphism

Mathlib has `AddMonoidHom.mulLeft` and its `coe_mulLeft` simp lemma, and bundles the map
`a ↦ AddMonoidHom.mulLeft a` as `AddMonoidHom.mul`, but does not record how `mulLeft` interacts
with the ring structure of its argument. These four lemmas do, so that multiplication by a scalar
can be manipulated as an additive endomorphism.
-/

public section

namespace AddMonoidHom

@[simp] lemma mulLeft_zero {R : Type*} [NonUnitalNonAssocSemiring R] :
    mulLeft (0 : R) = 0 := by
  ext
  simp

@[simp] lemma mulLeft_one {R : Type*} [NonAssocSemiring R] :
    mulLeft (1 : R) = AddMonoidHom.id R := by
  ext
  simp

@[simp] lemma mulLeft_add {R : Type*} [NonUnitalNonAssocSemiring R] (a b : R) :
    mulLeft (a + b) = mulLeft a + mulLeft b := by
  ext
  simp [add_mul]

@[simp] lemma mulLeft_mul {R : Type*} [NonUnitalSemiring R] (a b : R) :
    mulLeft (a * b) = (mulLeft a).comp (mulLeft b) := by
  ext
  simp [mul_assoc]

end AddMonoidHom
