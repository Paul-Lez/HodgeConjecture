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

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension

/-!
# Codimension-zero points of an integral scheme

An integral scheme has a unique point of codimension zero, namely its generic point.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- A codimension-zero point of an integral scheme is its generic point. -/
lemma eq_genericPoint_of_coheight_zero [IsIntegral X] (x : X) (hx : coheight x = 0) :
    x = genericPoint X := by
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨Order.coheight_eq_zero.mp hx le_top, genericPoint_specializes x⟩

end AlgebraicGeometry
