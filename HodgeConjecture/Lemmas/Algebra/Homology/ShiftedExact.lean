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

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Exactness for shifted morphisms

This file gives the elementwise exactness statement for morphisms into a distinguished triangle
in an arbitrary shifted degree. It is the shifted version of
`Pretriangulated.Triangle.coyoneda_exact₁`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.ShiftedHom

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {X Y Z : C}

/-- Postcomposition with an invertible shifted morphism is a bijection on every shifted Hom.
The shift-addition associator is included explicitly, so the source and target degrees may be
written in any provably equal normal form. -/
noncomputable def postcompEquivOfIsIso {a b c : ℤ}
    (g : ShiftedHom Y Z b) [IsIso g] (h : b + a = c) :
    ShiftedHom X Y a ≃ ShiftedHom X Z c :=
  (Iso.refl X).homCongr
    (asIso (g⟦a⟧') ≪≫ (shiftFunctorAdd' C b a c h).symm.app Z)

@[simp] lemma postcompEquivOfIsIso_apply {a b c : ℤ}
    (g : ShiftedHom Y Z b) [IsIso g] (h : b + a = c)
    (f : ShiftedHom X Y a) :
    postcompEquivOfIsIso g h f = f.comp g h := by
  simp [postcompEquivOfIsIso, ShiftedHom.comp]

end CategoryTheory.ShiftedHom
