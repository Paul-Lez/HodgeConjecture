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

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Bounded-below cochain complexes

This file provides the degree-zero functor into bounded-below cochain complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CochainComplex.Plus

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The functor from `C` to bounded-below cochain complexes supported in degree zero. -/
noncomputable abbrev single₀ : C ⥤ CochainComplex.Plus C :=
  (CochainComplex.plus C).lift
    (CochainComplex.single₀ C ⋙ ComplexShape.embeddingUpNat.extendFunctor C)
    (fun A ↦ ⟨0, (inferInstance : CochainComplex.IsStrictlyGE
      (((CochainComplex.single₀ C).obj A).extend ComplexShape.embeddingUpNat) 0)⟩)

instance single₀_obj_isStrictlyGE (A : C) : ((single₀ C).obj A).obj.IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE
    (((CochainComplex.single₀ C).obj A).extend ComplexShape.embeddingUpNat) 0
  infer_instance

instance single₀_additive : (single₀ C).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (CochainComplex.single₀ C ⋙
      ComplexShape.embeddingUpNat.extendFunctor C).map_add

end CochainComplex.Plus
