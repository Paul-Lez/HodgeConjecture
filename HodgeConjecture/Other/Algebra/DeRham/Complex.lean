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

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic
public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The algebraic de Rham complex

The generators-and-relations differential forms assemble into a cochain complex. An algebra
homomorphism induces a functorial cochain map by applying it to every coefficient of every form.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Algebra.DeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The algebraic de Rham cochain complex. -/
def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun p => ModuleCat.of R (Form R A p))
    (fun p => ModuleCat.ofHom (differential R A p))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact differential_squared R A p x)

@[simp] lemma complex_X (p : ℕ) : (complex R A).X p = ModuleCat.of R (Form R A p) := rfl

@[simp] lemma complex_d (p : ℕ) :
    (complex R A).d p (p + 1) = ModuleCat.ofHom (differential R A p) := by
  simp [complex]

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- The morphism of de Rham complexes induced by an algebra homomorphism. -/
def complexMap (f : A →ₐ[R] B) : complex R A ⟶ complex R B :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (map R f p)) fun p => by
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (map_differential R f p x).symm

@[simp] lemma complexMap_f (f : A →ₐ[R] B) (p : ℕ) :
    (complexMap R f).f p = ModuleCat.ofHom (map R f p) := rfl

@[simp] lemma complexMap_id : complexMap R (AlgHom.id R A) = 𝟙 (complex R A) := by
  apply HomologicalComplex.hom_ext
  intro p
  change ModuleCat.ofHom (map R (AlgHom.id R A) p) = _
  rw [map_id]
  rfl

variable {C : Type u} [CommRing C] [Algebra R C]

@[simp] lemma complexMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    complexMap R (g.comp f) = complexMap R f ≫ complexMap R g := by
  apply HomologicalComplex.hom_ext
  intro p
  change ModuleCat.ofHom (map R (g.comp f) p) =
    ModuleCat.ofHom (map R f p) ≫ ModuleCat.ofHom (map R g p)
  rw [map_comp]
  rfl

end Algebra.DeRham
