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

public import Mathlib.Topology.Category.TopPair

/-!
# Maps of topological pairs from maps of subsets

Mathlib builds a morphism of `TopPair` from two morphisms of `TopCat` and a commuting square.
For pairs that come from `TopPair.ofSubset`, the second morphism is always a restriction of the
first, so this file builds the morphism, and the isomorphism, from one map of spaces.
-/

universe u

open CategoryTheory

@[expose] public noncomputable section

namespace TopPair

variable {X Y : TopCat.{u}} {A : Set X} {B : Set Y}

/-- The morphism of pairs `(X, A) ⟶ (Y, B)` that comes from a map `f : X ⟶ Y` with
`f '' A ⊆ B`. -/
def ofSubsetHom (f : X ⟶ Y) (hf : ∀ a ∈ A, f a ∈ B) :
    TopPair.ofSubset A ⟶ TopPair.ofSubset B :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun a => ⟨f a.1, hf a.1 a.2⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩) rfl

@[simp]
lemma ofSubsetHom_fst_apply (f : X ⟶ Y) (hf : ∀ a ∈ A, f a ∈ B) (x : X) :
    TopPair.Hom.fst (ofSubsetHom f hf) x = f x :=
  rfl

@[simp]
lemma ofSubsetHom_snd_apply (f : X ⟶ Y) (hf : ∀ a ∈ A, f a ∈ B) (a : A) :
    (TopPair.Hom.snd (ofSubsetHom f hf) a).1 = f a.1 :=
  rfl

/-- The isomorphism of pairs `(X, A) ≅ (Y, B)` that comes from a homeomorphism `e : X ≃ₜ Y`
that maps `A` onto `B`. -/
def isoOfSubset (e : X ≃ₜ Y) (he : ∀ x, e x ∈ B ↔ x ∈ A) :
    TopPair.ofSubset A ≅ TopPair.ofSubset B where
  hom := ofSubsetHom (TopCat.ofHom ⟨e, e.continuous⟩) fun _ ha => (he _).mpr ha
  inv := ofSubsetHom (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) fun b hb =>
    (he _).mp (by simpa using hb)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext a; exact Subtype.ext (e.symm_apply_apply a.1)
    · ext x; exact e.symm_apply_apply x
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext b; exact Subtype.ext (e.apply_symm_apply b.1)
    · ext y; exact e.apply_symm_apply y

end TopPair
