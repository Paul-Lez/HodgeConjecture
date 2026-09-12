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

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The inclusion of a subspace as a morphism of `TopCat`

Mathlib has no bundled form of `Subtype.val` as a morphism of `TopCat`, so every construction
that restricts a sheaf to a subspace spells out `TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩`
again. This file names it once.
-/

@[expose] public section

namespace TopCat

/-- The inclusion of a subspace of a topological space. -/
def subtypeInclusion (X : TopCat) (S : Set X) : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] lemma subtypeInclusion_apply (X : TopCat) (S : Set X) (x : S) :
    subtypeInclusion X S x = x.1 :=
  rfl

end TopCat
