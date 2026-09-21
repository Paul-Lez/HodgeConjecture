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

public import HodgeConjecture.Mathlib.CategoryTheory.Sites.SheafCohomology.Pair
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sets.Closeds

/-!
# Sheaf cohomology with support in a closed set

For a closed subset `Z` of a topological space `X`, `H^n_Z(X; F)` is the cohomology of the pair
`(X, X \ Z)` with coefficients in the abelian sheaf `F`, that is `Ext (ℤ[X, X \ Z]) F n`.
Forgetting the support is the map `H^n_Z(X; F) → H^n(X; F)` of the long exact sequence of the
pair.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

universe w u

variable (X : TopCat.{u})

instance {U V : Opens X} (f : U ⟶ V) : Mono f := ⟨fun _ _ _ => Subsingleton.elim _ _⟩

variable [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- `H^n_Z(X; F)`, the sheaf cohomology of `X` with support in the closed set `Z` and coefficients
in `F`: the cohomology of the pair `(X, X \ Z)`. -/
abbrev supportH (Z : Closeds X)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) : Type w :=
  CategoryTheory.Sheaf.relH F n (homOfLE (le_top : Z.compl ≤ ⊤))

@[inherit_doc supportH]
scoped notation:max "H_[" Z "]^" n:max "(" X "; " F ")" => supportH X Z F n

variable {X} (Z : Closeds X)
  (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- `H^n_Z(X; F) → H^n(X; F)`, forgetting the support. -/
def supportH.forget (n : ℕ) : H_[Z]^n(X; F) →+ F.H n :=
  (CategoryTheory.Sheaf.H'.addEquivTerminal isTerminalTop F n).toAddMonoidHom.comp
    (CategoryTheory.Sheaf.relH.forget F _ n)

/-- The map on cohomology with support induced by a morphism of sheaves. -/
def supportH.map {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (g : F ⟶ G) (n : ℕ) : H_[Z]^n(X; F) →+ H_[Z]^n(X; G) :=
  CategoryTheory.Sheaf.relH.map _ g n

end TopCat.Sheaf

end
