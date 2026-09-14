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

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Constant sheaves of additive groups on a topological space

`CategoryTheory.constantSheaf` sheafifies the constant presheaf on a site. This file
specialises it to the site of open subsets of a topological space with values in additive
groups, and introduces notation for the two ways the value is given: as an object
`A : AddCommGrpCat`, written `𝓒[X, A]`, and as a type `R` carrying an `AddCommGroup`
instance — a field, a ring, `ℤ` — written `𝓒(X, R)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- The constant sheaf functor on `X`, from additive groups to sheaves of additive groups.

The codomain is written with `CategoryTheory.Sheaf`, whose category instance is the one
Mathlib's instances for `CategoryTheory.constantSheaf` are stated for; instance search is keyed
on that category instance, so writing it this way is what lets those instances be found. -/
abbrev constantFunctor :
    AddCommGrpCat.{u} ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The constant sheaf on `X` with value the additive group `A`.

The codomain is written with `TopCat.Sheaf`, whose category instance carries the sheaf-level
instances this object is used with. -/
abbrev const (A : AddCommGrpCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantFunctor X).obj A

@[inherit_doc const]
notation3 "𝓒[" X ", " A "]" => TopCat.Sheaf.const X A

/-- The constant sheaf on `X` with value the additive group of `R`. -/
notation3 "𝓒(" X ", " R ")" => TopCat.Sheaf.const X (AddCommGrpCat.of R)

end TopCat.Sheaf

end
