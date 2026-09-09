/-
Copyright 2026 Yaël Dillies and The Formal Conjectures Authors.

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

public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Printing `TopCat` using the `↧` notation

Mathlib registers `delabApp` as the delaborator for `TopCat.of`, purely to stop
`delabStructureInstance` printing it as `{ carrier := X, str := ... }`. This file re-registers it to
use `CategoryTheory.delabOf` instead, so that it prints as `↧X`.

The declaration is named `delabOf'` because `TopCat.delabOf` is already taken by the Mathlib one it
shadows. Delaborators for a given head constant are tried most-recently-registered first, and
`CategoryTheory.delabOf` falls back to `delabApp`, so this strictly refines the Mathlib behaviour.

This file is copied from [`mathlib4` pull request
#41811](https://github.com/leanprover-community/mathlib4/pull/41811). It can be deleted once that
lands.
-/

public meta section

open Lean.PrettyPrinter.Delaborator

/-- This prints `TopCat.of X` as `↧X`, and in particular prevents it being printed as
`{ carrier := X, str := ... }` by `delabStructureInstance`. -/
@[app_delab TopCat.of]
def TopCat.delabOf' : Delab := CategoryTheory.delabOf
