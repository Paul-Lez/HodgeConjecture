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
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Printing the ring categories using the `↧` notation

Mathlib registers `delabApp` as the delaborator for `SemiRingCat.of`, `RingCat.of`,
`CommSemiRingCat.of` and `CommRingCat.of`, purely to stop `delabStructureInstance` printing them as
`{ carrier := R, commRing := ... }`. This file re-registers them to use
`CategoryTheory.delabOf` instead, so that they print as `↧R`.

Delaborators for a given head constant are tried most-recently-registered first, and
`CategoryTheory.delabOf` falls back to `delabApp`, so these strictly refine the Mathlib behaviour.

This file is copied from [`mathlib4` pull request
#41811](https://github.com/leanprover-community/mathlib4/pull/41811). It can be deleted once that
lands.
-/

public meta section

open Lean.PrettyPrinter.Delaborator

/-- Print `SemiRingCat.of R` as `↧R`. -/
@[app_delab SemiRingCat.of]
def SemiRingCat.delabOf' : Delab := CategoryTheory.delabOf

/-- Print `RingCat.of R` as `↧R`. -/
@[app_delab RingCat.of]
def RingCat.delabOf' : Delab := CategoryTheory.delabOf

/-- Print `CommSemiRingCat.of R` as `↧R`. -/
@[app_delab CommSemiRingCat.of]
def CommSemiRingCat.delabOf' : Delab := CategoryTheory.delabOf

/-- Print `CommRingCat.of R` as `↧R`. -/
@[app_delab CommRingCat.of]
def CommRingCat.delabOf' : Delab := CategoryTheory.delabOf
