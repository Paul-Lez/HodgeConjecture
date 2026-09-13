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

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueAcyclic

/-!
# FlasqueAcyclic, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueAcyclic`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace
universe u
namespace TopCat.Sheaf
variable {X : TopCat.{u}}
namespace IsFlasque
attribute [local instance] extAddCommGroup

/-- The constant sheaf which represents global sections in sheaf cohomology. -/
abbrev globalSectionsSource : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

end IsFlasque
end TopCat.Sheaf
end
