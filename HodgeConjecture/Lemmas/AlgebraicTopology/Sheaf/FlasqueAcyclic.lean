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

/-!
# Flasque sheaves are acyclic

A flasque sheaf of abelian groups on a topological space has vanishing sheaf cohomology in
every positive degree.  The proof uses an injective embedding and dimension shifting.  The
degree-one step uses surjectivity on global sections, which follows from flasqueness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

local instance extAddCommGroup
    {A B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {n : ℕ} :
    AddCommGroup (Abelian.Ext A B n) :=
  Abelian.Ext.instAddCommGroup

namespace IsFlasque

/-- The constant sheaf which represents global sections in sheaf cohomology. -/
abbrev globalSectionsSource : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))





end IsFlasque

end TopCat.Sheaf
