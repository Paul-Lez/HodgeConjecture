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

public import Mathlib.Topology.Sheaves.Flasque

/-!
# Evaluation of an abelian sheaf on an open set

Evaluation of an additive sheaf on a fixed open set, as a functor. Global sections are the
special case of the top open set; this file is the common home of that functor, which both the
support theory and the flasque-complex machinery use.

This is deliberately the *concrete* evaluation functor rather than Mathlib's `Sheaf.Γ`, which is
defined as an abstract right adjoint of the constant sheaf functor and is therefore only
isomorphic, not equal, to evaluation at `⊤` (see `CategoryTheory.Sheaf.ΓNatIsoSheafSections`).
The proofs downstream depend on evaluation being definitionally transparent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Evaluation of an additive sheaf on an ambient open set. -/
def supportEvaluation (V : Opens X) : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op V)

instance (V : Opens X) : (supportEvaluation X V).Additive where
  map_add := by intros; rfl

end TopCat.Sheaf
