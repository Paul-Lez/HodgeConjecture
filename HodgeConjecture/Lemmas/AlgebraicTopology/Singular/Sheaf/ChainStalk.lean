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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Chain
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-!
# Stalks of the relative singular-chain presheaf

The key geometric fact is that a singular simplex avoiding a point has compact image and,
in a Hausdorff space, therefore avoids an open neighborhood of that point. This allows the
local relative chain complex to be identified with the colimit over open neighborhoods.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- Evaluating a chain complex in degree `n` and forgetting its scalar structure. -/
def chainDegreeAdditiveFunctor (n : ℕ) : ChainCategory R ⥤ AddCommGrpCat.{u} :=
  HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

instance chainDegreeAdditiveFunctor_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{u, u} (chainDegreeAdditiveFunctor R n) where
  preservesColimitsOfShape {J} _ := by
    unfold chainDegreeAdditiveFunctor
    infer_instance

end AlgebraicTopology.Singular
