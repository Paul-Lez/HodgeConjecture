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

public import HodgeConjecture.Mathlib.Algebra.Homology.StupidTruncation

/-!
# Natural transformation from a stupid truncation
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (e : c.Embedding c') [e.IsTruncGE]

/-- The inclusions of stupid truncations form a natural transformation. -/
def stupidTruncInclusionNatTrans :
    e.stupidTruncFunctor C ⟶ Functor.id (HomologicalComplex C c') where
  app K := stupidTruncInclusion K e
  naturality _ _ f := stupidTruncMap_comp_stupidTruncInclusion e f

end HomologicalComplex
