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

public import HodgeConjecture.Mathlib.AlgebraicGeometry.Over.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Etale
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

/-!
# SmoothCoordinates, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
open CategoryTheory Topology Filter
namespace AlgebraicGeometry
open ComplexAlgHom
noncomputable section
attribute [local instance] overSpecAlgebra
section SchemeStructure
variable {Y : Scheme} (f : Y ⟶ Spec ↧ℂ)
variable (X : Over (Spec ↧ℂ))

lemma algebraMap_isStandardSmooth {V : X.left.Opens}
    (h : (X.hom.appLE ⊤ V (by simp)).hom.IsStandardSmooth) :
    (algebraMap ℂ Γ(X.left, V)).IsStandardSmooth := by
  exact RingHom.isStandardSmooth_respectsIso.2 _
    (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv h

end SchemeStructure
end
end AlgebraicGeometry
end
