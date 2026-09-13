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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
public import Mathlib.Topology.IsLocalHomeomorph
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization

/-!
# Localization, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public section
open scoped Topology
open Topology
namespace AlgebraicGeometry.ComplexAlgHom
open ComplexPoint Point
noncomputable section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (S : Type) [CommRing S] [Algebra ℂ S]

lemma isLocalHomeomorph_localizationAwayAlgHomMap (f : S) :
    IsLocalHomeomorph (localizationAwayAlgHomMap S f) :=
  (isOpenEmbedding_localizationAwayAlgHomMap S f).isLocalHomeomorph

end
end AlgebraicGeometry.ComplexAlgHom
end
