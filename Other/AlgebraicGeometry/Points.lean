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

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped CommRingCat.HomTopology

namespace AlgebraicGeometry

variable (R : Type) [CommRing R]

namespace Point

variable {R}

section IsLocalRing

variable [IsLocalRing R] {X : Over (Spec ↧R)}

/-- Evaluation of a local regular function on its actual domain. -/
noncomputable def evaluateOnOpen (U : X.left.Opens) (s : Γ(X.left, U))
    (z : OverOpen (X := X) U) : R :=
  z.1.stalkHom (X.left.presheaf.germ U z.1.underlying z.2 s)

lemma evaluate_eq_evaluateOnOpen (U : X.left.Opens) (s : Γ(X.left, U))
    (z : OverOpen (X := X) U) :
    evaluate U s z.1 = evaluateOnOpen U s z := by
  rw [evaluate, dif_pos z.2]
  rfl

end IsLocalRing

end Point

/-- Analytification of schemes over `Spec ℂ` as a functor to topological spaces.

This is the canonical home for functorial complex points.  In particular, consumers need not
package their own morphism records or reprove identity and composition laws. -/
noncomputable def complexAnalytification :
    CategoryTheory.Functor (Over (Spec ↧ℂ)) TopCat where
  obj X := @TopCat.of (ComplexPoint X) Point.analyticTopology
  map f := @TopCat.ofHom _ _ Point.analyticTopology Point.analyticTopology
    (Point.continuousMap f)
  map_id X := by
    ext z
    simp [Point.continuousMap, Point.map]
  map_comp f g := by
    ext z
    simp [Point.continuousMap, Point.map, Category.assoc]

end AlgebraicGeometry
