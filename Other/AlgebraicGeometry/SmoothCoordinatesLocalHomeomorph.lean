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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
public import Other.AlgebraicGeometry.EtaleLocalHomeomorph

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Smooth coordinates are local homeomorphisms

The étale coordinates supplied by smoothness are local homeomorphisms onto complex affine space,
both as a map out of the coordinate neighborhood and as a map out of the corresponding analytic
open subset of the ambient complex-point space. This is the local-homeomorphism packaging of
`AlgebraicGeometry.ComplexAlgHom.isLocalHomeomorph_etaleBaseAlgHom`.

The charts the conjecture is stated with are the explicit projection charts of
`SmoothComplexCoordinates.lean`, whose inverses retain the standard étale construction, so this
packaging is not needed to state the conjecture.
-/

@[expose] public section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry

open ComplexAlgHom

attribute [local instance] overSpecAlgebra

noncomputable section

variable (X : Over (Spec ↧ℂ))

namespace LocalEtaleCoordinates

variable {X} {d : ℕ} [SmoothOfRelativeDimension d X.hom] {x : X.left}
  (D : LocalEtaleCoordinates X d x)

-- the coordinate ring's algebra structure over the polynomial ring is `local` where it is built
attribute [local instance] coordinateRingAlgebra coordinateRingComplexAlgebra
  coordinateRingScalarTower coordinateRingEtale

/-- The ring-theoretic coordinates are local homeomorphisms to complex affine space. -/
lemma isLocalHomeomorph_algebraicCoordinates :
    IsLocalHomeomorph D.algebraicCoordinates :=
  (ComplexAlgHom.mvPolynomialAlgHomHomeomorph d).isLocalHomeomorph.comp
    ((ComplexAlgHom.isLocalHomeomorph_etaleBaseAlgHom
      Γ(D.neighborhood.toScheme, ⊤)).comp
        D.pointAlgHomHomeomorph.isLocalHomeomorph)

/-- The analytic coordinates supplied by smoothness are local homeomorphisms to complex affine
space. -/
lemma isLocalHomeomorph_analyticCoordinates :
    IsLocalHomeomorph D.analyticCoordinates := by
  rw [← D.algebraicCoordinates_eq_analyticCoordinates]
  exact D.isLocalHomeomorph_algebraicCoordinates

/-- The same coordinates are a local homeomorphism on the corresponding analytic open subset of
the ambient complex-point space. -/
lemma isLocalHomeomorph_ambientAnalyticCoordinates :
    IsLocalHomeomorph D.ambientAnalyticCoordinates := by
  exact D.isLocalHomeomorph_analyticCoordinates.comp
    (ComplexPoint.openHomeomorph X D.neighborhood).symm.isLocalHomeomorph

end LocalEtaleCoordinates

end

end AlgebraicGeometry
