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

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Points over a commutative ring, and analytification

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public section

open CategoryTheory Topology
open scoped CommRingCat.HomTopology

namespace AlgebraicGeometry

variable (R : Type) [CommRing R]

/-- A projective complex scheme is Noetherian. -/
theorem isNoetherian_of_isProjective (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] : IsNoetherian X.left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom

namespace Point

variable {R}

section Functoriality

variable {X Y Z : Over (Spec ↧R)}

end Functoriality

section IsLocalRing

variable [IsLocalRing R] {X : Over (Spec ↧R)}

section Topology

variable [TopologicalSpace R]

variable [ContinuousMul R] [IsOpenUnits R]

end Topology

end IsLocalRing

section Field

variable {K : Type} [Field K] {X : Over (Spec ↧K)}

/-- Over a field, a `K`-point is a scheme point together with an embedding of its residue field.

This refines `stalkData`: the stalk homomorphism out of a local ring into a field factors through
the residue field. -/
noncomputable def residueData (z : Point K X) :
    Σ x : X.left, X.left.residueField x ⟶ ↧K :=
  Scheme.SpecToEquivOfField K X.left z.left

end Field

end Point

end AlgebraicGeometry

end

@[expose] public section

open CategoryTheory Topology
open scoped CommRingCat.HomTopology

namespace AlgebraicGeometry

variable (R : Type) [CommRing R]

namespace Point

variable {R}

section Functoriality

variable {X Y Z : Over (Spec ↧R)}

end Functoriality

section IsLocalRing

variable [IsLocalRing R] {X : Over (Spec ↧R)}

section Topology

variable [TopologicalSpace R]

variable [ContinuousMul R] [IsOpenUnits R]

/-- The `R`-points over a scheme open form an analytic open set. -/
lemma isOpen_overOpen (U : X.left.Opens) :
    IsOpen (overOpen U : Set (Point R X)) := by
  simpa using isOpen_overOpen_inter_preimage U 0 Set.univ isOpen_univ

end Topology

end IsLocalRing

section Field

variable {K : Type} [Field K] {X : Over (Spec ↧K)}

/-- Over a field, a `K`-point belongs to a principal open exactly when its defining function is
nonzero there. -/
lemma mem_overOpen_basicOpen_iff_evaluate_ne_zero {U : X.left.Opens} (s : Γ(X.left, U))
    (z : Point K X) (hz : z ∈ overOpen U) :
    z ∈ overOpen (X.left.basicOpen s) ↔ evaluate U s z ≠ 0 := by
  rw [mem_overOpen_basicOpen_iff_isUnit_evaluate s z hz, isUnit_iff_ne_zero]

/-- Over a field, a regular function on a principal open of an affine open is a genuine quotient
of regular functions on the whole affine open. -/
lemma exists_evaluate_basicOpen_eq_div {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (t : Γ(X.left, X.left.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X.left, U)), ∀ z : Point K X,
      z ∈ overOpen (X.left.basicOpen f) →
        evaluate (X.left.basicOpen f) t z = evaluate U a z / evaluate U f z ^ k := by
  obtain ⟨k, a, h⟩ :=
    exists_evaluate_basicOpen_eq_inverse_mul (X := X) hU f t
  exact ⟨k, a, fun z hz ↦ by rw [h z hz, Ring.inverse_eq_inv', div_eq_inv_mul]⟩

end Field

end Point

end AlgebraicGeometry
