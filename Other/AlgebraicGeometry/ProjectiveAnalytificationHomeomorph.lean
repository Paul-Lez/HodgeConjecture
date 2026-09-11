/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Mathlib.Topology.Homeomorph.Lemmas

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The analytification of projective space is the linear projectivization

`ProjectiveAnalytification.lean` builds a continuous bijection
`projectivizationToComplexPoint` from the linear projectivization of `ℂ^{N+1}` onto the complex
points of scheme-theoretic projective space, but never packages it as a homeomorphism.  Since the
source is compact and the target is Hausdorff, the two are in fact homeomorphic; this file
records that, so that topological questions about `ℙᴺ(ℂ)^an` — in particular the construction of
its standard affine charts, needed for the `H⁰` comparison for twists — can be transported to the
concrete quotient model.
-/

@[expose] public noncomputable section

open CategoryTheory Metric

namespace AlgebraicGeometry.ComplexProjectiveSpace

/-- Homogeneous coordinates identify the linear projectivization of `ℂ^{N+1}` with the
analytification of scheme-theoretic projective space, as topological spaces. -/
noncomputable def projectivizationHomeomorph (n : ℕ) :
    Projectivization ℂ (CoordinateSpace n) ≃ₜ
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (projectivizationToComplexPoint (n := n))
      ⟨injective_projectivizationToComplexPoint, surjective_projectivizationToComplexPoint⟩)
    continuous_projectivizationToComplexPoint

@[simp]
lemma projectivizationHomeomorph_apply (n : ℕ) (p : Projectivization ℂ (CoordinateSpace n)) :
    projectivizationHomeomorph n p = projectivizationToComplexPoint p :=
  rfl

@[simp]
lemma projectivizationHomeomorph_symm_apply (n : ℕ)
    (z : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    projectivizationToComplexPoint ((projectivizationHomeomorph n).symm z) = z :=
  (projectivizationHomeomorph n).apply_symm_apply z

end AlgebraicGeometry.ComplexProjectiveSpace
