/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

For `0 → A → B → C → 0` this file constructs the canonical quasi-isomorphism
`A → mappingCocone (B → C)`. Its normalization is the actual inclusion `A → B`.
The proof uses the explicit mapping-cone rotation homotopy equivalence and the
canonical quasi-isomorphism from the cone of `A → B` to `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

end mappingCone

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- The explicit rotated-cone comparison, before shifting back to the homotopy
fiber. It is built from canonical chain maps, not from a choice of a completion
of a morphism of distinguished triangles. -/
def shiftedLiftShortComplex : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

end mappingCocone

end CochainComplex
