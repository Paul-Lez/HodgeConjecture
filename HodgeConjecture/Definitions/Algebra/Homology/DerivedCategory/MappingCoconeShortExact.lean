/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

For `0 → A → B → C → 0` this file constructs the canonical quasi-isomorphism
`A → mappingCocone (B → C)`. Its normalization is the inclusion `A → B`.
The proof uses the explicit mapping-cone rotation homotopy equivalence and the
canonical quasi-isomorphism from the cone of `A → B` to `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- Let `A → B → C` be a sequence of integer-indexed cochain complexes in an abelian category, with
zero composite. This is the canonical map `A[1] → Cone(B → C)` obtained from the first map `A →
B` and the zero component in `C`. When the sequence is short exact, the map is a
quasi-isomorphism. -/
def shiftedLiftShortComplex : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

end mappingCocone

end CochainComplex
