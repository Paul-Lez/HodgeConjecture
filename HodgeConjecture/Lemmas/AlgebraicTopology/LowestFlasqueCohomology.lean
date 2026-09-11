/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.LowestFlasqueCohomology

/-!
# The actual lowest-degree cohomology comparison for flasque complexes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.LowestFlasqueCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

@[simp] theorem lowestSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (lowestSectionCohomologyIso X K N n hK hflasque U).hom =
      sectionCohomologyToSheafSection X K n U := rfl

@[simp] theorem lowestGlobalSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (lowestGlobalSectionCohomologyIso X K N n hK hflasque).hom =
      sectionCohomologyToSheafSection X K n ⊤ := rfl

end TopCat.Sheaf
