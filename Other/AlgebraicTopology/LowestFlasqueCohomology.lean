/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueLowestCohomology

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- In particular, the actual lowest-degree global section-complex cohomology
is canonically isomorphic to global sections of the cohomology sheaf. -/
def lowestGlobalSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (IsFlasque.BoundedBelowComplex.globalSectionsComplex K).homology n ≅
      (K.homology n).obj.obj (op (⊤ : Opens X)) :=
  lowestSectionCohomologyIso X K N n hK hflasque ⊤

@[simp]
theorem lowestGlobalSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (lowestGlobalSectionCohomologyIso X K N n hK hflasque).hom =
      sectionCohomologyToSheafSection X K n ⊤ := rfl

end TopCat.Sheaf
