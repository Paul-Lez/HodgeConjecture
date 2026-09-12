/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization

/-!
# The actual localization sequence on injective coefficient complexes

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

attribute [local instance] derivedSupportLocalizationSheafDerivedCategory

attribute [local instance] derivedSupportLocalizationGroupDerivedCategory

end TopCat.Sheaf
