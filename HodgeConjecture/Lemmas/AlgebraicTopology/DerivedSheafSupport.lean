/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.DerivedSheafSupport

/-!
# Concrete sheaf sections with support and their right derived functor

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.DerivedSheafSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Uniqueness in the universal property of supported sections. -/
lemma liftSheafSectionsSupportedOutside_unique (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0)
    (g : F ⟶ (sheafSectionsSupportedOutside X U).obj G)
    (hg : g ≫ (sheafSectionsSupportedOutsideInclusion X U).app G = f) :
    g = liftSheafSectionsSupportedOutside X U f hf :=
  (cancel_mono (kernel.ι _)).1 (hg.trans (kernel.lift_ι _ _ _).symm)

attribute [local instance] supportSheafHasDerivedCategory

attribute [local instance] supportGroupsHasDerivedCategory

end TopCat.Sheaf
