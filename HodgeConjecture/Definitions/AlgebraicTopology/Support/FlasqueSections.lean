/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsNaturality
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Supported sections preserve flasqueness

A supported section over `V` glues with zero on the excluded open `U` to a section on
`V ⊔ U`. Flasqueness extends that section to `W ⊔ U` when `V ≤ W`, and its restriction to
`W` vanishes on `W ⊓ U`, so it lies in the kernel defining supported sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)

/-- Restriction-pushforward on an ambient open is literally evaluation on its
intersection with the excluded open. -/
def supportedOutsideIntersectionIso :
    ((openRestrictionPushforward X U).obj F).obj.obj (op V) ≅ F.obj.obj (op (V ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V)))

variable {V} {W : Opens X}

end TopCat.Sheaf
