/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# `TopologicalSpace.Opens.map` is a final functor

For a continuous map `f : X ⟶ Y`, taking preimages is a final functor
`Opens Y ⟶ Opens X`. This lets colimits over open neighborhoods commute with pullback.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

/-- `Opens.map f` is final. -/
instance final_map {X Y : TopCat.{u}} (f : X ⟶ Y) : (Opens.map f).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun _ ↦ ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun {_ _} _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

end TopologicalSpace.Opens
