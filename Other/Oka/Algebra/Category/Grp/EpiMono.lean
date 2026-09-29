/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Epimorphisms and the forgetful functor on abelian groups -/

@[expose] public section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- The forgetful functor from abelian groups to types preserves epimorphisms. -/
instance : (forget AddCommGrpCat.{u}).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    exact (CategoryTheory.epi_iff_surjective _).2 hf

end AddCommGrpCat
