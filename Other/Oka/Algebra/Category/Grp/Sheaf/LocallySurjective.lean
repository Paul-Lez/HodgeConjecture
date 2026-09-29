/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Other.Oka.Algebra.Category.Grp.EpiMono

/-! # Local surjectivity of epimorphisms of sheaves of abelian groups -/

@[expose] public section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : Sheaf J AddCommGrpCat.{w}}

/-- A morphism of sheaves of abelian groups is locally surjective exactly when it is epi. -/
lemma isLocallySurjective_iff_epi_addCommGrp (f : F ⟶ G) :
    IsLocallySurjective f ↔ Epi f :=
  isLocallySurjective_iff_epi' (A := AddCommGrpCat.{w}) f

/-- An epimorphism of sheaves of abelian groups is locally surjective. -/
lemma isLocallySurjective_of_epi_addCommGrp (f : F ⟶ G) [Epi f] : IsLocallySurjective f :=
  (isLocallySurjective_iff_epi_addCommGrp f).2 ‹_›

end CategoryTheory.Sheaf
