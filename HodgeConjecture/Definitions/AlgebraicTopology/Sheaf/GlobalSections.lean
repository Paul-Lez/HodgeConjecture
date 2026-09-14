/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Topology.Sheaves.Abelian

/-! # Global sections of sheaves and sheaf complexes -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u v w

variable (C : Type u) [Category.{v} C] [Abelian C]
  (X : TopCat.{w}) [HasSheafify (Opens.grothendieckTopology X) C]

/-- Evaluation of a sheaf on the top open subset. -/
def globalSectionsFunctor : Sheaf C X ⥤ C :=
  (sheafSections (Opens.grothendieckTopology X) C).obj (op (⊤ : Opens X))

instance globalSectionsFunctor_additive : (globalSectionsFunctor C X).Additive where
  map_add {A B} f g := by
    change (((evaluation (Opens X)ᵒᵖ C).obj (op (⊤ : Opens X))).map
      ((TopCat.Sheaf.forget C X).map (f + g))) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

instance globalSectionsFunctor_preservesFiniteLimits (X : TopCat.{w}) :
    PreservesFiniteLimits (globalSectionsFunctor AddCommGrpCat.{w} X) := by
  let : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op (⊤ : Opens X))) :=
    inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{w} X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op (⊤ : Opens X)))

/-- The cochain complex obtained by applying global sections degreewise. -/
abbrev globalSectionsComplex (K : CochainComplex (Sheaf C X) ℤ) :
    CochainComplex C ℤ :=
  ((globalSectionsFunctor C X).mapHomologicalComplex (.up ℤ)).obj K

end TopCat.Sheaf
