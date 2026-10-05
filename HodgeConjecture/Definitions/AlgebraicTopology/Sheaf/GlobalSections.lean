/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Topology.Sheaves.Abelian

/-! # Global sections of sheaves and sheaf complexes -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u v w

variable (C : Type u) [Category.{v} C] (X : TopCat.{w})

/-- Evaluation of a sheaf on the top open subset. -/
def globalSections : Sheaf C X ⥤ C :=
  (sheafSections (Opens.grothendieckTopology X) C).obj (op (⊤ : Opens X))

/-- Notation for the global sections functor. -/
scoped notation3:max "Γ[" C "](" X ")" => globalSections C X

open scoped TopCat.Sheaf

variable [Abelian C] [HasSheafify (Opens.grothendieckTopology X) C]

instance sheaf_linear (R : Type*) [Semiring R] [Linear R C] : Linear R (Sheaf C X) := by
  change Linear R (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)
  infer_instance

instance globalSections_additive : (globalSections C X).Additive where
  map_add {A B} f g := by
    change (((evaluation (Opens X)ᵒᵖ C).obj (op (⊤ : Opens X))).map
      ((TopCat.Sheaf.forget C X).map (f + g))) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

instance globalSections_linear (R : Type*) [Semiring R] [Linear R C] :
    Functor.Linear R (globalSections C X) where
  map_smul _ _ := rfl

instance globalSections_preservesFiniteLimits (X : TopCat.{w}) :
    PreservesFiniteLimits (globalSections AddCommGrpCat.{w} X) := by
  let : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op (⊤ : Opens X))) :=
    inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{w} X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op (⊤ : Opens X)))

/-- The cochain complex obtained by applying global sections degreewise. -/
abbrev globalSectionsComplex {C : Type u} [Category.{v} C] (X : TopCat.{w}) [Abelian C]
    [HasSheafify (Opens.grothendieckTopology X) C]
    (K : CochainComplex (Sheaf C X) ℤ) :
    CochainComplex C ℤ :=
  ((Γ[C](X)).mapHomologicalComplex ℤᵘᵖ).obj K

end TopCat.Sheaf
