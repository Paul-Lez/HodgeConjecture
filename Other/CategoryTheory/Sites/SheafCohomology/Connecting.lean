/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! The connecting homomorphism in sheaf cohomology. -/

@[expose] public noncomputable section

universe w' w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- The connecting homomorphism associated to a short exact sequence of abelian sheaves. -/
def H.δ (hS : S.ShortExact) (n : ℕ) : H S.X₃ n →+ H S.X₁ (n + 1) :=
  hS.extClass.postcomp ((constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) rfl

end CategoryTheory.Sheaf
