/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation

/-!
# Lifting maps to a stupid truncation

A map from a complex supported in retained degrees factors canonically through the target's
stupid truncation. This is used to construct filtered de Rham maps from complexes of closed forms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
  (e : c.Embedding c') [e.IsTruncGE]
  {K L : HomologicalComplex C c'} [K.IsStrictlySupported e]

/-- The canonical factorization through the retained degrees of the target complex. -/
def liftStupidTrunc (f : K ⟶ L) : K ⟶ L.stupidTrunc e :=
  inv (stupidTruncInclusion K e) ≫ stupidTruncMap f e

/-- Forgetting the truncation recovers the original cochain map exactly. -/
@[reassoc (attr := simp)]
theorem liftStupidTrunc_inclusion (f : K ⟶ L) :
    liftStupidTrunc e f ≫ stupidTruncInclusion L e = f := by
  rw [liftStupidTrunc, Category.assoc, stupidTruncMap_comp_stupidTruncInclusion,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end HomologicalComplex
