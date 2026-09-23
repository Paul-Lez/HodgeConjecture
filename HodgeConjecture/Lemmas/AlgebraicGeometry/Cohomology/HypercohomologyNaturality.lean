/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.HypercohomologyNaturality

/-!
# Naturality of the hypercohomology/global-sections comparison

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.HypercohomologyNaturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

@[simp]
lemma isoHomCongrAddEquiv_apply
    {C : Type*} [Category* C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) :
    isoHomCongrAddEquiv eA eB f = eA.inv ≫ f ≫ eB.hom := rfl

end AlgebraicGeometry.ComplexPoint
