/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Quasi-isomorphisms on kernels in a morphism of short exact complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- In a morphism of short exact sequences of cochain complexes, if the middle
and last maps are quasi-isomorphisms, so is the first map. -/
lemma quasiIso_first_of_shortExact
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) [QuasiIso f.τ₂] [QuasiIso f.τ₃] :
    QuasiIso f.τ₁ := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).mp
  exact isIso₁_of_isIso₂₃ (DerivedCategory.triangleOfSES.map hS hT f)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hT)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₂)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₃)))

end CochainComplex
