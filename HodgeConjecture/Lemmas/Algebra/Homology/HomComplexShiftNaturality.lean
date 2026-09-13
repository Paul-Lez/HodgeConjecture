/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.HomComplexPostcompNaturality

/-! # Hom-complex cohomology and target shifts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

end CategoryTheory.ShortComplex

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (A K : CochainComplex C ℤ) (s n n' : ℤ) (h : n + s = n')

/-- Unshift the target on cocycles. -/
def rightUnshiftCocycle : Cocycle A (K⟦s⟧) n →+ Cocycle A K n' where
  toFun z := z.rightUnshift n' h
  map_zero' := by ext; simp [Cocycle.rightUnshift]
  map_add' _ _ := by ext; simp [Cocycle.rightUnshift, Cochain.rightUnshift_add]

/-- Target unshifting descends through actual coboundaries. The factor
`(-1)^s` is included in the witnessing primitive. -/
def rightUnshiftClass : CohomologyClass A (K⟦s⟧) n →+ CohomologyClass A K n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom A K n').comp (rightUnshiftCocycle A K s n n' h)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.rightUnshift n' h) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + s, by omega,
        s.negOnePow • a.rightUnshift (m + s) rfl, ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift a (m + s) rfl n' n h, ha,
        smul_smul, Int.units_mul_self, one_smul]
      rfl)

@[simp]
lemma rightUnshiftClass_mk (z : Cocycle A (K⟦s⟧) n) :
    rightUnshiftClass A K s n n' h (CohomologyClass.mk z) =
      CohomologyClass.mk (z.rightUnshift n' h) := rfl

end CochainComplex.HomComplex
