/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Postcomposition and naturality for the Hom complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ} (f : L ⟶ M)

/-- Let `K,L,M` be integer-indexed cochain complexes in an abelian category and `f : L → M` a
cochain map. Postcomposition sends a degree-`n` cocycle `z` of `Hom(K,L)` to the cocycle `f ∘ z`
of `Hom(K,M)`. This is the resulting additive map. -/
def postcompCocycle (n : ℤ) : Cocycle K L n →+ Cocycle K M n where
  toFun z := z.postcomp f
  map_zero' := by ext; simp [Cocycle.postcomp]
  map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp]

/-- Let `K,L,M` be integer-indexed cochain complexes in an abelian category and `f : L → M` a
cochain map. This additive map `H^n(Hom(K,L)) → H^n(Hom(K,M))` sends the class of a cocycle `z`
to the class of `f ∘ z`. Postcomposition preserves coboundaries, so it is well-defined on
cohomology. -/
def postcompClass (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K M n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K M n).comp (postcompCocycle K f n)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.postcomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, a.comp (Cochain.ofHom f) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, ha]
      rfl)

@[simp]
lemma postcompClass_mk (n : ℤ) (z : Cocycle K L n) :
    postcompClass K f n (CohomologyClass.mk z) = CohomologyClass.mk (z.postcomp f) := rfl

end CochainComplex.HomComplex
