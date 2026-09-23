/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# The Hom complex out of an object in degree zero

For an object `X` and a cochain complex `K`, the Hom complex from `X[0]` to `K` is the complex
`n ↦ Hom(X, K^n)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be a preadditive category with a zero object, `X` an object, and `K` an integer-indexed
cochain complex in `C`. This identifies the Hom complex from `X[0]` to `K` with the complex of
abelian groups `n ↦ Hom_C(X, K^n)`, whose differential is postcomposition with the differential
of `K`. -/
def fromSingleZeroIsoPreadditiveCoyoneda (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (.op X)).mapHomologicalComplex
        ℤᵘᵖ).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (p := 0) (q := n) (n := n)
      (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      apply AddCommGrpCat.hom_ext
      ext z
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
      have he : Cochain.fromSingleEquiv (zero_add j)
          (CochainComplex.HomComplex.δ i j
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
        simp
      have hleft : (preadditiveCoyoneda.obj (.op X)).map (K.d i j)
          (Cochain.fromSingleEquiv (zero_add i)
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.fromSingleEquiv_fromSingleMk]
        rfl
      have hcalc := hleft.trans he.symm
      simp only [AddCommGrpCat.comp_apply, AddEquiv.toAddCommGrpIso_hom,
        Functor.mapHomologicalComplex_obj_d]
      convert hcalc using 1 <;> rfl)

end CochainComplex.HomComplex

end
