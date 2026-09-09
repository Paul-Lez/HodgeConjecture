/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The first stupid truncation of a nonnegative cochain complex

The positive-degree truncation, the original complex, and its degree-zero term form a short
exact sequence. The maps are the actual stupid-truncation inclusion and degree-zero projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ) [K.IsStrictlyGE 0]

/-- Projection of a nonnegative complex to its degree-zero term. -/
def toDegreeZero : K ⟶ (singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = 0) =>
    (K.isZero_of_isStrictlyGE 0 i (by omega)).eq_of_src _ _)

@[simp]
theorem toDegreeZero_f_zero : (toDegreeZero K).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [toDegreeZero, HomologicalComplex.mkHomToSingle_f]

/-- The positive-degree inclusion has zero degree-zero projection. -/
@[reassoc (attr := simp)]
theorem stupidTruncInclusion_comp_toDegreeZero :
    HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE 1) ≫
      K.toDegreeZero = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  exact (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) 0
    (by intro i; simp; omega)).eq_of_src _ _

/-- The sequence retaining precisely the actual first stupid truncation. -/
def firstStupidTruncationSequence : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE 1))
    K.toDegreeZero (K.stupidTruncInclusion_comp_toDegreeZero)

/-- The first stupid-truncation sequence is short exact in every degree. -/
theorem firstStupidTruncationSequence_shortExact :
    K.firstStupidTruncationSequence.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : i = 0
  · subst i
    have hz := K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) 0
      (by intro i; simp; omega)
    have hg : (K.firstStupidTruncationSequence.map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) 0)).g =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv :=
      K.toDegreeZero_f_zero
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · apply (ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)).2
      rw [hg]
      infer_instance
    · exact hz.mono _
    · rw [hg]
      infer_instance
  · by_cases hpos : 0 < i
    · have hi' : (ComplexShape.embeddingUpIntGE 1).f (i - 1).toNat = i := by
        simp only [ComplexShape.embeddingUpIntGE_f]
        omega
      have hf : IsIso ((K.firstStupidTruncationSequence.map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).f) := by
        change IsIso ((HomologicalComplex.stupidTruncInclusion K
          (ComplexShape.embeddingUpIntGE 1)).f i)
        rw [HomologicalComplex.stupidTruncInclusion_f K _ hi']
        infer_instance
      have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) i hi
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · exact (ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)).2 inferInstance
      · infer_instance
      · exact hz.epi _
    · have hz := K.isZero_of_isStrictlyGE 0 i (by omega)
      have hz₁ := K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE 1) i
        (by intro j; simp; omega)
      have hz₃ := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) i hi
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz)
        (hz₁.mono _) (hz₃.epi _)

end CochainComplex
