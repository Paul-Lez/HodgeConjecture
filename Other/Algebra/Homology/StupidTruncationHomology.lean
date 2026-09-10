/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.StupidTruncation
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Homology of a stupid truncation

For a cochain complex, inclusion of the stupid truncation in degrees at least
`p` is surjective on cohomology in degree `p` and is an isomorphism in every
higher degree.  The boundary assertion records the elementary fact that every
degree-`p` cohomology class has a representative in the stupid truncation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- Every cohomology class in a retained degree is represented by the stupid
truncation.  At the cutoff this map need not be injective. -/
theorem epi_homologyMap_stupidTruncInclusion
    (K : CochainComplex C ℤ) (p n : ℤ) (hpn : p ≤ n) :
    Epi (HomologicalComplex.homologyMap
      (HomologicalComplex.stupidTruncInclusion K
        (ComplexShape.embeddingUpIntGE p)) n) := by
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map
    (HomologicalComplex.stupidTruncInclusion K
      (ComplexShape.embeddingUpIntGE p))
  have h₂ : IsIso φ.τ₂ := by
    dsimp [φ]
    rw [HomologicalComplex.stupidTruncInclusion_f K _
      (i := (n - p).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        rw [Int.toNat_of_nonneg (by omega)]
        omega)]
    infer_instance
  have h₃ : IsIso φ.τ₃ := by
    dsimp [φ]
    rw [CochainComplex.next]
    rw [HomologicalComplex.stupidTruncInclusion_f K _
      (i := (n + 1 - p).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        rw [Int.toNat_of_nonneg (by omega)]
        omega)]
    infer_instance
  have : Epi (ShortComplex.cyclesMap φ) := by
    haveI : IsIso φ.τ₂ := h₂
    haveI : IsIso φ.τ₃ := h₃
    infer_instance
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap' φ this

/-- Above the cutoff, stupid truncation does not change cohomology. -/
theorem isIso_homologyMap_stupidTruncInclusion
    (K : CochainComplex C ℤ) (p n : ℤ) (hpn : p < n) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.stupidTruncInclusion K
        (ComplexShape.embeddingUpIntGE p)) n) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  rw [quasiIsoAt_iff'
    _ (n - 1) n (n + 1) (by simp) (by simp)]
  let φ := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
    (n - 1) n (n + 1)).map
      (HomologicalComplex.stupidTruncInclusion K
        (ComplexShape.embeddingUpIntGE p))
  have h₁ : Epi φ.τ₁ := by
    dsimp [φ]
    rw [HomologicalComplex.stupidTruncInclusion_f K _
      (i := (n - 1 - p).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        rw [Int.toNat_of_nonneg (by omega)]
        omega)]
    infer_instance
  have h₂ : IsIso φ.τ₂ := by
    dsimp [φ]
    rw [HomologicalComplex.stupidTruncInclusion_f K _
      (i := (n - p).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        rw [Int.toNat_of_nonneg (by omega)]
        omega)]
    infer_instance
  have h₃ : Mono φ.τ₃ := by
    dsimp [φ]
    rw [HomologicalComplex.stupidTruncInclusion_f K _
      (i := (n + 1 - p).toNat) (by
        simp only [ComplexShape.embeddingUpIntGE_f]
        rw [Int.toNat_of_nonneg (by omega)]
        omega)]
    infer_instance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- Elementwise form of `epi_homologyMap_stupidTruncInclusion` for complexes
of abelian groups. -/
theorem homologyMap_stupidTruncInclusion_surjective
    (K : CochainComplex AddCommGrpCat ℤ) (p n : ℤ) (hpn : p ≤ n) :
    Function.Surjective (HomologicalComplex.homologyMap
      (HomologicalComplex.stupidTruncInclusion K
        (ComplexShape.embeddingUpIntGE p)) n) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  exact epi_homologyMap_stupidTruncInclusion K p n hpn

/-- Every retained cohomology class has an explicit preimage in the stupid
truncation. -/
theorem exists_stupidTrunc_homology_lift
    (K : CochainComplex AddCommGrpCat ℤ) (p n : ℤ) (hpn : p ≤ n)
    (a : K.homology n) :
    ∃ b : (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).homology n,
      HomologicalComplex.homologyMap
        (HomologicalComplex.stupidTruncInclusion K
          (ComplexShape.embeddingUpIntGE p)) n b = a :=
  homologyMap_stupidTruncInclusion_surjective K p n hpn a

end CochainComplex
