/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.RelativeCochainCone
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Relative singular cohomology as a cochain mapping cone

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.RelativeCochainCone`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section
open CategoryTheory Limits
open CategoryTheory.Pretriangulated
universe u
namespace AlgebraicTopology.Singular
variable (R : Type u) [CommRing R]

@[simp]
lemma relativeDualCochainShortComplexInt_g (X : TopPair.{u}) :
    (relativeDualCochainShortComplexInt R X).g = relativeCochainRestrictionInt R X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a nonnegative degree, evaluation of the integer extension recovers evaluation of the
original nonnegative short complex. -/
def relativeDualCochainShortComplexIntEvalIso (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) ℤᵘᵖ (n : ℤ)) ≅
      (relativeDualCochainShortComplexNat R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) :=
  have hn : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  ShortComplex.isoMk
    ((relativeDualCochainShortComplexNat R X).X₁.extendXIso
      ComplexShape.embeddingUpNat hn)
    ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
      ComplexShape.embeddingUpNat hn)
    ((relativeDualCochainShortComplexNat R X).X₃.extendXIso
      ComplexShape.embeddingUpNat hn)
    (by
      change ((relativeDualCochainShortComplexNat R X).X₁.extendXIso
          ComplexShape.embeddingUpNat hn).hom ≫
            (relativeDualCochainShortComplexNat R X).f.f n =
        (HomologicalComplex.extendMap
          (relativeDualCochainShortComplexNat R X).f
          ComplexShape.embeddingUpNat).f (n : ℤ) ≫
            ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
              ComplexShape.embeddingUpNat hn).hom
      rw [HomologicalComplex.extendMap_f _ _ hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
          ComplexShape.embeddingUpNat hn).hom ≫
            (relativeDualCochainShortComplexNat R X).g.f n =
        (HomologicalComplex.extendMap
          (relativeDualCochainShortComplexNat R X).g
          ComplexShape.embeddingUpNat).f (n : ℤ) ≫
            ((relativeDualCochainShortComplexNat R X).X₃.extendXIso
              ComplexShape.embeddingUpNat hn).hom
      rw [HomologicalComplex.extendMap_f _ _ hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end AlgebraicTopology.Singular
end

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- A degreewise splitting of the dual singular-chain sequence of a pair. -/
def relativeDualCochainShortComplexNatDegreewiseSplitting (X : TopPair.{u}) (n : ℕ) :
    ((relativeDualCochainShortComplexNat R X).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n)).Splitting := by
  -- Split the chain sequence in degree `n`, then dualise the splitting.
  have hT := ((HomologicalComplex.shortExact_iff_degreewise_shortExact
    (relativeChainShortComplex R X)).mp (relativeChainShortComplex_shortExact R X)) n
  let sm := (relativeChainMap_isSplitMono R X n).exists_splitMono.some
  exact (ShortComplex.Splitting.ofExactOfRetraction _ hT.exact sm.retraction sm.id
    hT.epi_g).linearDual

/-- Dualizing the singular-chain sequence of a pair gives a short exact sequence of
nonnegative cochain complexes. -/
private lemma relativeDualCochainShortComplexNat_shortExact (X : TopPair.{u}) :
    (relativeDualCochainShortComplexNat R X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => (relativeDualCochainShortComplexNatDegreewiseSplitting R X n).shortExact

/-- The integer-indexed dual cochain sequence of a pair is short exact. -/
lemma relativeDualCochainShortComplexInt_shortExact (X : TopPair.{u}) :
    (relativeDualCochainShortComplexInt R X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro z
  by_cases hz : 0 ≤ z
  · have hn : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    let e :
        (relativeDualCochainShortComplexNat R X).map
            (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) z.toNat) ≅
          (relativeDualCochainShortComplexInt R X).map
            (HomologicalComplex.eval (ModuleCat.{u} R) ℤᵘᵖ z) := by
      simpa only [hn] using
        (relativeDualCochainShortComplexIntEvalIso R X z.toNat).symm
    exact ShortComplex.shortExact_of_iso e
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact
        (relativeDualCochainShortComplexNat R X)).mp
          (relativeDualCochainShortComplexNat_shortExact R X)) z.toNat)
  · have hi : ∀ n : ℕ, ComplexShape.embeddingUpNat.f n ≠ z := by
      intro n hn
      apply hz
      rw [← hn]
      exact Int.natCast_nonneg n
    let S := (relativeDualCochainShortComplexInt R X).map
      (HomologicalComplex.eval (ModuleCat.{u} R) ℤᵘᵖ z)
    have h₁ : IsZero S.X₁ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₁.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    have h₂ : IsZero S.X₂ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₂.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    have h₃ : IsZero S.X₃ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₃.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    exact ShortComplex.Splitting.shortExact
      { r := 0
        s := 0
        f_r := h₁.eq_of_src _ _
        s_g := h₃.eq_of_tgt _ _
        id := h₂.eq_of_src _ _ }

end AlgebraicTopology.Singular

end
