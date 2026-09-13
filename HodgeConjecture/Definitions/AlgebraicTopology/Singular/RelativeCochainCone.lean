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

public import HodgeConjecture.Mathlib.Algebra.Homology.DualExact
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Relative singular cohomology as a cochain mapping cone

For a topological pair `A ⊆ X`, restriction of singular cochains is the algebraic dual of
the inclusion `C_*(A) ⟶ C_*(X)`.  This file proves, without a finite-dimensionality
hypothesis, that the cohomology in degree `n - 1` of its mapping cone is `H^n(X, A)`, the
degree-`n` cohomology of the dual relative cochain complex.

The proof dualizes the degreewise short exact sequence
`C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)`, extends the resulting cochain complexes by zero to
integer degrees, and compares its rotated triangle with Mathlib's mapping-cone triangle.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
/-- The dual relative, ambient, and subspace cochain complexes in nonnegative degrees. -/
def relativeDualCochainShortComplexNat (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (HomologicalComplex.linearDualMap (relativeChainProjection R X))
    (HomologicalComplex.linearDualMap ((chainPairFunctor R).obj X).hom)
    (by
      ext n φ
      change Module.Dual R (((relativeChainFunctor R).obj X).X n) at φ
      apply LinearMap.ext
      intro x
      change φ (((((chainPairFunctor R).obj X).hom ≫
        relativeChainProjection R X).f n).hom x) = 0
      rw [subspaceChainMap_relativeChainProjection]
      exact map_zero φ)

/-- The dual relative, ambient, and subspace cochain complexes, extended by zero to integer
degrees. -/
def relativeDualCochainShortComplexInt (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (relativeDualCochainShortComplexNat R X).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))

/-- Restriction from ambient singular cochains to subspace singular cochains, in integer
degrees. -/
def relativeCochainRestrictionInt (X : TopPair.{u}) :
    ((SingularChainComplex R X.fst).linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat) ⟶
      (((chainPairFunctor R).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
    (HomologicalComplex.linearDualMap ((chainPairFunctor R).obj X).hom)
    ComplexShape.embeddingUpNat

@[simp]
lemma relativeDualCochainShortComplexInt_g (X : TopPair.{u}) :
    (relativeDualCochainShortComplexInt R X).g = relativeCochainRestrictionInt R X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a nonnegative degree, evaluation of the integer extension recovers evaluation of the
original nonnegative short complex. -/
def relativeDualCochainShortComplexIntEvalIso (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (n : ℤ)) ≅
      (relativeDualCochainShortComplexNat R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) := by
  have hn : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  refine ShortComplex.isoMk
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
