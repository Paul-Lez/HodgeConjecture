/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone
public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
/-! # Canonical natural relative-cochain cone comparison

The explicit short-exact-sequence lift is natural already before passage to homology.

The lift is positive `(inclusion, 0)`; Mathlib's cone connecting morphism is the negative first
projection. Their composite is displayed below.

Agreement with `relativeCochainConeCohomologyEquiv`, which is built from a completed triangle map,
is a separate comparison theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- Canonical comparison from integer dual-relative cohomology to its
restriction cone, induced by the positive `(inclusion, 0)` lift. -/
def relativeDualCochainHomologyIsoCone (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≅
      (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone
    (relativeDualCochainShortComplexInt R X)
    (relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

/-- Integer dual-relative cohomology computes `RelativeCohomology` by the evaluation pairing. -/
def relativeDualCochainCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≃ₗ[R]
      RelativeCohomology R X n :=
  (((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv

/-- Relative cohomology computed from the explicit canonical cone lift. -/
def relativeCochainConeCohomologyEquivCanonical (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R] RelativeCohomology R X n :=
  (relativeDualCochainHomologyIsoCone R X n).symm.toLinearEquiv.trans
    (relativeDualCochainCohomologyEquiv R X n)

end AlgebraicTopology.Singular
